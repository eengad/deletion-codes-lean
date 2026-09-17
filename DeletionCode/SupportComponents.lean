import DeletionCode.RootSelection
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Card

/-!
Components of actual consecutive-window de Bruijn paths.

Vertices are the (L-1)-bit substrings of the family's finite word paths.
An edge is a consecutive pair of those vertices coming from a valid L-window;
it is not a clique on a bubble's vertices. If a bubble's two paths have the
same initial vertex, family connectedness agrees with connectedness of their
representatives in this graph. SignedSupport identifies this edge union with
the nonzero signed-spectrum supports of manuscript rules.
-/

namespace DeletionCode.SupportComponents

open Windows RootSelection

abbrev Vertex (L : ℕ) := Fin (L - 1) → Bool

/-- The actual vertex at a specified offset on a word path. -/
def vertex {B : Type*} (F : Family B) (L : ℕ) (b : B) (side : Bool)
    (i : ℕ) : Vertex L :=
  fun q => F.path b side (i + q.val)

/-- A vertex belongs to a bubble if it occurs on either of its finite paths. -/
def HasVertex {B : Type*} (F : Family B) (L : ℕ) (b : B) (v : Vertex L) : Prop :=
  ∃ side i, i ≤ F.extra b side + 1 ∧ v = vertex F L b side i

/-- Directed edges are precisely the consecutive vertices of valid L-windows. -/
def Edge {B : Type*} (F : Family B) (L : ℕ) (u v : Vertex L) : Prop :=
  ∃ b side i, i ≤ F.extra b side ∧
    u = vertex F L b side i ∧ v = vertex F L b side (i + 1)

/-- Undirected connectedness in the union of these actual path edges. -/
def GraphConnected {B : Type*} (F : Family B) (L : ℕ) : Vertex L → Vertex L → Prop :=
  Relation.EqvGen (Edge F L)

def representative {B : Type*} (F : Family B) (L : ℕ) (b : B) : Vertex L :=
  vertex F L b false 0

theorem vertex_eq_iff_agree {B : Type*} (F : Family B) (L : ℕ)
    (a b : B) (sa sb : Bool) (i j : ℕ) :
    vertex F L a sa i = vertex F L b sb j ↔
      Agree (F.path a sa) i (F.path b sb) j (L - 1) := by
  constructor
  · intro h q hq
    exact congrFun h ⟨q, hq⟩
  · intro h
    funext q
    exact h q.val q.isLt

/-- A path's first vertex reaches every one of its vertices via its own edges. -/
theorem path_connected {B : Type*} (F : Family B) (L : ℕ)
    (b : B) (side : Bool) (i : ℕ) (hi : i ≤ F.extra b side + 1) :
    GraphConnected F L (vertex F L b side 0) (vertex F L b side i) := by
  induction i with
  | zero => exact Relation.EqvGen.refl _
  | succ i ih =>
    have hprev := ih (by omega)
    have he : Edge F L (vertex F L b side i) (vertex F L b side (i + 1)) :=
      ⟨b, side, i, by omega, rfl, rfl⟩
    exact Relation.EqvGen.trans _ _ _ hprev (Relation.EqvGen.rel _ _ he)

/-- Common initial vertices connect both paths to the negative-first representative. -/
theorem representative_connected {B : Type*} (F : Family B) (L : ℕ)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    (b : B) (side : Bool) (i : ℕ) (hi : i ≤ F.extra b side + 1) :
    GraphConnected F L (representative F L b) (vertex F L b side i) := by
  cases side with
  | false => exact path_connected F L b false i hi
  | true =>
    change GraphConnected F L (vertex F L b false 0) (vertex F L b true i)
    rw [hstart b]
    exact path_connected F L b true i hi

/-- All vertices of one bubble are internally connected by its actual path edges. -/
theorem bubble_vertices_connected {B : Type*} (F : Family B) (L : ℕ)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    (b : B) (u v : Vertex L) (hu : HasVertex F L b u) (hv : HasVertex F L b v) :
    GraphConnected F L u v := by
  obtain ⟨su, i, hi, rfl⟩ := hu
  obtain ⟨sv, j, hj, rfl⟩ := hv
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (representative_connected F L hstart b su i hi))
    (representative_connected F L hstart b sv j hj)

/-- Two owners of the same concrete vertex are adjacent in the family. -/
theorem same_vertex_adjacent {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (a b : B) (v : Vertex L) (ha : HasVertex F L a v) (hb : HasVertex F L b v) :
    F.Adjacent L a b := by
  obtain ⟨sa, i, hi, hai⟩ := ha
  obtain ⟨sb, j, hj, hbj⟩ := hb
  refine ⟨sa, sb, i, j, hi, hj, by omega, by omega, ?_⟩
  exact (vertex_eq_iff_agree F L a b sa sb i j).mp (hai.symm.trans hbj)

theorem edge_owners {B : Type*} (F : Family B) (L : ℕ)
    {u v : Vertex L} (h : Edge F L u v) :
    ∃ b, HasVertex F L b u ∧ HasVertex F L b v := by
  obtain ⟨b, side, i, hi, hu, hv⟩ := h
  exact ⟨b, ⟨side, i, by omega, hu⟩, ⟨side, i + 1, by omega, hv⟩⟩

/-- Graph connectedness preserves membership in the vertex union. -/
theorem supported_iff {B : Type*} (F : Family B) (L : ℕ)
    {u v : Vertex L} (h : GraphConnected F L u v) :
    (∃ b, HasVertex F L b u) ↔ (∃ b, HasVertex F L b v) := by
  induction h with
  | rel u v he =>
    obtain ⟨b, hu, hv⟩ := edge_owners F L he
    exact ⟨fun _ => ⟨b, hv⟩, fun _ => ⟨b, hu⟩⟩
  | refl u => exact Iff.rfl
  | symm u v h ih => exact ih.symm
  | trans u v w huv hvw ihu ihv => exact ihu.trans ihv

/-- A path in the consecutive-window graph joins the families owning its endpoints. -/
theorem graph_connected_owners {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    {u v : Vertex L} (h : GraphConnected F L u v) :
    ∀ a b, HasVertex F L a u → HasVertex F L b v → F.Connected L a b := by
  induction h with
  | rel u v he =>
    intro a b ha hb
    obtain ⟨c, hcU, hcV⟩ := edge_owners F L he
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.rel _ _ (same_vertex_adjacent F L hL a c u ha hcU))
      (Relation.EqvGen.rel _ _ (same_vertex_adjacent F L hL c b v hcV hb))
  | refl u =>
    intro a b ha hb
    exact Relation.EqvGen.rel _ _ (same_vertex_adjacent F L hL a b u ha hb)
  | symm u v h ih =>
    intro a b ha hb
    exact Relation.EqvGen.symm _ _ (ih b a hb ha)
  | trans u v w huv hvw ihu ihv =>
    intro a b ha hb
    obtain ⟨c, hc⟩ := (supported_iff F L huv).mp ⟨a, ha⟩
    exact Relation.EqvGen.trans _ _ _ (ihu a c ha hc) (ihv c b hc hb)

/-- Sharing a true vertex joins the representatives using each bubble's path edges. -/
theorem adjacent_representatives_connected {B : Type*} (F : Family B) (L : ℕ)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    {a b : B} (h : F.Adjacent L a b) :
    GraphConnected F L (representative F L a) (representative F L b) := by
  obtain ⟨sa, sb, i, j, hi, hj, _, _, hagree⟩ := h
  have heq := (vertex_eq_iff_agree F L a b sa sb i j).mpr hagree
  have ha := representative_connected F L hstart a sa i hi
  have hb := representative_connected F L hstart b sb j hj
  rw [heq] at ha
  exact Relation.EqvGen.trans _ _ _ ha (Relation.EqvGen.symm _ _ hb)

/-- Family components equal components of the actual consecutive-window edge union. -/
theorem connected_iff_graph_connected {B : Type*} (F : Family B) (L : ℕ)
    (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    (a b : B) :
    F.Connected L a b ↔
      GraphConnected F L (representative F L a) (representative F L b) := by
  constructor
  · intro h
    induction h with
    | rel a b hab => exact adjacent_representatives_connected F L hstart hab
    | refl a => exact Relation.EqvGen.refl _
    | symm a b h ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c hab hbc ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc
  · intro h
    exact graph_connected_owners F L hL h a b
      ⟨false, 0, by omega, rfl⟩ ⟨false, 0, by omega, rfl⟩

/-- The setoid of actual path-family components. -/
def componentSetoid {B : Type*} (F : Family B) (L : ℕ) : Setoid B where
  r := F.Connected L
  iseqv := ⟨fun b => Relation.EqvGen.refl b,
    fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩

/-- Only vertices present on the family's paths enter the support graph. -/
def SupportedVertex {B : Type*} (F : Family B) (L : ℕ) :=
  {v : Vertex L // ∃ b, HasVertex F L b v}

/-- Graph components restricted to the actual vertex union, excluding isolated outsiders. -/
def supportedGraphSetoid {B : Type*} (F : Family B) (L : ℕ) :
    Setoid (SupportedVertex F L) where
  r := fun u v => GraphConnected F L u.val v.val
  iseqv := ⟨fun v => Relation.EqvGen.refl v.val,
    fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩

abbrev Components {B : Type*} (F : Family B) (L : ℕ) :=
  Quotient (componentSetoid F L)

abbrev GraphComponents {B : Type*} (F : Family B) (L : ℕ) :=
  Quotient (supportedGraphSetoid F L)

def supportedRepresentative {B : Type*} (F : Family B) (L : ℕ) (b : B) :
    SupportedVertex F L :=
  ⟨representative F L b, b, false, 0, by omega, rfl⟩

/-- Sending a bubble to its first negative vertex induces a map of component quotients. -/
def componentMap {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0) :
    Components F L → GraphComponents F L :=
  Quotient.map (supportedRepresentative F L) (fun a b hab =>
    (connected_iff_graph_connected F L hL hstart a b).mp hab)

theorem componentMap_injective {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0) :
    Function.Injective (componentMap F L hL hstart) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro a b h
  apply Quotient.sound
  apply (connected_iff_graph_connected F L hL hstart a b).mpr
  exact Quotient.exact h

theorem componentMap_surjective {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0) :
    Function.Surjective (componentMap F L hL hstart) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro v
  obtain ⟨b, side, i, hi, hv⟩ := v.property
  refine ⟨Quotient.mk (componentSetoid F L) b, ?_⟩
  apply Quotient.sound
  change GraphConnected F L (representative F L b) v.val
  rw [hv]
  exact representative_connected F L hstart b side i hi

/-- The family and actual supported graph have exactly the same components. -/
noncomputable def componentEquiv {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0) :
    Components F L ≃ GraphComponents F L :=
  Equiv.ofBijective (componentMap F L hL hstart)
    ⟨componentMap_injective F L hL hstart, componentMap_surjective F L hL hstart⟩

/-- Consequently any finite cardinality representations give the same component count. -/
theorem component_card_eq {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    [Fintype (Components F L)] [Fintype (GraphComponents F L)] :
    Fintype.card (Components F L) = Fintype.card (GraphComponents F L) :=
  Fintype.card_congr (componentEquiv F L hL hstart)

/-- Every vertex in the actual support graph reaches a root whose full negative
word occurs contiguously in x. No extra isolated ambient vertices are asserted
to have roots. -/
theorem graph_component_root_subword {B : Type*} (F : Family B)
    (x : Letters) (n k L : ℕ) (hx : KUnique x n k) (hk : k < L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    (hgen : F.Generating x n L) (v : SupportedVertex F L) :
    ∃ r a, GraphConnected F L v.val (representative F L r) ∧
      a + (L + F.extra r false) ≤ n ∧
      Agree x a (F.path r false) 0 (L + F.extra r false) := by
  obtain ⟨b, side, i, hi, hv⟩ := v.property
  obtain ⟨r, a, hr, ha, hagree⟩ := F.component_root_subword x n k L hx hk hgen b
  have hroot := (connected_iff_graph_connected F L (by omega) hstart r b).mp hr
  have hvb : GraphConnected F L v.val (representative F L b) := by
    rw [hv]
    exact Relation.EqvGen.symm _ _ (representative_connected F L hstart b side i hi)
  exact ⟨r, a, Relation.EqvGen.trans _ _ _ hvb (Relation.EqvGen.symm _ _ hroot),
    ha, hagree⟩

#print axioms path_connected
#print axioms bubble_vertices_connected
#print axioms graph_connected_owners
#print axioms connected_iff_graph_connected
#print axioms componentEquiv
#print axioms component_card_eq
#print axioms graph_component_root_subword

end DeletionCode.SupportComponents
