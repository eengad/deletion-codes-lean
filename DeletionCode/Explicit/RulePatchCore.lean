import DeletionCode.Explicit.CoreCatalogue
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! The rule–patch multigraph, its deterministic peeling, and manuscript `d:core`. -/

namespace DeletionCode.Explicit.RulePatch

open FieldHash

variable {d s c : ℕ}

/-- Bubble `(i,j)` is the `j`th edge of rule `i`; parallel edges have distinct indices. -/
abbrev Incidence (d s c : ℕ) := Fin d × Fin s → Fin c

def edges (S : Finset (Fin d)) : Finset (Fin d × Fin s) := S ×ˢ Finset.univ

def patches (a : Incidence d s c) (S : Finset (Fin d)) := (edges S).image a

def atPatch (a : Incidence d s c) (S : Finset (Fin d)) (p : Fin c) :=
  (edges S).filter (fun e => a e = p)

/-- The bubble edges in chronological order. -/
def edgeList (d s : ℕ) : List (Fin d × Fin s) :=
  (List.finRange d).flatMap (fun i => (List.finRange s).map (fun j => (i,j)))

@[simp] theorem mem_edgeList (e : Fin d × Fin s) : e ∈ edgeList d s := by
  obtain ⟨i,j⟩ := e
  simp [edgeList]

/-- Fixed tie order: first by rule index, then by bubble index within that rule. -/
def pivot (a : Incidence d s c) (S : Finset (Fin d)) : Option (Fin d × Fin s) :=
  (edgeList d s).find? (fun e => decide (e.1 ∈ S ∧ (atPatch a S (a e)).card = 1))

theorem pivot_spec {a : Incidence d s c} {S : Finset (Fin d)} {e : Fin d × Fin s}
    (h : pivot a S = some e) : e.1 ∈ S ∧ (atPatch a S (a e)).card = 1 := by
  unfold pivot at h
  have hh := List.find?_some (p := fun z : Fin d × Fin s =>
    decide (z.1 ∈ S ∧ (atPatch a S (a z)).card = 1)) h
  exact of_decide_eq_true hh

theorem pivot_none_iff (a : Incidence d s c) (S : Finset (Fin d)) :
    pivot a S = none ↔ ∀ e : Fin d × Fin s, e.1 ∈ S → (atPatch a S (a e)).card ≠ 1 := by
  simp only [pivot, List.find?_eq_none, mem_edgeList, forall_const, decide_eq_true_eq]
  simp [not_and]

/-- Replayable trace of the pivot bubbles, together with the terminal set of rules.
Only patches hit by surviving edges are retained. -/
def peel (a : Incidence d s c) (S : Finset (Fin d)) :
    List (Fin d × Fin s) × Finset (Fin d) :=
  match _h : pivot a S with
  | none => ([],S)
  | some e =>
    let rest := peel a (S.erase e.1)
    (e :: rest.1, rest.2)
termination_by S.card
decreasing_by
  apply Finset.card_erase_lt_of_mem
  exact (pivot_spec ‹pivot a S = some _›).1

theorem peel_terminal (a : Incidence d s c) (S : Finset (Fin d)) :
    pivot a (peel a S).2 = none ∧ (peel a S).2 ⊆ S := by
  rw [peel]
  split
  next h => exact ⟨h, Finset.Subset.rfl⟩
  next e h =>
    have ih := peel_terminal a (S.erase e.1)
    exact ⟨ih.1, ih.2.trans (Finset.erase_subset ..)⟩
termination_by S.card
decreasing_by
  apply Finset.card_erase_lt_of_mem
  exact (pivot_spec ‹pivot a S = some _›).1

/-- A nonisolated patch at termination contains at least two surviving bubbles. -/
theorem terminal_degree (a : Incidence d s c) (S : Finset (Fin d)) (h : pivot a S = none)
    {p : Fin c} (hp : p ∈ patches a S) : 2 ≤ (atPatch a S p).card := by
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
  have hpos : 0 < (atPatch a S (a e)).card :=
    Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he,rfl⟩⟩
  have hne := (pivot_none_iff a S).mp h e (Finset.mem_product.mp he).1
  omega

theorem patch_bound {t : ℕ} (a : Incidence d (2*t) c) (S : Finset (Fin d))
    (h : pivot a S = none) : (patches a S).card ≤ t * S.card := by
  have hsum : ∑ p ∈ patches a S, (atPatch a S p).card = (edges (s := 2*t) S).card := by
    exact (Finset.card_eq_sum_card_image a (edges S)).symm
  have hle := Finset.sum_le_sum (s := patches a S) (fun p hp => terminal_degree a S h hp)
  rw [hsum] at hle
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, edges, Finset.card_product,
    Finset.card_univ, Fintype.card_fin] at hle
  have twice : S.card * (2*t) = 2 * (t*S.card) := by ring
  omega

#print axioms peel_terminal
#print axioms patch_bound

section ConnectedCount

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

/-- The simple graph is used only for reachability. Edge counts always use the
original index type `E`, including multiple edges with the same endpoints. -/
private def shadow (u v : E → V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun x y => ∃ e, u e = x ∧ v e = y)

private def externalEdges (u v : E → V) (S : Finset V) : Finset E :=
  Finset.univ.filter (fun e => ¬ (u e ∈ S ∧ v e ∈ S))

private theorem crossing {G : SimpleGraph V} (hG : G.Connected)
    {S : Finset V} (hS : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ∃ x ∈ S, ∃ y ∉ S, G.Adj x y := by
  classical
  by_contra! h
  have closed {x y : V} (hx : x ∈ S) (hxy : G.Adj x y) : y ∈ S := by
    by_contra hy
    exact h x hx y hy hxy
  have along {x y : V} (w : G.Walk x y) (hx : x ∈ S) : y ∈ S := by
    induction w with
    | nil => exact hx
    | cons hxy w ih => exact ih (closed hx hxy)
  obtain ⟨x,hx⟩ := hS
  exact hproper (Finset.eq_univ_iff_forall.mpr (fun y => along (hG.preconnected x y).some hx))

/-- Grow a nonempty vertex set one vertex at a time. Each step uses a distinct
edge that was external and is now internal. This works for a disconnected set
inside a connected witness. -/
private theorem outside_count (u v : E → V) (hG : (shadow u v).Connected)
    (S : Finset V) (hS : S.Nonempty) :
    Fintype.card V ≤ S.card + (externalEdges u v S).card := by
  classical
  by_cases hs : S = Finset.univ
  · subst S
    simp
  obtain ⟨x,hx,y,hy,hxy⟩ := crossing hG hS hs
  obtain ⟨e,he⟩ : ∃ e, (u e = x ∧ v e = y) ∨ (u e = y ∧ v e = x) := by
    rcases hxy.2 with ⟨e,h⟩ | ⟨e,h⟩
    · exact ⟨e,Or.inl h⟩
    · exact ⟨e,Or.inr h⟩
  have hsub : externalEdges u v (insert y S) ⊆ externalEdges u v S := by
    intro e he
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, fun h => (Finset.mem_filter.mp he).2
      ⟨Finset.mem_insert_of_mem h.1, Finset.mem_insert_of_mem h.2⟩⟩
  have old : e ∈ externalEdges u v S := by
    rcases he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> simp [externalEdges,h₁,h₂,hx,hy]
  have new : e ∉ externalEdges u v (insert y S) := by
    rcases he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> simp [externalEdges,h₁,h₂,hx]
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hsub,fun h => new (h ▸ old)⟩)
  have ih := outside_count u v hG (insert y S) (Finset.insert_nonempty ..)
  rw [Finset.card_insert_of_notMem hy] at ih
  omega
termination_by Fintype.card V - S.card
decreasing_by
  rw [Finset.card_insert_of_notMem hy]
  have hlt : S.card < Fintype.card V := Finset.card_lt_univ_of_notMem hy
  omega

end ConnectedCount

/-- Reachability of the full rule–patch graph, forgetting multiplicities only
for the connectedness test. -/
def graph (a : Incidence d s c) : SimpleGraph (Fin d ⊕ Fin c) :=
  shadow (fun e : Fin d × Fin s => Sum.inl e.1) (fun e => Sum.inr (a e))

/-- A connected rule–patch multigraph has at least vertices minus one
edges, with parallel edges retained in the count. -/
theorem connected_vertices_le (a : Incidence d s c) (h : (graph a).Connected)
    (root : Fin d ⊕ Fin c) : d+c ≤ d*s+1 := by
  classical
  have hc := outside_count (fun e : Fin d × Fin s => Sum.inl e.1)
    (fun e => Sum.inr (a e)) h ({root} : Finset (Fin d ⊕ Fin c)) (Finset.singleton_nonempty _)
  have he := (externalEdges (fun e : Fin d × Fin s => Sum.inl e.1)
    (fun e => Sum.inr (a e)) ({root} : Finset (Fin d ⊕ Fin c))).card_le_univ
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Finset.card_singleton] at hc he
  omega

/-- Independent cycle count of a connected witness: edges plus one minus vertices. -/
def cycles (d s c : ℕ) := d*s + 1 - (d+c)

theorem vertices_le (a : Incidence d s c) (hc : (graph a).Connected)
    (S : Finset (Fin d)) (hne : S.Nonempty) :
    d+c + S.card*s ≤ S.card + (patches a S).card + d*s := by
  classical
  let U := S.disjSum (patches a S)
  have hu : U.Nonempty := by
    obtain ⟨i,hi⟩ := hne
    exact ⟨Sum.inl i, Finset.inl_mem_disjSum.mpr hi⟩
  have he : externalEdges (fun e : Fin d × Fin s => Sum.inl e.1)
      (fun e => Sum.inr (a e)) U = Finset.univ \ edges S := by
    ext e
    by_cases hi : e.1 ∈ S
    · have hm : e ∈ edges S := Finset.mem_product.mpr ⟨hi,Finset.mem_univ _⟩
      have hp : a e ∈ patches a S := Finset.mem_image_of_mem a hm
      simp [externalEdges,U,hi,hp,hm]
    · simp [externalEdges,U,edges,hi]
  have h := outside_count _ _ hc U hu
  rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _)] at h
  simp only [U, Fintype.card_sum, Fintype.card_fin, Finset.card_disjSum, Finset.card_univ,
    Fintype.card_prod, edges, Finset.card_product] at h
  have hle : S.card*s ≤ d*s := Nat.mul_le_mul_right _ (by simpa using S.card_le_univ)
  omega

/-- The patches, the rule count, and the cycle lower bound in `d:core`. The
premises are the connectedness and cycle cap supplied by `d:first-event`.
The terminal core itself need not be connected. -/
theorem core_bounds {t G : ℕ} (ht : 2 ≤ t) (a : Incidence d (2*t) c)
    (hconn : (graph a).Connected) (hcap : cycles d (2*t) c ≤ G)
    (S : Finset (Fin d)) (hleaf : pivot a S = none) (hne : S.Nonempty) :
    (patches a S).card ≤ t*S.card ∧ 1 ≤ S.card ∧ S.card ≤ (G-1)/(t-1) ∧ t ≤ cycles d (2*t) c := by
  have hp := patch_bound a S hleaf
  have hv := vertices_le a hconn S hne
  have hpos := Finset.card_pos.mpr hne
  have hc : (t-1)*S.card + 1 ≤ cycles d (2*t) c := by
    unfold cycles
    have hmul : (t-1)*S.card + S.card = t*S.card := by
      rw [← Nat.succ_mul, show (t-1).succ = t by omega]
    have htwice : S.card*(2*t) = 2*(t*S.card) := by ring
    omega
  have hm : (t-1)*1 ≤ (t-1)*S.card := Nat.mul_le_mul_left _ hpos
  rw [Nat.mul_one] at hm
  refine ⟨hp,hpos,?_,by omega⟩
  apply (Nat.le_div_iff_mul_le (by omega : 0 < t-1)).mpr
  rw [Nat.mul_comm]
  omega

/-- A legal trace records a unique pivot bubble in its patch at every deletion. -/
inductive LegalTrace (a : Incidence d s c) :
    Finset (Fin d) → List (Fin d × Fin s) → Finset (Fin d) → Prop where
  | stop {S} (h : pivot a S = none) : LegalTrace a S [] S
  | step {S T es e} (hm : e.1 ∈ S) (honly : atPatch a S (a e) = {e})
      (tail : LegalTrace a (S.erase e.1) es T) : LegalTrace a S (e :: es) T

theorem peel_legal (a : Incidence d s c) (S : Finset (Fin d)) :
    LegalTrace a S (peel a S).1 (peel a S).2 := by
  rw [peel]
  split
  next h => exact .stop h
  next e h =>
    obtain ⟨hm,ho⟩ := pivot_spec h
    have he : e ∈ atPatch a S (a e) :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm,Finset.mem_univ _⟩,rfl⟩
    obtain ⟨b,hb⟩ := Finset.card_eq_one.mp ho
    rw [hb, Finset.mem_singleton] at he
    exact .step hm (he ▸ hb) (peel_legal a (S.erase e.1))
termination_by S.card
decreasing_by
  apply Finset.card_erase_lt_of_mem
  exact (pivot_spec ‹pivot a S = some _›).1

def core (a : Incidence d s c) : Finset (Fin d) := (peel a Finset.univ).2

theorem peeled_core_bounds {t G : ℕ} (ht : 2 ≤ t) (a : Incidence d (2*t) c)
    (hconn : (graph a).Connected) (hcap : cycles d (2*t) c ≤ G) (hne : (core a).Nonempty) :
    (patches a (core a)).card ≤ t*(core a).card ∧ 1 ≤ (core a).card ∧
      (core a).card ≤ (G-1)/(t-1) ∧ t ≤ cycles d (2*t) c :=
  core_bounds ht a hconn hcap _ (peel_terminal a Finset.univ).1 hne

theorem core_empty_of_few_cycles {t : ℕ} (ht : 2 ≤ t) (a : Incidence d (2*t) c)
    (hconn : (graph a).Connected) (hfew : cycles d (2*t) c < t) : core a = ∅ := by
  by_contra h
  have hne := Finset.nonempty_iff_ne_empty.mpr h
  exact hfew.not_ge (peeled_core_bounds ht a hconn (le_refl _) hne).2.2.2

/-- The surviving rows in increasing order of their original rule indices. -/
def selectedRows {n r : ℕ} (A : TernaryMatrix d n) (S : Finset (Fin d)) (hr : S.card = r) :
    TernaryMatrix r n := fun i => A (S.orderEmbOfFin hr i)

theorem selectedRows_independent {n r : ℕ} (A : TernaryMatrix d n) (S : Finset (Fin d))
    (hr : S.card = r) (hind : LinearIndependent F₃ A.row) :
    LinearIndependent F₃ (selectedRows A S hr).row :=
  hind.comp _ (S.orderEmbOfFin hr).injective

theorem selectedRows_kernel {n r θ : ℕ} (A : TernaryMatrix d n) (S : Finset (Fin d))
    (hr : S.card = r) (H : TernaryMatrix θ n) (hker : ∀ j, A.mulVec (H j) = 0) :
    ∀ j, (selectedRows A S hr).mulVec (H j) = 0 := by
  intro j
  funext i
  exact congrFun (hker j) (S.orderEmbOfFin hr i)

/-- Encode anchors in increasing patch order inside the enumerator's `ℓ^m` range. -/
def packAnchors {ℓ m : ℕ} (hℓ : 0 < ℓ) (P : Finset (Fin c)) (hm : P.card ≤ m)
    (v : ↥P → Fin ℓ) : Fin (ℓ^m) :=
  Fin.castLE (Nat.pow_le_pow_right hℓ hm)
    (finFunctionFinEquiv (fun i : Fin P.card => v (P.orderIsoOfFin rfl i)))

/-- Read the anchor tuple back from the larger enumeration range. Codes above
the last tuple for this patch set denote unused slots. -/
def unpackAnchors {ℓ m : ℕ} (P : Finset (Fin c)) (code : Fin (ℓ^m)) :
    Option (↥P → Fin ℓ) :=
  if h : code.val < ℓ^P.card then
    some (fun p => finFunctionFinEquiv.symm ⟨code.val,h⟩ ((P.orderIsoOfFin rfl).symm p))
  else none

theorem unpack_packAnchors {ℓ m : ℕ} (hℓ : 0 < ℓ) (P : Finset (Fin c)) (hm : P.card ≤ m)
    (v : ↥P → Fin ℓ) : unpackAnchors P (packAnchors hℓ P hm v) = some v := by
  let f := fun i : Fin P.card => v (P.orderIsoOfFin rfl i)
  have h : (packAnchors hℓ P hm v).val < ℓ^P.card := (finFunctionFinEquiv f).isLt
  rw [unpackAnchors, dite_eq_left h]
  congr 1
  funext x
  change finFunctionFinEquiv.symm (finFunctionFinEquiv f) ((P.orderIsoOfFin rfl).symm x) = v x
  simp [f, Equiv.symm_apply_apply]

theorem unpackAnchors_eq_some_iff {ℓ m : ℕ} (hℓ : 0 < ℓ) (P : Finset (Fin c)) (hm : P.card ≤ m)
    (code : Fin (ℓ^m)) (v : ↥P → Fin ℓ) :
    unpackAnchors P code = some v ↔ code = packAnchors hℓ P hm v := by
  constructor
  · intro h
    unfold unpackAnchors at h
    split at h
    next hlt =>
      have he := Option.some.inj h
      subst v
      apply Fin.ext
      change code.val = (finFunctionFinEquiv _).val
      have hfun : (fun i : Fin P.card =>
          finFunctionFinEquiv.symm (⟨code.val,hlt⟩ : Fin (ℓ^P.card))
            ((P.orderIsoOfFin rfl).symm ((P.orderIsoOfFin rfl) i))) =
          finFunctionFinEquiv.symm (⟨code.val,hlt⟩ : Fin (ℓ^P.card)) := by simp
      rw [hfun, Equiv.apply_symm_apply]
    next => contradiction
  · rintro rfl
    exact unpack_packAnchors hℓ P hm v

theorem packAnchors_injective {ℓ m : ℕ} (hℓ : 0 < ℓ) (P : Finset (Fin c)) (hm : P.card ≤ m) :
    Function.Injective (packAnchors hℓ P hm) := by
  intro v w he
  simpa only [unpack_packAnchors, Option.some.injEq] using congrArg (unpackAnchors P) he

/-- The slot uses the actual size of the nonempty core and one supplied anchor
per surviving patch. Its row index agrees with the cardinality of the core. -/
def replaySlot {ℓ t G Γ : ℕ} (hℓ : 0 < ℓ) (ht : 2 ≤ t) (a : Incidence d (2*t) c)
    (hconn : (graph a).Connected) (hcap : cycles d (2*t) c ≤ G) (hne : (core a).Nonempty)
    (description : Fin Γ) (anchors : ↥(patches a (core a)) → Fin ℓ) :
    {k : CoreWeight.Slot ℓ t ((G-1)/(t-1)) Γ // (core a).card = k.1.val+1} :=
  let r := (core a).card
  have h := peeled_core_bounds ht a hconn hcap hne
  have hr : r = (r-1)+1 := by dsimp [r]; omega
  let i : Fin ((G-1)/(t-1)) := ⟨r-1,by dsimp [r]; omega⟩
  ⟨⟨i,description,packAnchors hℓ _ (by change _ ≤ t*((r-1)+1); rw [← hr]; exact h.1) anchors⟩,hr⟩

/-- With the core bounds, full rank, and kernel equations supplied by the
witness, coverage reduces to replay returning the ordered surviving rule rows. -/
theorem weight_pos_of_decoded_core {ℓ q n t r₀ Γ θ : ℕ}
    (D : CoreWeight.ReplayData ℓ q n t r₀ Γ) (a : Incidence d (2*t) c)
    (A : TernaryMatrix d n) (hind : LinearIndependent F₃ A.row)
    (H : TernaryMatrix θ n) (hker : ∀ j, A.mulVec (H j) = 0) (x : Fin ℓ → Fin q)
    (k : {k : CoreWeight.Slot ℓ t r₀ Γ // (core a).card = k.1.val + 1})
    (hdecode : D.rules k.val (fun i => x i.val) = some (selectedRows A (core a) k.property)) :
    0 < CoreWeight.weight D.object H x :=
  D.weight_pos_of_replay H x k.val _ hdecode (selectedRows_independent A _ _ hind)
    (selectedRows_kernel A _ _ H hker)

#print axioms peel_legal
#print axioms peeled_core_bounds
#print axioms unpackAnchors_eq_some_iff
#print axioms packAnchors_injective
#print axioms weight_pos_of_decoded_core

end DeletionCode.Explicit.RulePatch
