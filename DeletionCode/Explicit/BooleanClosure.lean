import DeletionCode.Explicit.FieldHash
import DeletionCode.Explicit.EditBall
import DeletionCode.Explicit.LiftDictionary
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Boolean fibres and the closure under exposed rules, manuscript
`d:applies`, `d:exposed`, `d:full-closure`, `d:closure-exists`,
`d:closure-invariance` and `d:boolean-fibers`. -/
namespace DeletionCode.Explicit.BooleanClosure

open LiftDictionary Qary.SignedSupport
open scoped BigOperators

abbrev Vector (α : Type*) (L : ℕ) := Gram α L → ZMod 3
abbrev Space (α : Type*) (L : ℕ) := Submodule (ZMod 3) (Vector α L)

variable {α : Type*} {L : ℕ}

def Applies (u ρ : Vector α L) : Prop := IsZeroOne u ∧ IsZeroOne (u + ρ)

def fibre (v : Vector α L) (W : Space α L) : Set (Vector α L) :=
  {u | u - v ∈ W ∧ IsZeroOne u}

theorem exposed_iff_exists_fibre {v ρ : Vector α L} {W : Space α L} :
    Exposed v W ρ ↔ ∃ u ∈ fibre v W, Applies u ρ := by
  constructor
  · rintro ⟨w, hw, h, hρ⟩
    exact ⟨v + w, ⟨by simpa only [add_sub_cancel_left] using hw, h⟩, h, hρ⟩
  · rintro ⟨u, ⟨hu, _⟩, h, hρ⟩
    exact ⟨u - v, hu, by simpa only [add_sub_cancel] using h,
      by simpa only [add_sub_cancel] using hρ⟩

theorem applies_iff_coordinates {u ρ : Vector α L} (hu : IsZeroOne u) :
    Applies u ρ ↔ ∀ g, (ρ g = 1 → u g = 0) ∧ (ρ g = -1 → u g = 1) := by
  have h : ∀ a b : ZMod 3, (a = 0 ∨ a = 1) →
      ((a + b = 0 ∨ a + b = 1) ↔ (b = 1 → a = 0) ∧ (b = -1 → a = 1)) := by decide
  exact ⟨fun ha g => (h _ _ (hu g)).mp (ha.2 g), fun ha => ⟨hu, fun g => (h _ _ (hu g)).mpr (ha g)⟩⟩

theorem exposed_mono {v ρ : Vector α L} {W U : Space α L} (hle : W ≤ U) :
    Exposed v W ρ → Exposed v U ρ := by
  rintro ⟨w, hw, h, hρ⟩
  exact ⟨w, hle hw, h, hρ⟩

def ClosedAt (rules : Set (Vector α L)) (v : Vector α L) (W : Space α L) : Prop :=
  ∀ ρ ∈ rules, Exposed v W ρ → ρ ∈ W

def closure (rules : Set (Vector α L)) (v : Vector α L) : Space α L :=
  sInf {W | ClosedAt rules v W}

theorem closure_le {rules : Set (Vector α L)} {v : Vector α L} {W : Space α L}
    (h : ClosedAt rules v W) : closure rules v ≤ W :=
  sInf_le h

theorem closure_closed (rules : Set (Vector α L)) (v : Vector α L) :
    ClosedAt rules v (closure rules v) := by
  intro ρ hρ hex
  apply Submodule.mem_sInf.mpr
  intro W hW
  exact hW ρ hρ (exposed_mono (closure_le hW) hex)

theorem closure_le_kernel {rules : Set (Vector α L)} {v : Vector α L} {ker : Space α L}
    (hker : rules ⊆ ker) : closure rules v ≤ ker :=
  closure_le (fun ρ hρ _ => hker hρ)

def adjoining (W : Space α L) (ρ : Vector α L) : Space α L :=
  W ⊔ Submodule.span (ZMod 3) {ρ}

inductive Greedy (rules : Set (Vector α L)) (v : Vector α L) : ℕ → Space α L → Prop
  | start : Greedy rules v 0 ⊥
  | add {k W ρ} : Greedy rules v k W → ρ ∈ rules → Exposed v W ρ → ρ ∉ W →
      Greedy rules v (k + 1) (adjoining W ρ)

theorem Greedy.le_closure {rules : Set (Vector α L)} {v : Vector α L}
    {k : ℕ} {W : Space α L} (h : Greedy rules v k W) : W ≤ closure rules v := by
  induction h with
  | start => exact bot_le
  | add _ hρ he _ ih =>
    apply sup_le ih
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr
      (closure_closed _ _ _ hρ (exposed_mono ih he))

theorem Greedy.eq_closure {rules : Set (Vector α L)} {v : Vector α L}
    {k : ℕ} {W : Space α L} (h : Greedy rules v k W) (hc : ClosedAt rules v W) :
    W = closure rules v :=
  le_antisymm h.le_closure (closure_le hc)

theorem Greedy.span_rules {rules : Set (Vector α L)} {v : Vector α L}
    {k : ℕ} {W : Space α L} (h : Greedy rules v k W) :
    ∃ S : Set (Vector α L), S ⊆ rules ∧ W = Submodule.span (ZMod 3) S := by
  induction h with
  | start => exact ⟨∅, Set.empty_subset _, by simp⟩
  | @add k W ρ _ hρ _ _ ih =>
    obtain ⟨S, hS, rfl⟩ := ih
    exact ⟨S ∪ {ρ}, Set.union_subset hS (Set.singleton_subset_iff.mpr hρ),
      (Submodule.span_union S {ρ}).symm⟩

private theorem space_rank_lt [Fintype α] {W U : Space α L} (h : W < U) :
    Module.finrank (ZMod 3) W < Module.finrank (ZMod 3) U := by
  classical
  have : Finite (Gram α L) := Finite.of_fintype _
  have : FiniteDimensional (ZMod 3) (Vector α L) := Module.Finite.pi
  exact Submodule.finrank_strictMono (K := ZMod 3) (V := Vector α L) h

set_option maxHeartbeats 1000000 in
theorem Greedy.steps_le_finrank [Fintype α] {rules : Set (Vector α L)} {v : Vector α L}
    {k : ℕ} {W : Space α L} (h : Greedy rules v k W) : k ≤ Module.finrank (ZMod 3) W := by
  classical
  induction h with
  | start => exact Nat.zero_le _
  | @add k W ρ _ _ _ hout ih =>
    have hlt : W < adjoining W ρ := by
      apply lt_of_le_of_ne le_sup_left
      intro h
      have hle : Submodule.span (ZMod 3) {ρ} ≤ adjoining W ρ := le_sup_right
      have hm : ρ ∈ adjoining W ρ := hle (Submodule.mem_span_singleton_self ρ)
      exact hout (h.symm ▸ hm)
    have hdim : Module.finrank (ZMod 3) W < Module.finrank (ZMod 3) (adjoining W ρ) :=
      space_rank_lt hlt
    exact Nat.succ_le_of_lt (ih.trans_lt hdim)

theorem Greedy.steps_le_ambient [Fintype α] {rules : Set (Vector α L)} {v : Vector α L}
    {k : ℕ} {W : Space α L} (h : Greedy rules v k W) : k ≤ Fintype.card α ^ L := by
  classical
  have hd : Module.finrank (ZMod 3) (Vector α L) = Fintype.card α ^ L := by
    simp [Vector, Gram]
  exact h.steps_le_finrank.trans (hd ▸ W.finrank_le)

theorem greedy_terminates [Fintype α] (rules : Set (Vector α L)) (v : Vector α L) :
    ∃ k ≤ Fintype.card α ^ L, Greedy rules v k (closure rules v) := by
  classical
  by_contra hnone
  have hrun (k : ℕ) : ∃ W, Greedy rules v k W := by
    induction k with
    | zero => exact ⟨⊥, .start⟩
    | succ k ih =>
      obtain ⟨W, hW⟩ := ih
      have hc : ¬ ClosedAt rules v W := fun hc =>
        hnone ⟨k, hW.steps_le_ambient, hW.eq_closure hc ▸ hW⟩
      unfold ClosedAt at hc
      push Not at hc
      obtain ⟨ρ, hρ, he, hout⟩ := hc
      exact ⟨adjoining W ρ, .add hW hρ he hout⟩
  obtain ⟨W, hW⟩ := hrun (Fintype.card α ^ L + 1)
  have := hW.steps_le_ambient
  omega

theorem closure_span_rules [Fintype α] (rules : Set (Vector α L)) (v : Vector α L) :
    ∃ S : Set (Vector α L), S ⊆ rules ∧ closure rules v = Submodule.span (ZMod 3) S := by
  obtain ⟨_, _, h⟩ := greedy_terminates rules v
  exact h.span_rules

private theorem exposed_translate {v w ρ : Vector α L} {W : Space α L} (hw : w ∈ W) :
    Exposed (v + w) W ρ ↔ Exposed v W ρ := by
  constructor
  · rintro ⟨s, hs, h, hρ⟩
    exact ⟨w + s, W.add_mem hw hs, by simpa only [add_assoc] using h,
      by simpa only [add_assoc] using hρ⟩
  · rintro ⟨s, hs, h, hρ⟩
    refine ⟨s - w, W.sub_mem hs hw, ?_, ?_⟩
    · simpa only [add_assoc, add_sub_cancel] using h
    · simpa only [add_assoc, add_sub_cancel] using hρ

private theorem closure_move_le {rules : Set (Vector α L)} {v ρ : Vector α L}
    (hρ : ρ ∈ rules) (hv : Applies v ρ) :
    closure rules (v + ρ) ≤ closure rules v := by
  have he : Exposed v (closure rules v) ρ :=
    ⟨0, (closure rules v).zero_mem, by simpa using hv.1, by simpa using hv.2⟩
  have hw : ρ ∈ closure rules v := closure_closed _ _ _ hρ he
  exact closure_le (fun r hr hx => closure_closed _ _ _ hr ((exposed_translate hw).mp hx))

theorem closure_invariance {rules : Set (Vector α L)} {v ρ : Vector α L}
    (hρ : ρ ∈ rules) (hneg : -ρ ∈ rules) (hv : Applies v ρ) :
    closure rules (v + ρ) = closure rules v := by
  apply le_antisymm (closure_move_le hρ hv)
  have hback : Applies (v + ρ) (-ρ) := ⟨hv.2, by simpa [add_assoc] using hv.1⟩
  simpa [add_assoc] using closure_move_le hneg hback

/-- Union of the supports of vectors in the subspace. -/
def support (W : Space α L) : Set (Gram α L) := {g | ∃ w ∈ W, w g ≠ 0}

theorem zero_off_support {W : Space α L} {w : Vector α L} (hw : w ∈ W)
    {g : Gram α L} (hg : g ∉ support W) : w g = 0 :=
  not_not.mp (fun hn => hg ⟨w, hw, hn⟩)

section Factors

variable {ι : Type*} [Fintype ι] (U : ι → Space α L)

theorem mem_sup_iff_sum {w : Vector α L} :
    w ∈ ⨆ i, U i ↔ ∃ x : ∀ i, U i, (∑ i, (x i : Vector α L)) = w := by
  classical
  simpa only [Finset.mem_univ, iSup_true] using
    (Submodule.mem_iSup_finset_iff_exists_sum (s := Finset.univ) U w)

theorem sum_coordinate (hdis : Pairwise fun i j => Disjoint (support (U i)) (support (U j)))
    (x : ∀ i, U i) {i : ι} {g : Gram α L} (hg : g ∈ support (U i)) :
    (∑ j, (x j : Vector α L)) g = (x i : Vector α L) g := by
  classical
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact zero_off_support (x j).property (fun hz => Set.disjoint_left.mp (hdis hji) hz hg)
  · simp

theorem sum_coordinate_off (x : ∀ i, U i) {g : Gram α L}
    (hg : ∀ i, g ∉ support (U i)) : (∑ i, (x i : Vector α L)) g = 0 := by
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun i _ => zero_off_support (x i).property (hg i))

def localFibre (v : Vector α L) (W : Space α L) : Set W :=
  {w | ∀ g ∈ support W, v g + (w : Vector α L) g = 0 ∨ v g + (w : Vector α L) g = 1}

/-- The local fibre is represented by its increment on the component support.
The disjoint supports make that increment determine the summand uniquely. -/
theorem fibre_iff_factors {v u : Vector α L} (hv : IsZeroOne v)
    (hdis : Pairwise fun i j => Disjoint (support (U i)) (support (U j))) :
    u ∈ fibre v (⨆ i, U i) ↔
      ∃ x : ∀ i, U i, (∀ i, x i ∈ localFibre v (U i)) ∧
        u = v + ∑ i, (x i : Vector α L) := by
  constructor
  · rintro ⟨hw, hu⟩
    obtain ⟨x, hx⟩ := (mem_sup_iff_sum U).mp hw
    have hsum : u = v + ∑ i, (x i : Vector α L) := by rw [hx, add_sub_cancel]
    refine ⟨x, fun i g hg => ?_, hsum⟩
    simpa only [hsum, Pi.add_apply, sum_coordinate U hdis x hg] using hu g
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, fun g => ?_⟩
    · simpa only [add_sub_cancel_left] using (mem_sup_iff_sum U).mpr ⟨x, rfl⟩
    · by_cases hi : ∃ i, g ∈ support (U i)
      · obtain ⟨i, hg⟩ := hi
        simpa only [Pi.add_apply, sum_coordinate U hdis x hg] using hx i g hg
      · push Not at hi
        simpa only [Pi.add_apply, sum_coordinate_off U x hi, add_zero] using hv g

theorem exposed_iff_local {v ρ : Vector α L} (hv : IsZeroOne v)
    (hdis : Pairwise fun i j => Disjoint (support (U i)) (support (U j))) :
    Exposed v (⨆ i, U i) ρ ↔
      (∀ g, (∀ i, g ∉ support (U i)) →
        ((ρ g = 1 → v g = 0) ∧ (ρ g = -1 → v g = 1))) ∧
      (∀ i, ∃ w ∈ localFibre v (U i), ∀ g ∈ support (U i),
        (ρ g = 1 → v g + (w : Vector α L) g = 0) ∧
        (ρ g = -1 → v g + (w : Vector α L) g = 1)) := by
  classical
  rw [exposed_iff_exists_fibre]
  constructor
  · rintro ⟨u, hu, ha⟩
    obtain ⟨x, hx, rfl⟩ := (fibre_iff_factors U hv hdis).mp hu
    have h := (applies_iff_coordinates ha.1).mp ha
    exact ⟨fun g hg => by simpa only [Pi.add_apply, sum_coordinate_off U x hg, add_zero] using h g,
      fun i => ⟨x i, hx i, fun g hg => by
        simpa only [Pi.add_apply, sum_coordinate U hdis x hg] using h g⟩⟩
  · rintro ⟨hoff, hlocal⟩
    choose x hx hreq using hlocal
    let u := v + ∑ i, (x i : Vector α L)
    have hu : u ∈ fibre v (⨆ i, U i) := (fibre_iff_factors U hv hdis).mpr ⟨x, hx, rfl⟩
    refine ⟨u, hu, (applies_iff_coordinates hu.2).mpr (fun g => ?_)⟩
    by_cases hi : ∃ i, g ∈ support (U i)
    · obtain ⟨i, hg⟩ := hi
      simpa only [u, Pi.add_apply, sum_coordinate U hdis x hg] using hreq i g hg
    · push Not at hi
      simpa only [u, Pi.add_apply, sum_coordinate_off U x hi, add_zero] using hoff g hi

end Factors

theorem sum_injective_of_disjoint {ι : Type*} [Fintype ι] (U : ι → Space α L)
    (hdis : Pairwise fun i j => Disjoint (support (U i)) (support (U j))) :
    Function.Injective (fun x : ∀ i, U i => ∑ i, (x i : Vector α L)) := by
  classical
  intro x y heq
  change (∑ i, (x i : Vector α L)) = (∑ i, (y i : Vector α L)) at heq
  funext i
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ support (U i)
  · rw [← sum_coordinate U hdis x hg, heq, sum_coordinate U hdis y hg]
  · rw [zero_off_support (x i).property hg, zero_off_support (y i).property hg]

/-- A bounded greedy scan. The callback searches for a rule exposed by the
current list's span and outside that span. -/
def greedyRules (choose : List (Vector α L) → Option (Vector α L)) :
    ℕ → List (Vector α L) → List (Vector α L)
  | 0, acc => acc
  | n + 1, acc => match choose acc with
    | none => acc
    | some r => greedyRules choose n (r :: acc)

abbrev ruleSpan (acc : List (Vector α L)) : Space α L :=
  Submodule.span (ZMod 3) {r | r ∈ acc}

theorem ruleSpan_cons (r : Vector α L) (acc : List (Vector α L)) :
    ruleSpan (r :: acc) = adjoining (ruleSpan acc) r := by
  change Submodule.span (ZMod 3) {x | x ∈ r :: acc} = _
  rw [adjoining, sup_comm, ← Submodule.span_union]
  congr 1
  ext x
  simp

/-- Exactness of the bounded greedy loop for a correct search callback. -/
theorem greedyRules_eq_closure [Fintype α] (rules : Set (Vector α L)) (v : Vector α L)
    (choose : List (Vector α L) → Option (Vector α L))
    (hsome : ∀ acc r, choose acc = some r →
      r ∈ rules ∧ Exposed v (ruleSpan acc) r ∧ r ∉ ruleSpan acc)
    (hnone : ∀ acc, choose acc = none → ClosedAt rules v (ruleSpan acc)) :
    ruleSpan (greedyRules choose (Fintype.card α ^ L + 1) []) = closure rules v := by
  suffices ∀ n k acc, Fintype.card α ^ L < k + n → Greedy rules v k (ruleSpan acc) →
      ruleSpan (greedyRules choose n acc) = closure rules v by
    apply this _ 0 [] (by simp)
    simpa [ruleSpan] using (Greedy.start (rules := rules) (v := v))
  intro n
  induction n with
  | zero =>
    intro k acc hn hg
    have := hg.steps_le_ambient
    omega
  | succ n ih =>
    intro k acc hn hg
    simp only [greedyRules]
    split
    · rename_i h
      exact hg.eq_closure (hnone _ h)
    · rename_i r h
      obtain ⟨hr, he, hout⟩ := hsome _ _ h
      apply ih (k + 1) (r :: acc) (by omega)
      rw [ruleSpan_cons]
      exact .add hg hr he hout

/-! `d:fiber-listing` -/

set_option maxHeartbeats 1000000 in
theorem separating_coordinates [Fintype α] (W : Space α L) :
    ∃ s : Finset (Gram α L), s.card ≤ Module.finrank (ZMod 3) W ∧
      ∀ w ∈ W, (∀ g ∈ s, w g = 0) → w = 0 := by
  classical
  let rank (U : Space α L) := Module.finrank (ZMod 3) U
  suffices ∀ n (U : Space α L), rank U = n →
      ∃ s : Finset (Gram α L), s.card ≤ rank U ∧
        ∀ w ∈ U, (∀ g ∈ s, w g = 0) → w = 0 by
    exact this (rank W) W rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro U hn
    by_cases hbot : U = ⊥
    · subst U
      exact ⟨∅, Nat.zero_le _, fun w hw _ => (Submodule.mem_bot (R := ZMod 3)).mp hw⟩
    obtain ⟨w, hw, hnw⟩ := U.ne_bot_iff.mp hbot
    have hex : ∃ g, w g ≠ 0 := by
      by_contra! h
      exact hnw (funext h)
    obtain ⟨g, hg⟩ := hex
    let ev : Vector α L →ₗ[ZMod 3] ZMod 3 := LinearMap.proj g
    let V := U ⊓ ev.ker
    have hlt : V < U := by
      apply lt_of_le_of_ne inf_le_left
      intro h
      have hv : w ∈ U ⊓ ev.ker := by rwa [h]
      have hek : w ∈ ev.ker := hv.2
      exact hg ((LinearMap.mem_ker (f := ev)).mp hek)
    have hd : rank V < rank U := space_rank_lt hlt
    obtain ⟨s, hs, hz⟩ := ih (rank V) (hn ▸ hd) V rfl
    refine ⟨insert g s, (Finset.card_insert_le g s).trans (by omega), ?_⟩
    intro u hu hzero
    apply hz u ⟨hu, LinearMap.mem_ker.mpr (hzero g (Finset.mem_insert_self _ _))⟩
    exact fun j hj => hzero j (Finset.mem_insert_of_mem hj)

theorem fibre_eq_of_agree {v u w : Vector α L} {W : Space α L}
    {s : Finset (Gram α L)}
    (hs : ∀ a ∈ W, (∀ g ∈ s, a g = 0) → a = 0)
    (hu : u ∈ fibre v W) (hw : w ∈ fibre v W)
    (h : ∀ g ∈ s, u g = w g) : u = w := by
  have hd : u - w ∈ W := by
    have hh := W.sub_mem hu.1 hw.1
    rwa [sub_sub_sub_cancel_right] at hh
  apply sub_eq_zero.mp (hs _ hd ?_)
  intro g hg
  exact sub_eq_zero.mpr (h g hg)

theorem fibre_card_le [Fintype α] (v : Vector α L) (W : Space α L) :
    Nat.card (fibre v W) ≤ 2 ^ Module.finrank (ZMod 3) W := by
  classical
  let : Fintype (fibre v W) := Fintype.ofFinite _
  obtain ⟨s, hs, hsep⟩ := separating_coordinates W
  let f (u : fibre v W) (g : s) : Bool := decide (u.1 g = 1)
  have hf : Function.Injective f := by
    intro u w heq
    apply Subtype.ext
    apply fibre_eq_of_agree hsep u.2 w.2
    intro g hg
    have hb := congrFun heq ⟨g, hg⟩
    change decide (u.1 g = 1) = decide (w.1 g = 1) at hb
    rcases u.2.2 g with hu | hu <;> rcases w.2.2 g with hw | hw
    · exact hu.trans hw.symm
    · simp [hu, hw] at hb
    · simp [hu, hw] at hb
    · exact hu.trans hw.symm
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card (fibre v W) ≤ Fintype.card (s → Bool) := Fintype.card_le_of_injective f hf
    _ = 2 ^ s.card := by simp
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hs

/-- Enumerate the Boolean pivot assignments, reconstruct, and retain the candidates
accepted by the Boolean check. `solve` supplies the affine reconstruction. -/
def listFibre (r : ℕ) (solve : QWord 2 → Vector α L)
    (keep : Vector α L → Bool) : List (Vector α L) :=
  ((wordsOfLength 2 r).map solve).filter keep

theorem mem_listFibre {r : ℕ} {v : Vector α L} {W : Space α L}
    (solve : QWord 2 → Vector α L) (keep : Vector α L → Bool)
    (hsolve : ∀ a : QWord 2, a.length = r → solve a - v ∈ W)
    (hcover : ∀ u ∈ fibre v W, ∃ a : QWord 2, a.length = r ∧ solve a = u)
    (hkeep : ∀ u, keep u = true ↔ IsZeroOne u) (u : Vector α L) :
    u ∈ listFibre r solve keep ↔ u ∈ fibre v W := by
  simp only [listFibre, List.mem_filter, List.mem_map, mem_wordsOfLength, hkeep]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hu⟩
    exact ⟨hsolve a ha, hu⟩
  · intro hu
    exact ⟨hcover u hu, hu.2⟩

#print axioms applies_iff_coordinates
#print axioms greedy_terminates
#print axioms closure_span_rules
#print axioms closure_invariance
#print axioms fibre_iff_factors
#print axioms exposed_iff_local

#print axioms sum_injective_of_disjoint
#print axioms greedyRules_eq_closure
#print axioms closure_le_kernel
#print axioms separating_coordinates
#print axioms fibre_card_le
#print axioms mem_listFibre

end DeletionCode.Explicit.BooleanClosure
