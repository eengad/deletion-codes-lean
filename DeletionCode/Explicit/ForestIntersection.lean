import DeletionCode.Explicit.SupplierRetention
import DeletionCode.Explicit.BooleanClosure

/-! Leaf patches detect combinations of several rules before a first event. -/

namespace DeletionCode.Explicit.RulePatch

open FieldHash
open scoped BigOperators

variable {d s c : ℕ}

/-- The patches incident to exactly one of the selected bubble edges. -/
def leafPatches (a : Incidence d s c) (S : Finset (Fin d)) : Finset (Fin c) :=
  (patches a S).filter (fun p => (atPatch a S p).card = 1)

theorem atPatch_card_sum (a : Incidence d s c) (S : Finset (Fin d)) :
    ∑ p ∈ patches a S, (atPatch a S p).card = S.card*s := by
  have hdis : (↑(patches a S) : Set (Fin c)).PairwiseDisjoint (atPatch a S) := by
    intro p _ q _ hne
    change Disjoint (atPatch a S p) (atPatch a S q)
    rw [Finset.disjoint_left]
    intro e hp hq
    exact hne ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2)
  have hu : (patches a S).biUnion (atPatch a S) = edges S := by
    ext e
    simp only [Finset.mem_biUnion,atPatch,Finset.mem_filter,patches,Finset.mem_image]
    constructor
    · rintro ⟨p,_,he,_⟩
      exact he
    · intro he
      exact ⟨a e,⟨e,he,rfl⟩,he,rfl⟩
  rw [← Finset.card_biUnion hdis,hu,edges,Finset.card_product,Finset.card_univ,Fintype.card_fin]

/-- The selected forest has at least `(s-2)*r+2` patch leaves. The input
inequality is the forest's vertex count for this nonempty selection. -/
theorem leaf_count (a : Incidence d s c) (S : Finset (Fin d)) (hs : 2 ≤ s)
    (hforest : S.card*s+1 ≤ S.card+(patches a S).card) :
    (s-2)*S.card+2 ≤ (leafPatches a S).card := by
  let P := patches a S
  let D := leafPatches a S
  have hD : D ⊆ P := Finset.filter_subset ..
  have hq : P.card + (P \ D).card ≤ S.card*s := by
    rw [← atPatch_card_sum a S]
    calc
      P.card + (P \ D).card = ∑ p ∈ P, (1+(if p ∈ D then 0 else 1)) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
        congr 1
        have hite (p : Fin c) : (if p ∈ D then 0 else 1 : ℕ) =
            (if p ∉ D then 1 else 0) := by by_cases h : p ∈ D <;> simp [h]
        simp_rw [hite]
        rw [Finset.sum_boole]
        congr 1
        ext p
        simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hp
        have hm : e ∈ atPatch a S p := Finset.mem_filter.mpr ⟨he,heq⟩
        have hpos := Finset.card_pos.mpr (show (atPatch a S p).Nonempty from ⟨e,hm⟩)
        by_cases hd : p ∈ D
        · simpa [hd] using (show (atPatch a S p).Nonempty from ⟨e,hm⟩)
        · have hne : (atPatch a S p).card ≠ 1 := fun he =>
            hd (Finset.mem_filter.mpr ⟨hp,he⟩)
          simp [hd]
          omega
  have he : (s-2)*S.card+2*S.card = S.card*s := by
    calc
      _ = (s-2+2)*S.card := (Nat.add_mul ..).symm
      _ = _ := by rw [Nat.sub_add_cancel hs,Nat.mul_comm]
  have hcard := Finset.card_le_card hD
  rw [Finset.card_sdiff_of_subset hD] at hq
  change (s-2)*S.card+2 ≤ D.card
  change S.card*s+1 ≤ S.card+P.card at hforest
  omega

section Detect

variable {γ : Type*}
variable (a : Incidence d s c) (support : Fin c → Finset γ) (rows : Fin d → γ → F₃)

/-- The occupied patches for a rule or a linear combination. -/
def occupied (row : γ → F₃) : Finset (Fin c) :=
  Finset.univ.filter (fun p => ((support p).filter (fun g => row g ≠ 0)).Nonempty)

/-- A patch with only one edge of the selected rules detects a nonzero
coefficient, since the other selected rules vanish in that patch. -/
theorem leaves_detect (S : Finset (Fin d)) (coeff : Fin d → F₃)
    (hcoeff : ∀ i ∈ S, coeff i ≠ 0)
    (hnonzero : ∀ e : Fin d × Fin s, ∃ g ∈ support (a e), rows e.1 g ≠ 0)
    (hvanish : ∀ i p, (∀ j, a (i,j) ≠ p) → ∀ g ∈ support p, rows i g = 0) :
    leafPatches a S ⊆ occupied support (fun g => ∑ i ∈ S, coeff i*rows i g) := by
  intro p hp
  have hcard := (Finset.mem_filter.mp hp).2
  obtain ⟨e,he⟩ := Finset.card_eq_one.mp hcard
  have hem : e ∈ atPatch a S p := by rw [he]; simp
  have hlabel := (Finset.mem_filter.mp hem).2
  have hsel := (Finset.mem_product.mp ((Finset.mem_filter.mp hem).1 : e ∈ edges S)).1
  obtain ⟨g,hg,hn⟩ := hnonzero e
  have hz : ∑ i ∈ S, coeff i*rows i g = coeff e.1*rows e.1 g := by
    apply Finset.sum_eq_single_of_mem e.1 hsel
    intro i hi hne
    have hnone (j : Fin s) : a (i,j) ≠ p := by
      intro h
      have hm : (i,j) ∈ atPatch a S p := Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hi,Finset.mem_univ _⟩,h⟩
      rw [he] at hm
      exact hne (congrArg Prod.fst (Finset.mem_singleton.mp hm))
    rw [hvanish i p hnone g (hlabel ▸ hg),mul_zero]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  exact ⟨g,Finset.mem_filter.mpr ⟨hlabel ▸ hg,by simpa [hz] using mul_ne_zero (hcoeff _ hsel) hn⟩⟩

theorem one_rule_of_patch_bound (S : Finset (Fin d)) (coeff : Fin d → F₃) (hs : 3 ≤ s)
    (hforest : S.card*s+1 ≤ S.card+(patches a S).card)
    (hcoeff : ∀ i ∈ S, coeff i ≠ 0)
    (hnonzero : ∀ e : Fin d × Fin s, ∃ g ∈ support (a e), rows e.1 g ≠ 0)
    (hvanish : ∀ i p, (∀ j, a (i,j) ≠ p) → ∀ g ∈ support p, rows i g = 0)
    (hbound : (occupied support (fun g => ∑ i ∈ S, coeff i*rows i g)).card ≤ s) :
    S.card ≤ 1 := by
  have h := (leaf_count a S (by omega) hforest).trans
    ((Finset.card_le_card (leaves_detect a support rows S coeff hcoeff hnonzero hvanish)).trans hbound)
  by_contra hne
  have hm : (s-2)*2 ≤ (s-2)*S.card := Nat.mul_le_mul_left _ (by omega)
  omega

#print axioms one_rule_of_patch_bound

end Detect
end DeletionCode.Explicit.RulePatch
