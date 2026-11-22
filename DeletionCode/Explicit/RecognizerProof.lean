import DeletionCode.Explicit.Recognizer
import DeletionCode.Explicit.ForestCatalogue

/-! Correctness of the next-rule scan for concrete recorded lifts. -/

namespace DeletionCode.Explicit.Recognizer

open FieldHash CanonicalColour RulePatch LetterGraphCuts ReplayEntry LiftDictionary PatchSupport
open Qary.SignedSupport

variable {ℓ q K b L Λ s θ : ℕ}

private theorem mem_oldRows (hs : History ℓ q L s) (v : Row (q^L)) :
    v ∈ oldRows hs ↔ ∃ i : Fin hs.length, (hs.get i).row = v := by
  rw [oldRows,List.mem_map]
  constructor
  · rintro ⟨h,hh,rfl⟩
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hh
    exact ⟨i,congrArg Batch.row hi⟩
  · rintro ⟨i,rfl⟩
    exact ⟨hs.get i,List.get_mem ..,rfl⟩

theorem parts_span (hs : History ℓ q L s) :
    span (ComponentExposure.flatRows (parts hs)) = span (oldRows hs) := by
  apply congrArg (Submodule.span F₃)
  ext v
  change v ∈ ComponentExposure.flatRows (parts hs) ↔ v ∈ oldRows hs
  rw [ComponentExposure.flatRows,List.mem_flatMap,mem_oldRows]
  constructor
  · rintro ⟨p,_,hp⟩
    obtain ⟨i,_,hi⟩ := (mem_partRows _ _ _ _).mp hp
    exact ⟨i,hi⟩
  · rintro ⟨i,rfl⟩
    exact ⟨representative (PatchTable.incidence (gates hs)) i,List.mem_finRange _,
      (mem_partRows _ _ _ _).mpr ⟨i,rfl,rfl⟩⟩

def lifts (hs : History ℓ q L s) (e : Fin hs.length × Fin s) : Completed ℓ (Fin q) :=
  ((hs.get e.1).bubbles e.2).completed

/-- Every stored row is the spectrum of its installed lifts. -/
def RowsMatch (pad : Fin q) (x : Fin ℓ → Fin q) (hs : History ℓ q L s) : Prop :=
  ∀ i : Fin hs.length, ∀ g : Gram (Fin q) L,
    (hs.get i).row (finFunctionFinEquiv g) = ruleVector (lifts hs) pad x L i g

theorem parts_support_disjoint (pad : Fin q) (x : Fin ℓ → Fin q) (hs : History ℓ q L s)
    (hx : LetterSequence.Strong x K Λ) (hfit : LiftsFit (gates hs) (lifts hs) Λ)
    (hL : K+2*Λ ≤ L) (hm : RowsMatch pad x hs) :
    ∀ {i j : Fin hs.length}, i ≠ j → ∀ g,
      ComponentExposure.occupies (parts hs i) g = true →
        ComponentExposure.occupies (parts hs j) g ≠ true := by
  let : Inhabited (Fin q) := ⟨pad⟩
  let a := PatchTable.incidence (gates hs)
  intro i j hij col hi hj
  obtain ⟨r,hr,hri⟩ := (ComponentExposure.occupies_iff _ _).mp hi
  obtain ⟨r',hr',hrj⟩ := (ComponentExposure.occupies_iff _ _).mp hj
  obtain ⟨u,hu,rfl⟩ := (mem_partRows _ _ _ _).mp hr
  obtain ⟨v,hv,rfl⟩ := (mem_partRows _ _ _ _).mp hr'
  let g := finFunctionFinEquiv.symm col
  have he : finFunctionFinEquiv g = col := Equiv.apply_symm_apply _ _
  rw [← he,hm] at hri hrj
  obtain ⟨k,hk⟩ := recorded_rule_occurrence (gates hs) (lifts hs) x u g hri
  obtain ⟨k',hk'⟩ := recorded_rule_occurrence (gates hs) (lifts hs) x v g hrj
  have h := gram_support_disjoint (gates hs) (lifts hs) g hx hfit hL hk hk'
  have hh := representatives_eq_of_patch a h
  exact hij (hu.symm.trans (hh.trans hv))

theorem candidateOK_iff (H : TernaryMatrix θ (q^L)) (pad : Fin q) (x : Fin ℓ → Fin q)
    (hs : History ℓ q L s) (words : Fin s → Borrowed.BubbleWord (Fin q) K b L)
    (hv : FibreEnumeration.IsBoolean (spectrum pad x L))
    (hp : ∀ {i j : Fin hs.length}, i ≠ j → ∀ g,
      ComponentExposure.occupies (parts hs i) g = true → ComponentExposure.occupies (parts hs j) g ≠ true) :
    let ρ := CatalogueEnumeration.row pad words
    let v := spectrum pad x L
    candidateOK H pad x hs words = true ↔
      H.mulVec ρ = 0 ∧ ρ ∉ span (oldRows hs) ∧
        ∃ w ∈ span (oldRows hs), FibreEnumeration.IsBoolean (v+w) ∧ FibreEnumeration.IsBoolean (v+w+ρ) := by
  dsimp only
  unfold candidateOK
  simp only [Bool.and_eq_true_iff,beq_iff_eq,Bool.not_eq_true',← Bool.not_eq_true]
  rw [ComponentExposure.check_span _ _ _ hv hp,parts_span]
  rw [show (¬inSpan (oldRows hs) (CatalogueEnumeration.row pad words) = true) ↔
    CatalogueEnumeration.row pad words ∉ span (oldRows hs) from not_congr (inSpan_iff _ _)]
  tauto

theorem parts_fibre_bound (hs : History ℓ q L s) (v : Row (q^L)) (p : Fin hs.length)
    {R : ℕ}
    (hc : ∀ i : Fin hs.length, (componentRules (PatchTable.incidence (gates hs)) (.inl i)).card ≤ R) :
    (FibreEnumeration.enumerate (parts hs p) v).length ≤ 2^R :=
  (FibreEnumeration.enumerate_length _ _).trans
    (Nat.pow_le_pow_right (by decide) (partRows_length_le _ _ _ hc))

#print axioms parts_support_disjoint
#print axioms candidateOK_iff
#print axioms parts_fibre_bound

end DeletionCode.Explicit.Recognizer
