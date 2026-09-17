import DeletionCode.WalkSelection
import DeletionCode.FiniteGenerating
import DeletionCode.CatalogueAlgebra

/-!
The finite scan selects step indices. This module transfers its conclusions to
the actual finite set of integer rules. Linear independence supplies the unique
selected occurrence of each rule, so its chronological rank is derived rather
than supplied as an additional hypothesis.
-/
namespace DeletionCode.FiniteWalkRules

open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating

variable {k m : ℕ}

def step (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (i : Fin m) :
    Gram (windowLength k) → ℤ := p i.succ - p i.castSucc

def rationalPath (p : Fin (m + 1) → Gram (windowLength k) → ℤ) :
    Fin (m + 1) → Gram (windowLength k) → ℚ := fun j => rational (p j)

noncomputable def selectedRules
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m)) :
    RuleSet k := by
  classical
  exact S.image (step p)

@[simp] theorem rational_step
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (i : Fin m) :
    rational (step p i) = walkStep (rationalPath p) i := by
  funext g
  simp [rational, step, walkStep, rationalPath]

@[simp] theorem mem_selectedRules
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (u : Gram (windowLength k) → ℤ) :
    u ∈ selectedRules p S ↔ ∃ i ∈ S, step p i = u := by
  classical
  exact Finset.mem_image

theorem step_mem_selectedRules
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (i : Fin m) (hi : i ∈ S) : step p i ∈ selectedRules p S :=
  (mem_selectedRules p S _).mpr ⟨i, hi, rfl⟩

@[simp] theorem selectedRules_empty
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) :
    selectedRules p ∅ = ∅ := by
  classical
  simp [selectedRules]

@[simp] theorem selectedRules_insert
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (i : Fin m) : selectedRules p (insert i S) = insert (step p i) (selectedRules p S) := by
  classical
  simp [selectedRules]

theorem selected_step_injOn
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m))) :
    Set.InjOn (step p) (↑S : Set (Fin m)) := by
  intro i hi j hj hij
  have heq : walkStep (rationalPath p) i = walkStep (rationalPath p) j := by
    simpa only [rational_step] using congrArg rational hij
  have hs : (⟨i, hi⟩ : S) = ⟨j, hj⟩ := hind.injective heq
  exact congrArg Subtype.val hs

private theorem selectedIndex_exists
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (u : selectedRules p S) : ∃ i : S, step p i.val = u.val := by
  obtain ⟨i, hi, heq⟩ := (mem_selectedRules p S u.val).mp u.property
  exact ⟨⟨i, hi⟩, heq⟩

noncomputable def selectedIndex
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (u : selectedRules p S) : S := Classical.choose (selectedIndex_exists p S u)

theorem selectedIndex_spec
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (u : selectedRules p S) : step p (selectedIndex p S u).val = u.val :=
  Classical.choose_spec (selectedIndex_exists p S u)

theorem selectedIndex_injective
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m)) :
    Function.Injective (selectedIndex p S) := by
  intro u v huv
  apply Subtype.ext
  calc
    u.val = step p (selectedIndex p S u).val := (selectedIndex_spec p S u).symm
    _ = step p (selectedIndex p S v).val := by rw [huv]
    _ = v.val := selectedIndex_spec p S v

theorem selectedIndex_step
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m)))
    (i : Fin m) (hi : i ∈ S) :
    (selectedIndex p S ⟨step p i, step_mem_selectedRules p S i hi⟩).val = i :=
  selected_step_injOn p S hind (selectedIndex p S _).property hi
    (selectedIndex_spec p S _)

theorem selected_independent
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m))) :
    Independent (selectedRules p S) := by
  have h := hind.comp (selectedIndex p S) (selectedIndex_injective p S)
  change LinearIndependent ℚ (fun u : selectedRules p S => rational u.val)
  convert h using 1
  funext u
  change rational u.val = walkStep (rationalPath p) (selectedIndex p S u).val
  rw [← rational_step, selectedIndex_spec]

noncomputable def selectedRank
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (u : Gram (windowLength k) → ℤ) : ℕ := by
  classical
  exact if hu : u ∈ selectedRules p S then (selectedIndex p S ⟨u, hu⟩).val.val else 0

theorem selectedRank_step
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m)))
    (i : Fin m) (hi : i ∈ S) : selectedRank p S (step p i) = i.val := by
  classical
  simp only [selectedRank, dif_pos (step_mem_selectedRules p S i hi)]
  rw [selectedIndex_step p S hind i hi]

theorem selectedRank_injOn
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m))) :
    Set.InjOn (selectedRank p S) (↑(selectedRules p S) : Set _) := by
  intro u hu v hv heq
  obtain ⟨i, hi, rfl⟩ := (mem_selectedRules p S u).mp hu
  obtain ⟨j, hj, rfl⟩ := (mem_selectedRules p S v).mp hv
  rw [selectedRank_step p S hind i hi, selectedRank_step p S hind j hj] at heq
  exact congrArg (step p) (Fin.ext heq)

theorem selected_generatingAt
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m)))
    (hgen : GeneratingSelected (rationalPath p) S) :
    GeneratingAt (p 0) (selectedRules p S) := by
  classical
  refine ⟨selected_independent p S hind, selectedRank p S,
    selectedRank_injOn p S hind, ?_⟩
  intro u hu g hneg
  obtain ⟨i, hi, rfl⟩ := (mem_selectedRules p S u).mp hu
  have hnegQ : walkStep (rationalPath p) i g = -1 := by
    rw [← rational_step]
    change (step p i g : ℚ) = -1
    exact_mod_cast hneg
  rcases hgen i hi g hnegQ with hbase | ⟨r, hr, hri, hrg⟩
  · left
    intro hz
    apply hbase
    simp [rationalPath, rational, hz]
  · right
    refine ⟨step p r, step_mem_selectedRules p S r hr, ?_, ?_⟩
    · simpa only [selectedRank_step p S hind r hr,
        selectedRank_step p S hind i hi] using hri
    · intro hz
      apply hrg
      rw [← rational_step]
      simp [rational, hz]

theorem rational_image_selectedRules
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m)) :
    rational '' (↑(selectedRules p S) : Set _) =
      walkStep (rationalPath p) '' (↑S : Set (Fin m)) := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨i, hi, rfl⟩ := (mem_selectedRules p S u).mp hu
    exact ⟨i, hi, (rational_step p i).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨step p i, step_mem_selectedRules p S i hi, rational_step p i⟩

theorem selectedSpan_eq
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m)) :
    selectedSpan (walkStep (rationalPath p)) S =
      Submodule.span ℚ (rational '' (↑(selectedRules p S) : Set _)) := by
  rw [rational_image_selectedRules]
  rfl

theorem novelty_transfer
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (i : Fin m)
    (hnew : ¬ SignedMember (walkStep (rationalPath p)) S (walkStep (rationalPath p) i)) :
    ∀ u ∈ selectedRules p S, step p i ≠ u ∧ step p i ≠ -u := by
  intro u hu
  obtain ⟨r, hr, rfl⟩ := (mem_selectedRules p S u).mp hu
  constructor
  · intro heq
    apply hnew
    refine ⟨r, hr, Or.inl ?_⟩
    simpa only [rational_step] using congrArg rational heq
  · intro heq
    apply hnew
    refine ⟨r, hr, Or.inr ?_⟩
    simpa only [rational_neg, rational_step] using congrArg rational heq

#print axioms selected_step_injOn
#print axioms selected_independent
#print axioms selected_generatingAt
#print axioms selectedSpan_eq
#print axioms novelty_transfer

end DeletionCode.FiniteWalkRules
