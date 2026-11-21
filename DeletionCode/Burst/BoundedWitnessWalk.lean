import DeletionCode.Burst.RelationSavings
import DeletionCode.Burst.WitnessExtraction
import DeletionCode.Qary.SpectrumPath

/-! Bounded burst-catalogue witnesses from actual odd closed word walks. -/
namespace DeletionCode.Burst.BoundedWitnessWalk

open DeletionCode.Qary.Windows DeletionCode.Qary.SignedSupport DeletionCode.Qary.SignedRuleCount
open DeletionCode.Qary.FiniteWalkRules

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

abbrev Witness (t k b : ℕ) (v : Gram α (windowLength k b) → ℤ)
    (K : Set (Gram α (windowLength k b) → ℤ)) (U : RuleSet α (k + b)) : Prop :=
  WitnessExtraction.Witness t (k + b) (2 * t * (2 * windowLength k b + 2 * b + 1))
    {u | Catalogue.Rule t k b u} v K U

theorem extract {t k b m : ℕ} (ht : 2 ≤ t)
    (p : Fin (m + 1) → Gram α (windowLength k b) → ℤ)
    (K : Set (Gram α (windowLength k b) → ℤ))
    (hp : ∀ j, Qary.WitnessAlgebra.BooleanVector (rationalPath p j))
    (hclosed : p 0 = p (Fin.last m)) (hodd : Odd m)
    (hcat : ∀ i, Catalogue.Rule t k b (step p i))
    (hK : ∀ i, step p i ∈ K) :
    ∃ U : RuleSet α (k + b), Witness t k b (p 0) K U :=
  WitnessExtraction.extract (RelationSavings.catalogue_facts t k b (by omega))
    ht p K hp hclosed hodd hcat hK

theorem extract_word_walk {t k b m n : ℕ} (ht : 2 ≤ t)
    (words : Fin (m + 1) → Letters α)
    (K : Set (Gram α (windowLength k b) → ℤ))
    (hunique : ∀ j, KUnique (words j) n k)
    (hclosed : Agree (words 0) 0 (words (Fin.last m)) 0 n) (hodd : Odd m)
    (hcat : ∀ i : Fin m, Catalogue.Rule t k b
      (wordSpectrum (words i.succ) n (windowLength k b) -
       wordSpectrum (words i.castSucc) n (windowLength k b)))
    (hK : ∀ i : Fin m, (wordSpectrum (words i.succ) n (windowLength k b) -
       wordSpectrum (words i.castSucc) n (windowLength k b)) ∈ K) :
    ∃ U : RuleSet α (k + b),
      Witness t k b (wordSpectrum (words 0) n (windowLength k b)) K U := by
  classical
  let p := fun j => wordSpectrum (words j) n (windowLength k b)
  have hp : ∀ j, Qary.WitnessAlgebra.BooleanVector (rationalPath p j) := by
    intro j g
    have hku := Qary.SpectrumPath.kunique_mono (words j) n k (windowLength k b - 1)
      (hunique j) (by unfold windowLength; omega)
    rcases Qary.SpectrumPath.spectrum_boolean (words j) n (windowLength k b) hku g with hz | ho
    · left; change (wordSpectrum (words j) n (windowLength k b) g : ℚ) = 0
      exact_mod_cast hz
    · right; change (wordSpectrum (words j) n (windowLength k b) g : ℚ) = 1
      exact_mod_cast ho
  have hclosedP : p 0 = p (Fin.last m) := by
    funext g
    unfold p wordSpectrum
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val + windowLength k b ≤ n
    · have heq : gram (words 0) (windowLength k b) i.val =
          gram (words (Fin.last m)) (windowLength k b) i.val := by
        funext q
        have hq := hclosed (i.val + q.val) (by have := q.isLt; omega)
        simpa only [Nat.zero_add, gram] using hq
      simp only [hi, true_and, heq]
    · simp only [hi, false_and, ite_false]
  exact extract ht p K hp hclosedP hodd hcat hK

end DeletionCode.Burst.BoundedWitnessWalk
