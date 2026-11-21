import DeletionCode.Burst.CodeExistence
import DeletionCode.Burst.OptimalCode

namespace DeletionCode.Burst.OptimalRedundancy

open DeletionCode.Qary.HeaderRecovery Filter

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

/-- The manuscript's upper bound for optimal bounded-burst-correcting redundancy. -/
theorem main (b t : ℕ) (hb : 1 ≤ b) (ht : 2 ≤ t) (hq : 2 ≤ Fintype.card α) :
    ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      optimalRedundancy α b t n ≤
        ((2 * t - 1 : ℕ) : ℝ) * Real.logb (Fintype.card α) (n : ℝ) +
          (K : ℝ) * Real.logb (Fintype.card α) (Real.logb (Fintype.card α) (n : ℝ)) := by
  obtain ⟨K, hK⟩ := CodeExistence.main (α := α) b t hb ht hq
  refine ⟨K, ?_⟩
  filter_upwards [hK] with n hn
  obtain ⟨C, hC, hne, hbound⟩ := hn
  exact (optimalRedundancy_le_code b t n C hC hne hq).trans hbound

/-- Quantifier order records that the remainder constant is independent of q. -/
theorem main_uniform (b t : ℕ) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ∃ K : ℕ, ∀ (β : Type*) [Fintype β], 2 ≤ Fintype.card β →
      ∀ᶠ n : ℕ in atTop,
        optimalRedundancy β b t n ≤
          ((2 * t - 1 : ℕ) : ℝ) * Real.logb (Fintype.card β) (n : ℝ) +
            (K : ℝ) * Real.logb (Fintype.card β) (Real.logb (Fintype.card β) (n : ℝ)) := by
  refine ⟨CodeExistence.remainderCoefficient b t, ?_⟩
  intro β _ hq
  classical
  let _ : Inhabited β := Classical.inhabited_of_nonempty (Fintype.card_pos_iff.mp (by omega))
  filter_upwards [CodeExistence.eventually_exists_code (α := β) b t hb ht hq] with n hn
  obtain ⟨C, hC, hne, _hcard, hbound⟩ := hn
  exact (optimalRedundancy_le_code b t n C hC hne hq).trans hbound

/-- The same statement using the canonical q-letter alphabet. -/
theorem main_fin (b t : ℕ) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ∃ K : ℕ, ∀ q : ℕ, 2 ≤ q → ∀ᶠ n : ℕ in atTop,
      optimalRedundancy (Fin q) b t n ≤
        ((2 * t - 1 : ℕ) : ℝ) * Real.logb q (n : ℝ) +
          (K : ℝ) * Real.logb q (Real.logb q (n : ℝ)) := by
  obtain ⟨K, hK⟩ := main_uniform b t hb ht
  refine ⟨K, ?_⟩
  intro q hq
  simpa only [Fintype.card_fin] using hK (Fin q) (by simpa using hq)

#print axioms optimalCodeSize_pos
#print axioms exists_optimal_code
#print axioms optimalRedundancy_le_code
#print axioms exists_code_redundancy_eq_optimal
#print axioms main
#print axioms main_uniform
#print axioms main_fin

end DeletionCode.Burst.OptimalRedundancy
