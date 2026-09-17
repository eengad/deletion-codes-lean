import DeletionCode.WitnessAlgebra

/-!
Support consequences of an actual rational relation between integer rule
vectors. In particular, a coordinate belonging to just one participating rule
cannot disappear when that rule's coefficient is nonzero.
-/
namespace DeletionCode.RelationSupport

open SignedSupport
open scoped BigOperators

/-- A coordinatewise rational relation on the actual integer spectrum vectors. -/
def Relation {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ) : Prop :=
  ∀ g, (w g : ℚ) = ∑ i, a i * (G i g : ℚ)

theorem support_inclusion {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hrel : Relation G w a) (g : Gram L) (hw : w g ≠ 0) :
    ∃ i, G i g ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hz : (w g : ℚ) = 0 := by
    rw [hrel g]
    apply Finset.sum_eq_zero
    intro i _
    simp [hnone i]
  exact hw (by exact_mod_cast hz)

theorem isolated_coordinate_nonzero {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hrel : Relation G w a) (i : I) (g : Gram L)
    (ha : a i ≠ 0) (hgi : G i g ≠ 0)
    (hother : ∀ j, j ≠ i → G j g = 0) : w g ≠ 0 := by
  classical
  have heq : (w g : ℚ) = a i * (G i g : ℚ) := by
    rw [hrel g]
    apply Finset.sum_eq_single i
    · intro j _ hji
      simp [hother j hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  intro hz
  have hcast : (G i g : ℚ) ≠ 0 := by exact_mod_cast hgi
  have hne := mul_ne_zero ha hcast
  apply hne
  simpa only [hz, Int.cast_zero] using heq.symm

#print axioms support_inclusion
#print axioms isolated_coordinate_nonzero

end DeletionCode.RelationSupport
