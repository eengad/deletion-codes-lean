import DeletionCode.WitnessAlgebra
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel

/-!
A finite closed walk whose steps are signed members of an independent family
has even length. The zero-sum relation is derived from the actual successive
vertices, rather than assumed separately.
-/

namespace DeletionCode.ClosedWalk

open scoped BigOperators

/-- Successive displacements telescope, including both endpoints. -/
theorem sum_displacements {V : Type*} [AddCommGroup V] {m : ℕ}
    (p : Fin (m + 1) → V) :
    (∑ i : Fin m, (p i.succ - p i.castSucc)) = p (Fin.last m) - p 0 := by
  rw [Finset.sum_sub_distrib]
  have h := (Fin.sum_univ_succ p).symm.trans (Fin.sum_univ_castSucc p)
  calc
    (∑ i : Fin m, p i.succ) - ∑ i : Fin m, p i.castSucc =
        (p 0 + ∑ i : Fin m, p i.succ) - (p 0 + ∑ i : Fin m, p i.castSucc) := by
      abel
    _ = ((∑ i : Fin m, p i.castSucc) + p (Fin.last m)) -
        (p 0 + ∑ i : Fin m, p i.castSucc) := by rw [h]
    _ = p (Fin.last m) - p 0 := by
      abel

/-- A closed walk using only signed independent generators has even length. -/
theorem signed_independent_closed_walk_even {I V : Type*} [Fintype I]
    [AddCommGroup V] [Module ℚ V] {m : ℕ}
    (G : I → V) (hG : LinearIndependent ℚ G) (p : Fin (m + 1) → V)
    (label : Fin m → I) (hclosed : p 0 = p (Fin.last m))
    (hsteps : ∀ i : Fin m,
      p i.succ - p i.castSucc = G (label i) ∨
      p i.succ - p i.castSucc = -G (label i)) : Even m := by
  classical
  let positive : Fin m → Prop := fun i => p i.succ - p i.castSucc = G (label i)
  have hstep : ∀ i : Fin m,
      (if positive i then (1 : ℚ) else -1) • G (label i) =
        p i.succ - p i.castSucc := by
    intro i
    by_cases hi : positive i
    · simpa only [ite_eq_left hi, one_smul] using hi.symm
    · have hneg := (hsteps i).resolve_left hi
      simpa only [ite_eq_right hi, neg_smul, one_smul] using hneg.symm
  have hsum : (∑ i : Fin m,
      (if positive i then (1 : ℚ) else -1) • G (label i)) = 0 := by
    simp_rw [hstep]
    rw [sum_displacements, ← hclosed, sub_self]
  simpa using WitnessAlgebra.signed_sum_even G hG label positive hsum

/-- In particular, an odd closed walk must use a step outside ±G. -/
theorem not_odd_signed_independent_closed_walk {I V : Type*} [Fintype I]
    [AddCommGroup V] [Module ℚ V] {m : ℕ}
    (G : I → V) (hG : LinearIndependent ℚ G) (p : Fin (m + 1) → V)
    (label : Fin m → I) (hclosed : p 0 = p (Fin.last m))
    (hsteps : ∀ i : Fin m,
      p i.succ - p i.castSucc = G (label i) ∨
      p i.succ - p i.castSucc = -G (label i)) : ¬ Odd m := by
  rintro ⟨a, ha⟩
  obtain ⟨b, hb⟩ := signed_independent_closed_walk_even G hG p label hclosed hsteps
  omega

#print axioms sum_displacements
#print axioms signed_independent_closed_walk_even
#print axioms not_odd_signed_independent_closed_walk

end DeletionCode.ClosedWalk
