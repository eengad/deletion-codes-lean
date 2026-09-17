import DeletionCode.CodeExistence
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold

/-!
The optimal cardinality is the maximum over all actual correcting subsets
of the finite n-bit word space. The maximum is attained and is positive.
The code-existence theorem therefore gives the claimed bound on red*(n),
rather than only a bound for an unspecified feasible code.
-/
namespace DeletionCode.OptimalRedundancy

open HeaderRecovery Filter

noncomputable def correctingCodes (t n : ℕ) : Finset (Finset (Bits n)) := by
  classical
  exact Finset.univ.filter (CodeSelection.Corrects t)

theorem mem_correctingCodes (t n : ℕ) (C : Finset (Bits n)) :
    C ∈ correctingCodes t n ↔ CodeSelection.Corrects t C := by
  classical
  simp only [correctingCodes, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The maximum number of words in an actual radius-t edit-correcting code. -/
noncomputable def optimalCodeSize (t n : ℕ) : ℕ :=
  (correctingCodes t n).sup Finset.card

theorem singleton_corrects (t n : ℕ) (x : Bits n) :
    CodeSelection.Corrects t ({x} : Finset (Bits n)) := by
  classical
  intro a ha b hb hne
  have ha' : a = x := Finset.mem_singleton.mp ha
  have hb' : b = x := Finset.mem_singleton.mp hb
  exact False.elim (hne (ha'.trans hb'.symm))

theorem correctingCodes_nonempty (t n : ℕ) : (correctingCodes t n).Nonempty := by
  classical
  refine ⟨{fun _ : Fin n => false}, ?_⟩
  exact (mem_correctingCodes t n _).mpr (singleton_corrects t n _)

theorem card_le_optimalCodeSize (t n : ℕ) (C : Finset (Bits n))
    (hC : CodeSelection.Corrects t C) : C.card ≤ optimalCodeSize t n := by
  unfold optimalCodeSize
  exact Finset.le_sup ((mem_correctingCodes t n C).mpr hC)

theorem one_le_optimalCodeSize (t n : ℕ) : 1 ≤ optimalCodeSize t n := by
  classical
  have h := card_le_optimalCodeSize t n {fun _ : Fin n => false}
    (singleton_corrects t n _)
  simpa only [Finset.card_singleton] using h

theorem optimalCodeSize_pos (t n : ℕ) : 0 < optimalCodeSize t n :=
  one_le_optimalCodeSize t n

/-- Finiteness gives a correcting code attaining the maximum. -/
theorem exists_optimal_code (t n : ℕ) :
    ∃ C : Finset (Bits n), CodeSelection.Corrects t C ∧ C.Nonempty ∧
      C.card = optimalCodeSize t n := by
  obtain ⟨C, hC, hmax⟩ := Finset.exists_mem_eq_sup
    (correctingCodes t n) (correctingCodes_nonempty t n) Finset.card
  have heq : C.card = optimalCodeSize t n := hmax.symm
  refine ⟨C, (mem_correctingCodes t n C).mp hC, ?_, heq⟩
  apply Finset.card_pos.mp
  rw [heq]
  exact optimalCodeSize_pos t n

/-- The manuscript's optimal redundancy red*(n), with the error radius explicit. -/
noncomputable def optimalRedundancy (t n : ℕ) : ℝ :=
  (n : ℝ) - Real.logb 2 (optimalCodeSize t n : ℝ)

theorem optimalRedundancy_le_code (t n : ℕ) (C : Finset (Bits n))
    (hC : CodeSelection.Corrects t C) (hne : C.Nonempty) :
    optimalRedundancy t n ≤ RedundancyBounds.redundancy n C := by
  have hc : (0 : ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hbound : (C.card : ℝ) ≤ optimalCodeSize t n := by
    exact_mod_cast card_le_optimalCodeSize t n C hC
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hc hbound
  unfold optimalRedundancy RedundancyBounds.redundancy
  linarith

/-- The maximum-cardinality definition is exactly the minimum attainable redundancy. -/
theorem exists_code_redundancy_eq_optimal (t n : ℕ) :
    ∃ C : Finset (Bits n), CodeSelection.Corrects t C ∧ C.Nonempty ∧
      RedundancyBounds.redundancy n C = optimalRedundancy t n := by
  obtain ⟨C, hC, hne, hcard⟩ := exists_optimal_code t n
  refine ⟨C, hC, hne, ?_⟩
  simp only [RedundancyBounds.redundancy, optimalRedundancy, hcard]

/-- The manuscript's upper bound for optimal edit-correcting redundancy. -/
theorem main (t : ℕ) (ht : 2 ≤ t) :
    ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      optimalRedundancy t n ≤
        ((2 * t - 1 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) +
          (K : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) := by
  obtain ⟨K, hK⟩ := CodeExistence.main t ht
  refine ⟨K, ?_⟩
  filter_upwards [hK] with n hn
  obtain ⟨C, hC, hne, hbound⟩ := hn
  exact (optimalRedundancy_le_code t n C hC hne).trans hbound

#print axioms optimalCodeSize_pos
#print axioms exists_optimal_code
#print axioms optimalRedundancy_le_code
#print axioms exists_code_redundancy_eq_optimal
#print axioms main

end DeletionCode.OptimalRedundancy
