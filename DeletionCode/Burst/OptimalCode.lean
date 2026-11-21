import DeletionCode.Burst.CodeSelection
import DeletionCode.Qary.RedundancyBounds
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold

/-!
The optimal cardinality is the maximum over all actual correcting subsets
of the finite word space over the given alphabet. The maximum is attained and is positive.
The code-existence theorem therefore gives the claimed bound on red*(n),
rather than only a bound for an unspecified feasible code.
-/
namespace DeletionCode.Burst.OptimalRedundancy

open DeletionCode.Qary.HeaderRecovery Filter

variable {α : Type*} [Fintype α] [Inhabited α]

noncomputable def correctingCodes (α : Type*) [Fintype α] (b t n : ℕ) : Finset (Finset (Bits α n)) := by
  classical
  exact Finset.univ.filter (CodeSelection.Corrects b t)

omit [Inhabited α] in
theorem mem_correctingCodes (b t n : ℕ) (C : Finset (Bits α n)) :
    C ∈ correctingCodes α b t n ↔ CodeSelection.Corrects b t C := by
  classical
  simp only [correctingCodes, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The maximum number of words in an actual radius-t bounded-burst-correcting code. -/
noncomputable def optimalCodeSize (α : Type*) [Fintype α] (b t n : ℕ) : ℕ :=
  (correctingCodes α b t n).sup Finset.card

omit [Fintype α] [Inhabited α] in
theorem singleton_corrects (b t n : ℕ) (x : Bits α n) :
    CodeSelection.Corrects b t ({x} : Finset (Bits α n)) := by
  classical
  intro a ha b hb hne
  have ha' : a = x := Finset.mem_singleton.mp ha
  have hb' : b = x := Finset.mem_singleton.mp hb
  exact False.elim (hne (ha'.trans hb'.symm))

theorem correctingCodes_nonempty (b t n : ℕ) : (correctingCodes α b t n).Nonempty := by
  classical
  refine ⟨{fun _ : Fin n => (default : α)}, ?_⟩
  exact (mem_correctingCodes b t n _).mpr (singleton_corrects b t n _)

omit [Inhabited α] in
theorem card_le_optimalCodeSize (b t n : ℕ) (C : Finset (Bits α n))
    (hC : CodeSelection.Corrects b t C) : C.card ≤ optimalCodeSize α b t n := by
  unfold optimalCodeSize
  exact Finset.le_sup ((mem_correctingCodes b t n C).mpr hC)

theorem one_le_optimalCodeSize (b t n : ℕ) : 1 ≤ optimalCodeSize α b t n := by
  classical
  have h := card_le_optimalCodeSize b t n {fun _ : Fin n => (default : α)}
    (singleton_corrects b t n _)
  simpa only [Finset.card_singleton] using h

theorem optimalCodeSize_pos (b t n : ℕ) : 0 < optimalCodeSize α b t n :=
  one_le_optimalCodeSize (α := α) b t n

/-- Finiteness gives a correcting code attaining the maximum. -/
theorem exists_optimal_code (b t n : ℕ) :
    ∃ C : Finset (Bits α n), CodeSelection.Corrects b t C ∧ C.Nonempty ∧
      C.card = optimalCodeSize α b t n := by
  obtain ⟨C, hC, hmax⟩ := Finset.exists_mem_eq_sup
    (correctingCodes α b t n) (correctingCodes_nonempty b t n) Finset.card
  have heq : C.card = optimalCodeSize α b t n := hmax.symm
  refine ⟨C, (mem_correctingCodes b t n C).mp hC, ?_, heq⟩
  apply Finset.card_pos.mp
  rw [heq]
  exact optimalCodeSize_pos b t n

/-- The manuscript's optimal redundancy red*(n), with the error radius and block bound explicit. -/
noncomputable def optimalRedundancy (α : Type*) [Fintype α] (b t n : ℕ) : ℝ :=
  (n : ℝ) - Real.logb (Fintype.card α) (optimalCodeSize α b t n : ℝ)

omit [Inhabited α] in
theorem optimalRedundancy_le_code (b t n : ℕ) (C : Finset (Bits α n))
    (hC : CodeSelection.Corrects b t C) (hne : C.Nonempty) (hq : 2 ≤ Fintype.card α) :
    optimalRedundancy α b t n ≤ Qary.RedundancyBounds.redundancy (Fintype.card α) n C := by
  have hc : (0 : ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hbound : (C.card : ℝ) ≤ optimalCodeSize α b t n := by
    exact_mod_cast card_le_optimalCodeSize b t n C hC
  have hb : (1 : ℝ) < Fintype.card α := by exact_mod_cast (show 1 < Fintype.card α by omega)
  have hlog := Real.logb_le_logb_of_le hb hc hbound
  unfold optimalRedundancy Qary.RedundancyBounds.redundancy
  linarith

/-- The maximum-cardinality definition is exactly the minimum attainable redundancy. -/
theorem exists_code_redundancy_eq_optimal (b t n : ℕ) :
    ∃ C : Finset (Bits α n), CodeSelection.Corrects b t C ∧ C.Nonempty ∧
      Qary.RedundancyBounds.redundancy (Fintype.card α) n C = optimalRedundancy α b t n := by
  obtain ⟨C, hC, hne, hcard⟩ := exists_optimal_code (α := α) b t n
  refine ⟨C, hC, hne, ?_⟩
  simp only [Qary.RedundancyBounds.redundancy, optimalRedundancy, hcard]

#print axioms optimalCodeSize_pos
#print axioms exists_optimal_code
#print axioms optimalRedundancy_le_code
#print axioms exists_code_redundancy_eq_optimal

end DeletionCode.Burst.OptimalRedundancy
