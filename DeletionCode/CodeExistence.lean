import DeletionCode.PaperProbability
import DeletionCode.FiniteDiscard
import DeletionCode.GoodWordBridge
import DeletionCode.RedundancyBounds

/-!
The final code-existence argument of Theorem `thm:main` in the active
circle-hash manuscript. The actual random hash has an outcome retaining
at least half the unique words; bipartite selection and a common label
give a correcting code. All probability, cardinality, and large-n
conditions are proved, rather than supplied by the theorem's caller.
-/
namespace DeletionCode.CodeExistence

open HeaderRecovery Windows SignedSupport CircleUniform CircleHash
open ExceptionalProbability ObstructionProbability CodeSelection

/-- The chosen integer Q is exactly the required scale; no rounding loss
is needed because all factors in the manuscript's ceiling are integers. -/
theorem labelCount_eq_scale (t n : ℕ) :
    RedundancyBounds.labelCount t n =
      8 * ObstructionBound.scale t n (PaperParameters.k n) := by
  unfold RedundancyBounds.labelCount ObstructionBound.scale PaperParameters.L
  ring

/-- The finite code-size bound under the explicit parameter thresholds.
The code corrects the actual insertion/deletion relation on binary words. -/
theorem exists_large_code (t n : ℕ) (ht : 2 ≤ t) (hn : 1 ≤ n)
    (hfit : PaperParameters.L n ≤ n)
    (hready : PaperProbability.threshold t ≤ PaperParameters.L n) :
    ∃ C : Finset (Bits n), Corrects t C ∧
      2 ^ n ≤ 8 * RedundancyBounds.labelCount t n * C.card := by
  classical
  let Q := RedundancyBounds.labelCount t n
  have hQ : 8 * ObstructionBound.scale t n (PaperParameters.k n) ≤ Q := by
    dsimp only [Q]
    rw [labelCount_eq_scale]
  have hQtwo : 2 ≤ Q := PaperProbability.labels_ge_two t n Q hn hQ
  let s := UniqueWordCount.uniqueWords n (PaperParameters.k n)
  let E := fun x : Bits n =>
    exceptionalEvent t (PaperParameters.k n) Q x ∪
      obstructionEvent t (PaperParameters.k n) Q x
  obtain ⟨weights, hhalf⟩ := FiniteDiscard.exists_half_retained
    (realWeights (Gram (windowLength (PaperParameters.k n)))) s E (by
      intro x hx
      have h := PaperProbability.total_discard_le t Q ht x
        ((UniqueWordCount.mem_uniqueWords x).mp hx) hfit hready hQ
      unfold PaperParameters.L at h
      exact h)
  have hhalf' : s.card ≤ 2 *
      (GoodWordBridge.retainedWords (n := n) t (PaperParameters.k n) Q weights).card := by
    simpa only [GoodWordBridge.retainedWords, s, E] using hhalf
  rw [GoodWordBridge.card_retainedWords] at hhalf'
  obtain ⟨C, hselect, hcorrect⟩ := exists_correcting_code (n := n) t Q hQtwo
    (realWeightedHash weights)
  have hunique : 2 ^ (n - 1) ≤ s.card := UniqueWordCount.half_words_le_card_unique n hn
  have hpow : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ, Nat.mul_comm]
  refine ⟨C, hcorrect, ?_⟩
  change 2 ^ n ≤ 8 * Q * C.card
  calc
    2 ^ n = 2 * 2 ^ (n - 1) := hpow
    _ ≤ 2 * s.card := Nat.mul_le_mul_left 2 hunique
    _ ≤ 2 * (2 * (2 * Q * C.card)) :=
      Nat.mul_le_mul_left 2 (hhalf'.trans (Nat.mul_le_mul_left 2 hselect))
    _ = 8 * Q * C.card := by ring

/-- For every fixed t ≥ 2 and all sufficiently large n, an actual binary
code corrects t insertions/deletions and has the stated explicit redundancy. -/
theorem eventually_exists_code (t : ℕ) (ht : 2 ≤ t) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ C : Finset (Bits n),
      Corrects t C ∧ C.Nonempty ∧
      2 ^ n ≤ 8 * RedundancyBounds.labelCount t n * C.card ∧
      RedundancyBounds.redundancy n C ≤
        ((2 * t - 1 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) +
          ((6 * WitnessCost.exponent t + 6 : ℕ) : ℝ) *
            Real.logb 2 (Real.logb 2 (n : ℝ)) := by
  filter_upwards [PaperParameters.eventually_ready (PaperProbability.threshold t),
    Filter.eventually_ge_atTop 4] with n hready hn
  obtain ⟨C, hcorrect, hcard⟩ := exists_large_code t n ht (by omega) hready.2.1 hready.2.2
  exact ⟨C, hcorrect, RedundancyBounds.code_nonempty n _ C hcard, hcard,
    RedundancyBounds.paper_redundancy_bound t n C hn hcard⟩

/-- The code-existence form of the manuscript's main theorem, with the
O_t(log log n) term expressed by an explicit existential constant. -/
theorem main (t : ℕ) (ht : 2 ≤ t) :
    ∃ K : ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∃ C : Finset (Bits n),
      Corrects t C ∧ C.Nonempty ∧
      RedundancyBounds.redundancy n C ≤
        ((2 * t - 1 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) +
          (K : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) := by
  refine ⟨6 * WitnessCost.exponent t + 6, ?_⟩
  filter_upwards [eventually_exists_code t ht] with n hn
  obtain ⟨C, hc, hne, _hcard, hred⟩ := hn
  exact ⟨C, hc, hne, hred⟩

#print axioms exists_large_code
#print axioms eventually_exists_code
#print axioms main

end DeletionCode.CodeExistence
