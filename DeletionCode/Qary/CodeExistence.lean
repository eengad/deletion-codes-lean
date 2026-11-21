import DeletionCode.Qary.PaperProbability
import DeletionCode.FiniteDiscard
import DeletionCode.Qary.GoodWordBridge
import DeletionCode.Qary.RedundancyBounds

/-!
The full finite-alphabet code-existence argument. Uniform random circle
hashes retain a constant fraction of all words, and bipartite selection
gives actual correcting codes. The explicit remainder coefficient depends
only on t; the eventual length threshold may depend on the alphabet.
-/
namespace DeletionCode.Qary.CodeExistence

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

open DeletionCode.Qary.HeaderRecovery DeletionCode.Qary.Windows DeletionCode.Qary.SignedSupport DeletionCode.CircleUniform DeletionCode.CircleHash
open DeletionCode.Qary.ExceptionalProbability DeletionCode.Qary.ObstructionProbability DeletionCode.Qary.CodeSelection

def labelCount (q t n : ℕ) : ℕ :=
  RedundancyBounds.labelCount q (2 * t - 1) (12 * t) (WitnessCost.exponent t) n

def remainderCoefficient (t : ℕ) : ℕ := 2 * WitnessCost.exponent t + 12 * t + 6

theorem labelCount_eq_scale (q t n : ℕ) :
    labelCount q t n = 8 * ObstructionBound.scale q t n (PaperParameters.k n) := by
  unfold labelCount RedundancyBounds.labelCount ObstructionBound.scale PaperParameters.L
    DeletionCode.Qary.HeaderRecovery.windowLength DeletionCode.HeaderRecovery.windowLength
  ring

/-- A finite code with the required cardinality, under explicit parameter thresholds. -/
theorem exists_large_code (t n : ℕ) (ht : 2 ≤ t) (hq : 2 ≤ Fintype.card α)
    (hn : 1 ≤ n) (hfit : PaperParameters.L n ≤ n)
    (hready : PaperProbability.threshold t ≤ PaperParameters.L n) :
    ∃ C : Finset (Bits α n), Corrects t C ∧
      Fintype.card α ^ n ≤ 8 * labelCount (Fintype.card α) t n * C.card := by
  classical
  let q := Fintype.card α
  let Q := labelCount q t n
  have hQ : 8 * ObstructionBound.scale q t n (PaperParameters.k n) ≤ Q := by
    dsimp only [Q]
    rw [labelCount_eq_scale]
  have hQtwo : 2 ≤ Q := PaperProbability.labels_ge_two q t n Q (by dsimp [q]; omega) hn hQ
  let s := UniqueWordCount.uniqueWords α n (PaperParameters.k n)
  let E := fun x : Bits α n =>
    exceptionalEvent t (PaperParameters.k n) Q x ∪
      obstructionEvent t (PaperParameters.k n) Q x
  obtain ⟨weights, hhalf⟩ := FiniteDiscard.exists_half_retained
    (realWeights (Gram α (windowLength (PaperParameters.k n)))) s E (by
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
  have hunique : q ^ n ≤ 2 * s.card := UniqueWordCount.card_pow_le_two_mul_card_unique n hq
  refine ⟨C, hcorrect, ?_⟩
  change q ^ n ≤ 8 * Q * C.card
  calc
    q ^ n ≤ 2 * s.card := hunique
    _ ≤ 2 * (2 * (2 * Q * C.card)) :=
      Nat.mul_le_mul_left 2 (hhalf'.trans (Nat.mul_le_mul_left 2 hselect))
    _ = 8 * Q * C.card := by ring

/-- The actual code theorem, with an explicit alphabet-independent coefficient. -/
theorem eventually_exists_code (t : ℕ) (ht : 2 ≤ t) (hq : 2 ≤ Fintype.card α) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ C : Finset (Bits α n),
      Corrects t C ∧ C.Nonempty ∧
      Fintype.card α ^ n ≤ 8 * labelCount (Fintype.card α) t n * C.card ∧
      RedundancyBounds.redundancy (Fintype.card α) n C ≤
        ((2 * t - 1 : ℕ) : ℝ) * Real.logb (Fintype.card α) (n : ℝ) +
          (remainderCoefficient t : ℝ) *
            Real.logb (Fintype.card α) (Real.logb (Fintype.card α) (n : ℝ)) := by
  filter_upwards [PaperParameters.eventually_ready (PaperProbability.threshold t),
    RedundancyBounds.eventually_paper_redundancy_bound
      (Fintype.card α) (2 * t - 1) (12 * t) (WitnessCost.exponent t) hq] with n hready hbound
  obtain ⟨C, hcorrect, hcard⟩ := exists_large_code t n ht hq (by omega) hready.2.1 hready.2.2
  exact ⟨C, hcorrect,
    RedundancyBounds.code_nonempty (Fintype.card α) n _ C (by omega) hcard,
    hcard, hbound C hcard⟩

theorem main (t : ℕ) (ht : 2 ≤ t) (hq : 2 ≤ Fintype.card α) :
    ∃ K : ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∃ C : Finset (Bits α n),
      Corrects t C ∧ C.Nonempty ∧
      RedundancyBounds.redundancy (Fintype.card α) n C ≤
        ((2 * t - 1 : ℕ) : ℝ) * Real.logb (Fintype.card α) (n : ℝ) +
          (K : ℝ) * Real.logb (Fintype.card α) (Real.logb (Fintype.card α) (n : ℝ)) := by
  refine ⟨remainderCoefficient t, ?_⟩
  filter_upwards [eventually_exists_code (α := α) t ht hq] with n hn
  obtain ⟨C, hC, hne, _hcard, hred⟩ := hn
  exact ⟨C, hC, hne, hred⟩

/-- The same K works over every finite alphabet of size at least two. -/
theorem main_uniform (t : ℕ) (ht : 2 ≤ t) :
    ∃ K : ℕ, ∀ (β : Type*) [Fintype β], 2 ≤ Fintype.card β →
      ∀ᶠ n : ℕ in Filter.atTop, ∃ C : Finset (Bits β n),
        Corrects t C ∧ C.Nonempty ∧
        RedundancyBounds.redundancy (Fintype.card β) n C ≤
          ((2 * t - 1 : ℕ) : ℝ) * Real.logb (Fintype.card β) (n : ℝ) +
            (K : ℝ) * Real.logb (Fintype.card β) (Real.logb (Fintype.card β) (n : ℝ)) := by
  refine ⟨remainderCoefficient t, ?_⟩
  intro β _ hq
  classical
  let _ : Inhabited β := Classical.inhabited_of_nonempty (Fintype.card_pos_iff.mp (by omega))
  filter_upwards [eventually_exists_code (α := β) t ht hq] with n hn
  obtain ⟨C, hC, hne, _hcard, hred⟩ := hn
  exact ⟨C, hC, hne, hred⟩

#print axioms exists_large_code
#print axioms eventually_exists_code
#print axioms main_uniform

end DeletionCode.Qary.CodeExistence
