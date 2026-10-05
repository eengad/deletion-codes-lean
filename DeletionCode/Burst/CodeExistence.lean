import DeletionCode.Burst.PaperProbability
import DeletionCode.FiniteDiscard
import DeletionCode.Burst.GoodWordBridge
import DeletionCode.Burst.RedundancyBounds

/-!
The full finite-alphabet code-existence argument. Uniform random circle
hashes retain a constant fraction of all words, and bipartite selection
gives actual correcting codes. The explicit remainder coefficient depends
only on t and b; the eventual length threshold may depend on the alphabet.
-/
namespace DeletionCode.Burst.CodeExistence

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

open Qary.HeaderRecovery (Bits padBits)
open Qary.Windows Qary.SignedSupport CircleUniform CircleHash
open ExceptionalProbability ObstructionProbability CodeSelection

def labelCount (q b t n : ℕ) : ℕ :=
  RedundancyBounds.labelCount b q (2 * t - 1) (12 * b * t) (WitnessCost.exponent t) n

def remainderCoefficient (b t : ℕ) : ℕ := 2 * WitnessCost.exponent t + 12 * b * t + 6

theorem labelCount_eq_scale (q b t n : ℕ) :
    labelCount q b t n = 8 * ObstructionBound.scale q b t n (Parameters.k n) := by
  unfold labelCount RedundancyBounds.labelCount ObstructionBound.scale Parameters.L
    windowLength
  ring

/-- A finite code with the required cardinality, under explicit parameter thresholds. -/
theorem exists_large_code (b t n : ℕ) (hb : 1 ≤ b) (ht : 2 ≤ t) (hq : 2 ≤ Fintype.card α)
    (hn : 1 ≤ n) (hfit : Parameters.L b n ≤ n)
    (hready : PaperProbability.threshold b t ≤ Parameters.L b n) :
    ∃ C : Finset (Bits α n), Corrects b t C ∧
      Fintype.card α ^ n ≤ 8 * labelCount (Fintype.card α) b t n * C.card := by
  classical
  let q := Fintype.card α
  let Q := labelCount q b t n
  have hQ : 8 * ObstructionBound.scale q b t n (Parameters.k n) ≤ Q := by
    dsimp only [Q]
    rw [labelCount_eq_scale]
  have hQtwo : 2 ≤ Q := PaperProbability.labels_ge_two q b t n Q (by dsimp [q]; omega) hn hQ
  let s := Qary.UniqueWordCount.uniqueWords α n (Parameters.k n)
  let E := fun x : Bits α n =>
    exceptionalEvent b t (Parameters.k n) Q x ∪
      obstructionEvent b t (Parameters.k n) Q x
  obtain ⟨weights, hhalf⟩ := FiniteDiscard.exists_half_retained
    (realWeights (Gram α (windowLength (Parameters.k n) b))) s E (by
      intro x hx
      have h := PaperProbability.total_discard_le b t Q ht hb x
        ((Qary.UniqueWordCount.mem_uniqueWords x).mp hx) hfit hready hQ
      unfold Parameters.L at h
      exact h)
  have hhalf' : s.card ≤ 2 *
      (GoodWordBridge.retainedWords (n := n) b t (Parameters.k n) Q weights).card := by
    simpa only [GoodWordBridge.retainedWords, s, E] using hhalf
  rw [GoodWordBridge.card_retainedWords] at hhalf'
  obtain ⟨C, hselect, hcorrect⟩ := exists_correcting_code (n := n) b t Q hQtwo
    (realWeightedHash weights)
  have hunique : q ^ n ≤ 2 * s.card := Qary.UniqueWordCount.card_pow_le_two_mul_card_unique n hq
  refine ⟨C, hcorrect, ?_⟩
  change q ^ n ≤ 8 * Q * C.card
  calc
    q ^ n ≤ 2 * s.card := hunique
    _ ≤ 2 * (2 * (2 * Q * C.card)) :=
      Nat.mul_le_mul_left 2 (hhalf'.trans (Nat.mul_le_mul_left 2 hselect))
    _ = 8 * Q * C.card := by ring

/-- The actual code theorem, with an explicit alphabet-independent coefficient. -/
theorem eventually_exists_code (b t : ℕ) (hb : 1 ≤ b) (ht : 2 ≤ t) (hq : 2 ≤ Fintype.card α) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ C : Finset (Bits α n),
      Corrects b t C ∧ C.Nonempty ∧
      Fintype.card α ^ n ≤ 8 * labelCount (Fintype.card α) b t n * C.card ∧
      Qary.RedundancyBounds.redundancy (Fintype.card α) n C ≤
        ((2 * t - 1 : ℕ) : ℝ) * Real.logb (Fintype.card α) (n : ℝ) +
          (remainderCoefficient b t : ℝ) *
            Real.logb (Fintype.card α) (Real.logb (Fintype.card α) (n : ℝ)) := by
  filter_upwards [Parameters.eventually_ready b (PaperProbability.threshold b t),
    RedundancyBounds.eventually_paper_redundancy_bound
      b (Fintype.card α) (2 * t - 1) (12 * b * t) (WitnessCost.exponent t) hq] with n hready hbound
  obtain ⟨C, hcorrect, hcard⟩ := exists_large_code b t n hb ht hq (by omega) hready.2.2.1 hready.2.2.2
  exact ⟨C, hcorrect,
    Qary.RedundancyBounds.code_nonempty (Fintype.card α) n _ C (by omega) hcard,
    hcard, hbound C hcard⟩

theorem main (b t : ℕ) (hb : 1 ≤ b) (ht : 2 ≤ t) (hq : 2 ≤ Fintype.card α) :
    ∃ K : ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∃ C : Finset (Bits α n),
      Corrects b t C ∧ C.Nonempty ∧
      Qary.RedundancyBounds.redundancy (Fintype.card α) n C ≤
        ((2 * t - 1 : ℕ) : ℝ) * Real.logb (Fintype.card α) (n : ℝ) +
          (K : ℝ) * Real.logb (Fintype.card α) (Real.logb (Fintype.card α) (n : ℝ)) := by
  refine ⟨remainderCoefficient b t, ?_⟩
  filter_upwards [eventually_exists_code (α := α) b t hb ht hq] with n hn
  obtain ⟨C, hC, hne, _hcard, hred⟩ := hn
  exact ⟨C, hC, hne, hred⟩

/-- The same K works over every finite alphabet of size at least two. -/
theorem main_uniform (b t : ℕ) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ∃ K : ℕ, ∀ (β : Type*) [Fintype β], 2 ≤ Fintype.card β →
      ∀ᶠ n : ℕ in Filter.atTop, ∃ C : Finset (Bits β n),
        Corrects b t C ∧ C.Nonempty ∧
        Qary.RedundancyBounds.redundancy (Fintype.card β) n C ≤
          ((2 * t - 1 : ℕ) : ℝ) * Real.logb (Fintype.card β) (n : ℝ) +
            (K : ℝ) * Real.logb (Fintype.card β) (Real.logb (Fintype.card β) (n : ℝ)) := by
  refine ⟨remainderCoefficient b t, ?_⟩
  intro β _ hq
  classical
  let _ : Inhabited β := Classical.inhabited_of_nonempty (Fintype.card_pos_iff.mp (by omega))
  filter_upwards [eventually_exists_code (α := β) b t hb ht hq] with n hn
  obtain ⟨C, hC, hne, _hcard, hred⟩ := hn
  exact ⟨C, hC, hne, hred⟩

#print axioms exists_large_code
#print axioms eventually_exists_code
#print axioms main_uniform

end DeletionCode.Burst.CodeExistence
