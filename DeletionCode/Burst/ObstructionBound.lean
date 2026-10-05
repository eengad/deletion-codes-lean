import DeletionCode.Burst.ObstructionProbability
import DeletionCode.Burst.WitnessCost
import DeletionCode.Qary.ObstructionBound

/-!
The numerical and counting conclusion of the obstruction proposition. Fixed
candidate sets are counted before sampling; the graph event is bounded by
their survival union without conditioning on the exceptional set or graph.
-/
namespace DeletionCode.Burst.ObstructionBound

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

open MeasureTheory Qary.Windows Qary.SignedSupport Qary.SignedRuleCount
open Qary.HeaderRecovery (Bits padBits)
open CircleUniform WitnessCounting ObstructionProbability
open Qary.ObstructionBound (survival_term_le geometric_tail_le)
open scoped BigOperators ENNReal

def scale (q b t n k : ℕ) : ℕ := q ^ (12 * b * t) * n ^ (2 * t - 1) * (windowLength k b) ^ (WitnessCost.exponent t)

theorem candidate_count_le (t : ℕ) (ht : 2 ≤ t) (x : Letters α) (n k b R : ℕ)
    (hR : 2 ≤ R) (hx : KUnique x n k) (hn : 1 ≤ n)
    (hbonus : windowLength k b < R → n ≤ 2 ^ R)
    (hL : 8 * t + 2 ≤ windowLength k b) (hcut : R ≤ cutoff t k b) :
    Nat.card {U : RuleSet α (k + b) // Candidate t x n k b R U} ≤ (scale (Fintype.card α) b t n k) ^ R := by
  calc
    _ ≤ 2 ^ R * (2 * t * R + 1) * n ^ ((2 * t - 1) * R) *
        (windowLength k b * R) ^ (CountExponent.exponent t * R) * Fintype.card α ^ (12 * b * t * R) :=
      candidate_card_bound t ht x n k b R hR hx hn hbonus
    _ = (n ^ ((2 * t - 1) * R) *
        (2 ^ R * (2 * t * R + 1) * (windowLength k b * R) ^ (CountExponent.exponent t * R))) *
          Fintype.card α ^ (12 * b * t * R) := by ring
    _ ≤ (n ^ ((2 * t - 1) * R) * (windowLength k b) ^ (WitnessCost.exponent t * R)) *
          Fintype.card α ^ (12 * b * t * R) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (WitnessCost.cost_le t b (windowLength k b) R (by unfold windowLength; omega) hL hcut))
    _ = _ := by simp only [scale, mul_pow, ← pow_mul]; ring

/-- The complete 1/12 obstruction bound, for explicit parameter inequalities.
The actual logarithmic choice supplies hbonus, and the size threshold depends only on t. -/
theorem obstruction_measure_le {n : ℕ} (b t k Q : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) (hk : 1 ≤ k) (x : Bits α n)
    (hx : KUnique (padBits x) n k) (hn : 1 ≤ n)
    (hL : 8 * t + 2 ≤ windowLength k b)
    (hbonus : ∀ R, windowLength k b < R → n ≤ 2 ^ R)
    (hQ : 8 * scale (Fintype.card α) b t n k ≤ Q) (hQtwo : 2 ≤ Q) :
    realWeights (Gram α (windowLength k b)) (obstructionEvent b t k Q x) ≤
      ENNReal.ofReal (1 / 12 : ℝ) := by
  calc
    _ ≤ ∑ R ∈ Finset.Icc 2 (cutoff t k b),
        (Nat.card {U : RuleSet α (k + b) // Candidate t (padBits x) n k b R U} : ENNReal) *
          ENNReal.ofReal (2 / (Q : ℝ)) ^ R := obstruction_probability_le b t k Q ht hb hk hQtwo x
    _ ≤ ∑ R ∈ Finset.Icc 2 (cutoff t k b), ENNReal.ofReal ((1 / 4 : ℝ) ^ R) := by
      apply Finset.sum_le_sum
      intro R hR
      exact survival_term_le _ _ Q R
        (candidate_count_le t ht (padBits x) n k b R (Finset.mem_Icc.mp hR).1 hx hn
          (hbonus R) hL (Finset.mem_Icc.mp hR).2) hQ (by omega)
    _ = ENNReal.ofReal (∑ R ∈ Finset.Icc 2 (cutoff t k b), (1 / 4 : ℝ) ^ R) :=
      (ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (geometric_tail_le _)

#print axioms candidate_count_le
#print axioms obstruction_measure_le

end DeletionCode.Burst.ObstructionBound
