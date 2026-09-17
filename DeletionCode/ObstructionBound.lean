import DeletionCode.ObstructionProbability
import DeletionCode.WitnessCost

/-!
The numerical and counting conclusion of the obstruction proposition. Fixed
candidate sets are counted before sampling; the graph event is bounded by
their survival union without conditioning on the exceptional set or graph.
-/
namespace DeletionCode.ObstructionBound

open MeasureTheory Windows HeaderRecovery SignedSupport SignedRuleCount
open CircleUniform WitnessCounting ObstructionProbability
open scoped BigOperators ENNReal

def scale (t n k : ℕ) : ℕ := n ^ (2 * t - 1) * (windowLength k) ^ (WitnessCost.exponent t)

theorem candidate_count_le (t : ℕ) (ht : 2 ≤ t) (x : Letters) (n k R : ℕ)
    (hR : 2 ≤ R) (hx : KUnique x n k) (hn : 1 ≤ n)
    (hbonus : windowLength k < R → n ≤ 2 ^ R)
    (hL : 4 * t + 2 ≤ windowLength k) (hcut : R ≤ cutoff t k) :
    Nat.card {U : RuleSet k // Candidate t x n k R U} ≤ (scale t n k) ^ R := by
  calc
    _ ≤ 2 ^ R * (2 * t * R + 1) * n ^ ((2 * t - 1) * R) *
        (windowLength k * R) ^ (CountExponent.exponent t * R) :=
      candidate_card_bound t ht x n k R hR hx hn hbonus
    _ = n ^ ((2 * t - 1) * R) *
        (2 ^ R * (2 * t * R + 1) * (windowLength k * R) ^ (CountExponent.exponent t * R)) := by ring
    _ ≤ n ^ ((2 * t - 1) * R) * (windowLength k) ^ (WitnessCost.exponent t * R) :=
      Nat.mul_le_mul_left _ (WitnessCost.cost_le t (windowLength k) R hL hcut)
    _ = _ := by simp only [scale, mul_pow, ← pow_mul]

theorem survival_term_le (C N Q R : ℕ) (hC : C ≤ N ^ R) (hQ : 8 * N ≤ Q)
    (hQpos : 0 < Q) :
    (C : ENNReal) * ENNReal.ofReal (2 / (Q : ℝ)) ^ R ≤
      ENNReal.ofReal ((1 / 4 : ℝ) ^ R) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQpos
  have hNQ : 8 * (N : ℝ) ≤ Q := by exact_mod_cast hQ
  have hratio : (N : ℝ) * (2 / (Q : ℝ)) ≤ 1 / 4 := by
    rw [← mul_div_assoc, div_le_iff₀ hQr]
    linarith
  have hcast : (C : ENNReal) ≤ (N : ENNReal) ^ R := by exact_mod_cast hC
  calc
    _ ≤ (N : ENNReal) ^ R * ENNReal.ofReal (2 / (Q : ℝ)) ^ R :=
      mul_le_mul_of_nonneg_right hcast (by positivity)
    _ = ENNReal.ofReal ((N : ℝ) * (2 / (Q : ℝ))) ^ R := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast, mul_pow]
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) ^ R := pow_le_pow_left' (ENNReal.ofReal_le_ofReal hratio) R
    _ = _ := (ENNReal.ofReal_pow (by positivity) R).symm

theorem geometric_tail_identity (N : ℕ) :
    (∑ i ∈ Finset.range N, (1 / 4 : ℝ) ^ (i + 2)) = (1 - (1 / 4 : ℝ) ^ N) / 12 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [pow_succ]
    ring

theorem geometric_tail_le (M : ℕ) :
    (∑ R ∈ Finset.Icc 2 M, (1 / 4 : ℝ) ^ R) ≤ 1 / 12 := by
  have hset : Finset.Icc 2 M = Finset.Ico 2 (M + 1) := by ext i; simp
  rw [hset, Finset.sum_Ico_eq_sum_range]
  simp_rw [Nat.add_comm 2]
  rw [geometric_tail_identity]
  have hpos : 0 ≤ (1 / 4 : ℝ) ^ (M + 1 - 2) := by positivity
  linarith

/-- The complete 1/12 obstruction bound, for explicit parameter inequalities.
The actual logarithmic choice supplies hbonus, and the size threshold depends only on t. -/
theorem obstruction_measure_le {n : ℕ} (t k Q : ℕ) (ht : 2 ≤ t) (x : Bits n)
    (hx : KUnique (padBits x) n k) (hn : 1 ≤ n)
    (hL : 4 * t + 2 ≤ windowLength k)
    (hbonus : ∀ R, windowLength k < R → n ≤ 2 ^ R)
    (hQ : 8 * scale t n k ≤ Q) (hQtwo : 2 ≤ Q) :
    realWeights (Gram (windowLength k)) (obstructionEvent t k Q x) ≤
      ENNReal.ofReal (1 / 12 : ℝ) := by
  calc
    _ ≤ ∑ R ∈ Finset.Icc 2 (cutoff t k),
        (Nat.card {U : RuleSet k // Candidate t (padBits x) n k R U} : ENNReal) *
          ENNReal.ofReal (2 / (Q : ℝ)) ^ R := obstruction_probability_le t k Q ht hQtwo x
    _ ≤ ∑ R ∈ Finset.Icc 2 (cutoff t k), ENNReal.ofReal ((1 / 4 : ℝ) ^ R) := by
      apply Finset.sum_le_sum
      intro R hR
      exact survival_term_le _ _ Q R
        (candidate_count_le t ht (padBits x) n k R (Finset.mem_Icc.mp hR).1 hx hn
          (hbonus R) hL (Finset.mem_Icc.mp hR).2) hQ (by omega)
    _ = ENNReal.ofReal (∑ R ∈ Finset.Icc 2 (cutoff t k), (1 / 4 : ℝ) ^ R) :=
      (ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (geometric_tail_le _)

#print axioms candidate_count_le
#print axioms survival_term_le
#print axioms geometric_tail_le
#print axioms obstruction_measure_le

end DeletionCode.ObstructionBound
