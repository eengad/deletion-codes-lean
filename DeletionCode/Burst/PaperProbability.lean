import DeletionCode.Burst.ExceptionalProbability
import DeletionCode.Burst.ObstructionBound
import DeletionCode.Burst.Parameters

/-!
The two actual discard events together cost at most one third per unique
word. The uniqueness length uses a base-two logarithm; the burst window is
enlarged by 3b. The threshold here depends only on t and b.
-/
namespace DeletionCode.Burst.PaperProbability

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

open MeasureTheory Qary.Windows Qary.SignedSupport CircleUniform
open Qary.HeaderRecovery (Bits padBits)
open ExceptionalProbability ObstructionProbability
open Qary.ObstructionBound (survival_term_le)
open scoped ENNReal

def threshold (b t : ℕ) : ℕ := max (8 * t + 2) (ExceptionalCountArithmetic.constant t b)

theorem labels_ge_two (q b t n Q : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hQ : 8 * ObstructionBound.scale q b t n (Parameters.k n) ≤ Q) : 2 ≤ Q := by
  have hqp : 1 ≤ q ^ (12 * b * t) := one_le_pow₀ hq
  have hnp : 1 ≤ n ^ (2 * t - 1) := one_le_pow₀ hn
  have hLp : 1 ≤ (Parameters.L b n) ^ (WitnessCost.exponent t) :=
    one_le_pow₀ (by have := Parameters.nine_le_L b n; omega)
  have hs : 1 ≤ ObstructionBound.scale q b t n (Parameters.k n) := by
    simpa only [one_mul, ObstructionBound.scale, Parameters.L,
      windowLength] using
      Nat.mul_le_mul (Nat.mul_le_mul hqp hnp) hLp
  omega

theorem exceptional_quarter_bound {n : ℕ} (b t Q : ℕ) (x : Bits α n)
    (hx : KUnique (padBits x) n (Parameters.k n))
    (hfit : Parameters.L b n ≤ n)
    (hconstant : ExceptionalCountArithmetic.constant t b ≤ Parameters.L b n)
    (hQ : 8 * ObstructionBound.scale (Fintype.card α) b t n (Parameters.k n) ≤ Q) :
    realWeights (Gram α (Parameters.L b n))
        (exceptionalEvent b t (Parameters.k n) Q x) ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  have hL : 1 ≤ Parameters.L b n := by have := Parameters.nine_le_L b n; omega
  have hn : 1 ≤ n := hL.trans hfit
  have hq : 1 ≤ Fintype.card α := Fintype.card_pos
  have hQtwo := labels_ge_two (Fintype.card α) b t n Q hq hn hQ
  have hCL : ExceptionalCountArithmetic.constant t b * Parameters.L b n ≤
      (Parameters.L b n) ^ (WitnessCost.exponent t) := by
    calc
      _ ≤ Parameters.L b n * Parameters.L b n := Nat.mul_le_mul_right _ hconstant
      _ = (Parameters.L b n) ^ 2 := (pow_two _).symm
      _ ≤ _ := pow_le_pow_right₀ hL (WitnessCost.exponent_ge_two t)
  have hqp : Fintype.card α ^ (2 * b * t) ≤ Fintype.card α ^ (12 * b * t) :=
    pow_le_pow_right₀ hq (by nlinarith)
  let C := ExceptionalCountArithmetic.constant t b * Fintype.card α ^ (2 * b * t) *
    Parameters.L b n * n ^ (2 * t - 1)
  have hC : C ≤ ObstructionBound.scale (Fintype.card α) b t n (Parameters.k n) := by
    calc
      C = (ExceptionalCountArithmetic.constant t b * Parameters.L b n) * Fintype.card α ^ (2 * b * t) *
          n ^ (2 * t - 1) := by dsimp [C]; ring
      _ ≤ (Parameters.L b n) ^ (WitnessCost.exponent t) * Fintype.card α ^ (12 * b * t) *
          n ^ (2 * t - 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul hCL hqp)
      _ = _ := by
        unfold ObstructionBound.scale Parameters.L
        simp only [windowLength]
        ring
  have h8 : 8 * C ≤ Q := (Nat.mul_le_mul_left 8 hC).trans hQ
  have hp := survival_term_le C C Q 1 (by simp) h8 (by omega)
  simp only [pow_one] at hp
  exact (ExceptionalProbability.exceptional_measure_le b t (Parameters.k n) Q x hx hfit hQtwo).trans hp

theorem total_discard_le {n : ℕ} (b t Q : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) (x : Bits α n)
    (hx : KUnique (padBits x) n (Parameters.k n))
    (hfit : Parameters.L b n ≤ n) (hready : threshold b t ≤ Parameters.L b n)
    (hQ : 8 * ObstructionBound.scale (Fintype.card α) b t n (Parameters.k n) ≤ Q) :
    realWeights (Gram α (Parameters.L b n))
      (exceptionalEvent b t (Parameters.k n) Q x ∪ obstructionEvent b t (Parameters.k n) Q x) ≤
        ENNReal.ofReal (1 / 3 : ℝ) := by
  have hn : 1 ≤ n := by have := Parameters.nine_le_L b n; omega
  have hL : 8 * t + 2 ≤ Parameters.L b n := (le_max_left _ _).trans hready
  have hC : ExceptionalCountArithmetic.constant t b ≤ Parameters.L b n := (le_max_right _ _).trans hready
  calc
    _ ≤ realWeights (Gram α (Parameters.L b n)) (exceptionalEvent b t (Parameters.k n) Q x) +
        realWeights (Gram α (Parameters.L b n)) (obstructionEvent b t (Parameters.k n) Q x) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 12 : ℝ) :=
      add_le_add (exceptional_quarter_bound b t Q x hx hfit hC hQ)
        (ObstructionBound.obstruction_measure_le b t (Parameters.k n) Q ht hb (by unfold Parameters.k DeletionCode.PaperParameters.k DeletionCode.UniqueWordParameters.uniquenessLength; omega) x hx hn hL
          (Parameters.le_two_pow_of_L_lt b n) hQ
          (labels_ge_two (Fintype.card α) b t n Q Fintype.card_pos hn hQ))
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      norm_num

/-- The obstruction proposition with the actual paper parameters and all
large-n side conditions derived, for every allowed number of labels. -/
theorem obstructions_are_rare (b t : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ Q : ℕ,
      8 * ObstructionBound.scale (Fintype.card α) b t n (Parameters.k n) ≤ Q → ∀ x : Bits α n,
        KUnique (padBits x) n (Parameters.k n) →
          realWeights (Gram α (Parameters.L b n)) (obstructionEvent b t (Parameters.k n) Q x) ≤
            ENNReal.ofReal (1 / 12 : ℝ) := by
  filter_upwards [Parameters.eventually_ready b (8 * t + 2)] with n hn
  intro Q hQ x hx
  exact ObstructionBound.obstruction_measure_le b t (Parameters.k n) Q ht hb (by unfold Parameters.k DeletionCode.PaperParameters.k DeletionCode.UniqueWordParameters.uniquenessLength; omega) x hx (by omega) hn.2.2.2
    (Parameters.le_two_pow_of_L_lt b n) hQ
    (labels_ge_two (Fintype.card α) b t n Q Fintype.card_pos (by omega) hQ)

#print axioms exceptional_quarter_bound
#print axioms total_discard_le
#print axioms obstructions_are_rare

end DeletionCode.Burst.PaperProbability
