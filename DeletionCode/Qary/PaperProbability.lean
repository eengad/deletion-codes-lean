import DeletionCode.Qary.NonseparatedFamily
import DeletionCode.Qary.ObstructionBound
import DeletionCode.PaperParameters

/-!
The two actual discard events together cost at most one third per unique
word. We retain the binary logarithmic window length and include the alphabet
factor in the label scale; the length threshold here still depends only on t.
-/
namespace DeletionCode.Qary.PaperProbability

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

open MeasureTheory DeletionCode.Qary.Windows DeletionCode.Qary.HeaderRecovery DeletionCode.Qary.SignedSupport DeletionCode.CircleUniform
open DeletionCode.Qary.ExceptionalCountArithmetic DeletionCode.Qary.ExceptionalProbability DeletionCode.Qary.ObstructionProbability
open scoped ENNReal

def threshold (t : ℕ) : ℕ := max (4 * t + 3) (exceptionalConstant t)

theorem labels_ge_two (q t n Q : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hQ : 8 * ObstructionBound.scale q t n (PaperParameters.k n) ≤ Q) : 2 ≤ Q := by
  have hqp : 1 ≤ q ^ (12 * t) := one_le_pow₀ hq
  have hnp : 1 ≤ n ^ (2 * t - 1) := one_le_pow₀ hn
  have hLp : 1 ≤ (PaperParameters.L n) ^ (WitnessCost.exponent t) :=
    one_le_pow₀ (by have := PaperParameters.nine_le_L n; omega)
  have hs : 1 ≤ ObstructionBound.scale q t n (PaperParameters.k n) := by
    simpa only [one_mul, ObstructionBound.scale, PaperParameters.L,
      HeaderRecovery.windowLength, DeletionCode.HeaderRecovery.windowLength] using
      Nat.mul_le_mul (Nat.mul_le_mul hqp hnp) hLp
  omega

theorem exceptional_quarter_bound {n : ℕ} (t Q : ℕ) (x : Bits α n)
    (hx : KUnique (padBits x) n (PaperParameters.k n))
    (hfit : PaperParameters.L n ≤ n)
    (hconstant : exceptionalConstant t ≤ PaperParameters.L n)
    (hQ : 8 * ObstructionBound.scale (Fintype.card α) t n (PaperParameters.k n) ≤ Q) :
    realWeights (Gram α (PaperParameters.L n))
        (exceptionalEvent t (PaperParameters.k n) Q x) ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  have hL : 1 ≤ PaperParameters.L n := by have := PaperParameters.nine_le_L n; omega
  have hn : 1 ≤ n := hL.trans hfit
  have hq : 1 ≤ Fintype.card α := Fintype.card_pos
  have hQtwo := labels_ge_two (Fintype.card α) t n Q hq hn hQ
  have hCL : exceptionalConstant t * PaperParameters.L n ≤
      (PaperParameters.L n) ^ (WitnessCost.exponent t) := by
    calc
      _ ≤ PaperParameters.L n * PaperParameters.L n := Nat.mul_le_mul_right _ hconstant
      _ = (PaperParameters.L n) ^ 2 := (pow_two _).symm
      _ ≤ _ := pow_le_pow_right₀ hL (WitnessCost.exponent_ge_two t)
  have hqp : Fintype.card α ^ (2 * t) ≤ Fintype.card α ^ (12 * t) :=
    pow_le_pow_right₀ hq (by omega)
  let C := exceptionalConstant t * Fintype.card α ^ (2 * t) *
    PaperParameters.L n * n ^ (2 * t - 1)
  have hC : C ≤ ObstructionBound.scale (Fintype.card α) t n (PaperParameters.k n) := by
    calc
      C = (exceptionalConstant t * PaperParameters.L n) * Fintype.card α ^ (2 * t) *
          n ^ (2 * t - 1) := by dsimp [C]; ring
      _ ≤ (PaperParameters.L n) ^ (WitnessCost.exponent t) * Fintype.card α ^ (12 * t) *
          n ^ (2 * t - 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul hCL hqp)
      _ = _ := by
        unfold ObstructionBound.scale PaperParameters.L
        simp only [HeaderRecovery.windowLength, DeletionCode.HeaderRecovery.windowLength]
        ring
  have h8 : 8 * C ≤ Q := (Nat.mul_le_mul_left 8 hC).trans hQ
  have hp := ObstructionBound.survival_term_le C C Q 1 (by simp) h8 (by omega)
  simp only [pow_one] at hp
  exact (NonseparatedFamily.exceptional_measure_le t (PaperParameters.k n) Q x hx hfit hQtwo).trans hp

theorem total_discard_le {n : ℕ} (t Q : ℕ) (ht : 2 ≤ t) (x : Bits α n)
    (hx : KUnique (padBits x) n (PaperParameters.k n))
    (hfit : PaperParameters.L n ≤ n) (hready : threshold t ≤ PaperParameters.L n)
    (hQ : 8 * ObstructionBound.scale (Fintype.card α) t n (PaperParameters.k n) ≤ Q) :
    realWeights (Gram α (PaperParameters.L n))
      (exceptionalEvent t (PaperParameters.k n) Q x ∪ obstructionEvent t (PaperParameters.k n) Q x) ≤
        ENNReal.ofReal (1 / 3 : ℝ) := by
  have hn : 1 ≤ n := by have := PaperParameters.nine_le_L n; omega
  have hL : 4 * t + 3 ≤ PaperParameters.L n := (le_max_left _ _).trans hready
  have hC : exceptionalConstant t ≤ PaperParameters.L n := (le_max_right _ _).trans hready
  calc
    _ ≤ realWeights (Gram α (PaperParameters.L n)) (exceptionalEvent t (PaperParameters.k n) Q x) +
        realWeights (Gram α (PaperParameters.L n)) (obstructionEvent t (PaperParameters.k n) Q x) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 12 : ℝ) :=
      add_le_add (exceptional_quarter_bound t Q x hx hfit hC hQ)
        (ObstructionBound.obstruction_measure_le t (PaperParameters.k n) Q ht x hx hn hL
          (PaperParameters.le_two_pow_of_L_lt n) hQ
          (labels_ge_two (Fintype.card α) t n Q Fintype.card_pos hn hQ))
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      norm_num

/-- The obstruction proposition with the actual paper parameters and all
large-n side conditions derived, for every allowed number of labels. -/
theorem obstructions_are_rare (t : ℕ) (ht : 2 ≤ t) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ Q : ℕ,
      8 * ObstructionBound.scale (Fintype.card α) t n (PaperParameters.k n) ≤ Q → ∀ x : Bits α n,
        KUnique (padBits x) n (PaperParameters.k n) →
          realWeights (Gram α (PaperParameters.L n)) (obstructionEvent t (PaperParameters.k n) Q x) ≤
            ENNReal.ofReal (1 / 12 : ℝ) := by
  filter_upwards [PaperParameters.eventually_ready (4 * t + 3)] with n hn
  intro Q hQ x hx
  exact ObstructionBound.obstruction_measure_le t (PaperParameters.k n) Q ht x hx (by omega) hn.2.2
    (PaperParameters.le_two_pow_of_L_lt n) hQ
    (labels_ge_two (Fintype.card α) t n Q Fintype.card_pos (by omega) hQ)

#print axioms exceptional_quarter_bound
#print axioms total_discard_le
#print axioms obstructions_are_rare

end DeletionCode.Qary.PaperProbability
