import DeletionCode.NonseparatedFamily
import DeletionCode.ObstructionBound
import DeletionCode.PaperParameters

/-!
The two actual discard events together cost at most one third per unique
word for the manuscript's logarithmic parameters. All thresholds depend
only on t and hold eventually by the proved parameter growth.
-/
namespace DeletionCode.PaperProbability

open MeasureTheory Windows HeaderRecovery SignedSupport CircleUniform
open ExceptionalCountArithmetic ExceptionalProbability ObstructionProbability
open scoped ENNReal

def threshold (t : ℕ) : ℕ := max (4 * t + 3) (exceptionalConstant t)

theorem labels_ge_two (t n Q : ℕ) (hn : 1 ≤ n)
    (hQ : 8 * ObstructionBound.scale t n (PaperParameters.k n) ≤ Q) : 2 ≤ Q := by
  have hnp : 1 ≤ n ^ (2 * t - 1) := one_le_pow₀ hn
  have hLp : 1 ≤ (PaperParameters.L n) ^ (WitnessCost.exponent t) :=
    one_le_pow₀ (by have := PaperParameters.nine_le_L n; omega)
  have hs : 1 ≤ ObstructionBound.scale t n (PaperParameters.k n) := by
    simpa only [one_mul, ObstructionBound.scale, PaperParameters.L] using Nat.mul_le_mul hnp hLp
  omega

theorem exceptional_quarter_bound {n : ℕ} (t Q : ℕ) (x : Bits n)
    (hx : KUnique (padBits x) n (PaperParameters.k n))
    (hfit : PaperParameters.L n ≤ n)
    (hconstant : exceptionalConstant t ≤ PaperParameters.L n)
    (hQ : 8 * ObstructionBound.scale t n (PaperParameters.k n) ≤ Q) :
    realWeights (Gram (PaperParameters.L n))
        (exceptionalEvent t (PaperParameters.k n) Q x) ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  have hL : 1 ≤ PaperParameters.L n := by have := PaperParameters.nine_le_L n; omega
  have hn : 1 ≤ n := hL.trans hfit
  have hQtwo := labels_ge_two t n Q hn hQ
  have hCL : exceptionalConstant t * PaperParameters.L n ≤
      (PaperParameters.L n) ^ (WitnessCost.exponent t) := by
    calc
      _ ≤ PaperParameters.L n * PaperParameters.L n := Nat.mul_le_mul_right _ hconstant
      _ = (PaperParameters.L n) ^ 2 := (pow_two _).symm
      _ ≤ _ := pow_le_pow_right₀ hL (WitnessCost.exponent_ge_two t)
  let C := exceptionalConstant t * PaperParameters.L n * n ^ (2 * t - 1)
  have hC : C ≤ ObstructionBound.scale t n (PaperParameters.k n) := by
    calc
      _ ≤ (PaperParameters.L n) ^ (WitnessCost.exponent t) * n ^ (2 * t - 1) :=
        Nat.mul_le_mul_right _ hCL
      _ = _ := by unfold ObstructionBound.scale PaperParameters.L; ring
  have h8 : 8 * C ≤ Q := (Nat.mul_le_mul_left 8 hC).trans hQ
  have hp := ObstructionBound.survival_term_le C C Q 1 (by simp) h8 (by omega)
  simp only [pow_one] at hp
  exact (NonseparatedFamily.exceptional_measure_le t (PaperParameters.k n) Q x hx hfit hQtwo).trans hp

theorem total_discard_le {n : ℕ} (t Q : ℕ) (ht : 2 ≤ t) (x : Bits n)
    (hx : KUnique (padBits x) n (PaperParameters.k n))
    (hfit : PaperParameters.L n ≤ n) (hready : threshold t ≤ PaperParameters.L n)
    (hQ : 8 * ObstructionBound.scale t n (PaperParameters.k n) ≤ Q) :
    realWeights (Gram (PaperParameters.L n))
      (exceptionalEvent t (PaperParameters.k n) Q x ∪ obstructionEvent t (PaperParameters.k n) Q x) ≤
        ENNReal.ofReal (1 / 3 : ℝ) := by
  have hn : 1 ≤ n := by have := PaperParameters.nine_le_L n; omega
  have hL : 4 * t + 3 ≤ PaperParameters.L n := (le_max_left _ _).trans hready
  have hC : exceptionalConstant t ≤ PaperParameters.L n := (le_max_right _ _).trans hready
  calc
    _ ≤ realWeights (Gram (PaperParameters.L n)) (exceptionalEvent t (PaperParameters.k n) Q x) +
        realWeights (Gram (PaperParameters.L n)) (obstructionEvent t (PaperParameters.k n) Q x) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 12 : ℝ) :=
      add_le_add (exceptional_quarter_bound t Q x hx hfit hC hQ)
        (ObstructionBound.obstruction_measure_le t (PaperParameters.k n) Q ht x hx hn hL
          (PaperParameters.le_two_pow_of_L_lt n) hQ (labels_ge_two t n Q hn hQ))
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      norm_num

/-- The obstruction proposition with the actual paper parameters and all
large-n side conditions derived, for every allowed number of labels. -/
theorem obstructions_are_rare (t : ℕ) (ht : 2 ≤ t) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ Q : ℕ,
      8 * ObstructionBound.scale t n (PaperParameters.k n) ≤ Q → ∀ x : Bits n,
        KUnique (padBits x) n (PaperParameters.k n) →
          realWeights (Gram (PaperParameters.L n)) (obstructionEvent t (PaperParameters.k n) Q x) ≤
            ENNReal.ofReal (1 / 12 : ℝ) := by
  filter_upwards [PaperParameters.eventually_ready (4 * t + 3)] with n hn
  intro Q hQ x hx
  exact ObstructionBound.obstruction_measure_le t (PaperParameters.k n) Q ht x hx (by omega) hn.2.2
    (PaperParameters.le_two_pow_of_L_lt n) hQ (labels_ge_two t n Q (by omega) hQ)

#print axioms exceptional_quarter_bound
#print axioms total_discard_le
#print axioms obstructions_are_rare

end DeletionCode.PaperProbability
