import DeletionCode.Burst.Parameters
import DeletionCode.Qary.RedundancyBounds

/-!
Base-q redundancy for the burst window choice. The exponents are explicit
parameters, so the remainder coefficient is independent of q even when the
window and description constants depend on the fixed burst bound.
-/
namespace DeletionCode.Burst.RedundancyBounds

open Filter
open Qary.RedundancyBounds

/-- For fixed burst width, the larger window still has logarithmic length. -/
theorem logb_L_le_logb_logb_add (width q n : ℕ) (hq : 2 ≤ q) (hn : 2 ≤ n) :
    Real.logb q (Parameters.L width n : ℝ) ≤
      Real.logb q (Real.logb q (n : ℝ)) + Real.logb q ((3 * (width : ℝ) + 21) * Real.logb 2 q) := by
  have hb : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlogn : 0 < Real.logb q (n : ℝ) := Real.logb_pos hb hnreal
  have hlogq : 0 < Real.logb 2 (q : ℝ) := Real.logb_pos (by norm_num) hb
  have hchange : Real.logb 2 (q : ℝ) * Real.logb q (n : ℝ) =
      Real.logb 2 (n : ℝ) :=
    Real.mul_logb (by linarith) (by linarith) (by linarith)
  have hwindow := Parameters.L_le_logb width n hn
  rw [← hchange] at hwindow
  have hL : (0 : ℝ) < Parameters.L width n := by
    exact_mod_cast (show 0 < Parameters.L width n by have := Parameters.nine_le_L width n; omega)
  have h := Real.logb_le_logb_of_le hb hL hwindow
  rw [← mul_assoc, Real.logb_mul (mul_ne_zero (by positivity : (3 * (width : ℝ) + 21) ≠ 0)
    (ne_of_gt hlogq)) (ne_of_gt hlogn)] at h
  linarith

theorem tendsto_logb_logb_atTop (q : ℕ) (hq : 2 ≤ q) :
    Tendsto (fun n : ℕ => Real.logb q (Real.logb q (n : ℝ))) atTop atTop := by
  have hb : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  exact (Real.tendsto_logb_atTop hb).comp
    ((Real.tendsto_logb_atTop hb).comp tendsto_natCast_atTop_atTop)

/-- The multiplicative constant two is independent of q. -/
theorem eventually_logb_L_le_twice_logb_logb (width q : ℕ) (hq : 2 ≤ q) :
    ∀ᶠ n : ℕ in atTop, Real.logb q (Parameters.L width n : ℝ) ≤
      2 * Real.logb q (Real.logb q (n : ℝ)) := by
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_logb_logb_atTop q hq).eventually_ge_atTop
      (Real.logb q ((3 * (width : ℝ) + 21) * Real.logb 2 q))] with n hn hlarge
  have h := logb_L_le_logb_logb_add width q n hq hn
  linarith

/-- Integer label scale with separate alphabet, length and window exponents. -/
def labelCount (width q d a b n : ℕ) : ℕ :=
  8 * q ^ a * n ^ d * Parameters.L width n ^ b

theorem labelCount_positive (width q d a b n : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n) :
    0 < labelCount width q d a b n := by
  have hL : 0 < Parameters.L width n := by have := Parameters.nine_le_L width n; omega
  unfold labelCount
  positivity

theorem logb_labelCount (width q d a b n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    Real.logb q (labelCount width q d a b n : ℝ) =
      Real.logb q (8 : ℝ) + a + (d : ℝ) * Real.logb q (n : ℝ) +
        (b : ℝ) * Real.logb q (Parameters.L width n : ℝ) := by
  have hb : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLpos : (0 : ℝ) < Parameters.L width n := by
    exact_mod_cast (show 0 < Parameters.L width n by have := Parameters.nine_le_L width n; omega)
  simp only [labelCount, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  rw [Real.logb_mul (by positivity) (pow_ne_zero _ (ne_of_gt hLpos)),
    Real.logb_mul (by positivity) (pow_ne_zero _ (ne_of_gt hnpos)),
    Real.logb_mul (by norm_num : (8 : ℝ) ≠ 0) (by positivity),
    Real.logb_pow, Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hb, mul_one]

/-- The coefficient 2b+a+6 is independent of q; the threshold may depend on q.
The only hypothesis on the finite code is the cardinality estimate. -/
theorem eventually_paper_redundancy_bound (width q d a b : ℕ) (hq : 2 ≤ q) :
    ∀ᶠ n : ℕ in atTop, ∀ {γ : Type*} (C : Finset γ),
      q ^ n ≤ 8 * labelCount width q d a b n * C.card →
      redundancy q n C ≤ (d : ℝ) * Real.logb q (n : ℝ) +
        ((2 * b + a + 6 : ℕ) : ℝ) * Real.logb q (Real.logb q (n : ℝ)) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_logb_L_le_twice_logb_logb width q hq,
    (tendsto_logb_logb_atTop q hq).eventually_ge_atTop 1] with n hn hwindow hll
  intro γ C hcard
  have hbase := redundancy_le_log_labels q n (labelCount width q d a b n) C hq
    (labelCount_positive width q d a b n (by omega) hn) hcard
  rw [logb_labelCount width q d a b n hq hn] at hbase
  have h8 := logb_eight_le q hq
  have hmul := mul_le_mul_of_nonneg_left hwindow (Nat.cast_nonneg b : (0 : ℝ) ≤ b)
  have ha := mul_le_mul_of_nonneg_left hll (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith


#print axioms eventually_logb_L_le_twice_logb_logb
#print axioms eventually_paper_redundancy_bound

end DeletionCode.Burst.RedundancyBounds
