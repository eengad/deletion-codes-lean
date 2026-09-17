import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
The numerical choice in manuscript lemma `lem:family`.
The computable natural parameter is proved equal to the ordinary real-log
ceiling expression. Its collision allowance is at most one eighth, so any
corresponding union-bound estimate retains at least seven eighths of all
words and, for positive word length, at least 2^(n-1) words.
The counting and overlapping-window collision arguments are separate.
-/

namespace DeletionCode.UniqueWordParameters

/-- The manuscript's k = 2 ceil(log_2 n) + 2, computed with ceiling logarithms. -/
def uniquenessLength (n : ℕ) : ℕ := 2 * Nat.clog 2 n + 2

theorem uniquenessLength_ge_two (n : ℕ) : 2 ≤ uniquenessLength n := by
  unfold uniquenessLength
  omega

/-- Exact agreement with the natural ceiling of the real logarithm. -/
theorem uniquenessLength_eq_natCeil (n : ℕ) :
    uniquenessLength n = 2 * ⌈Real.logb 2 (n : ℝ)⌉₊ + 2 := by
  have hceil : ⌈Real.logb 2 (n : ℝ)⌉₊ = Nat.clog 2 n := by
    simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 n
  rw [hceil]
  rfl

/-- For positive n, the natural ceiling is the ordinary integer ceiling
appearing in the manuscript; the logarithm is nonnegative. -/
theorem uniquenessLength_eq_ceil (n : ℕ) (hn : 1 ≤ n) :
    (uniquenessLength n : ℤ) = 2 * ⌈Real.logb 2 (n : ℝ)⌉ + 2 := by
  rw [uniquenessLength_eq_natCeil]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [Int.natCast_ceil_eq_ceil
    (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hn))]

theorem two_mul_choose_le_square (n : ℕ) : 2 * n.choose 2 ≤ n ^ 2 := by
  rw [Nat.choose_two_right]
  have hdiv := Nat.div_mul_le_self (n * (n - 1)) 2
  have hmul := Nat.mul_le_mul_left n (Nat.sub_le n 1)
  nlinarith

theorem pow_uniquenessLength (n : ℕ) :
    2 ^ uniquenessLength n = 4 * (2 ^ Nat.clog 2 n) ^ 2 := by
  unfold uniquenessLength
  rw [show 2 * Nat.clog 2 n = Nat.clog 2 n * 2 by omega, pow_add, pow_mul]
  ring

theorem four_mul_square_le_pow (n : ℕ) : 4 * n ^ 2 ≤ 2 ^ uniquenessLength n := by
  have hn := Nat.le_pow_clog (by decide : 1 < 2) n
  have hsquare := Nat.mul_le_mul hn hn
  rw [pow_uniquenessLength]
  nlinarith

/-- An exact natural-number form of the paper's collision fraction bound. -/
theorem eight_mul_choose_le_pow (n : ℕ) : 8 * n.choose 2 ≤ 2 ^ uniquenessLength n := by
  have hchoose := two_mul_choose_le_square n
  have hpow := four_mul_square_le_pow n
  omega

/-- The total pairwise collision allowance is at most one eighth. -/
theorem collision_fraction_le (n : ℕ) :
    (n.choose 2 : ℚ) / (2 : ℚ) ^ uniquenessLength n ≤ 1 / 8 := by
  have hpow : (0 : ℚ) < 2 ^ uniquenessLength n := pow_pos (by norm_num) _
  have hscaled : (8 : ℚ) * n.choose 2 ≤ (2 : ℚ) ^ uniquenessLength n := by
    exact_mod_cast eight_mul_choose_le_pow n
  apply (div_le_iff₀ hpow).mpr
  nlinarith

theorem collision_fraction_le_real (n : ℕ) :
    (n.choose 2 : ℝ) / (2 : ℝ) ^ uniquenessLength n ≤ 1 / 8 := by
  have hpow : (0 : ℝ) < 2 ^ uniquenessLength n := pow_pos (by norm_num) _
  have hscaled : (8 : ℝ) * n.choose 2 ≤ (2 : ℝ) ^ uniquenessLength n := by
    exact_mod_cast eight_mul_choose_le_pow n
  apply (div_le_iff₀ hpow).mpr
  nlinarith

theorem seven_eighths_le_retained (n : ℕ) :
    (7 / 8 : ℚ) * (2 : ℚ) ^ n ≤
      (1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ uniquenessLength n) * (2 : ℚ) ^ n := by
  apply mul_le_mul_of_nonneg_right
  · have h := collision_fraction_le n
    linarith
  · exact le_of_lt (pow_pos (by norm_num : (0 : ℚ) < 2) n)

theorem seven_eighths_le_retained_real (n : ℕ) :
    (7 / 8 : ℝ) * (2 : ℝ) ^ n ≤
      (1 - (n.choose 2 : ℝ) / (2 : ℝ) ^ uniquenessLength n) * (2 : ℝ) ^ n := by
  apply mul_le_mul_of_nonneg_right
  · have h := collision_fraction_le_real n
    linarith
  · exact le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) n)

theorem half_words_le_seven_eighths (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℚ) ^ (n - 1) ≤ (7 / 8 : ℚ) * (2 : ℚ) ^ n := by
  have hpow : (2 : ℚ) ^ n = (2 : ℚ) ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
  rw [hpow]
  have hnonneg := le_of_lt (pow_pos (by norm_num : (0 : ℚ) < 2) (n - 1))
  nlinarith

theorem half_words_le_seven_eighths_real (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ (n - 1) ≤ (7 / 8 : ℝ) * (2 : ℝ) ^ n := by
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
  rw [hpow]
  have hnonneg := le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) (n - 1))
  nlinarith

/-- A finite cardinality satisfying the collision union bound inherits
both of the manuscript's concluding lower bounds. -/
theorem count_lower_bounds (n count : ℕ) (hn : 1 ≤ n)
    (hcount : (1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ uniquenessLength n) * (2 : ℚ) ^ n ≤ count) :
    (7 / 8 : ℚ) * (2 : ℚ) ^ n ≤ count ∧ 2 ^ (n - 1) ≤ count := by
  have hlarge := (seven_eighths_le_retained n).trans hcount
  refine ⟨hlarge, ?_⟩
  exact_mod_cast (half_words_le_seven_eighths n hn).trans hlarge

#print axioms uniquenessLength_eq_ceil
#print axioms eight_mul_choose_le_pow
#print axioms collision_fraction_le
#print axioms count_lower_bounds

end DeletionCode.UniqueWordParameters
