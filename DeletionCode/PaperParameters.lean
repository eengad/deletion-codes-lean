import DeletionCode.UniqueWordParameters
import DeletionCode.HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs

/-!
Growth bounds for the manuscript's actual parameters, with no asymptotic
hypotheses supplied by the caller. The explicit estimates also discharge
the finite thresholds used in the counting and probability arguments.
-/
namespace DeletionCode.PaperParameters

open Filter Asymptotics
open scoped Topology

def k (n : ℕ) : ℕ := UniqueWordParameters.uniquenessLength n

def L (n : ℕ) : ℕ := HeaderRecovery.windowLength (k n)

theorem L_eq (n : ℕ) : L n = 6 * Nat.clog 2 n + 9 := by
  unfold L k HeaderRecovery.windowLength UniqueWordParameters.uniquenessLength
  omega

theorem nine_le_L (n : ℕ) : 9 ≤ L n := by rw [L_eq]; omega

/-- A concrete, albeit deliberately generous, threshold for every fixed M. -/
theorem threshold (M n : ℕ) (hn : 2 ^ M + 1 ≤ n) : M ≤ L n := by
  have hc : M < Nat.clog 2 n :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (by omega)
  rw [L_eq]
  omega

theorem eventually_threshold (M : ℕ) : ∀ᶠ n : ℕ in atTop, M ≤ L n := by
  filter_upwards [eventually_ge_atTop (2 ^ M + 1)] with n hn
  exact threshold M n hn

theorem tendsto_L_atTop : Tendsto L atTop atTop :=
  tendsto_atTop.2 eventually_threshold

private theorem affine_le_pow (q : ℕ) : 6 * (q + 6) + 15 ≤ 2 ^ (q + 6) := by
  induction q with
  | zero => norm_num
  | succ q ih =>
    have he : (q + 1) + 6 = (q + 6) + 1 := by omega
    change 6 * ((q + 1) + 6) + 15 ≤ 2 ^ ((q + 1) + 6)
    rw [he, pow_succ]
    omega

/-- The required window fits in the word from the explicit threshold 65. -/
theorem L_le_n (n : ℕ) (hn : 65 ≤ n) : L n ≤ n := by
  let c := Nat.clog 2 n
  have hc : 6 < c := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr
    norm_num
    omega
  have hpow := affine_le_pow (c - 7)
  have he : (c - 7) + 6 = c - 1 := by omega
  rw [he] at hpow
  have hnpow : 2 ^ (c - 1) < n := Nat.pow_lt_of_lt_clog (by omega : c - 1 < c)
  rw [L_eq]
  change 6 * c + 9 ≤ n
  omega

theorem eventually_L_le_n : ∀ᶠ n : ℕ in atTop, L n ≤ n := by
  filter_upwards [eventually_ge_atTop 65] with n hn
  exact L_le_n n hn

theorem eventually_three_le_n : ∀ᶠ n : ℕ in atTop, 3 ≤ n := eventually_ge_atTop 3

/-- All concrete fixed thresholds can be imposed together for large n. -/
theorem eventually_ready (M : ℕ) :
    ∀ᶠ n : ℕ in atTop, 3 ≤ n ∧ L n ≤ n ∧ M ≤ L n := by
  filter_upwards [eventually_three_le_n, eventually_L_le_n, eventually_threshold M]
    with n hn hfit hM
  exact ⟨hn, hfit, hM⟩

/-- This discharges the extra-component arithmetic premise in WitnessCounting. -/
theorem le_two_pow_of_L_lt (n R : ℕ) (hR : L n < R) : n ≤ 2 ^ R := by
  have hc : Nat.clog 2 n ≤ R := by rw [L_eq] at hR; omega
  exact (Nat.le_pow_clog (by decide : 1 < 2) n).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) hc)

theorem one_le_logb (n : ℕ) (hn : 2 ≤ n) : 1 ≤ Real.logb 2 (n : ℝ) := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ n by exact_mod_cast hn)
  simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h

theorem two_le_logb (n : ℕ) (hn : 4 ≤ n) : 2 ≤ Real.logb 2 (n : ℝ) := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2 ^ (2 : ℕ))
    (show (2 : ℝ) ^ (2 : ℕ) ≤ n by norm_num; exact_mod_cast hn)
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    Nat.cast_ofNat, mul_one] using h

/-- A pointwise logarithmic bound for the actual ceiling parameter. -/
theorem L_le_twenty_one_logb (n : ℕ) (hn : 2 ≤ n) :
    (L n : ℝ) ≤ 21 * Real.logb 2 (n : ℝ) := by
  have hlog := one_le_logb n hn
  have hceil : (Nat.clog 2 n : ℝ) < Real.logb 2 (n : ℝ) + 1 := by
    have he : Nat.clog 2 n = ⌈Real.logb 2 (n : ℝ)⌉₊ := by
      symm
      simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 n
    rw [he]
    exact Nat.ceil_lt_add_one (by linarith)
  have hL : (L n : ℝ) = 6 * (Nat.clog 2 n : ℝ) + 9 := by
    exact_mod_cast L_eq n
  linarith

theorem L_isBigO_logb :
    (fun n : ℕ => (L n : ℝ)) =O[atTop] (fun n => Real.logb 2 (n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 21
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : 0 ≤ Real.logb 2 (n : ℝ) := by have := one_le_logb n hn; linarith
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (L n) : (0 : ℝ) ≤ (L n : ℝ)),
    abs_of_nonneg hlog] using L_le_twenty_one_logb n hn

theorem one_le_logb_logb (n : ℕ) (hn : 4 ≤ n) :
    1 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2) (two_le_logb n hn)
  simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h

/-- The logarithm of the window length is bounded by six times log-log. -/
theorem logb_L_le_six_logb_logb (n : ℕ) (hn : 4 ≤ n) :
    Real.logb 2 (L n : ℝ) ≤ 6 * Real.logb 2 (Real.logb 2 (n : ℝ)) := by
  have hlog : 0 < Real.logb 2 (n : ℝ) := by have := two_le_logb n hn; linarith
  have hL : (0 : ℝ) < L n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 9) (nine_le_L n))
  have hmono := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    hL (L_le_twenty_one_logb n (by omega))
  rw [Real.logb_mul (by norm_num : (21 : ℝ) ≠ 0) (ne_of_gt hlog)] at hmono
  have h21 : Real.logb 2 (21 : ℝ) ≤ 5 := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 21) (by norm_num : (21 : ℝ) ≤ 2 ^ (5 : ℕ))
    simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      Nat.cast_ofNat, mul_one] using h
  have hll := one_le_logb_logb n hn
  linarith

theorem logb_L_isBigO_logb_logb :
    (fun n : ℕ => Real.logb 2 (L n : ℝ)) =O[atTop]
      (fun n => Real.logb 2 (Real.logb 2 (n : ℝ))) := by
  apply Asymptotics.IsBigO.of_bound 6
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hL : 0 ≤ Real.logb 2 (L n : ℝ) := Real.logb_nonneg
    (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast (show 1 ≤ L n by have := nine_le_L n; omega))
  have hll : 0 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) := by
    have := one_le_logb_logb n hn
    linarith
  simpa only [Real.norm_eq_abs, abs_of_nonneg hL, abs_of_nonneg hll] using
    logb_L_le_six_logb_logb n hn

#print axioms tendsto_L_atTop
#print axioms eventually_ready
#print axioms le_two_pow_of_L_lt
#print axioms L_isBigO_logb
#print axioms logb_L_isBigO_logb_logb

end DeletionCode.PaperParameters
