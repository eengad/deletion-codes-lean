import DeletionCode.Burst.Basic
import DeletionCode.PaperParameters

/-!
Concrete window parameters for each fixed burst bound. The base-two choice of
k keeps the verified finite-alphabet uniqueness estimate available unchanged.
All bounds below hold eventually in n without additional growth assumptions.
-/
namespace DeletionCode.Burst.Parameters

open Filter

def k (n : ℕ) : ℕ := PaperParameters.k n

def L (b n : ℕ) : ℕ := windowLength (k n) b

theorem L_eq (b n : ℕ) : L b n = PaperParameters.L n + 3 * b := by
  unfold L k windowLength PaperParameters.L HeaderRecovery.windowLength
  omega

theorem L_explicit (b n : ℕ) : L b n = 6 * Nat.clog 2 n + 9 + 3 * b := by
  rw [L_eq, PaperParameters.L_eq]

theorem nine_le_L (b n : ℕ) : 9 ≤ L b n := by rw [L_explicit]; omega

theorem eventually_threshold (b M : ℕ) : ∀ᶠ n : ℕ in atTop, M ≤ L b n := by
  filter_upwards [PaperParameters.eventually_threshold M] with n hn
  rw [L_eq]
  omega

theorem eventually_k_gt (b : ℕ) : ∀ᶠ n : ℕ in atTop, b < k n := by
  filter_upwards [eventually_ge_atTop (2 ^ b + 1)] with n hn
  have hc : b < Nat.clog 2 n :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (by omega)
  unfold k PaperParameters.k UniqueWordParameters.uniquenessLength
  omega

private theorem affine_le_pow (r : ℕ) : 9 * (r + 7) + 18 ≤ 2 ^ (r + 7) := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    have he : (r + 1) + 7 = (r + 7) + 1 := by omega
    change 9 * ((r + 1) + 7) + 18 ≤ 2 ^ ((r + 1) + 7)
    rw [he, pow_succ]
    omega

theorem L_le_n (b n : ℕ) (hn : 2 ^ (b + 8) + 1 ≤ n) : L b n ≤ n := by
  let c := Nat.clog 2 n
  have hc : b + 8 < c :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (by omega)
  have hpow := affine_le_pow (c - 8)
  have he : c - 8 + 7 = c - 1 := by omega
  rw [he] at hpow
  have hnlow : 2 ^ (c - 1) < n := Nat.pow_lt_of_lt_clog (by omega : c - 1 < c)
  rw [L_explicit]
  change 6 * c + 9 + 3 * b ≤ n
  omega

theorem eventually_L_le_n (b : ℕ) : ∀ᶠ n : ℕ in atTop, L b n ≤ n := by
  filter_upwards [eventually_ge_atTop (2 ^ (b + 8) + 1)] with n hn
  exact L_le_n b n hn

theorem eventually_ready (b M : ℕ) :
    ∀ᶠ n : ℕ in atTop, 3 ≤ n ∧ b < k n ∧ L b n ≤ n ∧ M ≤ L b n := by
  filter_upwards [eventually_ge_atTop 3, eventually_k_gt b,
    eventually_L_le_n b, eventually_threshold b M] with n hn hk hfit hM
  exact ⟨hn, hk, hfit, hM⟩

theorem le_two_pow_of_L_lt (b n R : ℕ) (hR : L b n < R) : n ≤ 2 ^ R := by
  apply PaperParameters.le_two_pow_of_L_lt n R
  rw [L_eq] at hR
  omega

theorem L_le_logb (b n : ℕ) (hn : 2 ≤ n) :
    (L b n : ℝ) ≤ (3 * (b : ℝ) + 21) * Real.logb 2 (n : ℝ) := by
  have h := PaperParameters.L_le_twenty_one_logb n hn
  have hlog := PaperParameters.one_le_logb n hn
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hL : (L b n : ℝ) = (PaperParameters.L n : ℝ) + 3 * (b : ℝ) := by
    exact_mod_cast L_eq b n
  rw [hL]
  nlinarith

#print axioms eventually_ready
#print axioms le_two_pow_of_L_lt
#print axioms L_le_logb

end DeletionCode.Burst.Parameters
