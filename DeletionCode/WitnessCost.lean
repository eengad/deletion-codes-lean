import DeletionCode.CountExponent
import DeletionCode.UniqueWordParameters

/-!
The polynomial description factors in the obstruction count are absorbed
by an explicit power of L. The threshold on L depends only on t. The
separate logarithmic-parameter fact handles witness sizes larger than L.
These are exact natural-number inequalities, before any probability estimate.
-/
namespace DeletionCode.WitnessCost

open HeaderRecovery UniqueWordParameters

/-- An explicit replacement for the paper's sufficiently large exponent b_t. -/
def exponent (t : ℕ) : ℕ := 4 * CountExponent.exponent t + 2

theorem exponent_ge_two (t : ℕ) : 2 ≤ exponent t := by
  unfold exponent
  omega

/-- The elementary Bernoulli bound, including exponent zero. -/
theorem linear_le_power (c R : ℕ) : c * R + 1 ≤ (c + 1) ^ R := by
  induction R with
  | zero => simp
  | succ R ih =>
      calc
        c * (R + 1) + 1 ≤ (c * R + 1) * (c + 1) := by
          have hnonneg : 0 ≤ c * c * R := Nat.zero_le _
          nlinarith
        _ ≤ (c + 1) ^ R * (c + 1) := Nat.mul_le_mul_right _ ih
        _ = (c + 1) ^ (R + 1) := (pow_succ _ _).symm

/-- Every allowed bounded witness size is at most L cubed. -/
theorem size_le_cube (t L R : ℕ) (hL : 4 * t + 3 ≤ L)
    (hR : R ≤ 1 + 4 * t * L ^ 2 + 2 * t * L) : R ≤ L ^ 3 := by
  have hsq : 1 ≤ L ^ 2 := one_le_pow₀ (by omega)
  have hlin : 2 * t * L ≤ 2 * t * L ^ 2 := by nlinarith
  calc
    R ≤ 1 + 4 * t * L ^ 2 + 2 * t * L := hR
    _ ≤ (4 * t + 2 + 1) * L ^ 2 := by nlinarith
    _ ≤ L * L ^ 2 := Nat.mul_le_mul_right _ (by omega)
    _ = L ^ 3 := by ring

theorem linear_factor_le (t L R : ℕ) (hL : 4 * t + 3 ≤ L) :
    2 * t * R + 1 ≤ L ^ R := by
  calc
    _ ≤ (2 * t + 1) ^ R := linear_le_power (2 * t) R
    _ ≤ L ^ R := Nat.pow_le_pow_left (by omega) R

/-- All non-position factors in the paper's bounded-witness count fit into
L^(b_t R), with b_t explicit. This also holds for R = 0 and R = 1. -/
theorem cost_le (t L R : ℕ) (hL : 4 * t + 3 ≤ L)
    (hR : R ≤ 1 + 4 * t * L ^ 2 + 2 * t * L) :
    2 ^ R * (2 * t * R + 1) * (L * R) ^ (CountExponent.exponent t * R) ≤
      L ^ (exponent t * R) := by
  have htwo : 2 ^ R ≤ L ^ R := Nat.pow_le_pow_left (by omega) R
  have hlinear := linear_factor_le t L R hL
  have hprod : L * R ≤ L ^ 4 := by
    calc
      L * R ≤ L * L ^ 3 := Nat.mul_le_mul_left _ (size_le_cube t L R hL hR)
      _ = L ^ 4 := by ring
  have hpower : (L * R) ^ (CountExponent.exponent t * R) ≤
      (L ^ 4) ^ (CountExponent.exponent t * R) :=
    Nat.pow_le_pow_left hprod _
  calc
    _ ≤ L ^ R * L ^ R * (L ^ 4) ^ (CountExponent.exponent t * R) :=
      Nat.mul_le_mul (Nat.mul_le_mul htwo hlinear) hpower
    _ = L ^ (exponent t * R) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      unfold exponent
      ring

/-- The paper's actual ceiling-logarithm choice bounds n by 2^L. -/
theorem length_le_two_pow_window (n : ℕ) :
    n ≤ 2 ^ windowLength (uniquenessLength n) := by
  have hclog : Nat.clog 2 n ≤ windowLength (uniquenessLength n) := by
    dsimp [windowLength, uniquenessLength]
    omega
  exact (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp hclog

/-- In the large-witness case L < R, the extra factor n costs at most 2^R.
No asymptotic or logarithmic approximation is assumed. The result even
includes n = 0; positive n is the manuscript's intended application. -/
theorem length_le_two_pow_of_window_lt (n R : ℕ)
    (hR : windowLength (uniquenessLength n) < R) : n ≤ 2 ^ R := by
  exact (length_le_two_pow_window n).trans
    (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.le_of_lt hR))

#print axioms exponent_ge_two
#print axioms linear_le_power
#print axioms size_le_cube
#print axioms cost_le
#print axioms length_le_two_pow_of_window_lt

end DeletionCode.WitnessCost
