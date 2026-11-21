import DeletionCode.Burst.CountExponent
import DeletionCode.Burst.WitnessExtraction
import DeletionCode.WitnessCost
import DeletionCode.UniqueWordParameters

/-!
The polynomial description factors in the obstruction count are absorbed
by an explicit power of L. The threshold on L depends only on t. The
separate logarithmic-parameter fact handles witness sizes larger than L.
These are exact natural-number inequalities, before any probability estimate.
-/
namespace DeletionCode.Burst.WitnessCost

open HeaderRecovery UniqueWordParameters

/-- An explicit replacement for the paper's sufficiently large exponent b_t. -/
def exponent (t : ℕ) : ℕ := 4 * CountExponent.exponent t + 2

theorem exponent_ge_two (t : ℕ) : 2 ≤ exponent t := by
  unfold exponent
  omega

/-- Every allowed bounded witness size is at most L cubed. -/
theorem size_le_cube (t b L R : ℕ) (hb : b ≤ L) (hL : 8 * t + 2 ≤ L)
    (hR : R ≤ 1 + 2 * t * (2 * L + 2 * b + 1) * L) : R ≤ L ^ 3 := by
  have hLpos : 1 ≤ L := by omega
  calc
    R ≤ 1 + 2 * t * (2 * L + 2 * b + 1) * L := hR
    _ ≤ (8 * t + 2) * L ^ 2 := by nlinarith
    _ ≤ L * L ^ 2 := Nat.mul_le_mul_right _ hL
    _ = L ^ 3 := by ring

theorem linear_factor_le (t b L R : ℕ) (hb : b ≤ L) (hL : 8 * t + 2 ≤ L) :
    2 * t * R + 1 ≤ L ^ R := by
  calc
    _ ≤ (2 * t + 1) ^ R := DeletionCode.WitnessCost.linear_le_power (2 * t) R
    _ ≤ L ^ R := Nat.pow_le_pow_left (by omega) R

/-- All non-position factors in the paper's bounded-witness count fit into
L^(b_t R), with b_t explicit. This also holds for R = 0 and R = 1. -/
theorem cost_le (t b L R : ℕ) (hb : b ≤ L) (hL : 8 * t + 2 ≤ L)
    (hR : R ≤ 1 + 2 * t * (2 * L + 2 * b + 1) * L) :
    2 ^ R * (2 * t * R + 1) * (L * R) ^ (CountExponent.exponent t * R) ≤
      L ^ (exponent t * R) := by
  have htwo : 2 ^ R ≤ L ^ R := Nat.pow_le_pow_left (by omega) R
  have hlinear := linear_factor_le t b L R hb hL
  have hprod : L * R ≤ L ^ 4 := by
    calc
      L * R ≤ L * L ^ 3 := Nat.mul_le_mul_left _ (size_le_cube t b L R hb hL hR)
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

#print axioms exponent_ge_two
#print axioms size_le_cube
#print axioms cost_le

end DeletionCode.Burst.WitnessCost
