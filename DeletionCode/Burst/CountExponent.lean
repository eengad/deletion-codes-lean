import DeletionCode.DescriptionCount
import DeletionCode.HeaderRecovery

/-! An explicit constant depending only on t for the manuscript's (LR)^(a_t R) bound. -/
namespace DeletionCode.Burst.CountExponent

open DescriptionCount HeaderRecovery

def exponent (t : ℕ) : ℕ := 106 * t * (32 * (2 * t + 1) + 1)

theorem exponent_pos (t : ℕ) (ht : 1 ≤ t) : 1 ≤ exponent t := by
  unfold exponent
  nlinarith

private theorem self_le_power (base : ℕ) (hbase : 2 ≤ base) : ∀ q, q ≤ base ^ q := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    have hp : 1 ≤ base ^ q := one_le_pow₀ (by omega)
    calc
      q + 1 ≤ base ^ q + base ^ q := by omega
      _ = 2 * base ^ q := by omega
      _ ≤ base * base ^ q := Nat.mul_le_mul_right _ hbase
      _ = base ^ (q + 1) := by rw [pow_succ, Nat.mul_comm]

theorem field_power_bound (L t R : ℕ) (hL : 3 ≤ L) (hR : 1 ≤ R) :
    fieldBound (2 * L) (2 * t * R) ^ (53 * (2 * t * R)) ≤
      (L * R) ^ (exponent t * R) := by
  let C := 32 * (2 * t + 1)
  have hbase : 2 ≤ L * R := by nlinarith
  have hC : C ≤ (L * R) ^ C := self_le_power (L * R) hbase C
  have hfield : fieldBound (2 * L) (2 * t * R) ≤ C * (L * R) := by
    have hinner : 2 * t * R + 1 ≤ (2 * t + 1) * R := by nlinarith
    calc
      fieldBound (2 * L) (2 * t * R) = 32 * L * (2 * t * R + 1) := by unfold fieldBound; ring
      _ ≤ 32 * L * ((2 * t + 1) * R) := Nat.mul_le_mul_left _ hinner
      _ = C * (L * R) := by dsimp [C]; ring
  have hb : fieldBound (2 * L) (2 * t * R) ≤ (L * R) ^ (C + 1) := by
    calc
      fieldBound (2 * L) (2 * t * R) ≤ C * (L * R) := hfield
      _ ≤ (L * R) ^ C * (L * R) := Nat.mul_le_mul_right _ hC
      _ = (L * R) ^ (C + 1) := (pow_succ _ _).symm
  change fieldBound (2 * L) (2 * t * R) ^ (53 * (2 * t * R)) ≤ (L * R) ^ (exponent t * R)
  calc
    _ ≤ ((L * R) ^ (C + 1)) ^ (53 * (2 * t * R)) := by gcongr
    _ = (L * R) ^ (exponent t * R) := by
      rw [← pow_mul]
      congr 1
      dsimp [C, exponent]
      ring

#print axioms exponent_pos
#print axioms field_power_bound

end DeletionCode.Burst.CountExponent
