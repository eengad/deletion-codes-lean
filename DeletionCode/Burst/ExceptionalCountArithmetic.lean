import DeletionCode.Burst.ExceptionalRecords
import Mathlib.Tactic.Linarith

namespace DeletionCode.Burst.ExceptionalCountArithmetic

open scoped BigOperators

/-- This constant depends only on the operation budget and burst length. -/
def constant (t b : ℕ) : ℕ :=
  (2 * t + (2 * t) * (2 * t + 2) * 16 * (1 + t * b)) *
    ((b + 1) ^ 2) ^ (2 * t) * (2 * t * b + 2) ^ (2 * t - 1)

theorem short_records_bound (N P t : ℕ) (hN : 1 ≤ N) (hP : 1 ≤ P) :
    (∑ r ∈ Finset.range (2 * t), N ^ r * P ^ r) ≤
      (2 * t) * N ^ (2 * t - 1) * P ^ (2 * t) := by
  calc
    _ ≤ ∑ _r ∈ Finset.range (2 * t), N ^ (2 * t - 1) * P ^ (2 * t) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrt := Finset.mem_range.mp hr
      exact Nat.mul_le_mul (pow_le_pow_right₀ hN (by omega))
        (pow_le_pow_right₀ hP (by omega))
    _ = _ := by simp [mul_assoc]

theorem combined_records_bound (q n t b L : ℕ)
    (hq : 1 ≤ q) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    (∑ r ∈ Finset.range (2 * t), (n + 2 * t * b + 1) ^ r *
      ((b + 1) ^ 2 * q ^ b) ^ r) +
      (2 * t) * (2 * t + 2) * (2 * (8 * (L + t * b))) *
        (n + 2 * t * b + 1) ^ (2 * t - 1) *
          ((b + 1) ^ 2 * q ^ b) ^ (2 * t) ≤
      constant t b * q ^ (2 * b * t) * L * n ^ (2 * t - 1) := by
  let N := n + 2 * t * b + 1
  let P := (b + 1) ^ 2 * q ^ b
  have hP : 1 ≤ P := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega)))
  have hs := short_records_bound N P t (by dsimp [N]; omega) hP
  have hN : N ≤ (2 * t * b + 2) * n := by
    have hh := Nat.mul_le_mul_left (2 * t * b + 1) hn
    dsimp [N]
    nlinarith
  have hpow := Nat.pow_le_pow_left hN (2 * t - 1)
  have hD : 2 * (8 * (L + t * b)) ≤ 16 * (1 + t * b) * L := by
    have hh := Nat.mul_le_mul_left (t * b) hL
    nlinarith
  have hc : 2 * t + (2 * t) * (2 * t + 2) * (2 * (8 * (L + t * b))) ≤
      (2 * t + (2 * t) * (2 * t + 2) * 16 * (1 + t * b)) * L := by
    have hmul := Nat.mul_le_mul_left ((2 * t) * (2 * t + 2)) hD
    nlinarith
  calc
    _ ≤ (2 * t + (2 * t) * (2 * t + 2) * (2 * (8 * (L + t * b)))) *
        N ^ (2 * t - 1) * P ^ (2 * t) := by
      calc
        _ ≤ (2 * t) * N ^ (2 * t - 1) * P ^ (2 * t) +
            (2 * t) * (2 * t + 2) * (2 * (8 * (L + t * b))) *
              N ^ (2 * t - 1) * P ^ (2 * t) := Nat.add_le_add_right hs _
        _ = _ := by ring
    _ ≤ ((2 * t + (2 * t) * (2 * t + 2) * 16 * (1 + t * b)) * L) *
        ((2 * t * b + 2) * n) ^ (2 * t - 1) * P ^ (2 * t) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hc hpow)
    _ = _ := by
      simp only [P, constant, mul_pow, ← pow_mul]
      rw [show b * (2 * t) = 2 * b * t by ring]
      ring

theorem words_card_le {α : Type*} [Fintype α] (n t b L : ℕ) (x : Word α)
    (hq : 1 ≤ Fintype.card α) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    (ExceptionalRecords.words b t n (8 * (L + t * b)) x).card ≤
      constant t b * Fintype.card α ^ (2 * b * t) * L * n ^ (2 * t - 1) :=
  (ExceptionalRecords.words_card_le ..).trans
    (combined_records_bound _ n t b L hq hn hL)

end DeletionCode.Burst.ExceptionalCountArithmetic
