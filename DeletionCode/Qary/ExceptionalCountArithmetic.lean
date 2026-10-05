import DeletionCode.ExceptionalCountArithmetic

/-!
Exceptional chronological records over a finite alphabet. A packet has at
most 4q payloads, so at most 2t packets introduce only q^(2t) beyond the
binary radius-dependent constant. The positional saving is unchanged.
-/
namespace DeletionCode.Qary.ExceptionalCountArithmetic

open scoped BigOperators

abbrev exceptionalConstant := DeletionCode.ExceptionalCountArithmetic.exceptionalConstant

theorem exceptionalConstant_pos {t : ℕ} (ht : 1 ≤ t) :
    0 < exceptionalConstant t :=
  DeletionCode.ExceptionalCountArithmetic.exceptionalConstant_pos ht

theorem short_records_bound (q n t : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n) :
    (∑ r ∈ Finset.range (2 * t), n ^ r * (4 * q) ^ r) ≤
      2 * t * 4 ^ (2 * t) * q ^ (2 * t) * n ^ (2 * t - 1) := by
  calc
    _ ≤ ∑ _r ∈ Finset.range (2 * t),
        (4 * q) ^ (2 * t) * n ^ (2 * t - 1) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrt : r < 2 * t := Finset.mem_range.mp hr
      have hn' : n ^ r ≤ n ^ (2 * t - 1) :=
        pow_le_pow_right₀ hn (by omega)
      have htag : (4 * q) ^ r ≤ (4 * q) ^ (2 * t) :=
        pow_le_pow_right₀ (by omega) (by omega)
      calc
        _ ≤ n ^ (2 * t - 1) * (4 * q) ^ (2 * t) := Nat.mul_le_mul hn' htag
        _ = _ := Nat.mul_comm _ _
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_pow]
      ring

theorem combined_records_bound (q n t L : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    (∑ r ∈ Finset.range (2 * t), n ^ r * (4 * q) ^ r) +
        (t + 1) * ((2 * t) * (2 * t + 2) * (2 * (4 * L)) *
          n ^ (2 * t - 1) * (4 * q) ^ (2 * t)) ≤
      exceptionalConstant t * q ^ (2 * t) * L * n ^ (2 * t - 1) := by
  have hs := short_records_bound q n t hq hn
  have hsL : 2 * t * 4 ^ (2 * t) * q ^ (2 * t) * n ^ (2 * t - 1) ≤
      2 * t * 4 ^ (2 * t) * q ^ (2 * t) * n ^ (2 * t - 1) * L :=
    Nat.le_mul_of_pos_right _ hL
  calc
    _ ≤ 2 * t * 4 ^ (2 * t) * q ^ (2 * t) * n ^ (2 * t - 1) * L +
        (t + 1) * ((2 * t) * (2 * t + 2) * (2 * (4 * L)) *
          n ^ (2 * t - 1) * (4 * q) ^ (2 * t)) :=
      Nat.add_le_add_right (hs.trans hsL) _
    _ = _ := by
      unfold exceptionalConstant DeletionCode.ExceptionalCountArithmetic.exceptionalConstant
      rw [mul_pow]
      ring

#print axioms short_records_bound
#print axioms combined_records_bound

end DeletionCode.Qary.ExceptionalCountArithmetic
