import DeletionCode.FinitePairUnion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
Explicit constants for counting short and nonseparated alignment records.
Four edit tags encode a deletion, a substitution, or an insertion with its
bit. Short records have fewer than 2t packets; full records have 2t packets
and one of t+1 possible matched-column totals. This changes only the
constant depending on t, not the essential power n^(2*t-1).
-/
namespace DeletionCode.ExceptionalCountArithmetic

open scoped BigOperators

/-- A deliberately generous constant, depending only on the edit radius. -/
def exceptionalConstant (t : ℕ) : ℕ :=
  (2 * t + 8 * (t + 1) * (2 * t) * (2 * t + 2)) * 4 ^ (2 * t)

theorem exceptionalConstant_pos {t : ℕ} (ht : 1 ≤ t) :
    0 < exceptionalConstant t := by
  unfold exceptionalConstant
  apply Nat.mul_pos
  · omega
  · positivity

/-- All smaller edit counts contribute a lower power of n. Including the
unused zero-edit record is harmless and simplifies the upper bound. -/
theorem short_records_bound (n t : ℕ) (hn : 1 ≤ n) :
    (∑ r ∈ Finset.range (2 * t), n ^ r * 4 ^ r) ≤
      2 * t * 4 ^ (2 * t) * n ^ (2 * t - 1) := by
  calc
    _ ≤ ∑ _r ∈ Finset.range (2 * t), 4 ^ (2 * t) * n ^ (2 * t - 1) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrt : r < 2 * t := Finset.mem_range.mp hr
      have he : r ≤ 2 * t - 1 := by omega
      have hn' : n ^ r ≤ n ^ (2 * t - 1) := pow_le_pow_right₀ hn he
      have hfour : (4 : ℕ) ^ r ≤ 4 ^ (2 * t) :=
        pow_le_pow_right₀ (by decide) (by omega)
      calc
        _ ≤ n ^ (2 * t - 1) * 4 ^ (2 * t) := Nat.mul_le_mul hn' hfour
        _ = _ := Nat.mul_comm _ _
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

/-- The close-anchor saving and the short-trace bound combine into one
constant times L*n^(2*t-1). -/
theorem combined_records_bound (n t L : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    (∑ r ∈ Finset.range (2 * t), n ^ r * 4 ^ r) +
        (t + 1) * ((2 * t) * (2 * t + 2) * (2 * (4 * L)) * n ^ (2 * t - 1) * 4 ^ (2 * t)) ≤
      exceptionalConstant t * L * n ^ (2 * t - 1) := by
  have hs := short_records_bound n t hn
  have hsL : 2 * t * 4 ^ (2 * t) * n ^ (2 * t - 1) ≤
      2 * t * 4 ^ (2 * t) * n ^ (2 * t - 1) * L :=
    Nat.le_mul_of_pos_right _ hL
  calc
    _ ≤ 2 * t * 4 ^ (2 * t) * n ^ (2 * t - 1) * L +
        (t + 1) * ((2 * t) * (2 * t + 2) * (2 * (4 * L)) * n ^ (2 * t - 1) * 4 ^ (2 * t)) :=
      Nat.add_le_add_right (hs.trans hsL) _
    _ = _ := by unfold exceptionalConstant; ring

#print axioms short_records_bound
#print axioms combined_records_bound

end DeletionCode.ExceptionalCountArithmetic
