import DeletionCode.FinitePairUnion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
Explicit constants for counting short and nonseparated alignment records.
Four edit tags over-encode the orientation and inserted bit. This changes
only the constant depending on t, not the essential power n^(2*t-1).
-/
namespace DeletionCode.ExceptionalCountArithmetic

open scoped BigOperators

/-- A deliberately generous constant, depending only on the edit radius. -/
def exceptionalConstant (t : ℕ) : ℕ :=
  (t + 8 * (2 * t) * (2 * t + 2)) * 4 ^ (2 * t)

theorem exceptionalConstant_pos {t : ℕ} (ht : 1 ≤ t) :
    0 < exceptionalConstant t := by
  unfold exceptionalConstant
  apply Nat.mul_pos
  · omega
  · positivity

/-- All smaller balanced edit counts contribute a lower power of n. Including
the unused zero-edit record is harmless and simplifies the upper bound. -/
theorem short_records_bound (n t : ℕ) (hn : 1 ≤ n) :
    (∑ d ∈ Finset.range t, n ^ (2 * d) * 4 ^ (2 * d)) ≤
      t * 4 ^ (2 * t) * n ^ (2 * t - 1) := by
  calc
    _ ≤ ∑ _d ∈ Finset.range t, 4 ^ (2 * t) * n ^ (2 * t - 1) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdt : d < t := Finset.mem_range.mp hd
      have he : 2 * d ≤ 2 * t - 1 := by omega
      have hn' : n ^ (2 * d) ≤ n ^ (2 * t - 1) := pow_le_pow_right₀ hn he
      have hfour : (4 : ℕ) ^ (2 * d) ≤ 4 ^ (2 * t) :=
        pow_le_pow_right₀ (by decide) (by omega)
      calc
        _ ≤ n ^ (2 * t - 1) * 4 ^ (2 * t) := Nat.mul_le_mul hn' hfour
        _ = _ := Nat.mul_comm _ _
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

/-- The close-anchor saving and the short-trace bound combine into one
constant times L*n^(2*t-1). -/
theorem combined_records_bound (n t L : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    (∑ d ∈ Finset.range t, n ^ (2 * d) * 4 ^ (2 * d)) +
        (2 * t) * (2 * t + 2) * (2 * (4 * L)) * n ^ (2 * t - 1) * 4 ^ (2 * t) ≤
      exceptionalConstant t * L * n ^ (2 * t - 1) := by
  have hs := short_records_bound n t hn
  have hsL : t * 4 ^ (2 * t) * n ^ (2 * t - 1) ≤
      t * 4 ^ (2 * t) * n ^ (2 * t - 1) * L :=
    Nat.le_mul_of_pos_right _ hL
  calc
    _ ≤ t * 4 ^ (2 * t) * n ^ (2 * t - 1) * L +
        (2 * t) * (2 * t + 2) * (2 * (4 * L)) * n ^ (2 * t - 1) * 4 ^ (2 * t) :=
      Nat.add_le_add_right (hs.trans hsL) _
    _ = _ := by unfold exceptionalConstant; ring

#print axioms short_records_bound
#print axioms combined_records_bound

end DeletionCode.ExceptionalCountArithmetic
