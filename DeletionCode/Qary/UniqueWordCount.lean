import DeletionCode.Qary.HeaderRecovery
import DeletionCode.Qary.OverlapCollision
import DeletionCode.FinitePairUnion
import DeletionCode.UniqueWordParameters
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
The actual finite family of k-unique finite-alphabet words. A failure of uniqueness
is represented by a pair of distinct, in-bounds starting positions, including
overlapping windows. Counts below use the same padded words and uniqueness
predicate as the conflict graph and the deterministic proof chain.
-/
namespace DeletionCode.Qary.UniqueWordCount

open DeletionCode.Qary.Windows DeletionCode.Qary.HeaderRecovery

variable {α : Type*} [Fintype α] [Inhabited α]
attribute [local instance] Classical.propDecidable

noncomputable def uniqueWords (α : Type*) [Fintype α] [Inhabited α] (n k : ℕ) : Finset (Bits α n) := by
  classical
  exact Finset.univ.filter (fun x => KUnique (padBits x) n k)

noncomputable def nonuniqueWords (α : Type*) [Fintype α] [Inhabited α] (n k : ℕ) : Finset (Bits α n) := by
  classical
  exact Finset.univ.filter (fun x => ¬ KUnique (padBits x) n k)

/-- Both starting positions are actual valid windows in the finite word. -/
def RepeatedWindow {n : ℕ} (k : ℕ) (a b : Fin n) (x : Bits α n) : Prop :=
  a.val + k ≤ n ∧ b.val + k ≤ n ∧ Agree (padBits x) a.val (padBits x) b.val k

theorem mem_uniqueWords {n k : ℕ} (x : Bits α n) :
    x ∈ uniqueWords α n k ↔ KUnique (padBits x) n k := by
  classical
  simp only [uniqueWords, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype α] in
theorem not_unique_iff_pair {n k : ℕ} (hk : 1 ≤ k) (x : Bits α n) :
    ¬ KUnique (padBits x) n k ↔
      ∃ a b : Fin n, a < b ∧ RepeatedWindow k a b x := by
  classical
  constructor
  · intro hx
    simp only [KUnique, not_forall] at hx
    obtain ⟨a, b, ha, hb, hab, hne⟩ := hx
    have han : a < n := by omega
    have hbn : b < n := by omega
    by_cases hlt : a < b
    · exact ⟨⟨a, han⟩, ⟨b, hbn⟩, hlt, ha, hb, hab⟩
    · refine ⟨⟨b, hbn⟩, ⟨a, han⟩, ?_, hb, ha, ?_⟩
      · change b < a
        omega
      · intro i hi
        exact (hab i hi).symm
  · rintro ⟨a, b, hlt, ha, hb, hab⟩ hx
    have heq := hx a.val b.val ha hb hab
    exact (Nat.ne_of_lt hlt) heq

theorem family_partition (n k : ℕ) :
    (uniqueWords α n k).card + (nonuniqueWords α n k).card = Fintype.card α ^ n := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Bits α n))) (fun x => KUnique (padBits x) n k)
  simpa only [uniqueWords, nonuniqueWords, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin] using h

omit [Fintype α] in
theorem unique_of_length_lt {n k : ℕ} (hk : n < k) (x : Bits α n) :
    KUnique (padBits x) n k := by
  intro a b ha hb hab
  omega

theorem uniqueWords_eq_univ_of_length_lt {n k : ℕ} (hk : n < k) :
    uniqueWords α n k = Finset.univ := by
  classical
  ext x
  simp only [uniqueWords, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact unique_of_length_lt hk x

theorem card_uniqueWords_of_length_lt {n k : ℕ} (hk : n < k) :
    (uniqueWords α n k).card = Fintype.card α ^ n := by
  rw [uniqueWords_eq_univ_of_length_lt hk]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

/-- A fixed pair contributes at most q^(n-k) words, with overlapping and
out-of-bounds pairs both handled explicitly. -/
theorem repeatedWindow_card_le (n k : ℕ) (a b : Fin n) (hab : a < b) :
    (Finset.univ.filter (RepeatedWindow (α := α) k a b)).card ≤ Fintype.card α ^ (n - k) := by
  classical
  by_cases ha : a.val + k ≤ n
  · by_cases hb : b.val + k ≤ n
    · have heq : (Finset.univ.filter (RepeatedWindow (α := α) k a b)).card =
          Fintype.card (OverlapCollision.Collision α n k a.val b.val) := by
        rw [Fintype.card_subtype]
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, RepeatedWindow, ha, hb, true_and]
      rw [heq]
      exact OverlapCollision.collision_card_le n k a.val b.val hab ha hb
    · have hz : Finset.univ.filter (RepeatedWindow (α := α) k a b) = ∅ := by
        ext x
        simp [RepeatedWindow, hb]
      rw [hz]
      exact Nat.zero_le _
  · have hz : Finset.univ.filter (RepeatedWindow (α := α) k a b) = ∅ := by
      ext x
      simp [RepeatedWindow, ha]
    rw [hz]
    exact Nat.zero_le _

/-- Union bound on the actual nonunique family, counted once per word. -/
theorem nonunique_card_le (n k : ℕ) (hk : 1 ≤ k) :
    (nonuniqueWords α n k).card ≤ n.choose 2 * Fintype.card α ^ (n - k) := by
  classical
  have h := FinitePairUnion.ordered_pair_union_bound n (Fintype.card α ^ (n - k))
    (RepeatedWindow (α := α) k) (repeatedWindow_card_le n k)
  simpa only [nonuniqueWords, not_unique_iff_pair hk] using h

theorem scaled_nonunique_card_le (n k : ℕ) (hk : 1 ≤ k) :
    (nonuniqueWords α n k).card * Fintype.card α ^ k ≤ n.choose 2 * Fintype.card α ^ n := by
  by_cases hkn : k ≤ n
  · have h := Nat.mul_le_mul_right (Fintype.card α ^ k) (nonunique_card_le (α := α) n k hk)
    have hp : Fintype.card α ^ (n - k) * Fintype.card α ^ k = Fintype.card α ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hkn]
    simpa only [Nat.mul_assoc, hp] using h
  · have h := family_partition (α := α) n k
    rw [card_uniqueWords_of_length_lt (α := α) (by omega)] at h
    have hz : (nonuniqueWords α n k).card = 0 := by omega
    simp only [hz, Nat.zero_mul, Nat.zero_le]

/-- The manuscript's union-bound estimate, with the cardinality of the
actual k-unique family and no assumed collision-probability premise. -/
theorem card_unique_lower_bound (n k : ℕ) (hk : 1 ≤ k) :
    (1 - (n.choose 2 : ℚ) / (Fintype.card α : ℚ) ^ k) * (Fintype.card α : ℚ) ^ n ≤
      (uniqueWords α n k).card := by
  have hpow : (0 : ℚ) < Fintype.card α ^ k :=
    pow_pos (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)) _
  have hscaled : ((nonuniqueWords α n k).card : ℚ) * (Fintype.card α : ℚ) ^ k ≤
      (n.choose 2 : ℚ) * (Fintype.card α : ℚ) ^ n := by
    exact_mod_cast scaled_nonunique_card_le (α := α) n k hk
  have hbad : ((nonuniqueWords α n k).card : ℚ) ≤
      (n.choose 2 : ℚ) / (Fintype.card α : ℚ) ^ k * (Fintype.card α : ℚ) ^ n := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hpow).mpr hscaled
  have hpart : ((uniqueWords α n k).card : ℚ) + (nonuniqueWords α n k).card = (Fintype.card α : ℚ) ^ n := by
    exact_mod_cast family_partition (α := α) n k
  nlinarith

theorem card_unique_lower_bound_real (n k : ℕ) (hk : 1 ≤ k) :
    (1 - (n.choose 2 : ℝ) / (Fintype.card α : ℝ) ^ k) * (Fintype.card α : ℝ) ^ n ≤
      (uniqueWords α n k).card := by
  have h : (((1 - (n.choose 2 : ℚ) / (Fintype.card α : ℚ) ^ k) * (Fintype.card α : ℚ) ^ n : ℚ) : ℝ) ≤
      (((uniqueWords α n k).card : ℚ) : ℝ) := by
    exact_mod_cast card_unique_lower_bound (α := α) n k hk
  simpa only [Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] using h

/-- Binary k is conservative for every alphabet with at least two letters. -/
theorem eight_mul_choose_le_pow (q n : ℕ) (hq : 2 ≤ q) :
    8 * n.choose 2 ≤ q ^ UniqueWordParameters.uniquenessLength n :=
  (UniqueWordParameters.eight_mul_choose_le_pow n).trans (Nat.pow_le_pow_left hq _)

theorem collision_fraction_le (q n : ℕ) (hq : 2 ≤ q) :
    (n.choose 2 : ℚ) / (q : ℚ) ^ UniqueWordParameters.uniquenessLength n ≤ 1 / 8 := by
  have hpow : (0 : ℚ) < (q : ℚ) ^ UniqueWordParameters.uniquenessLength n := by
    positivity
  have hscaled : (8 : ℚ) * n.choose 2 ≤ (q : ℚ) ^ UniqueWordParameters.uniquenessLength n := by
    exact_mod_cast eight_mul_choose_le_pow q n hq
  apply (div_le_iff₀ hpow).mpr
  nlinarith

theorem seven_eighths_le_card_unique (n : ℕ) (hq : 2 ≤ Fintype.card α) :
    (7 / 8 : ℚ) * (Fintype.card α : ℚ) ^ n ≤
      (uniqueWords α n (UniqueWordParameters.uniquenessLength n)).card := by
  have hcount := card_unique_lower_bound (α := α) n
    (UniqueWordParameters.uniquenessLength n) (by
      have := UniqueWordParameters.uniquenessLength_ge_two n
      omega)
  have hfrac := collision_fraction_le (Fintype.card α) n hq
  have hret := mul_le_mul_of_nonneg_right (show (7 / 8 : ℚ) ≤
    1 - (n.choose 2 : ℚ) / (Fintype.card α : ℚ) ^ UniqueWordParameters.uniquenessLength n by
    linarith) (pow_nonneg (Nat.cast_nonneg (Fintype.card α)) n)
  exact hret.trans hcount

theorem seven_eighths_le_card_unique_real (n : ℕ) (hq : 2 ≤ Fintype.card α) :
    (7 / 8 : ℝ) * (Fintype.card α : ℝ) ^ n ≤
      (uniqueWords α n (UniqueWordParameters.uniquenessLength n)).card := by
  have h : (((7 / 8 : ℚ) * (Fintype.card α : ℚ) ^ n : ℚ) : ℝ) ≤
      (((uniqueWords α n (UniqueWordParameters.uniquenessLength n)).card : ℚ) : ℝ) := by
    exact_mod_cast seven_eighths_le_card_unique (α := α) n hq
  simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_ofNat] using h

/-- Keep the factor two independent of q in the final code selection. -/
theorem card_pow_le_two_mul_card_unique (n : ℕ) (hq : 2 ≤ Fintype.card α) :
    Fintype.card α ^ n ≤
      2 * (uniqueWords α n (UniqueWordParameters.uniquenessLength n)).card := by
  have h := seven_eighths_le_card_unique (α := α) n hq
  have hp : (0 : ℚ) ≤ (Fintype.card α : ℚ) ^ n := pow_nonneg (Nat.cast_nonneg _) _
  have hbound : (Fintype.card α : ℚ) ^ n ≤
      2 * ((uniqueWords α n (UniqueWordParameters.uniquenessLength n)).card : ℚ) := by
    nlinarith
  exact_mod_cast hbound

#print axioms card_unique_lower_bound
#print axioms seven_eighths_le_card_unique
#print axioms card_pow_le_two_mul_card_unique

end DeletionCode.Qary.UniqueWordCount
