import DeletionCode.FiniteConflictGraph
import DeletionCode.OverlapCollision
import DeletionCode.FinitePairUnion
import DeletionCode.UniqueWordParameters
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
The actual finite family of k-unique binary words. A failure of uniqueness
is represented by a pair of distinct, in-bounds starting positions, including
overlapping windows. Counts below use the same padded words and uniqueness
predicate as the conflict graph and the deterministic proof chain.
-/
namespace DeletionCode.UniqueWordCount

open Windows HeaderRecovery
attribute [local instance] Classical.propDecidable

noncomputable def uniqueWords (n k : ℕ) : Finset (Bits n) := by
  classical
  exact Finset.univ.filter (fun x => KUnique (padBits x) n k)

noncomputable def nonuniqueWords (n k : ℕ) : Finset (Bits n) := by
  classical
  exact Finset.univ.filter (fun x => ¬ KUnique (padBits x) n k)

/-- Both starting positions are actual valid windows in the finite word. -/
def RepeatedWindow {n : ℕ} (k : ℕ) (a b : Fin n) (x : Bits n) : Prop :=
  a.val + k ≤ n ∧ b.val + k ≤ n ∧ Agree (padBits x) a.val (padBits x) b.val k

theorem mem_uniqueWords {n k : ℕ} (x : Bits n) :
    x ∈ uniqueWords n k ↔ FiniteConflictGraph.Unique k x := by
  classical
  simp only [uniqueWords, Finset.mem_filter, Finset.mem_univ, true_and,
    FiniteConflictGraph.Unique]

theorem not_unique_iff_pair {n k : ℕ} (hk : 1 ≤ k) (x : Bits n) :
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
    (uniqueWords n k).card + (nonuniqueWords n k).card = 2 ^ n := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Bits n))) (fun x => KUnique (padBits x) n k)
  simpa only [uniqueWords, nonuniqueWords, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool] using h

theorem unique_of_length_lt {n k : ℕ} (hk : n < k) (x : Bits n) :
    KUnique (padBits x) n k := by
  intro a b ha hb hab
  omega

theorem uniqueWords_eq_univ_of_length_lt {n k : ℕ} (hk : n < k) :
    uniqueWords n k = Finset.univ := by
  classical
  ext x
  simp only [uniqueWords, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact unique_of_length_lt hk x

theorem card_uniqueWords_of_length_lt {n k : ℕ} (hk : n < k) :
    (uniqueWords n k).card = 2 ^ n := by
  rw [uniqueWords_eq_univ_of_length_lt hk]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- A fixed pair contributes at most 2^(n-k) words, with overlapping and
out-of-bounds pairs both handled explicitly. -/
theorem repeatedWindow_card_le (n k : ℕ) (a b : Fin n) (hab : a < b) :
    (Finset.univ.filter (RepeatedWindow k a b)).card ≤ 2 ^ (n - k) := by
  classical
  by_cases ha : a.val + k ≤ n
  · by_cases hb : b.val + k ≤ n
    · have heq : (Finset.univ.filter (RepeatedWindow k a b)).card =
          Fintype.card (OverlapCollision.Collision n k a.val b.val) := by
        rw [Fintype.card_subtype]
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, RepeatedWindow, ha, hb, true_and]
      rw [heq]
      exact OverlapCollision.collision_card_le n k a.val b.val hab ha hb
    · have hz : Finset.univ.filter (RepeatedWindow k a b) = ∅ := by
        ext x
        simp [RepeatedWindow, hb]
      rw [hz]
      exact Nat.zero_le _
  · have hz : Finset.univ.filter (RepeatedWindow k a b) = ∅ := by
      ext x
      simp [RepeatedWindow, ha]
    rw [hz]
    exact Nat.zero_le _

/-- Union bound on the actual nonunique family, counted once per word. -/
theorem nonunique_card_le (n k : ℕ) (hk : 1 ≤ k) :
    (nonuniqueWords n k).card ≤ n.choose 2 * 2 ^ (n - k) := by
  classical
  have h := FinitePairUnion.ordered_pair_union_bound n (2 ^ (n - k))
    (RepeatedWindow k) (repeatedWindow_card_le n k)
  simpa only [nonuniqueWords, not_unique_iff_pair hk] using h

theorem scaled_nonunique_card_le (n k : ℕ) (hk : 1 ≤ k) :
    (nonuniqueWords n k).card * 2 ^ k ≤ n.choose 2 * 2 ^ n := by
  by_cases hkn : k ≤ n
  · have h := Nat.mul_le_mul_right (2 ^ k) (nonunique_card_le n k hk)
    have hp : 2 ^ (n - k) * 2 ^ k = 2 ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hkn]
    simpa only [Nat.mul_assoc, hp] using h
  · have h := family_partition n k
    rw [card_uniqueWords_of_length_lt (by omega)] at h
    have hz : (nonuniqueWords n k).card = 0 := by omega
    simp only [hz, Nat.zero_mul, Nat.zero_le]

/-- The manuscript's union-bound estimate, with the cardinality of the
actual k-unique family and no assumed collision-probability premise. -/
theorem card_unique_lower_bound (n k : ℕ) (hk : 1 ≤ k) :
    (1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ k) * (2 : ℚ) ^ n ≤
      (uniqueWords n k).card := by
  have hpow : (0 : ℚ) < 2 ^ k := pow_pos (by norm_num) _
  have hscaled : ((nonuniqueWords n k).card : ℚ) * (2 : ℚ) ^ k ≤
      (n.choose 2 : ℚ) * (2 : ℚ) ^ n := by
    exact_mod_cast scaled_nonunique_card_le n k hk
  have hbad : ((nonuniqueWords n k).card : ℚ) ≤
      (n.choose 2 : ℚ) / (2 : ℚ) ^ k * (2 : ℚ) ^ n := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hpow).mpr hscaled
  have hpart : ((uniqueWords n k).card : ℚ) + (nonuniqueWords n k).card = (2 : ℚ) ^ n := by
    exact_mod_cast family_partition n k
  nlinarith

theorem card_unique_lower_bound_real (n k : ℕ) (hk : 1 ≤ k) :
    (1 - (n.choose 2 : ℝ) / (2 : ℝ) ^ k) * (2 : ℝ) ^ n ≤
      (uniqueWords n k).card := by
  have h : (((1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ k) * (2 : ℚ) ^ n : ℚ) : ℝ) ≤
      (((uniqueWords n k).card : ℚ) : ℝ) := by
    exact_mod_cast card_unique_lower_bound n k hk
  simpa only [Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] using h

/-- Complete lemma `lem:family`: the paper's parameter retains at least
seven eighths of all n-bit words, and hence at least 2^(n-1) words. -/
theorem most_words_unique (n : ℕ) (hn : 1 ≤ n) :
    let k := UniqueWordParameters.uniquenessLength n
    (1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ k) * (2 : ℚ) ^ n ≤ (uniqueWords n k).card ∧
    (7 / 8 : ℚ) * (2 : ℚ) ^ n ≤ (1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ k) * (2 : ℚ) ^ n ∧
    (2 : ℚ) ^ (n - 1) ≤ (7 / 8 : ℚ) * (2 : ℚ) ^ n := by
  dsimp
  exact ⟨card_unique_lower_bound n _ (by
      have h := UniqueWordParameters.uniquenessLength_ge_two n
      omega),
    UniqueWordParameters.seven_eighths_le_retained n,
    UniqueWordParameters.half_words_le_seven_eighths n hn⟩

theorem most_words_unique_real (n : ℕ) (hn : 1 ≤ n) :
    let k := 2 * ⌈Real.logb 2 (n : ℝ)⌉₊ + 2
    (1 - (n.choose 2 : ℝ) / (2 : ℝ) ^ k) * (2 : ℝ) ^ n ≤ (uniqueWords n k).card ∧
    (7 / 8 : ℝ) * (2 : ℝ) ^ n ≤ (1 - (n.choose 2 : ℝ) / (2 : ℝ) ^ k) * (2 : ℝ) ^ n ∧
    (2 : ℝ) ^ (n - 1) ≤ (7 / 8 : ℝ) * (2 : ℝ) ^ n := by
  dsimp
  rw [← UniqueWordParameters.uniquenessLength_eq_natCeil n]
  exact ⟨card_unique_lower_bound_real n _ (by
      have h := UniqueWordParameters.uniquenessLength_ge_two n
      omega),
    UniqueWordParameters.seven_eighths_le_retained_real n,
    UniqueWordParameters.half_words_le_seven_eighths_real n hn⟩

/-- Natural cardinality version used by subsequent code-size estimates. -/
theorem half_words_le_card_unique (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (n - 1) ≤ (uniqueWords n (UniqueWordParameters.uniquenessLength n)).card := by
  obtain ⟨hcount, hfrac, hhalf⟩ := most_words_unique n hn
  exact_mod_cast hhalf.trans (hfrac.trans hcount)

#print axioms not_unique_iff_pair
#print axioms family_partition
#print axioms card_uniqueWords_of_length_lt
#print axioms nonunique_card_le
#print axioms card_unique_lower_bound
#print axioms most_words_unique
#print axioms most_words_unique_real
#print axioms half_words_le_card_unique

end DeletionCode.UniqueWordCount
