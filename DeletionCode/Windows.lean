import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-!
Local word-recovery lemmas — partial formalization.
Target: Section 5, `lem:resolve`, of binary_existence_2t_minus_1.tex.
Checked with Lean 4.34.0; this file alone does not verify the counting lemma.
Finite words are represented by total letter functions with explicit bounds.
-/
namespace DeletionCode.Windows

abbrev Letters := ℕ → Bool

def Agree (x : Letters) (a : ℕ) (y : Letters) (b k : ℕ) : Prop :=
  ∀ i, i < k → x (a + i) = y (b + i)

def KUnique (x : Letters) (n k : ℕ) : Prop :=
  ∀ a b, a + k ≤ n → b + k ≤ n → Agree x a x b k → a = b

/-- A known k-stretch at a fixed offset determines a window in x. -/
theorem unique_window_lookup
    (x : Letters) (n k L a b r : ℕ)
    (hx : KUnique x n k) (ha : a + L ≤ n) (hb : b + L ≤ n)
    (hr : r + k ≤ L) (h : Agree x (a + r) x (b + r) k) : a = b := by
  have heq : a + r = b + r :=
    hx (a + r) (b + r) (by omega) (by omega) h
  omega

/-- The three selected windows contain every valid k-stretch. -/
theorem three_windows_cover
    (k D s : ℕ) (hD : D < 3 * (k + 1))
    (hs : s + k ≤ 3 * (k + 1) + D) :
    ∃ a : ℕ, (a = 0 ∨ a = D / 2 ∨ a = D) ∧
      a ≤ s ∧ s + k ≤ a + 3 * (k + 1) := by
  by_cases hfirst : s + k ≤ 3 * (k + 1)
  · exact ⟨0, Or.inl rfl, Nat.zero_le s, by omega⟩
  · by_cases hmiddle : s + k ≤ D / 2 + 3 * (k + 1)
    · exact ⟨D / 2, Or.inr (Or.inl rfl), by omega, hmiddle⟩
    · exact ⟨D, Or.inr (Or.inr rfl), by omega, by omega⟩

theorem three_windows_overlap (k D : ℕ) (hD : D < 3 * (k + 1)) :
    D / 2 + k ≤ 3 * (k + 1) ∧
    (D - D / 2) + k ≤ 3 * (k + 1) := by omega

theorem bubble_lengths (k ρ : ℕ) (hρ0 : 1 ≤ ρ) (hρ1 : ρ ≤ k + 1) :
    let L := 3 * (k + 1)
    L - ρ < L ∧ L - ρ - 1 < L ∧
    k + 1 < 2 * L - ρ - 1 ∧ (L - 1) + k < 2 * L - ρ := by
  dsimp
  omega

def deleteAt (p : Letters) (ell : ℕ) : Letters :=
  fun i => if i < ell then p i else p (i + 1)

def insertAt (p : Letters) (ell : ℕ) (d : Bool) : Letters :=
  fun i => if i < ell then p i else if i = ell then d else p (i - 1)

/-- Rebuild the shortened seed using its old k bits and one extension bit. -/
def deletionSeed (k cut : ℕ) (extra : Bool) (u : Letters) : Letters :=
  fun i => if i < cut then u i else if i + 1 < k then u (i + 1) else extra

def insertionSeed (cut : ℕ) (d : Bool) (u : Letters) : Letters :=
  fun i => if i < cut then u i else if i = cut then d else u (i - 1)

theorem delete_insert (p : Letters) (ell : ℕ) (d : Bool) :
    deleteAt (insertAt p ell d) ell = p := by
  funext i
  by_cases h : i < ell
  · simp [deleteAt, insertAt, h]
  · have hnext : ¬ i + 1 < ell := by omega
    have hne : i + 1 ≠ ell := by omega
    simp [deleteAt, insertAt, h, hnext, hne]

theorem insert_delete (p : Letters) (ell : ℕ) :
    insertAt (deleteAt p ell) ell (p ell) = p := by
  funext i
  by_cases h : i < ell
  · simp [insertAt, deleteAt, h]
  · by_cases heq : i = ell
    · subst i
      simp [insertAt]
    · have hprev : ¬ i - 1 < ell := by omega
      have hidx : i - 1 + 1 = i := by omega
      simp [insertAt, deleteAt, h, heq, hprev, hidx]

theorem deletion_before (p : Letters) (ell s k : ℕ)
    (h : s + k ≤ ell) : Agree (deleteAt p ell) s p s k := by
  intro i hi
  have hidx : s + i < ell := by omega
  simp [deleteAt, hidx]

theorem deletion_after (p : Letters) (ell s k : ℕ)
    (h : ell < s) : Agree (deleteAt p ell) (s - 1) p s k := by
  intro i hi
  have hidx : ¬ s - 1 + i < ell := by omega
  have heq : s - 1 + i + 1 = s + i := by omega
  simp [deleteAt, hidx, heq]

/-- Crossing deletion: k-1 surviving letters and one right-extension bit. -/
theorem deletion_crossing (p : Letters) (ell s k : ℕ)
    (hs : s ≤ ell) (he : ell < s + k) :
    ∀ i, i < k → deleteAt p ell (s + i) =
      deletionSeed k (ell - s) (deleteAt p ell (s + k - 1))
        (fun j => p (s + j)) i := by
  intro i hi
  unfold deletionSeed
  by_cases hcut : i < ell - s
  · have hidx : s + i < ell := by omega
    simp [hcut, deleteAt, hidx]
  · by_cases hlast : i + 1 < k
    · have hidx : ¬ s + i < ell := by omega
      simp [hcut, hlast, deleteAt, hidx, Nat.add_assoc]
    · have hidx : s + i = s + k - 1 := by omega
      simp only [if_neg hcut, if_neg hlast]
      exact congrArg (deleteAt p ell) hidx

/-- For the paper's parameters, a crossing seed has room to extend right. -/
theorem crossing_extension_in_bounds
    (k ρ s : ℕ) (hρ0 : 1 ≤ ρ) (hρ1 : ρ ≤ k + 1)
    (hs : s ≤ 3 * (k + 1) - 1) :
    s + k ≤ 2 * (3 * (k + 1)) - ρ - 1 := by omega

theorem insertion_before (p : Letters) (ell s k : ℕ) (d : Bool)
    (h : s + k ≤ ell) : Agree (insertAt p ell d) s p s k := by
  intro i hi
  have hidx : s + i < ell := by omega
  simp [insertAt, hidx]

theorem insertion_after (p : Letters) (ell s k : ℕ) (d : Bool)
    (h : ell ≤ s) : Agree (insertAt p ell d) (s + 1) p s k := by
  intro i hi
  have hlt : ¬ s + 1 + i < ell := by omega
  have hne : s + 1 + i ≠ ell := by omega
  have hidx : s + 1 + i - 1 = s + i := by omega
  simp [insertAt, hlt, hne, hidx]

theorem insertion_crossing (p : Letters) (ell s k : ℕ) (d : Bool)
    (hs : s ≤ ell) :
    ∀ i, i < k → insertAt p ell d (s + i) =
      insertionSeed (ell - s) d (fun j => p (s + j)) i := by
  intro i hi
  unfold insertionSeed
  by_cases hcut : i < ell - s
  · have hidx : s + i < ell := by omega
    simp [hcut, insertAt, hidx]
  · by_cases heq : i = ell - s
    · have hidx : s + i = ell := by omega
      simp only [if_neg hcut, if_pos heq]
      simp [insertAt, hidx]
    · have hlt : ¬ s + i < ell := by omega
      have hne : s + i ≠ ell := by omega
      have hidx : s + i - 1 = s + (i - 1) := by omega
      simp [hcut, heq, insertAt, hlt, hne, hidx]

#print axioms unique_window_lookup
#print axioms three_windows_cover
#print axioms three_windows_overlap
#print axioms bubble_lengths
#print axioms delete_insert
#print axioms insert_delete
#print axioms deletion_before
#print axioms deletion_after
#print axioms deletion_crossing
#print axioms crossing_extension_in_bounds
#print axioms insertion_before
#print axioms insertion_after
#print axioms insertion_crossing
end DeletionCode.Windows
