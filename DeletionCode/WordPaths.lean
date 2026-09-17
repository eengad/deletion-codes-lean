import DeletionCode.Windows

/-!
Concrete contiguity of a word whose L-windows occur in a k-unique word.

This is the word-level step used to place a component's root negative path
inside x. It does not assume that the occurrence positions are consecutive:
that fact is proved from k-uniqueness and the overlaps of consecutive windows.
Finite lengths are explicit bounds on total letter functions, as in Windows.
-/

namespace DeletionCode.WordPaths

open Windows

/-- A length-L window has a valid occurrence in the finite prefix of x. -/
def Occurs (x : Letters) (n : ℕ) (p : Letters) (i L : ℕ) : Prop :=
  ∃ a, a + L ≤ n ∧ Agree x a p i L

/-- Two consecutive L-windows must occur consecutively in a k-unique x. -/
theorem consecutive_occurrences
    (x p : Letters) (n k L i a b : ℕ)
    (hx : KUnique x n k) (hk : k < L)
    (ha : a + L ≤ n) (hb : b + L ≤ n)
    (hleft : Agree x a p i L) (hright : Agree x b p (i + 1) L) :
    b = a + 1 := by
  have hmatch : Agree x (a + 1) x b k := by
    intro j hj
    have hl := hleft (j + 1) (by omega)
    have hr := hright j (by omega)
    calc
      x (a + 1 + j) = x (a + (j + 1)) := congrArg x (by omega)
      _ = p (i + (j + 1)) := hl
      _ = p (i + 1 + j) := congrArg p (by omega)
      _ = x (b + j) := hr.symm
  exact (hx (a + 1) b (by omega) (by omega) hmatch).symm

/--
All L-windows of p occurring in x forces the whole length-(L+D) word to
occur in x. This establishes contiguity rather than taking it as a premise.
-/
theorem all_windows_occur_implies_subword
    (x p : Letters) (n k L D : ℕ)
    (hx : KUnique x n k) (hk : k < L)
    (hocc : ∀ i, i ≤ D → Occurs x n p i L) :
    ∃ a, a + (L + D) ≤ n ∧ Agree x a p 0 (L + D) := by
  obtain ⟨a, ha, hzero⟩ := hocc 0 (by omega)
  have aligned : ∀ i, i ≤ D →
      a + i + L ≤ n ∧ Agree x (a + i) p i L := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa only [Nat.add_zero] using And.intro ha hzero
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      obtain ⟨b, hb, hnext⟩ := hocc (i + 1) hi
      have heq := consecutive_occurrences x p n k L i (a + i) b
        hx hk hprev.1 hb hprev.2 hnext
      constructor
      · omega
      · have hindex : a + (i + 1) = b := by omega
        simpa only [hindex] using hnext
  refine ⟨a, by have hlast := (aligned D le_rfl).1; omega, ?_⟩
  intro j hj
  let i := min j D
  have hiD : i ≤ D := Nat.min_le_right j D
  have hij : i ≤ j := Nat.min_le_left j D
  have hlocal : j - i < L := by
    dsimp [i]
    by_cases h : j ≤ D
    · rw [Nat.min_eq_left h]
      omega
    · rw [Nat.min_eq_right (by omega)]
      omega
  have heq := (aligned i hiD).2 (j - i) hlocal
  have hsource : a + i + (j - i) = a + j := by omega
  have htarget : i + (j - i) = 0 + j := by omega
  simpa only [hsource, htarget] using heq

/-- The full word occurrence is unique; no second root position is needed. -/
theorem subword_position_unique
    (x p : Letters) (n k m a b : ℕ)
    (hx : KUnique x n k) (hkm : k ≤ m)
    (ha : a + m ≤ n) (hb : b + m ≤ n)
    (hleft : Agree x a p 0 m) (hright : Agree x b p 0 m) :
    a = b := by
  apply hx a b (by omega) (by omega)
  intro i hi
  exact (hleft i (by omega)).trans (hright i (by omega)).symm

#print axioms consecutive_occurrences
#print axioms all_windows_occur_implies_subword
#print axioms subword_position_unique

end DeletionCode.WordPaths
