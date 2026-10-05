import DeletionCode.Qary.CatalogueWords
import DeletionCode.Qary.EditRigidity

/-!
Endpoint-only intersections of the actual local words A d^rho B and
A d^(rho-1) B. Flank symbols unequal to the run symbol exclude interior matches once a common
surviving source letter fixes the displacement. For actual same-start
substrings of a source and its deletion or insertion, rigidity derives that
displacement, so it is not an assumption of the final results. For a
substitution the two words A d B and A e B with d ≠ e have equal length, rigidity
gives displacement zero, and the replaced letter itself excludes every
interior common window, so no flank-letter condition is needed.
-/

namespace DeletionCode.Qary.BubbleEndpoints

open DeletionCode.Qary.Windows DeletionCode.Qary.HeaderRecovery DeletionCode.Qary.CatalogueWords DeletionCode.Qary.SingleEditOrigins

variable {α : Type*} [Inhabited α]

private theorem long_first_run {k : ℕ} (bubble : BubbleWord α k) :
    listLetters bubble.longWord (windowLength k - bubble.rho) = bubble.bit := by
  have hlo := bubble.rho_lower
  simp only [listLetters, BubbleWord.longWord, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by rw [bubble.left_length])]
  rw [bubble.left_length, Nat.sub_self]
  rw [List.getElem?_append_left (by simp only [List.length_replicate]; omega)]
  rw [List.getElem?_replicate_of_lt (by omega)]
  rfl

private theorem long_first_right {k : ℕ} (bubble : BubbleWord α k)
    (hright : bubble.right.head? ≠ some bubble.bit) :
    listLetters bubble.longWord (windowLength k) ≠ bubble.bit := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  have hlength := bubble.left_length
  have hindex : windowLength k - bubble.left.length = bubble.rho := by
    unfold windowLength at *
    omega
  simp only [listLetters, BubbleWord.longWord, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), hindex]
  rw [List.getElem?_append_right (by simp only [List.length_replicate]; omega)]
  simp only [List.length_replicate, Nat.sub_self]
  rw [← List.head?_eq_getElem?]
  have hrightlen : 0 < bubble.right.length := by
    rw [bubble.right_length]
    unfold windowLength
    omega
  cases hword : bubble.right with
  | nil => simp [hword] at hrightlen
  | cons a tail => simpa only [hword, List.head?_cons, Option.getD_some,
      ne_eq, Option.some.injEq] using hright

private theorem short_first_right {k : ℕ} (bubble : BubbleWord α k)
    (hright : bubble.right.head? ≠ some bubble.bit) :
    listLetters bubble.shortWord (windowLength k - 1) ≠ bubble.bit := by
  rw [← bubble.delete_longWord]
  have hpos : 0 < windowLength k := by unfold windowLength; omega
  simp only [deleteAt, editOffset, lt_self_iff_false, ite_false]
  have hindex : windowLength k - 1 + 1 = windowLength k := by omega
  rw [hindex]
  exact long_first_right bubble hright

private theorem short_last_left {k : ℕ} (bubble : BubbleWord α k)
    (hleft : bubble.left.getLast? ≠ some bubble.bit) :
    listLetters bubble.shortWord (windowLength k - bubble.rho - 1) ≠ bubble.bit := by
  have hhi := bubble.rho_upper
  have hlength := bubble.left_length
  have hindex : windowLength k - bubble.rho - 1 = bubble.left.length - 1 := by
    rw [hlength]
  have hbound : windowLength k - bubble.rho - 1 < bubble.left.length := by
    unfold windowLength at *
    omega
  simp only [listLetters, BubbleWord.shortWord, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hbound, hindex, ← List.getLast?_eq_getElem?]
  cases hlast : bubble.left.getLast? with
  | none =>
    have hempty : bubble.left = [] := List.getLast?_eq_none_iff.mp hlast
    simp [hempty] at hbound
  | some a => simpa only [hlast, Option.getD_some, ne_eq, Option.some.injEq] using hleft

/-- The actual flank mismatches rule out all interior common vertices with
the displacement furnished by surviving source positions. -/
theorem endpoints_of_displacement {k : ℕ} (bubble : BubbleWord α k)
    (hleft : bubble.left.getLast? ≠ some bubble.bit)
    (hright : bubble.right.head? ≠ some bubble.bit)
    (a b : ℕ) (_ha : a ≤ windowLength k - bubble.rho + 1)
    (hb : b ≤ windowLength k - bubble.rho)
    (hag : Agree (listLetters bubble.longWord) a
      (listLetters bubble.shortWord) b (windowLength k - 1))
    (hdis : a = b ∨ a = b + 1) :
    (a = 0 ∧ b = 0) ∨
      (a = windowLength k - bubble.rho + 1 ∧ b = windowLength k - bubble.rho) := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  have hL : 0 < windowLength k := by unfold windowLength; omega
  rcases hdis with heq | heq
  · have ha0 : a = 0 := by
      by_contra hnot
      have hoff : windowLength k - 1 - a < windowLength k - 1 := by omega
      have hindex : a + (windowLength k - 1 - a) = windowLength k - 1 := by omega
      have hindex' : b + (windowLength k - 1 - a) = windowLength k - 1 := by omega
      have hbits := hag _ hoff
      rw [hindex, hindex'] at hbits
      have hrun : listLetters bubble.longWord (windowLength k - 1) = bubble.bit :=
        bubble.header_bit
      rw [hrun] at hbits
      exact short_first_right bubble hright hbits.symm
    exact Or.inl ⟨ha0, by omega⟩
  · have hbLast : b = windowLength k - bubble.rho := by
      by_contra hnot
      have hoff : windowLength k - bubble.rho - 1 - b < windowLength k - 1 := by omega
      have hindex : a + (windowLength k - bubble.rho - 1 - b) =
          windowLength k - bubble.rho := by omega
      have hindex' : b + (windowLength k - bubble.rho - 1 - b) =
          windowLength k - bubble.rho - 1 := by omega
      have hbits := hag _ hoff
      rw [hindex, hindex', long_first_run bubble] at hbits
      exact short_last_left bubble hleft hbits.symm
    exact Or.inr ⟨by omega, hbLast⟩

/-- A shared source letter in a source/deletion pair fixes the offset displacement. -/
theorem deletion_window_displacement {n k : ℕ} (hk : 1 ≤ k) (x : Letters α)
    (hx : KUnique x n k) (pos : ℕ) (hpos : pos < n) (s a b : ℕ)
    (ha : s + a + (windowLength k - 1) ≤ n)
    (hb : s + b + (windowLength k - 1) ≤ n - 1)
    (hag : Agree x (s + a) (deleteAt x pos) (s + b) (windowLength k - 1)) :
    a = b ∨ a = b + 1 := by
  obtain ⟨r, u, _, _, hsource⟩ := EditRigidity.shared_source_letters hk x hx
    .unchanged (.delete pos) trivial hpos (s + a) (s + b) ha hb hag
  have hfirst := (hsource 0 (by omega)).1
  have hsecond := (hsource 0 (by omega)).2
  simp only [Edit.origin, Nat.add_zero, Option.some.injEq] at hfirst
  by_cases hcut : s + b + r < pos
  · simp only [Edit.origin, Nat.add_zero, ite_eq_left hcut, Option.some.injEq] at hsecond
    exact Or.inl (by omega)
  · simp only [Edit.origin, Nat.add_zero, ite_eq_right hcut, Option.some.injEq] at hsecond
    exact Or.inr (by omega)

/-- The same displacement follows for an insertion/source pair; the matched
letter cannot be the inserted letter, since its origin would be none. -/
theorem insertion_window_displacement {n k : ℕ} (hk : 1 ≤ k) (x : Letters α)
    (hx : KUnique x n k) (pos : ℕ) (bit : α) (hpos : pos ≤ n) (s a b : ℕ)
    (ha : s + a + (windowLength k - 1) ≤ n + 1)
    (hb : s + b + (windowLength k - 1) ≤ n)
    (hag : Agree (insertAt x pos bit) (s + a) x (s + b) (windowLength k - 1)) :
    a = b ∨ a = b + 1 := by
  obtain ⟨r, u, _, _, hsource⟩ := EditRigidity.shared_source_letters hk x hx
    (.insert pos bit) .unchanged hpos trivial (s + a) (s + b) ha hb hag
  have hfirst := (hsource 0 (by omega)).1
  have hsecond := (hsource 0 (by omega)).2
  simp only [Edit.origin, Nat.add_zero, Option.some.injEq] at hsecond
  by_cases hcut : s + a + r < pos
  · simp only [Edit.origin, Nat.add_zero, ite_eq_left hcut, Option.some.injEq] at hfirst
    exact Or.inl (by omega)
  · by_cases heq : s + a + r = pos
    · simp only [Edit.origin, Nat.add_zero, ite_eq_right hcut, ite_eq_left heq, reduceCtorEq] at hfirst
    · simp only [Edit.origin, Nat.add_zero, ite_eq_right hcut, ite_eq_right heq, Option.some.injEq] at hfirst
      exact Or.inr (by omega)

private theorem local_window_bounds {k : ℕ} (bubble : BubbleWord α k) (a b : ℕ)
    (ha : a ≤ windowLength k - bubble.rho + 1)
    (hb : b ≤ windowLength k - bubble.rho) :
    a + (windowLength k - 1) ≤ bubble.longWord.length ∧
      b + (windowLength k - 1) ≤ bubble.shortWord.length := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [bubble.longWord_length, bubble.shortWord_length, longLength, shortLength,
    BubbleWord.header]
  unfold windowLength at *
  omega

private theorem transfer_equal_windows (p q x y : Letters α) (s a b m lenp lenq : ℕ)
    (hp : Agree p 0 x s lenp) (hq : Agree q 0 y s lenq)
    (ha : a + m ≤ lenp) (hb : b + m ≤ lenq) (hag : Agree p a q b m) :
    Agree x (s + a) y (s + b) m := by
  intro i hi
  calc
    x (s + a + i) = p (a + i) := by
      simpa only [Nat.zero_add, Nat.add_assoc] using (hp (a + i) (by omega)).symm
    _ = q (b + i) := hag i hi
    _ = y (s + b + i) := by
      simpa only [Nat.zero_add, Nat.add_assoc] using hq (b + i) (by omega)

/-- Actual local grammar words at the same position in a k-unique source
and its deletion share only their initial and terminal vertices. -/
theorem deletion_endpoints {n k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord α k)
    (hleft : bubble.left.getLast? ≠ some bubble.bit)
    (hright : bubble.right.head? ≠ some bubble.bit)
    (x : Letters α) (hx : KUnique x n k) (pos : ℕ) (hpos : pos < n) (s : ℕ)
    (hlength : s + bubble.longWord.length ≤ n)
    (hslength : s + bubble.shortWord.length ≤ n - 1)
    (hlong : Agree (listLetters bubble.longWord) 0 x s bubble.longWord.length)
    (hshort : Agree (listLetters bubble.shortWord) 0 (deleteAt x pos) s bubble.shortWord.length)
    (a b : ℕ) (ha : a ≤ windowLength k - bubble.rho + 1)
    (hb : b ≤ windowLength k - bubble.rho)
    (hag : Agree (listLetters bubble.longWord) a
      (listLetters bubble.shortWord) b (windowLength k - 1)) :
    (a = 0 ∧ b = 0) ∨
      (a = windowLength k - bubble.rho + 1 ∧ b = windowLength k - bubble.rho) := by
  obtain ⟨halocal, hblocal⟩ := local_window_bounds bubble a b ha hb
  have hglobal := transfer_equal_windows _ _ _ _ s a b _ _ _ hlong hshort halocal hblocal hag
  exact endpoints_of_displacement bubble hleft hright a b ha hb hag
    (deletion_window_displacement hk x hx pos hpos s a b (by omega) (by omega) hglobal)

/-- The corresponding result when the shorter grammar word lies in the
source and the longer word lies at the same position after an insertion. -/
theorem insertion_endpoints {n k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord α k)
    (hleft : bubble.left.getLast? ≠ some bubble.bit)
    (hright : bubble.right.head? ≠ some bubble.bit)
    (x : Letters α) (hx : KUnique x n k) (pos : ℕ) (bit : α) (hpos : pos ≤ n) (s : ℕ)
    (hlength : s + bubble.longWord.length ≤ n + 1)
    (hslength : s + bubble.shortWord.length ≤ n)
    (hlong : Agree (listLetters bubble.longWord) 0 (insertAt x pos bit) s bubble.longWord.length)
    (hshort : Agree (listLetters bubble.shortWord) 0 x s bubble.shortWord.length)
    (a b : ℕ) (ha : a ≤ windowLength k - bubble.rho + 1)
    (hb : b ≤ windowLength k - bubble.rho)
    (hag : Agree (listLetters bubble.longWord) a
      (listLetters bubble.shortWord) b (windowLength k - 1)) :
    (a = 0 ∧ b = 0) ∨
      (a = windowLength k - bubble.rho + 1 ∧ b = windowLength k - bubble.rho) := by
  obtain ⟨halocal, hblocal⟩ := local_window_bounds bubble a b ha hb
  have hglobal := transfer_equal_windows _ _ _ _ s a b _ _ _ hlong hshort halocal hblocal hag
  exact endpoints_of_displacement bubble hleft hright a b ha hb hag
    (insertion_window_displacement hk x hx pos bit hpos s a b (by omega) (by omega) hglobal)

/-- A shared surviving source letter in a source/substitution pair forces
equal offsets: the substituted position has no source origin. -/
theorem substitution_window_displacement {n k : ℕ} (hk : 1 ≤ k) (x : Letters α) (newBit : α)
    (hx : KUnique x n k) (pos : ℕ) (hpos : pos < n) (s a b : ℕ)
    (ha : s + a + (windowLength k - 1) ≤ n)
    (hb : s + b + (windowLength k - 1) ≤ n)
    (hag : Agree x (s + a) (replaceAt x pos newBit) (s + b) (windowLength k - 1)) :
    a = b := by
  obtain ⟨r, u, _, _, hsource⟩ := EditRigidity.shared_source_letters hk x hx
    .unchanged (.substitute pos newBit) trivial hpos (s + a) (s + b) ha hb hag
  have hfirst := (hsource 0 (by omega)).1
  have hsecond := (hsource 0 (by omega)).2
  simp only [Edit.origin, Nat.add_zero, Option.some.injEq] at hfirst
  by_cases heq : s + b + r = pos
  · simp only [Edit.origin, Nat.add_zero, ite_eq_left heq, reduceCtorEq] at hsecond
  · simp only [Edit.origin, Nat.add_zero, ite_eq_right heq, Option.some.injEq] at hsecond
    omega

/-- With displacement zero, every common window other than the two
endpoint windows contains the replaced letter at offset L-1. -/
theorem substitution_endpoints_of_displacement {k : ℕ} (bubble : BubbleWord α k)
    (hne : bubble.bit ≠ bubble.newBit) (a b : ℕ)
    (ha : a ≤ bubble.longWord.length - windowLength k + 1)
    (hag : Agree (listLetters bubble.longWord) a
      (listLetters bubble.replaceWord) b (windowLength k - 1))
    (hdis : a = b) :
    (a = 0 ∧ b = 0) ∨
      (a = bubble.longWord.length - windowLength k + 1 ∧
        b = bubble.replaceWord.length - windowLength k + 1) := by
  subst hdis
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  have hlong : bubble.longWord.length = 2 * windowLength k - bubble.rho := by
    simpa only [longLength, BubbleWord.header] using bubble.longWord_length
  have hflip : bubble.replaceWord.length = 2 * windowLength k - bubble.rho := by
    simpa only [longLength, BubbleWord.header] using bubble.replaceWord_length
  have hL : windowLength k = 3 * (k + 1) := rfl
  by_cases ha0 : a = 0
  · exact Or.inl ⟨ha0, ha0⟩
  by_cases hin : a ≤ windowLength k - 1
  · exfalso
    have hoff : windowLength k - 1 - a < windowLength k - 1 := by omega
    have hindex : a + (windowLength k - 1 - a) = editOffset k := by
      unfold editOffset
      omega
    have hbits := hag _ hoff
    rw [hindex, bubble.header_bit, ← bubble.replace_longWord, replaceAt_at] at hbits
    exact hne hbits
  · right
    omega

/-- The longer source word and its replacement version at the same position in
a k-unique source and its substitution share only their endpoint vertices.
No flank-letter hypothesis is used. -/
theorem substitution_endpoints {n k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord α k)
    (hne : bubble.bit ≠ bubble.newBit)
    (x : Letters α) (hx : KUnique x n k) (pos : ℕ) (hpos : pos < n) (s : ℕ)
    (hlength : s + bubble.longWord.length ≤ n)
    (hflength : s + bubble.replaceWord.length ≤ n)
    (hlong : Agree (listLetters bubble.longWord) 0 x s bubble.longWord.length)
    (hflip : Agree (listLetters bubble.replaceWord) 0 (replaceAt x pos bubble.newBit) s bubble.replaceWord.length)
    (a b : ℕ) (ha : a ≤ bubble.longWord.length - windowLength k + 1)
    (hb : b ≤ bubble.replaceWord.length - windowLength k + 1)
    (hag : Agree (listLetters bubble.longWord) a
      (listLetters bubble.replaceWord) b (windowLength k - 1)) :
    (a = 0 ∧ b = 0) ∨
      (a = bubble.longWord.length - windowLength k + 1 ∧
        b = bubble.replaceWord.length - windowLength k + 1) := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  have hlonglen : bubble.longWord.length = 2 * windowLength k - bubble.rho := by
    simpa only [longLength, BubbleWord.header] using bubble.longWord_length
  have hfliplen : bubble.replaceWord.length = 2 * windowLength k - bubble.rho := by
    simpa only [longLength, BubbleWord.header] using bubble.replaceWord_length
  have hL : windowLength k = 3 * (k + 1) := rfl
  have halocal : a + (windowLength k - 1) ≤ bubble.longWord.length := by omega
  have hblocal : b + (windowLength k - 1) ≤ bubble.replaceWord.length := by omega
  have hglobal := transfer_equal_windows _ _ _ _ s a b _ _ _ hlong hflip halocal hblocal hag
  exact substitution_endpoints_of_displacement bubble hne a b ha hag
    (substitution_window_displacement hk x bubble.newBit hx pos hpos s a b (by omega) (by omega) hglobal)

#print axioms endpoints_of_displacement
#print axioms deletion_window_displacement
#print axioms insertion_window_displacement
#print axioms substitution_window_displacement
#print axioms deletion_endpoints
#print axioms insertion_endpoints
#print axioms substitution_endpoints

end DeletionCode.Qary.BubbleEndpoints
