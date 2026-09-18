import DeletionCode.SpectrumLocalization

/-!
The local replacement identity for the actual bubble grammar. The repeated
run gives equal first and last L-1 letters without any flank-bit or path
assumption. Consequently arbitrary unchanged exterior words cancel from the
integer spectrum difference, in either edit orientation.
-/

namespace DeletionCode.BubbleLocalSpectrum

open Windows HeaderRecovery CatalogueWords SignedSupport SpectrumLocalization

/-- Removing the last run bit leaves the first L-1 letters unchanged. -/
theorem shared_prefix {k : ℕ} (bubble : BubbleWord k) :
    Agree (listLetters bubble.longWord) 0 (listLetters bubble.shortWord) 0
      (windowLength k - 1) := by
  rw [← bubble.delete_longWord]
  intro i hi
  simp only [Nat.zero_add, deleteAt, editOffset, ite_eq_left hi]

/-- The two local words end in the same actual word d^(rho-1) B. -/
theorem shared_suffix {k : ℕ} (bubble : BubbleWord k) :
    Agree (listLetters bubble.longWord) (bubble.longWord.length + 1 - windowLength k)
      (listLetters bubble.shortWord) (bubble.shortWord.length + 1 - windowLength k)
      (windowLength k - 1) := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  have hleft := bubble.left_length
  have hlstart : bubble.longWord.length + 1 - windowLength k = bubble.left.length + 1 := by
    rw [bubble.longWord_length]
    simp only [longLength, BubbleWord.header]
    unfold windowLength at *
    omega
  have hsstart : bubble.shortWord.length + 1 - windowLength k = bubble.left.length := by
    rw [bubble.shortWord_length]
    simp only [shortLength, longLength, BubbleWord.header]
    unfold windowLength at *
    omega
  have hrep : List.replicate bubble.rho bubble.bit =
      bubble.bit :: List.replicate (bubble.rho - 1) bubble.bit := by
    conv_lhs => rw [show bubble.rho = (bubble.rho - 1) + 1 by omega, List.replicate_succ]
  rw [hlstart, hsstart]
  intro i _hi
  change listLetters (bubble.left ++ (List.replicate bubble.rho bubble.bit ++ bubble.right))
      (bubble.left.length + 1 + i) =
    listLetters (bubble.left ++ (List.replicate (bubble.rho - 1) bubble.bit ++ bubble.right))
      (bubble.left.length + i)
  have hindex : bubble.left.length + 1 + i = bubble.left.length + (i + 1) := by omega
  rw [hindex, listLetters_append_right, listLetters_append_right, hrep]
  simp only [List.cons_append, listLetters, List.getD_cons_succ]

theorem length_bounds {k : ℕ} (bubble : BubbleWord k) :
    windowLength k ≤ bubble.longWord.length + 1 ∧
      windowLength k ≤ bubble.shortWord.length + 1 := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [bubble.longWord_length, bubble.shortWord_length, shortLength, longLength,
    BubbleWord.header, windowLength]
  omega

/-- The flipped word agrees with the longer word before the flipped letter,
which sits at position L-1 in every bubble. -/
theorem shared_prefix_flip {k : ℕ} (bubble : BubbleWord k) :
    Agree (listLetters bubble.longWord) 0 (listLetters bubble.flipWord) 0
      (windowLength k - 1) := by
  rw [← bubble.flip_longWord]
  intro i hi
  simp only [Nat.zero_add]
  have hne : i ≠ editOffset k := by
    unfold editOffset; omega
  exact (flipAt_of_ne _ _ _ hne).symm

/-- With rho = 1 the flipped word ends in the same word B as the longer word. -/
theorem shared_suffix_flip {k : ℕ} (bubble : BubbleWord k) (hrho : bubble.rho = 1) :
    Agree (listLetters bubble.longWord) (bubble.longWord.length + 1 - windowLength k)
      (listLetters bubble.flipWord) (bubble.flipWord.length + 1 - windowLength k)
      (windowLength k - 1) := by
  have hleft := bubble.left_length
  have hlstart : bubble.longWord.length + 1 - windowLength k = bubble.left.length + 1 := by
    rw [bubble.longWord_length]
    simp only [longLength, BubbleWord.header]
    unfold windowLength at *
    omega
  have hfstart : bubble.flipWord.length + 1 - windowLength k = bubble.left.length + 1 := by
    rw [bubble.flipWord_length]
    simp only [longLength, BubbleWord.header]
    unfold windowLength at *
    omega
  rw [hlstart, hfstart]
  intro i _hi
  change listLetters (bubble.left ++ (List.replicate bubble.rho bubble.bit ++ bubble.right))
      (bubble.left.length + 1 + i) =
    listLetters (bubble.left ++
      (List.replicate (bubble.rho - 1) bubble.bit ++ ((!bubble.bit) :: bubble.right)))
      (bubble.left.length + 1 + i)
  have hindex : bubble.left.length + 1 + i = bubble.left.length + (i + 1) := by omega
  rw [hindex, listLetters_append_right, listLetters_append_right, hrho]
  simp only [Nat.sub_self, List.replicate_zero, List.nil_append, List.replicate_one,
    List.singleton_append, listLetters, List.getD_cons_succ]

theorem flip_length_bounds {k : ℕ} (bubble : BubbleWord k) :
    windowLength k ≤ bubble.longWord.length + 1 ∧
      windowLength k ≤ bubble.flipWord.length + 1 := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [bubble.longWord_length, bubble.flipWord_length, longLength,
    BubbleWord.header, windowLength]
  omega

/-- Replacing the longer local word by the shorter changes the full spectrum
by precisely the local spectrum difference, with arbitrary unchanged context. -/
theorem context_replacement {k : ℕ} (bubble : BubbleWord k) (x y : List Bool)
    (g : Gram (windowLength k)) :
    wordSpectrum (listLetters (x ++ (bubble.shortWord ++ y)))
        (x ++ (bubble.shortWord ++ y)).length (windowLength k) g -
      wordSpectrum (listLetters (x ++ (bubble.longWord ++ y)))
        (x ++ (bubble.longWord ++ y)).length (windowLength k) g =
      wordSpectrum (listLetters bubble.shortWord) bubble.shortWord.length (windowLength k) g -
        wordSpectrum (listLetters bubble.longWord) bubble.longWord.length (windowLength k) g := by
  have hL : 1 ≤ windowLength k := by unfold windowLength; omega
  simpa only [List.length_append, Nat.add_assoc] using
    SpectrumLocalization.context_replacement x bubble.longWord bubble.shortWord y
      (windowLength k) hL (length_bounds bubble).1 (length_bounds bubble).2
      (shared_prefix bubble) (shared_suffix bubble) g

/-- The same local replacement formula for a substitution bubble, whose
positive word is the flipped word. -/
theorem context_replacement_flip {k : ℕ} (bubble : BubbleWord k) (hrho : bubble.rho = 1)
    (x y : List Bool) (g : Gram (windowLength k)) :
    wordSpectrum (listLetters (x ++ (bubble.flipWord ++ y)))
        (x ++ (bubble.flipWord ++ y)).length (windowLength k) g -
      wordSpectrum (listLetters (x ++ (bubble.longWord ++ y)))
        (x ++ (bubble.longWord ++ y)).length (windowLength k) g =
      wordSpectrum (listLetters bubble.flipWord) bubble.flipWord.length (windowLength k) g -
        wordSpectrum (listLetters bubble.longWord) bubble.longWord.length (windowLength k) g := by
  have hL : 1 ≤ windowLength k := by unfold windowLength; omega
  simpa only [List.length_append, Nat.add_assoc] using
    SpectrumLocalization.context_replacement x bubble.longWord bubble.flipWord y
      (windowLength k) hL (flip_length_bounds bubble).1 (flip_length_bounds bubble).2
      (shared_prefix_flip bubble) (shared_suffix_flip bubble hrho) g

/-- The local replacement formula uses the actual negative and positive
grammar words in all three edit orientations. -/
theorem oriented_context_replacement {k : ℕ} (bubble : BubbleWord k) (x y : List Bool)
    (g : Gram (windowLength k)) :
    wordSpectrum (listLetters (x ++ (bubble.positiveWord ++ y)))
        (x ++ (bubble.positiveWord ++ y)).length (windowLength k) g -
      wordSpectrum (listLetters (x ++ (bubble.negativeWord ++ y)))
        (x ++ (bubble.negativeWord ++ y)).length (windowLength k) g =
      wordSpectrum (listLetters bubble.positiveWord) bubble.positiveWord.length (windowLength k) g -
        wordSpectrum (listLetters bubble.negativeWord) bubble.negativeWord.length (windowLength k) g := by
  have h := context_replacement bubble x y g
  cases ho : bubble.orientation with
  | deletion =>
    simpa only [BubbleWord.positiveWord, BubbleWord.negativeWord, ho] using h
  | insertion =>
    simp only [BubbleWord.positiveWord, BubbleWord.negativeWord, ho]
    omega
  | substitution =>
    simpa only [BubbleWord.positiveWord, BubbleWord.negativeWord, ho] using
      context_replacement_flip bubble (bubble.sub_rho ho) x y g

/-- Function equality of the actual signed integer spectrum vectors. -/
theorem oriented_context_replacement_vector {k : ℕ} (bubble : BubbleWord k) (x y : List Bool) :
    wordSpectrum (listLetters (x ++ (bubble.positiveWord ++ y)))
        (x ++ (bubble.positiveWord ++ y)).length (windowLength k) -
      wordSpectrum (listLetters (x ++ (bubble.negativeWord ++ y)))
        (x ++ (bubble.negativeWord ++ y)).length (windowLength k) =
      wordSpectrum (listLetters bubble.positiveWord) bubble.positiveWord.length (windowLength k) -
        wordSpectrum (listLetters bubble.negativeWord) bubble.negativeWord.length (windowLength k) := by
  funext g
  exact oriented_context_replacement bubble x y g

#print axioms shared_prefix
#print axioms shared_suffix
#print axioms shared_prefix_flip
#print axioms shared_suffix_flip
#print axioms context_replacement
#print axioms context_replacement_flip
#print axioms oriented_context_replacement
#print axioms oriented_context_replacement_vector

end DeletionCode.BubbleLocalSpectrum
