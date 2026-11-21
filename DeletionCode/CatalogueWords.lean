import DeletionCode.GeneratingModel
import Init.Data.List.Nat.Erase

/-!
The manuscript's concrete local-word grammar, connected to header semantics.
The words are A d^rho B and A d^(rho-1) B, where both flanks have length
L-rho. Deleting at L-1 is proved to remove a bit of the displayed run. A
substitution bubble has rho = 1, so its words are A d B and A (1-d) B with
flanks of length L-1, and flipping at L-1 replaces the run letter.
Boundary-bit and simple-path restrictions are additional catalogue filters;
they are not needed for these word identities.
-/

namespace DeletionCode.CatalogueWords

open Windows HeaderRecovery GeneratingModel

def listLetters (word : List Bool) : Letters := fun i => word.getD i false

/-- Deleting a list entry agrees everywhere with deletion of its padded letters. -/
theorem listLetters_eraseIdx (word : List Bool) (ell : ℕ) :
    listLetters (word.eraseIdx ell) = deleteAt (listLetters word) ell := by
  funext i
  simp only [listLetters, deleteAt, List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
  by_cases hi : i < ell <;> simp only [hi, ite_true, ite_false]

/-- Word grammar only; the graph conditions defining a catalogue bubble are separate. -/
structure BubbleWord (k : ℕ) where
  left : List Bool
  right : List Bool
  rho : ℕ
  bit : Bool
  orientation : Orientation
  rho_lower : 1 ≤ rho
  rho_upper : rho ≤ k + 1
  left_length : left.length = windowLength k - rho
  right_length : right.length = windowLength k - rho
  sub_rho : orientation = .substitution → rho = 1

namespace BubbleWord

variable {k : ℕ}

def header (bubble : BubbleWord k) : Header :=
  ⟨bubble.orientation, bubble.rho, bubble.bit⟩

def longWord (bubble : BubbleWord k) : List Bool :=
  bubble.left ++ (List.replicate bubble.rho bubble.bit ++ bubble.right)

def shortWord (bubble : BubbleWord k) : List Bool :=
  bubble.left ++ (List.replicate (bubble.rho - 1) bubble.bit ++ bubble.right)

/-- The longer word with its last run letter replaced by the other letter. -/
def flipWord (bubble : BubbleWord k) : List Bool :=
  bubble.left ++ (List.replicate (bubble.rho - 1) bubble.bit ++ ((!bubble.bit) :: bubble.right))

def negativeWord (bubble : BubbleWord k) : List Bool :=
  match bubble.orientation with
  | .deletion => bubble.longWord
  | .insertion => bubble.shortWord
  | .substitution => bubble.longWord

def positiveWord (bubble : BubbleWord k) : List Bool :=
  match bubble.orientation with
  | .deletion => bubble.shortWord
  | .insertion => bubble.longWord
  | .substitution => bubble.flipWord

theorem longWord_length (bubble : BubbleWord k) :
    bubble.longWord.length = longLength k bubble.header := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [longWord, List.length_append, List.length_replicate,
    bubble.left_length, bubble.right_length, longLength, header, windowLength]
  omega

theorem shortWord_length (bubble : BubbleWord k) :
    bubble.shortWord.length = shortLength k bubble.header := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [shortWord, List.length_append, List.length_replicate,
    bubble.left_length, bubble.right_length, shortLength, longLength, header, windowLength]
  omega

theorem flipWord_length (bubble : BubbleWord k) :
    bubble.flipWord.length = longLength k bubble.header := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [flipWord, List.length_append, List.length_replicate, List.length_cons,
    bubble.left_length, bubble.right_length, longLength, header, windowLength]
  omega

theorem negativeWord_length (bubble : BubbleWord k) :
    bubble.negativeWord.length = negativeLength k bubble.header := by
  cases ho : bubble.orientation <;>
    simp only [negativeWord, negativeLength, header, ho]
  · exact bubble.longWord_length
  · exact bubble.shortWord_length
  · exact bubble.longWord_length

theorem positiveWord_length (bubble : BubbleWord k) :
    bubble.positiveWord.length = positiveLength k bubble.header := by
  cases ho : bubble.orientation <;>
    simp only [positiveWord, positiveLength, header, ho]
  · exact bubble.shortWord_length
  · exact bubble.longWord_length
  · exact bubble.flipWord_length

theorem edit_in_run (bubble : BubbleWord k) :
    bubble.left.length ≤ editOffset k ∧
      editOffset k - bubble.left.length < bubble.rho := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  rw [bubble.left_length]
  dsimp [editOffset, windowLength]
  omega

/-- The header bit is derived from the run word at the prescribed edit offset. -/
theorem header_bit (bubble : BubbleWord k) :
    listLetters bubble.longWord (editOffset k) = bubble.header.bit := by
  have hleft := bubble.edit_in_run.1
  have hrun := bubble.edit_in_run.2
  simp only [listLetters, longWord, header, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right hleft]
  rw [List.getElem?_append_left (by simpa only [List.length_replicate] using hrun)]
  rw [List.getElem?_replicate_of_lt hrun]
  rfl

/-- Removing the indicated run bit gives exactly the shorter grammar word. -/
theorem eraseIdx_longWord (bubble : BubbleWord k) :
    bubble.longWord.eraseIdx (editOffset k) = bubble.shortWord := by
  have hleft := bubble.edit_in_run.1
  have hrun := bubble.edit_in_run.2
  unfold longWord shortWord
  rw [List.eraseIdx_append_of_length_le hleft]
  rw [List.eraseIdx_append_of_lt_length
    (by simpa only [List.length_replicate] using hrun)]
  rw [List.eraseIdx_replicate, ite_eq_left hrun]

/-- The finite-word edit identity also holds for the complete padded functions. -/
theorem delete_longWord (bubble : BubbleWord k) :
    deleteAt (listLetters bubble.longWord) (editOffset k) = listLetters bubble.shortWord := by
  rw [← listLetters_eraseIdx, bubble.eraseIdx_longWord]

/-- The actual bit at a list split. -/
theorem listLetters_split (pre suffix : List Bool) (bit : Bool) :
    listLetters (pre ++ bit :: suffix) pre.length = bit := by
  simp only [listLetters, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem listLetters_delete_split (pre suffix : List Bool) (bit : Bool) :
    deleteAt (listLetters (pre ++ bit :: suffix)) pre.length = listLetters (pre ++ suffix) := by
  rw [← listLetters_eraseIdx, List.eraseIdx_append_of_length_le (Nat.le_refl _)]
  simp

/-- Insertion at a list split, derived from the inverse edit identity. -/
theorem listLetters_insert_split (pre suffix : List Bool) (bit : Bool) :
    insertAt (listLetters (pre ++ suffix)) pre.length bit = listLetters (pre ++ bit :: suffix) := by
  calc
    insertAt (listLetters (pre ++ suffix)) pre.length bit =
        insertAt (deleteAt (listLetters (pre ++ bit :: suffix)) pre.length)
          pre.length (listLetters (pre ++ bit :: suffix) pre.length) := by
      rw [listLetters_delete_split, listLetters_split]
    _ = listLetters (pre ++ bit :: suffix) := insert_delete _ _

theorem prefix_length (bubble : BubbleWord k) :
    (bubble.left ++ List.replicate (bubble.rho - 1) bubble.bit).length = editOffset k := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [List.length_append, List.length_replicate, bubble.left_length, editOffset, windowLength]
  omega

/-- Inserting the other letter at the edit offset of the shorter word gives the flipped word. -/
theorem insert_flipWord (bubble : BubbleWord k) :
    insertAt (listLetters bubble.shortWord) (editOffset k) (!bubble.bit) =
      listLetters bubble.flipWord := by
  have hshort : bubble.shortWord =
      (bubble.left ++ List.replicate (bubble.rho - 1) bubble.bit) ++ bubble.right := by
    simp [shortWord, List.append_assoc]
  have hflip : bubble.flipWord =
      (bubble.left ++ List.replicate (bubble.rho - 1) bubble.bit) ++ (!bubble.bit) :: bubble.right := by
    simp [flipWord, List.append_assoc]
  rw [hshort, hflip, ← bubble.prefix_length]
  exact listLetters_insert_split _ _ _

/-- Flipping the run letter of the longer word gives the flipped grammar word. -/
theorem flip_longWord (bubble : BubbleWord k) :
    flipAt (listLetters bubble.longWord) (editOffset k) = listLetters bubble.flipWord := by
  rw [← bubble.insert_flipWord, ← bubble.delete_longWord]
  have hlong : listLetters bubble.longWord =
      insertAt (deleteAt (listLetters bubble.longWord) (editOffset k)) (editOffset k)
        bubble.bit := by
    conv_lhs => rw [← insert_delete (listLetters bubble.longWord) (editOffset k)]
    rw [bubble.header_bit]
    rfl
  conv_lhs => rw [hlong]
  exact flip_insertAt _ _ _

theorem negativeWord_semantics (bubble : BubbleWord k) :
    listLetters bubble.negativeWord =
      negativePath k bubble.header (listLetters bubble.longWord) := by
  cases ho : bubble.orientation with
  | deletion => simp only [negativeWord, negativePath, header, ho]
  | insertion =>
    simp only [negativeWord, negativePath, header, ho]
    exact bubble.delete_longWord.symm
  | substitution => simp only [negativeWord, negativePath, header, ho]

theorem positiveWord_semantics (bubble : BubbleWord k) :
    listLetters bubble.positiveWord =
      positivePath k bubble.header (listLetters bubble.longWord) := by
  cases ho : bubble.orientation with
  | deletion =>
    simp only [positiveWord, positivePath, header, ho]
    exact bubble.delete_longWord.symm
  | insertion => simp only [positiveWord, positivePath, header, ho]
  | substitution =>
    simp only [positiveWord, positivePath, header, ho]
    exact bubble.flip_longWord.symm

/-- Rebuilding from the grammar's negative word recovers the grammar's positive word. -/
theorem rebuild_positiveWord (bubble : BubbleWord k) :
    rebuildPositive k bubble.header (listLetters bubble.negativeWord) =
      listLetters bubble.positiveWord := by
  rw [bubble.negativeWord_semantics, bubble.positiveWord_semantics]
  exact rebuild_positive_correct k bubble.header (listLetters bubble.longWord) bubble.header_bit

end BubbleWord

/-- Indexed grammar words supply the edited-family data, including the derived header bit. -/
def editedFamily {B : Type*} {k : ℕ} (bubbles : B → BubbleWord k) (rank : B → ℕ) :
    EditedFamily B k where
  header b := (bubbles b).header
  long b := listLetters (bubbles b).longWord
  rank := rank
  rho_lower b := (bubbles b).rho_lower
  rho_upper b := (bubbles b).rho_upper
  header_bit b := (bubbles b).header_bit

theorem editedFamily_negative {B : Type*} {k : ℕ}
    (bubbles : B → BubbleWord k) (rank : B → ℕ) (b : B) :
    (editedFamily bubbles rank).family.path b false = listLetters (bubbles b).negativeWord :=
  (bubbles b).negativeWord_semantics.symm

theorem editedFamily_positive {B : Type*} {k : ℕ}
    (bubbles : B → BubbleWord k) (rank : B → ℕ) (b : B) :
    (editedFamily bubbles rank).family.path b true = listLetters (bubbles b).positiveWord :=
  (bubbles b).positiveWord_semantics.symm

#print axioms listLetters_eraseIdx
#print axioms BubbleWord.longWord_length
#print axioms BubbleWord.shortWord_length
#print axioms BubbleWord.header_bit
#print axioms BubbleWord.eraseIdx_longWord
#print axioms BubbleWord.flipWord_length
#print axioms BubbleWord.flip_longWord
#print axioms BubbleWord.negativeWord_semantics
#print axioms BubbleWord.positiveWord_semantics
#print axioms BubbleWord.rebuild_positiveWord
#print axioms editedFamily

end DeletionCode.CatalogueWords
