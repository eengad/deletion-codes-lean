import DeletionCode.Qary.HeaderRecovery
import Init.Data.List.Nat.Erase
import Mathlib.Tactic.Conv

/-!
The manuscript's concrete local-word grammar, connected to header semantics.
The words are A d^rho B and A d^(rho-1) B, where both flanks have length
L-rho. Deleting at L-1 is proved to remove a letter of the displayed run. A
substitution bubble has rho = 1, so its words are A d B and A e B with e distinct from d and
flanks of length L-1, and replacing at L-1 replaces the run letter.
Boundary-letter and simple-path restrictions are additional catalogue filters;
they are not needed for these word identities.
-/

namespace DeletionCode.Qary.CatalogueWords

open DeletionCode.Qary.Windows DeletionCode.Qary.HeaderRecovery

variable {α : Type*}

def listLetters [Inhabited α] (word : List α) : Letters α := fun i => word.getD i default

/-- Deleting a list entry agrees everywhere with deletion of its padded letters. -/
theorem listLetters_eraseIdx [Inhabited α] (word : List α) (ell : ℕ) :
    listLetters (word.eraseIdx ell) = deleteAt (listLetters word) ell := by
  funext i
  simp only [listLetters, deleteAt, List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
  by_cases hi : i < ell <;> simp only [hi, ite_true, ite_false]

/-- Word grammar only; the graph conditions defining a catalogue bubble are separate. -/
structure BubbleWord (α : Type*) (k : ℕ) where
  left : List α
  right : List α
  rho : ℕ
  bit : α
  newBit : α
  orientation : Orientation
  rho_lower : 1 ≤ rho
  rho_upper : rho ≤ k + 1
  left_length : left.length = windowLength k - rho
  right_length : right.length = windowLength k - rho
  sub_rho : orientation = .substitution → rho = 1
  sub_ne : orientation = .substitution → bit ≠ newBit

namespace BubbleWord

variable {k : ℕ}

def header (bubble : BubbleWord α k) : Header α :=
  ⟨bubble.orientation, bubble.rho, bubble.bit, bubble.newBit⟩

def longWord (bubble : BubbleWord α k) : List α :=
  bubble.left ++ (List.replicate bubble.rho bubble.bit ++ bubble.right)

def shortWord (bubble : BubbleWord α k) : List α :=
  bubble.left ++ (List.replicate (bubble.rho - 1) bubble.bit ++ bubble.right)

/-- The longer word with its last run letter replaced by the recorded replacement symbol. -/
def replaceWord (bubble : BubbleWord α k) : List α :=
  bubble.left ++ (List.replicate (bubble.rho - 1) bubble.bit ++ (bubble.newBit :: bubble.right))

def negativeWord (bubble : BubbleWord α k) : List α :=
  match bubble.orientation with
  | .deletion => bubble.longWord
  | .insertion => bubble.shortWord
  | .substitution => bubble.longWord

def positiveWord (bubble : BubbleWord α k) : List α :=
  match bubble.orientation with
  | .deletion => bubble.shortWord
  | .insertion => bubble.longWord
  | .substitution => bubble.replaceWord

theorem longWord_length (bubble : BubbleWord α k) :
    bubble.longWord.length = longLength k bubble.header := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [longWord, List.length_append, List.length_replicate,
    bubble.left_length, bubble.right_length, longLength, header, windowLength]
  omega

theorem shortWord_length (bubble : BubbleWord α k) :
    bubble.shortWord.length = shortLength k bubble.header := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [shortWord, List.length_append, List.length_replicate,
    bubble.left_length, bubble.right_length, shortLength, longLength, header, windowLength]
  omega

theorem replaceWord_length (bubble : BubbleWord α k) :
    bubble.replaceWord.length = longLength k bubble.header := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [replaceWord, List.length_append, List.length_replicate, List.length_cons,
    bubble.left_length, bubble.right_length, longLength, header, windowLength]
  omega

theorem negativeWord_length (bubble : BubbleWord α k) :
    bubble.negativeWord.length = negativeLength k bubble.header := by
  cases ho : bubble.orientation <;>
    simp only [negativeWord, negativeLength, header, ho]
  · exact bubble.longWord_length
  · exact bubble.shortWord_length
  · exact bubble.longWord_length

theorem positiveWord_length (bubble : BubbleWord α k) :
    bubble.positiveWord.length = positiveLength k bubble.header := by
  cases ho : bubble.orientation <;>
    simp only [positiveWord, positiveLength, header, ho]
  · exact bubble.shortWord_length
  · exact bubble.longWord_length
  · exact bubble.replaceWord_length

theorem edit_in_run (bubble : BubbleWord α k) :
    bubble.left.length ≤ editOffset k ∧
      editOffset k - bubble.left.length < bubble.rho := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  rw [bubble.left_length]
  dsimp [editOffset, windowLength]
  omega

/-- The header letter is derived from the run word at the prescribed edit offset. -/
theorem header_bit [Inhabited α] (bubble : BubbleWord α k) :
    listLetters bubble.longWord (editOffset k) = bubble.header.bit := by
  have hleft := bubble.edit_in_run.1
  have hrun := bubble.edit_in_run.2
  simp only [listLetters, longWord, header, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right hleft]
  rw [List.getElem?_append_left (by simpa only [List.length_replicate] using hrun)]
  rw [List.getElem?_replicate_of_lt hrun]
  rfl

/-- Removing the indicated run letter gives exactly the shorter grammar word. -/
theorem eraseIdx_longWord (bubble : BubbleWord α k) :
    bubble.longWord.eraseIdx (editOffset k) = bubble.shortWord := by
  have hleft := bubble.edit_in_run.1
  have hrun := bubble.edit_in_run.2
  unfold longWord shortWord
  rw [List.eraseIdx_append_of_length_le hleft]
  rw [List.eraseIdx_append_of_lt_length
    (by simpa only [List.length_replicate] using hrun)]
  rw [List.eraseIdx_replicate, ite_eq_left hrun]

/-- The finite-word edit identity also holds for the complete padded functions. -/
theorem delete_longWord [Inhabited α] (bubble : BubbleWord α k) :
    deleteAt (listLetters bubble.longWord) (editOffset k) = listLetters bubble.shortWord := by
  rw [← listLetters_eraseIdx, bubble.eraseIdx_longWord]

/-- The actual letter at a list split. -/
theorem listLetters_split [Inhabited α] (pre suffix : List α) (bit : α) :
    listLetters (pre ++ bit :: suffix) pre.length = bit := by
  simp only [listLetters, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem listLetters_delete_split [Inhabited α] (pre suffix : List α) (bit : α) :
    deleteAt (listLetters (pre ++ bit :: suffix)) pre.length = listLetters (pre ++ suffix) := by
  rw [← listLetters_eraseIdx, List.eraseIdx_append_of_length_le (Nat.le_refl _)]
  simp

/-- Insertion at a list split, derived from the inverse edit identity. -/
theorem listLetters_insert_split [Inhabited α] (pre suffix : List α) (bit : α) :
    insertAt (listLetters (pre ++ suffix)) pre.length bit = listLetters (pre ++ bit :: suffix) := by
  calc
    insertAt (listLetters (pre ++ suffix)) pre.length bit =
        insertAt (deleteAt (listLetters (pre ++ bit :: suffix)) pre.length)
          pre.length (listLetters (pre ++ bit :: suffix) pre.length) := by
      rw [listLetters_delete_split, listLetters_split]
    _ = listLetters (pre ++ bit :: suffix) := insert_delete _ _

theorem prefix_length (bubble : BubbleWord α k) :
    (bubble.left ++ List.replicate (bubble.rho - 1) bubble.bit).length = editOffset k := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [List.length_append, List.length_replicate, bubble.left_length, editOffset, windowLength]
  omega

/-- Inserting the recorded replacement symbol at the edit offset of the shorter word gives the replacement word. -/
theorem insert_replaceWord [Inhabited α] (bubble : BubbleWord α k) :
    insertAt (listLetters bubble.shortWord) (editOffset k) bubble.newBit =
      listLetters bubble.replaceWord := by
  have hshort : bubble.shortWord =
      (bubble.left ++ List.replicate (bubble.rho - 1) bubble.bit) ++ bubble.right := by
    simp [shortWord, List.append_assoc]
  have hflip : bubble.replaceWord =
      (bubble.left ++ List.replicate (bubble.rho - 1) bubble.bit) ++ bubble.newBit :: bubble.right := by
    simp [replaceWord, List.append_assoc]
  rw [hshort, hflip, ← bubble.prefix_length]
  exact listLetters_insert_split _ _ _

/-- Replacing the run letter of the longer word gives the replacement grammar word. -/
theorem replace_longWord [Inhabited α] (bubble : BubbleWord α k) :
    replaceAt (listLetters bubble.longWord) (editOffset k) bubble.newBit = listLetters bubble.replaceWord := by
  rw [← bubble.insert_replaceWord, ← bubble.delete_longWord]
  have hlong : listLetters bubble.longWord =
      insertAt (deleteAt (listLetters bubble.longWord) (editOffset k)) (editOffset k)
        bubble.bit := by
    conv_lhs => rw [← insert_delete (listLetters bubble.longWord) (editOffset k)]
    rw [bubble.header_bit]
    rfl
  conv_lhs => rw [hlong]
  exact replace_insertAt _ _ _ _

theorem negativeWord_semantics [Inhabited α] (bubble : BubbleWord α k) :
    listLetters bubble.negativeWord =
      negativePath k bubble.header (listLetters bubble.longWord) := by
  cases ho : bubble.orientation with
  | deletion => simp only [negativeWord, negativePath, header, ho]
  | insertion =>
    simp only [negativeWord, negativePath, header, ho]
    exact bubble.delete_longWord.symm
  | substitution => simp only [negativeWord, negativePath, header, ho]

theorem positiveWord_semantics [Inhabited α] (bubble : BubbleWord α k) :
    listLetters bubble.positiveWord =
      positivePath k bubble.header (listLetters bubble.longWord) := by
  cases ho : bubble.orientation with
  | deletion =>
    simp only [positiveWord, positivePath, header, ho]
    exact bubble.delete_longWord.symm
  | insertion => simp only [positiveWord, positivePath, header, ho]
  | substitution =>
    simp only [positiveWord, positivePath, header, ho]
    exact bubble.replace_longWord.symm

/-- Rebuilding from the grammar's negative word recovers the grammar's positive word. -/
theorem rebuild_positiveWord [Inhabited α] (bubble : BubbleWord α k) :
    rebuildPositive k bubble.header (listLetters bubble.negativeWord) =
      listLetters bubble.positiveWord := by
  rw [bubble.negativeWord_semantics, bubble.positiveWord_semantics]
  exact rebuild_positive_correct k bubble.header (listLetters bubble.longWord) bubble.header_bit

end BubbleWord

#print axioms BubbleWord.replace_longWord
#print axioms BubbleWord.rebuild_positiveWord

end DeletionCode.Qary.CatalogueWords
