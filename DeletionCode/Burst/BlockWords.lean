import DeletionCode.Burst.Basic
import DeletionCode.Qary.HeaderRecovery

/-! Removing and inserting whole blocks in total letter functions. -/
namespace DeletionCode.Burst.BlockWords
open DeletionCode.Qary.Windows
variable {α : Type*} [Inhabited α]

def deleteBlock (p : Letters α) (a r : ℕ) : Letters α :=
  fun i => if i < a then p i else p (i + r)

def insertBlock (p : Letters α) (a : ℕ) (word : List α) : Letters α :=
  (Edit.mk a 0 word).word p

theorem deleteBlock_zero (p : Letters α) (a : ℕ) : deleteBlock p a 0 = p := by
  funext i
  simp [deleteBlock]

theorem deleteBlock_succ (p : Letters α) (a r : ℕ) :
    deleteBlock p a (r + 1) = deleteBlock (deleteAt p a) a r := by
  funext i
  by_cases h : i < a
  · simp [deleteBlock, deleteAt, h]
  · have hn : ¬i + r < a := by omega
    simp [deleteBlock, deleteAt, h, hn, Nat.add_assoc]

theorem insertBlock_nil (p : Letters α) (a : ℕ) : insertBlock p a [] = p := by
  funext i
  by_cases h : i < a <;> simp [insertBlock, Edit.word, h]

theorem insertBlock_cons (p : Letters α) (a : ℕ) (symbol : α) (word : List α) :
    insertBlock p a (symbol :: word) = insertAt (insertBlock p a word) a symbol := by
  funext i
  by_cases hleft : i < a
  · simp [insertBlock, Edit.word, insertAt, hleft]
  · by_cases heq : i = a
    · subst i
      simp [insertBlock, Edit.word, insertAt]
    · have hpred : ¬ i - 1 < a := by omega
      have hidx : i - a = (i - 1 - a) + 1 := by omega
      have hcut : (i < a + (symbol :: word).length) ↔ (i - 1 < a + word.length) := by simp; omega
      simp only [insertBlock, Edit.word, insertAt, hleft, heq, hpred, ite_eq_right,
        List.length_cons, Nat.add_zero]
      by_cases hin : i - 1 < a + word.length
      · have hin' : i < a + (word.length + 1) := by omega
        simp [hin, hin', hidx, List.getD]
      · have hout : ¬ i < a + (word.length + 1) := by omega
        have hs : i - (word.length + 1) = i - 1 - word.length := by omega
        simp [hin, hout, hs]

theorem delete_insertBlock (p : Letters α) (a : ℕ) (word : List α) :
    deleteBlock (insertBlock p a word) a word.length = p := by
  induction word with
  | nil => simp [insertBlock_nil, deleteBlock_zero]
  | cons symbol word ih =>
    rw [List.length_cons, deleteBlock_succ, insertBlock_cons, delete_insert]
    exact ih

theorem insert_deleteBlock (p : Letters α) (a : ℕ) (word : List α)
    (hword : ∀ i, i < word.length → word.getD i default = p (a + i)) :
    insertBlock (deleteBlock p a word.length) a word = p := by
  funext i
  by_cases hl : i < a
  · simp [insertBlock, Edit.word, deleteBlock, hl]
  · by_cases hm : i < a + word.length
    · have hi : i - a < word.length := by omega
      have he : a + (i - a) = i := by omega
      simpa [insertBlock, Edit.word, hl, hm, he] using hword (i - a) hi
    · have hi : ¬ i - word.length < a := by omega
      have he : i - word.length + word.length = i := by omega
      simp [insertBlock, Edit.word, deleteBlock, hl, hm, hi, he]

theorem edit_word_eq (p : Letters α) (a r : ℕ) (word : List α) :
    (Edit.mk a r word).word p = insertBlock (deleteBlock p a r) a word := by
  funext i
  by_cases hl : i < a
  · simp [insertBlock, Edit.word, deleteBlock, hl]
  · by_cases hm : i < a + word.length
    · simp [insertBlock, Edit.word, hl, hm]
    · have hi : ¬i - word.length < a := by omega
      have he : i + r - word.length = i - word.length + r := by omega
      simp [insertBlock, Edit.word, deleteBlock, hl, hm, hi, he]

#print axioms insertBlock_cons
#print axioms edit_word_eq
end DeletionCode.Burst.BlockWords
