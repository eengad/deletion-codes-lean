import DeletionCode.EditAlignment
import DeletionCode.SingleEditOrigins
import DeletionCode.CatalogueWords

/-!
Realization of genuine edit scripts of total cost at most one by the concrete
single-edit model. The edit position comes from the actual list split in the
script. The realized words agree as complete padded letter functions.
-/

namespace DeletionCode.EditAlignment

/-- A script containing no deletion or insertion leaves its source unchanged. -/
theorem Script.zero_eq {x y : Word} (h : Script x y 0 0) : x = y := by
  cases h
  rfl

/-- A script of total cost at most one is unchanged, one deletion, or one insertion. -/
theorem Script.classify_of_le_one {x y : Word} {d i : ℕ}
    (h : Script x y d i) (hcost : d + i ≤ 1) :
    x = y ∨
      (∃ (pre suffix : Word) (bit : Bool),
        x = pre ++ bit :: suffix ∧ y = pre ++ suffix) ∨
      (∃ (pre suffix : Word) (bit : Bool),
        x = pre ++ suffix ∧ y = pre ++ bit :: suffix) := by
  cases h with
  | refl => exact Or.inl rfl
  | @delete pre suffix bit d i h =>
    have hd : d = 0 := by omega
    have hi : i = 0 := by omega
    subst d
    subst i
    exact Or.inr (Or.inl ⟨pre, suffix, bit, h.zero_eq, rfl⟩)
  | @insert pre suffix bit d i h =>
    have hd : d = 0 := by omega
    have hi : i = 0 := by omega
    subst d
    subst i
    exact Or.inr (Or.inr ⟨pre, suffix, bit, h.zero_eq, rfl⟩)

end DeletionCode.EditAlignment

namespace DeletionCode.SingleEditScripts

open Windows CatalogueWords EditAlignment SingleEditOrigins

theorem eraseIdx_at_split (pre suffix : List Bool) (bit : Bool) :
    (pre ++ bit :: suffix).eraseIdx pre.length = pre ++ suffix := by
  rw [List.eraseIdx_append_of_length_le (Nat.le_refl _)]
  simp

/-- The actual bit at a list split is the inserted/deleted bit. -/
theorem listLetters_at_split (pre suffix : List Bool) (bit : Bool) :
    listLetters (pre ++ bit :: suffix) pre.length = bit := by
  simp only [listLetters, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem delete_split (pre suffix : List Bool) (bit : Bool) :
    deleteAt (listLetters (pre ++ bit :: suffix)) pre.length =
      listLetters (pre ++ suffix) := by
  rw [← listLetters_eraseIdx, eraseIdx_at_split]

/-- Insertion semantics follow from the already verified inverse edit identity. -/
theorem insert_split (pre suffix : List Bool) (bit : Bool) :
    insertAt (listLetters (pre ++ suffix)) pre.length bit =
      listLetters (pre ++ bit :: suffix) := by
  have hdel := delete_split pre suffix bit
  have hbit := listLetters_at_split pre suffix bit
  calc
    insertAt (listLetters (pre ++ suffix)) pre.length bit =
        insertAt (deleteAt (listLetters (pre ++ bit :: suffix)) pre.length)
          pre.length (listLetters (pre ++ bit :: suffix) pre.length) := by
      rw [hdel, hbit]
    _ = listLetters (pre ++ bit :: suffix) := insert_delete _ _

/-- Every genuine script of cost at most one has a valid concrete edit realization.
The output length and complete padded word are both derived from the script. -/
theorem within_one_realized {x y : List Bool} (h : WithinEdits 1 x y) :
    ∃ e : Edit, e.Valid x.length ∧ e.outputLength x.length = y.length ∧
      e.word (listLetters x) = listLetters y := by
  obtain ⟨d, i, hscript, hcost⟩ := h
  rcases hscript.classify_of_le_one hcost with hsame | hdelete | hinsert
  · subst y
    exact ⟨.unchanged, trivial, rfl, rfl⟩
  · obtain ⟨pre, suffix, bit, rfl, rfl⟩ := hdelete
    refine ⟨.delete pre.length, ?_, ?_, ?_⟩
    · simp only [Edit.Valid, List.length_append, List.length_cons]
      omega
    · simp only [Edit.outputLength, List.length_append, List.length_cons]
      omega
    · exact delete_split pre suffix bit
  · obtain ⟨pre, suffix, bit, rfl, rfl⟩ := hinsert
    refine ⟨.insert pre.length bit, ?_, ?_, ?_⟩
    · simp only [Edit.Valid, List.length_append]
      omega
    · simp only [Edit.outputLength, List.length_append, List.length_cons]
      omega
    · exact insert_split pre suffix bit

#print axioms EditAlignment.Script.zero_eq
#print axioms EditAlignment.Script.classify_of_le_one
#print axioms delete_split
#print axioms insert_split
#print axioms within_one_realized

end DeletionCode.SingleEditScripts
