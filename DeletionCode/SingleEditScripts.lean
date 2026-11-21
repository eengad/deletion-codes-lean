import DeletionCode.EditAlignment
import DeletionCode.SingleEditOrigins
import DeletionCode.CatalogueWords

/-!
Realization of genuine edit scripts of total cost at most one by the concrete
single-edit model. The edit position comes from the actual list split in the
script. The realized words agree as complete padded letter functions.
-/

namespace DeletionCode.EditAlignment

/-- A script containing no edit leaves its source unchanged. -/
theorem Script.zero_eq {x y : Word} (h : Script x y 0 0 0) : x = y := by
  cases h
  rfl

/-- A script of total cost at most one is unchanged, one deletion, one
insertion, or one substitution. -/
theorem Script.classify_of_le_one {x y : Word} {d i s : ℕ}
    (h : Script x y d i s) (hcost : d + i + s ≤ 1) :
    x = y ∨
      (∃ (pre suffix : Word) (bit : Bool),
        x = pre ++ bit :: suffix ∧ y = pre ++ suffix) ∨
      (∃ (pre suffix : Word) (bit : Bool),
        x = pre ++ suffix ∧ y = pre ++ bit :: suffix) ∨
      (∃ (pre suffix : Word) (bit : Bool),
        x = pre ++ bit :: suffix ∧ y = pre ++ (!bit) :: suffix) := by
  cases h with
  | refl => exact Or.inl rfl
  | @delete pre suffix bit d i s h =>
    have hd : d = 0 := by omega
    have hi : i = 0 := by omega
    have hs : s = 0 := by omega
    subst d
    subst i
    subst s
    exact Or.inr (Or.inl ⟨pre, suffix, bit, h.zero_eq, rfl⟩)
  | @insert pre suffix bit d i s h =>
    have hd : d = 0 := by omega
    have hi : i = 0 := by omega
    have hs : s = 0 := by omega
    subst d
    subst i
    subst s
    exact Or.inr (Or.inr (Or.inl ⟨pre, suffix, bit, h.zero_eq, rfl⟩))
  | @substitute pre suffix bit d i s h =>
    have hd : d = 0 := by omega
    have hi : i = 0 := by omega
    have hs : s = 0 := by omega
    subst d
    subst i
    subst s
    exact Or.inr (Or.inr (Or.inr ⟨pre, suffix, bit, h.zero_eq, rfl⟩))

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

/-- Flipping the letter at a list split is the substitution semantics. -/
theorem flip_split (pre suffix : List Bool) (bit : Bool) :
    flipAt (listLetters (pre ++ bit :: suffix)) pre.length =
      listLetters (pre ++ (!bit) :: suffix) := by
  funext i
  by_cases hi : i = pre.length
  · subst hi
    rw [flipAt_at, listLetters_at_split, listLetters_at_split]
  · rw [flipAt_of_ne _ _ _ hi]
    simp only [listLetters, List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_gt_of_ne hi with hlt | hgt
    · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
    · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
      have hpos : i - pre.length = (i - pre.length - 1) + 1 := by omega
      rw [hpos]
      simp

/-- Every genuine script of cost at most one has a valid concrete edit realization.
The output length and complete padded word are both derived from the script. -/
theorem within_one_realized {x y : List Bool} (h : WithinEdits 1 x y) :
    ∃ e : Edit, e.Valid x.length ∧ e.outputLength x.length = y.length ∧
      e.word (listLetters x) = listLetters y := by
  obtain ⟨d, i, s, hscript, hcost⟩ := h
  rcases hscript.classify_of_le_one hcost with hsame | hdelete | hinsert | hsubstitute
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
  · obtain ⟨pre, suffix, bit, rfl, rfl⟩ := hsubstitute
    refine ⟨.substitute pre.length, ?_, ?_, ?_⟩
    · simp only [Edit.Valid, List.length_append, List.length_cons]
      omega
    · simp only [Edit.outputLength, List.length_append, List.length_cons]
    · exact flip_split pre suffix bit

#print axioms EditAlignment.Script.zero_eq
#print axioms EditAlignment.Script.classify_of_le_one
#print axioms delete_split
#print axioms insert_split
#print axioms flip_split
#print axioms within_one_realized

end DeletionCode.SingleEditScripts
