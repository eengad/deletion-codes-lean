import DeletionCode.Burst.Origins
import DeletionCode.Burst.ChronologicalRecords

/-!
Exact links between finite replacement words and the total letter functions
used for windows. Default padding is never used as a finite source letter.
-/
namespace DeletionCode.Burst

open DeletionCode.Qary.CatalogueWords DeletionCode.Qary.Windows

variable {α : Type*} [Inhabited α]

namespace Edit

theorem listLetters_apply (e : Edit α) (x : Word α) (he : e.InBounds x.length) :
    listLetters (e.apply x) = e.word (listLetters x) := by
  have hp : e.pos ≤ x.length := by unfold InBounds at he; omega
  have htake : (x.take e.pos).length = e.pos := List.length_take_of_le hp
  funext i
  simp only [listLetters, apply, word, List.getD_eq_getElem?_getD]
  rw [List.append_assoc]
  by_cases hbefore : i < e.pos
  · rw [ite_eq_left hbefore, List.getElem?_append_left (by omega),
      List.getElem?_take_of_lt hbefore]
  · rw [ite_eq_right hbefore, List.getElem?_append_right (by omega), htake]
    by_cases hnew : i < e.pos + e.replacement.length
    · rw [ite_eq_left hnew, List.getElem?_append_left (by omega)]
    · rw [ite_eq_right hnew, List.getElem?_append_right (by omega), List.getElem?_drop]
      have hindex : e.pos + e.removed + (i - e.pos - e.replacement.length) =
          i + e.removed - e.replacement.length := by omega
      rw [hindex]

theorem sourceBlock_letters (e : Edit α) (x : Word α) {i : ℕ} (hi : i < e.removed) :
    listLetters (e.sourceBlock x) i = listLetters x (e.pos + i) := by
  simp only [sourceBlock, listLetters, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hi, List.getElem?_drop]

theorem word_replacement (e : Edit α) (x : Letters α) {i : ℕ}
    (hi : i < e.replacement.length) :
    e.word x (e.pos + i) = listLetters e.replacement i := by
  have hb : ¬ e.pos + i < e.pos := by omega
  have hn : e.pos + i < e.pos + e.replacement.length := by omega
  simp only [word, hb, hn, ite_false, ite_true, Nat.add_sub_cancel_left, listLetters]

end Edit

theorem eq_of_listLetters {x y : Word α} (hl : x.length = y.length)
    (h : Agree (listLetters x) 0 (listLetters y) 0 x.length) : x = y := by
  apply List.ext_getElem hl
  intro i hi hj
  have heq := h i hi
  simpa only [Nat.zero_add, listLetters, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some] using heq

theorem listLetters_reverse (x : Word α) {i : ℕ} (hi : i < x.length) :
    listLetters x.reverse i = listLetters x (x.length - 1 - i) := by
  simp only [listLetters, List.getD_eq_getElem?_getD, List.getElem?_reverse hi]

end DeletionCode.Burst
