import DeletionCode.Burst.LocalBubble

/-!
Regression examples for whole substring replacements: two-letter operations
count once, either block may be empty, and chronological edits may overlap.
A finite nonbinary source also instantiates the complete local-bubble theorem
for unequal block lengths, including all simplicity and endpoint conclusions.
-/
namespace DeletionCode.Burst.Examples

open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords

theorem two_letter_replacement : Script 2 ([0, 1, 2] : Word (Fin 3)) [2, 2, 2] 1 :=
  Script.step (pre := []) (suffix := [2]) (U := [0, 1]) (V := [2, 2])
    (by decide) (by decide) (by decide) (Script.refl _)

theorem two_letter_deletion : Script 2 ([0, 1, 2] : Word (Fin 3)) [2] 1 :=
  Script.step (pre := []) (suffix := [2]) (U := [0, 1]) (V := [])
    (by decide) (by decide) (by decide) (Script.refl _)

theorem two_letter_insertion : Script 2 ([2] : Word (Fin 3)) [0, 1, 2] 1 :=
  Script.step (pre := []) (suffix := [2]) (U := []) (V := [0, 1])
    (by decide) (by decide) (by decide) (Script.refl _)

/-- The second operation removes one newly inserted letter and one surviving
source letter. Separation is not a restriction on the channel itself. -/
theorem overlapping_replacements : Script 2 ([0, 1, 2] : Word (Fin 3)) [2, 1] 2 :=
  Script.step (pre := [2]) (suffix := []) (U := [2, 2]) (V := [1])
    (by decide) (by decide) (by decide) two_letter_replacement

theorem replacement_letters_have_no_origin :
    (Edit.mk 0 2 ([2, 2] : Word (Fin 3))).origin 0 = none ∧
    (Edit.mk 0 2 ([2, 2] : Word (Fin 3))).origin 1 = none ∧
    (Edit.mk 0 2 ([2, 2] : Word (Fin 3))).origin 2 = some 2 := by decide

theorem cannot_delete_three_in_one_unit_burst :
    ¬ WithinBursts 1 1 ([0, 0, 0] : Word (Fin 3)) [] := by
  rintro ⟨r, hr, hs⟩
  have hlen := hs.source_length_le
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one] at hlen
  omega

def uniqueSource : Word (Fin 67) :=
  List.ofFn (fun i : Fin 64 => (⟨i.val, by have hi := i.isLt; omega⟩ : Fin 67))

theorem uniqueSource_unique : KUnique (listLetters uniqueSource) uniqueSource.length 1 := by
  intro a c ha hc hag
  simp only [uniqueSource, List.length_ofFn] at ha hc
  have hal : a < 64 := by omega
  have hcl : c < 64 := by omega
  have heq := hag 0 (by decide)
  simp only [Nat.add_zero, listLetters, uniqueSource, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, dite_eq_left hal, dite_eq_left hcl, Option.getD_some] at heq
  exact congrArg Fin.val heq

def unequalEdit : Edit (Fin 67) := ⟨30, 2, [65]⟩

theorem unequalEdit_valid : unequalEdit.Valid 2 uniqueSource := by
  unfold Edit.Valid Edit.Bounded Edit.InBounds
  decide

/-- A genuine two-to-one replacement has the fully proved local geometry,
not just the word grammar. -/
theorem unequal_block_local_bubble :
    ∃ p : LocalBubble (Fin 67) 1 2 uniqueSource (unequalEdit.apply uniqueSource) 30,
      p.bubble.removed = [30, 31] ∧ p.bubble.replacement = [65] := by
  obtain ⟨p, hU, hV⟩ := exists_localBubble (k := 1) (b := 2) (by decide)
    unequalEdit uniqueSource unequalEdit_valid uniqueSource_unique (by decide) (by decide)
  refine ⟨p, ?_, hV⟩
  exact hU.trans (by decide)

def insertionEdit : Edit (Fin 67) := ⟨30, 0, [64, 65]⟩
def deletionEdit : Edit (Fin 67) := ⟨30, 2, []⟩

theorem empty_removed_local_bubble :
    ∃ p : LocalBubble (Fin 67) 1 2 uniqueSource (insertionEdit.apply uniqueSource) 30,
      p.bubble.removed = [] ∧ p.bubble.replacement = [64, 65] := by
  have hv : insertionEdit.Valid 2 uniqueSource := by
    unfold Edit.Valid Edit.Bounded Edit.InBounds
    decide
  obtain ⟨p, hU, hV⟩ := exists_localBubble (k := 1) (b := 2) (by decide)
    insertionEdit uniqueSource hv uniqueSource_unique (by decide) (by decide)
  exact ⟨p, hU.trans (by decide), hV⟩

theorem empty_replacement_local_bubble :
    ∃ p : LocalBubble (Fin 67) 1 2 uniqueSource (deletionEdit.apply uniqueSource) 30,
      p.bubble.removed = [30, 31] ∧ p.bubble.replacement = [] := by
  have hv : deletionEdit.Valid 2 uniqueSource := by
    unfold Edit.Valid Edit.Bounded Edit.InBounds
    decide
  obtain ⟨p, hU, hV⟩ := exists_localBubble (k := 1) (b := 2) (by decide)
    deletionEdit uniqueSource hv uniqueSource_unique (by decide) (by decide)
  exact ⟨p, hU.trans (by decide), hV⟩

#print axioms overlapping_replacements
#print axioms unequal_block_local_bubble
#print axioms empty_removed_local_bubble
#print axioms empty_replacement_local_bubble

end DeletionCode.Burst.Examples
