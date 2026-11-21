import DeletionCode.Burst.BubbleWords
import DeletionCode.Burst.HeaderRecovery
import DeletionCode.Burst.WordFacts

/-! Actual finite burst words satisfy the header decoder's exact semantics. -/
namespace DeletionCode.Burst.BubbleWord

open HeaderRecovery Qary.CatalogueWords
variable {α : Type*} [Inhabited α] {k b : ℕ}

def header (p : BubbleWord α k b) : Header α :=
  ⟨p.left.length, p.right.length, p.removed, p.replacement⟩

theorem header_valid (p : BubbleWord α k b) : p.header.Valid k b :=
  ⟨p.removed_bound, p.replacement_bound, p.left_lower, p.left_upper,
    p.right_lower, p.right_upper⟩

theorem header_matches (p : BubbleWord α k b) : p.header.Matches (listLetters p.negativeWord) := by
  intro i hi
  have h := Edit.sourceBlock_letters p.edit p.negativeWord hi
  simpa only [edit, negativeWord, Edit.sourceBlock_split, header, listLetters] using h

theorem positivePath_header (p : BubbleWord α k b) :
    positivePath p.header (listLetters p.negativeWord) = listLetters p.positiveWord := by
  have h := Edit.listLetters_apply p.edit p.negativeWord p.edit_inBounds
  simpa only [edit, negativeWord, positiveWord, Edit.apply_split, header, positivePath] using h.symm

theorem negativeLength_header (p : BubbleWord α k b) : negativeLength p.header = p.negativeWord.length := by
  simp [negativeLength, header, negativeWord, Nat.add_assoc]

theorem positiveLength_header (p : BubbleWord α k b) : positiveLength p.header = p.positiveWord.length := by
  simp [positiveLength, header, positiveWord, Nat.add_assoc]

#print axioms header_matches
#print axioms positivePath_header
end DeletionCode.Burst.BubbleWord
