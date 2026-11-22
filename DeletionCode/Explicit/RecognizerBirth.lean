import DeletionCode.Explicit.RecognizerState

/-! Frozen dictionaries and local-word facts for every completed rule. -/

namespace DeletionCode.Explicit.Recognizer

open LetterGraphCuts FieldHash

variable {ℓ q K b L Λ R s : ℕ}

/-- The facts retained about the instant a batch of gates was prepared. -/
structure RecordedBatch (P : RuleAddition.Bounds K b L Λ s R) (pad : Fin q)
    (x : Fin ℓ → Fin q) (root : Fin ℓ) (old : History ℓ q L s) (new : Batch ℓ q L s) : Prop where
  outside : new.row ∉ CanonicalColour.span (oldRows old)
  fromCatalogue : ∃ words : Fin s → Borrowed.BubbleWord (Fin q) K b L,
    words ∈ CatalogueEnumeration.rules q K b L s pad ∧
    new.row = CatalogueEnumeration.row pad words ∧
    ∃ edges, ∀ j : Fin s,
      prepareBubble pad x (completed old) (words j) root ((completed old).size+j.val)
        old.length (RuleAddition.left_pos P _) (RuleAddition.right_pos P _) = some (new.bubbles j) ∧
      RuleAddition.PreparedSpec P x edges (words j) ((completed old).size+j.val) old.length (new.bubbles j)

inductive RecordedBatches (P : RuleAddition.Bounds K b L Λ s R) (pad : Fin q)
    (x : Fin ℓ → Fin q) (root : Fin ℓ) : History ℓ q L s → Prop
  | empty : RecordedBatches P pad x root []
  | append {old : History ℓ q L s} {new : Batch ℓ q L s} :
    RecordedBatches P pad x root old → RecordedBatch P pad x root old new →
    RecordedBatches P pad x root (old++[new])

/-- Locate the frozen dictionary for an arbitrary completed rule in the
current history. -/
theorem RecordedBatches.batch_at {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q}
    {x : Fin ℓ → Fin q} {root : Fin ℓ} {hs : History ℓ q L s}
    (h : RecordedBatches P pad x root hs) (i : Fin hs.length) :
    RecordedBatch P pad x root (hs.take i.val) (hs.get i) := by
  induction h with
  | empty => exact i.elim0
  | @append old new h ho ih =>
    have htotal : (old++[new]).length = old.length+1 := by simp
    by_cases hi : i.val < old.length
    · have hprefix : (old++[new]).take i.val = old.take i.val :=
        List.take_append_of_le_length hi.le
      have hget : (old++[new]).get i = old.get ⟨i.val,hi⟩ := List.getElem_append_left hi
      rw [hprefix,hget]
      exact ih ⟨i.val,hi⟩
    · have he : i.val = old.length := by have h := i.isLt; omega
      have hprefix : (old++[new]).take i.val = old := by
        rw [he,List.take_append_of_le_length le_rfl,List.take_length]
      have hget : (old++[new]).get i = new := by
        change (old++[new])[i.val] = new
        rw [List.getElem_append_right (Nat.le_of_eq he.symm)]
        simp [he]
      rwa [hprefix,hget]

#print axioms RecordedBatches.batch_at

end DeletionCode.Explicit.Recognizer
