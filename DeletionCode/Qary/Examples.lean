import DeletionCode.Qary.EditAlignment
import DeletionCode.Qary.AnchorRecords
import DeletionCode.Qary.BubbleEndpoints
import DeletionCode.Qary.CatalogueWords

/-!
Small ternary regression examples for behavior absent over the binary alphabet:
successive substitutions need not cancel, records carry the replacement symbol,
and the two boundaries of a constant run may carry different letters.
-/
namespace DeletionCode.Qary.Examples

open DeletionCode.Qary.EditAlignment DeletionCode.Qary.AlignmentTrace DeletionCode.Qary.CatalogueWords DeletionCode.Qary.HeaderRecovery

/-- Two substitutions through three distinct letters give a nonidentity script. -/
theorem two_substitutions : Script ([0] : List (Fin 3)) [2] 0 0 2 := by
  have h01 : Script ([0] : List (Fin 3)) [1] 0 0 1 :=
    Script.substitute (pre := []) (suffix := []) (by decide : (0 : Fin 3) ≠ 1)
      (Script.refl _)
  exact Script.substitute (pre := []) (suffix := []) (by decide : (1 : Fin 3) ≠ 2) h01

/-- The same two endpoint words admit one substitution, not an all-matched alignment. -/
theorem endpoint_alignment : Alignment ([0] : List (Fin 3)) [2] 0 0 1 :=
  Alignment.substitution 0 2 (by decide) Alignment.nil

theorem substituted_word_ne_source : ([2] : List (Fin 3)) ≠ [0] := by decide

/-- A substitution packet stores the target symbol explicitly. -/
theorem substitution_payload : AnchorRecords.payload (Column.substitution (0 : Fin 3) 2 (by decide)) =
    ((false, true), 2) := rfl

/-- Decoding the record reconstructs the arbitrary replacement target. -/
theorem substitution_record_decodes : AnchorRecords.decode ([0] : List (Fin 3))
    (AnchorRecords.encode [Column.substitution 0 2 (by decide)]) = [2] := rfl

/-- A local deletion grammar with run symbol 0 and distinct boundary symbols 1 and 2.
The endpoint test below isolates the boundary condition and does not assume that
this illustrative word belongs to the unique-word family. -/
def ternaryDeletionBubble : BubbleWord (Fin 3) 1 where
  left := [1, 1, 1, 1, 1]
  right := [2, 2, 2, 2, 2]
  rho := 1
  bit := 0
  newBit := 0
  orientation := .deletion
  rho_lower := by decide
  rho_upper := by decide
  left_length := by decide
  right_length := by decide
  sub_rho := by intro h; cases h
  sub_ne := by intro h; cases h

theorem different_run_boundaries : ternaryDeletionBubble.left.getLast? = some 1 ∧
    ternaryDeletionBubble.right.head? = some 2 ∧ (1 : Fin 3) ≠ 2 := by decide

/-- Unequal flank symbols satisfy the actual endpoint-displacement theorem. -/
theorem deletion_endpoints (a b : ℕ)
    (ha : a ≤ windowLength 1 - ternaryDeletionBubble.rho + 1)
    (hb : b ≤ windowLength 1 - ternaryDeletionBubble.rho)
    (hag : Windows.Agree (listLetters ternaryDeletionBubble.longWord) a
      (listLetters ternaryDeletionBubble.shortWord) b (windowLength 1 - 1))
    (hdis : a = b ∨ a = b + 1) :
    (a = 0 ∧ b = 0) ∨
      (a = windowLength 1 - ternaryDeletionBubble.rho + 1 ∧
        b = windowLength 1 - ternaryDeletionBubble.rho) :=
  BubbleEndpoints.endpoints_of_displacement ternaryDeletionBubble (by decide) (by decide)
    a b ha hb hag hdis

end DeletionCode.Qary.Examples
