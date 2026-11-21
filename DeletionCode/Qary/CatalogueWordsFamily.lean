import DeletionCode.Qary.CatalogueWords
import DeletionCode.Qary.GeneratingModel

/-! Connect the alphabet-generic local word grammar to recovery families. -/
namespace DeletionCode.Qary.CatalogueWords

open DeletionCode.Qary.Windows DeletionCode.Qary.HeaderRecovery DeletionCode.Qary.GeneratingModel
variable {α : Type*} [DecidableEq α] [Inhabited α]

/-- Indexed grammar words supply the edited-family data, including the derived header letter. -/
def editedFamily {B : Type*} {k : ℕ} (bubbles : B → BubbleWord α k) (rank : B → ℕ) :
    EditedFamily α B k where
  header b := (bubbles b).header
  long b := listLetters (bubbles b).longWord
  rank := rank
  rho_lower b := (bubbles b).rho_lower
  rho_upper b := (bubbles b).rho_upper
  header_bit b := (bubbles b).header_bit

theorem editedFamily_negative {B : Type*} {k : ℕ}
    (bubbles : B → BubbleWord α k) (rank : B → ℕ) (b : B) :
    (editedFamily bubbles rank).family.path b false = listLetters (bubbles b).negativeWord :=
  (bubbles b).negativeWord_semantics.symm

theorem editedFamily_positive {B : Type*} {k : ℕ}
    (bubbles : B → BubbleWord α k) (rank : B → ℕ) (b : B) :
    (editedFamily bubbles rank).family.path b true = listLetters (bubbles b).positiveWord :=
  (bubbles b).positiveWord_semantics.symm


#print axioms editedFamily

end DeletionCode.Qary.CatalogueWords
