import DeletionCode.Burst.Catalogue
import DeletionCode.Burst.BubbleHeaders
import DeletionCode.Burst.GeneratingModel

/-!
Concrete finite catalogue words provide every hypothesis required by the
executable recovery model. The resulting path family equals the catalogue
family as total functions, including the default padding beyond each word.
-/
namespace DeletionCode.Burst.CatalogueBridge

open Qary.Windows Qary.CatalogueWords Qary.SupportComponents
open DeletionCode.Burst.HeaderRecovery DeletionCode.Burst.GeneratingModel
variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

def editedFamily {k b ν R : ℕ} (words : Fin ν → BubbleWord α k b)
    (group : Fin ν → Fin R) (hv : Catalogue.ValidCatalogue words group) :
    EditedFamily α (Fin ν) k b where
  header i := (words i).header
  long i := listLetters (words i).negativeWord
  rank i := (group i).val
  valid i := (words i).header_valid
  header_matches i := (words i).header_matches
  initial_agreement i := by
    rw [(words i).positivePath_header]
    exact (vertex_eq_iff_agree (Catalogue.indexedFamily words group) (windowLength k b)
      i i false true 0 0).mp (hv.common_start i)

theorem family_eq {k b ν R : ℕ} (words : Fin ν → BubbleWord α k b)
    (group : Fin ν → Fin R) (hv : Catalogue.ValidCatalogue words group) :
    (editedFamily words group hv).family = Catalogue.indexedFamily words group := by
  unfold EditedFamily.family Catalogue.indexedFamily Catalogue.family
  congr 1
  · funext i side
    cases side
    · rfl
    · exact (words i).positivePath_header
  · funext i side
    cases side
    · exact congrArg (fun n => n - windowLength k b) (words i).negativeLength_header
    · exact congrArg (fun n => n - windowLength k b) (words i).positiveLength_header

#print axioms editedFamily
#print axioms family_eq
end DeletionCode.Burst.CatalogueBridge
