import DeletionCode.Explicit.ReplayFamily
import DeletionCode.Explicit.FamilyBuckets
import DeletionCode.Explicit.GateGeometry
import DeletionCode.Explicit.CatalogueEnumeration

/-! A replayed catalogue bubble belongs to the family determined by its shape. -/

namespace DeletionCode.Explicit.BubbleFamilies

open LetterSequence LetterGraphCuts ReplayEntry Borrowed

variable {ℓ q K b L Λ s n : ℕ}

theorem active_card (w : Lift ℓ n (Fin q)) : (active w).card = w.positions.card := by
  have he : (active w).image Fin.val = w.positions := by
    ext i
    constructor
    · intro hi
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hi
      exact (active_iff w p).mp hp
    · intro hi
      obtain ⟨_,p,_,rfl⟩ := w.mem_positions.mp hi
      exact Finset.mem_image.mpr ⟨p,(active_iff w p).mpr hi,rfl⟩
  rw [← he,Finset.card_image_of_injective _ Fin.val_injective]

theorem replayShape_freshCount (pad : Fin q) (p : Entry (Fin q) × Completed ℓ (Fin q)) :
    (replayShape p).freshCount = p.2.negative.2.freshOffsets.card := by
  have h := shapeCounts_add (replayShape p)
  rw [replayShape_card pad p,active_card] at h
  have ht : (replayShape p).fresh.length = p.2.negative.1 := by
    simp [replayShape,shapeOf]
  rw [ht] at h
  have hp := positions_add_fresh p.2.negative.2
  omega

/-- Validity of a bubble's words and geometry survives restricting the
catalogue rule to that one bubble. -/
theorem member_catalogue [Inhabited (Fin q)] (words : Fin s → BubbleWord (Fin q) K b L)
    (hcat : Catalogue.ValidCatalogue words (fun _ => (0 : Fin 1))) (j : Fin s) :
    Catalogue.ValidCatalogue (fun _ : Fin 1 => words j) (fun _ => (0 : Fin 1)) := by
  refine ⟨fun _ => hcat.length_lower j,⟨?_,?_,?_⟩,fun _ => hcat.common_start j,
    fun _ => hcat.common_end j,?_⟩
  · intro _ side
    exact hcat.geometry.simple j side
  · intro _ i k
    exact hcat.geometry.endpoints j i k
  · intro _
    exact hcat.geometry.notBothSingle j
  · intro _ i _ j _ h
    exact (h (Subsingleton.elim i j)).elim

theorem member_of_replay_spelling (pad : Fin q) (p : Entry (Fin q) × Completed ℓ (Fin q)) (x : Fin ℓ → Fin q)
    (w : BubbleWord (Fin q) K b L)
    (hc : @Catalogue.ValidCatalogue _ ⟨pad⟩ K b L 1 1 (fun _ => w) (fun _ => 0))
    (hleft : p.1.left = w.left.length) (hright : p.1.right = w.right.length)
    (hu : p.1.removed = w.removed) (hv : p.1.replacement = w.replacement)
    (hneg : List.ofFn (p.2.negative.2.spelling x) = w.negativeWord)
    (hfresh : p.2.negative.2.freshOffsets.card ≤ Λ) :
    (replayShape p).member K b L Λ pad (originalValues p.2.negative.2 x) = some w := by
  let : Inhabited (Fin q) := ⟨pad⟩
  have hf : (replayShape p).freshCount ≤ Λ := by rw [replayShape_freshCount pad p]; exact hfresh
  have hlen : (replayShape p).fresh.length = (replayShape p).left+(replayShape p).removed.length+(replayShape p).right := by
    have hsize := congrArg List.length hneg
    simp only [List.length_ofFn,BubbleWord.negativeWord,List.length_append] at hsize
    simpa [replayShape,shapeOf,hleft,hright,hu,Nat.add_assoc] using hsize
  unfold Shape.member
  rw [ite_eq_left ⟨hf,hlen⟩]
  have hfill : fill (replayShape p).fresh (originalValues p.2.negative.2 x) = some w.negativeWord :=
    (fill_shapeOf p.1.left p.1.right p.1.removed p.1.replacement p.2.negative.2 x).trans (congrArg some hneg)
  rw [hfill]
  have hcalc : localWord K b L (replayShape p).left (replayShape p).removed (replayShape p).replacement w.negativeWord =
      some w := by
    change localWord K b L p.1.left p.1.removed p.1.replacement w.negativeWord = some w
    rw [hleft,hu,hv]
    exact CatalogueEnumeration.localWord_roundtrip w
  have hvalid : Catalogue.validCheck (fun _ : Fin 1 => w) (fun _ => (0 : Fin 1)) = true :=
    (Catalogue.validCheck_iff _ _).mpr hc
  simp [hcalc,hvalid]

#print axioms member_of_replay_spelling

end DeletionCode.Explicit.BubbleFamilies
