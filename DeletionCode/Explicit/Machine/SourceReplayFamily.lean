import DeletionCode.Explicit.Machine.SourceCoreReplay
import DeletionCode.Explicit.Machine.SourceFamilyMembers
import DeletionCode.Explicit.ReplayFamily

/-! Read the active positions and the ordered family from a symbolic replay. -/
namespace DeletionCode.Explicit.Machine.SourceReplayFamily

open SourceGrammar SourceLetters SourceLists SourceFamilyMembers BubbleFamilies
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open private patternLetter assignedLetter from DeletionCode.Explicit.BubbleFamilies

variable {q ℓ n : ℕ}

def pattern (neg : LiftData q) : List (Option (Fin q)) :=
  neg.map (fun a => a.2.map Prod.snd)

def shape (d : Decoded q) (e : SourceDictionary.Stored q) : Shape q :=
  ⟨d.left,d.right,d.removed,d.replacement,pattern e.2.1⟩

theorem shape_eq (d : ReplayGrammar.DecodedEntry q) (e : ReplayEntry.Completed ℓ (Fin q)) :
    shape (decodedData d) (SourceDictionary.store e) = replayShape (d.entry,e) := by
  unfold shape replayShape shapeOf decodedData SourceDictionary.store pattern liftData
  simp only [List.map_ofFn,Function.comp_def]
  congr 2
  funext i
  cases e.negative.2.letters i <;> rfl

def positions (neg : LiftData q) : List ℕ := SourcePrepare.positions neg

theorem positions_eq (w : LetterSequence.Lift ℓ n (Fin q)) :
    positions (liftData w) = (originalNames w).map Fin.val := by
  unfold positions SourcePrepare.positions originalNames liftData
  have h : List.ofFn (letterData ∘ w.letters) = (List.ofFn w.letters).map letterData := by
    rw [List.map_ofFn]
  rw [h,List.filterMap_map,List.map_filterMap]
  apply List.filterMap_congr
  intro a _
  exact position_eq a

def values (pad : Fin q) (w : QWord q) (neg : LiftData q) : QWord q :=
  (positions neg).map (fun pos => w.getD pos pad)

theorem values_eq (pad : Fin q) (w : LetterSequence.Lift ℓ n (Fin q)) (x : Fin ℓ → Fin q) :
    values pad (List.ofFn x) (liftData w) = originalValues w x := by
  rw [values,positions_eq,List.map_map]
  unfold originalNames originalValues
  rw [List.map_filterMap]
  apply List.filterMap_congr
  intro a _
  cases a with
  | original i => simpa [LetterSequence.Letter.position,assignedLetter,Function.comp_def]
      using congrArg some (BooleanFibres.ofFn_getD x i pad)
  | fresh j a v => rfl

def assignments (pad : Fin q) (b t ℓ : ℕ) (d : Decoded q) (e : SourceDictionary.Stored q) :
    List (QWord q) := (members pad b t ℓ (shape d e)).map Prod.fst

theorem assignments_eq (pad : Fin q) (b t : ℕ)
    (d : ReplayGrammar.DecodedEntry q) (e : ReplayEntry.Completed ℓ (Fin q)) :
    assignments pad b t ℓ (decodedData d) (SourceDictionary.store e) =
      (replayAssignments (UniformParameters.windowLength q ℓ) b (UniformParameters.gram q b t ℓ)
        (UniformParameters.omittedLetters q b t ℓ) pad (d.entry,e)).map List.ofFn := by
  rw [assignments,shape_eq,members_eq,List.map_map,replayAssignments,List.map_map]
  unfold SmallFamilyCodec.shapeAssignments
  rw [List.map_filterMap,← List.filterMap_eq_map]
  apply List.filterMap_congr
  intro w hw
  let K := UniformParameters.windowLength q ℓ
  let L := UniformParameters.gram q b t ℓ
  let Λ := UniformParameters.omittedLetters q b t ℓ
  let s := replayShape (d.entry,e)
  have hlen := ((mem_members s K b L Λ pad w.1 w.2).mp hw).1
  simp only [Function.comp_def,show w.1.length = s.originalCount from hlen]
  rw [dite_eq_left (show s.originalCount = (replayShape (d.entry,e)).originalCount from rfl),Option.map_some]
  apply congrArg some
  symm
  apply List.ext_getElem
  · simp only [List.length_ofFn,hlen]
    exact (replayShape_card pad (d.entry,e)).symm
  · intro i hi hj
    simp

theorem pattern_polyTime (q : ℕ) :
    ComputableInPolyTime (pattern (q := q)) (liftEncoding q) (patternEncoding q) := by
  let a := letterEncoding q
  let e := freshEncoding q
  let c := alphabetEncoding q
  let w := encPair a e
  have hg := optionMapWithInput (encA := a) (encB := e) (encC := c)
    (f := fun _ x => x.2) (snd encUnary (encOption e)) (snd encUnary c |>.comp (snd a e))
  exact (ComputableInPolyTime.map hg).of_enc_eq (fun _ => rfl)

theorem shape_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : Decoded q × SourceDictionary.Stored q => shape x.1 x.2)
      (SourceCoreReplay.materialPairEncoding q) (familyShapeEncoding q) := by
  let d := decodedEncoding q
  let e := SourceDictionary.storedEncoding q
  have x := fst d e
  have hneg := (snd d e).snd'.fst'
  exact familyShapeEncoding_mk_polyTime q (decodedEncoding_left_polyTime q x)
    (decodedEncoding_right_polyTime q x) (decodedEncoding_removed_polyTime q x)
    (decodedEncoding_replacement_polyTime q x) ((pattern_polyTime q).comp hneg)

theorem values_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : QWord q × LiftData q => values pad x.1 x.2)
      (encPair (wordEncoding q) (liftEncoding q)) (wordEncoding q) := by
  let e := encPair (wordEncoding q) (liftEncoding q)
  have hpos := (SourcePrepare.positions_polyTime q).comp (snd (wordEncoding q) (liftEncoding q))
  have hword := (fst (wordEncoding q) (liftEncoding q)).comp (fst e encUnary)
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := alphabetEncoding q)
    (f := fun x p => x.1.getD p pad) hpos (listGetDWithInput hword (snd e encUnary) pad)

theorem assignments_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : ℕ × (Decoded q × SourceDictionary.Stored q) =>
      assignments pad b t x.1 x.2.1 x.2.2)
      (encPair encUnary (SourceCoreReplay.materialPairEncoding q)) (encList (wordEncoding q)) := by
  let p := SourceCoreReplay.materialPairEncoding q
  let e := encPair encUnary p
  have hs := (shape_polyTime q).comp (snd encUnary p)
  have hm := (members_polyTime pad b t hq).comp (encIn := e) ((fst encUnary p).prod hs)
  exact (ComputableInPolyTime.map (fst (wordEncoding q) (OrderedCatalogue.bubbleEncoding q))).comp hm

#print axioms shape_eq
#print axioms positions_eq
#print axioms values_eq
#print axioms assignments_eq
#print axioms shape_polyTime
#print axioms values_polyTime
#print axioms assignments_polyTime

end DeletionCode.Explicit.Machine.SourceReplayFamily
