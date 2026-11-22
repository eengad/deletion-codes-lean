import DeletionCode.Explicit.Machine.SourceCoreCheck
import DeletionCode.Explicit.Machine.SourceBuckets
import DeletionCode.Explicit.Machine.SourceReplayPayload
import DeletionCode.Explicit.PeelingBuckets
import Batteries.Tactic.OpenPrivate

/-! Bucket ranks and local restoration for the pivot of a peeling rule. -/
namespace DeletionCode.Explicit.Machine.SourcePeelingBuckets

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open FieldHash Ternary CataloguePrefix SourceReplayPayload SourceGrammar SourceLists
open _root_.DeletionCode.Explicit.UniformParameters
open private bubble_delta_eq from DeletionCode.Explicit.Machine.SourceCoreCheck

variable {q ℓ θ : ℕ}

def recordHash (pad : Fin q) (b t l : ℕ) (H : Rows) (record : Record q) (word : QWord q) : Row :=
  let L := gram q b t l
  SourceSpectrum.applyRows (q^L) H (SourceBuckets.vector pad L (SourceCoreCheck.bubblePair pad word record))

theorem recordHash_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q)
    (H : TernaryMatrix θ (q^gram q b t ℓ)) (d : ReplayGrammar.DecodedEntry q)
    (v : ReplayEntry.Completed ℓ (Fin q)) (word : Fin ℓ → Fin q) :
    recordHash pad b t ℓ (matrixRows H) (decodedData d, SourceDictionary.store v) (List.ofFn word) =
      List.ofFn (H.mulVec (PeelingBuckets.vectorOf (gram q b t ℓ) pad (d.entry, v) word)) := by
  let L := gram q b t ℓ
  have hvec : SourceBuckets.vector pad L (SourceCoreCheck.bubblePair pad (List.ofFn word)
      (decodedData d, SourceDictionary.store v)) =
      List.ofFn (PeelingBuckets.vectorOf L pad (d.entry, v) word) := by
    unfold SourceBuckets.vector SourceRuleRows.row SourceRuleRows.rowWith
    rw [GramOrder.mainWords_eq pad hq, List.map_ofFn]
    congr 1
    funext i
    simpa [Function.comp_def, PeelingBuckets.vectorOf] using
      bubble_delta_eq pad L word (d, v) (finFunctionFinEquiv.symm i)
  rw [recordHash, hvec, SourceSpectrum.applyRows_matrix_eq]

def bucketValues (pad : Fin q) (b t l : ℕ) (H : Rows) (record : Record q) (z : Row) : List (QWord q) :=
  (SourceBuckets.bucket pad b t l (SourceReplayFamily.shape record.1 record.2) H z).map Prod.fst

theorem bucketValues_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q)
    (H : TernaryMatrix θ (q^gram q b t ℓ)) (d : ReplayGrammar.DecodedEntry q)
    (v : ReplayEntry.Completed ℓ (Fin q)) (z : Fin θ → F₃) :
    bucketValues pad b t ℓ (matrixRows H) (decodedData d, SourceDictionary.store v) (List.ofFn z) =
      PeelingBuckets.bucketValues (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ)
        pad H (d.entry, v) z := by
  unfold bucketValues PeelingBuckets.bucketValues
  rw [SourceReplayFamily.shape_eq, SourceBuckets.bucket_eq pad b t ℓ hq, List.map_map]
  rfl

def pivotDigit (pad : Fin q) (b t l : ℕ) (H : Rows) (record : Record q) (word : QWord q) : ℕ :=
  (bucketValues pad b t l H record (recordHash pad b t l H record word)).idxOf
    (SourceReplayFamily.values pad word record.2.2.1)

theorem pivotDigit_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q)
    (H : TernaryMatrix θ (q^gram q b t ℓ)) (d : ReplayGrammar.DecodedEntry q)
    (v : ReplayEntry.Completed ℓ (Fin q)) (word : Fin ℓ → Fin q) :
    pivotDigit pad b t ℓ (matrixRows H) (decodedData d, SourceDictionary.store v) (List.ofFn word) =
      PeelingBuckets.pivotDigit (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ)
        pad H (d.entry, v) word := by
  unfold pivotDigit PeelingBuckets.pivotDigit
  rw [recordHash_eq pad b t hq, bucketValues_eq pad b t hq]
  change (PeelingBuckets.bucketValues _ _ _ _ pad H (d.entry, v) _).idxOf
      (SourceReplayFamily.values pad (List.ofFn word) (SourceLetters.liftData v.negative.2)) = _
  rw [SourceReplayFamily.values_eq]

def restoreWithHash (pad : Fin q) (b t l : ℕ) (H : Rows) (record : Record q)
    (z : Row) (digit : ℕ) (old : QWord q) : Option (QWord q) := do
  let vals ← (bucketValues pad b t l H record z)[digit]?
  let keys := SourceReplayPayload.keys record
  if vals.length = keys.length then
    some (SourceSmallCodec.assemble pad l keys vals (SourceSmallCodec.select pad (SourceSmallCodec.outside l keys) old))
  else none

theorem restoreWithHash_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q)
    (H : TernaryMatrix θ (q^gram q b t ℓ)) (d : ReplayGrammar.DecodedEntry q)
    (v : ReplayEntry.Completed ℓ (Fin q)) (z : Fin θ → F₃) (digit : ℕ) (old : Fin ℓ → Fin q) :
    restoreWithHash pad b t ℓ (matrixRows H) (decodedData d, SourceDictionary.store v)
      (List.ofFn z) digit (List.ofFn old) =
    (do
      let vals ← (PeelingBuckets.bucketValues (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ)
        pad H (d.entry, v) z)[digit]?
      let S := BubbleFamilies.active v.negative.2
      if hv : vals.length = S.card then
        some (SmallFamilyCodec.assemble S (fun i => vals.get (Fin.cast hv.symm i)) (SmallFamilyCodec.select Sᶜ old))
      else none).map List.ofFn := by
  unfold restoreWithHash
  rw [bucketValues_eq pad b t hq, SourceReplayPayload.keys_eq]
  cases (PeelingBuckets.bucketValues (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ)
    pad H (d.entry, v) z)[digit]? with
  | none => rfl
  | some vals =>
    let S := BubbleFamilies.active v.negative.2
    simp only [bind, Option.bind]
    rw [SourceSmallCodec.names_length]
    change (if vals.length = S.card then some _ else none) =
      (if hv : vals.length = S.card then some (SmallFamilyCodec.assemble S
        (fun i => vals.get (Fin.cast hv.symm i)) (SmallFamilyCodec.select Sᶜ old)) else none).map List.ofFn
    by_cases hv : vals.length = S.card
    · rw [ite_eq_left hv, dite_eq_left hv, Option.map_some, SourceSmallCodec.outside_eq, SourceSmallCodec.select_eq]
      have hvals : vals = List.ofFn (fun i : Fin S.card => vals.get (Fin.cast hv.symm i)) := by
        apply List.ext_getElem (by simp [hv])
        intro i hi hj
        simp
      exact congrArg some ((congrArg (fun vals => SourceSmallCodec.assemble pad ℓ (SourceSmallCodec.names S) vals
        (List.ofFn (SmallFamilyCodec.select Sᶜ old))) hvals).trans (SourceSmallCodec.assemble_eq pad S _ _))
    · rw [ite_eq_right hv, dite_eq_right hv]
      rfl

abbrev pivotInputEncoding (q : ℕ) := encPair (encPair encUnary rowsEncoding)
  (encPair (recordEncoding q) (wordEncoding q))

private theorem bubblePair_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun p : QWord q × Record q => SourceCoreCheck.bubblePair pad p.1 p.2)
      (encPair (wordEncoding q) (recordEncoding q)) (OrderedCatalogue.bubbleEncoding q) := by
  let w := wordEncoding q
  let r := recordEncoding q
  have hw := fst w r
  have h := (snd w r).snd'.snd'
  have hs := SourceLetters.spell_polyTime pad
  exact (const (encOut := OrderedCatalogue.wordPairEncoding q) ([], [])).prod
    ((hs.comp (hw.prod h.fst')).prod (hs.comp (hw.prod h.snd')))

set_option maxHeartbeats 550000 in
theorem recordHash_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : (ℕ × Rows) × (Record q × QWord q) =>
      recordHash pad b t p.1.1 p.1.2 p.2.1 p.2.2) (pivotInputEncoding q) rowEncoding := by
  let r := recordEncoding q
  let w := wordEncoding q
  let a := encPair encUnary rowsEncoding
  have hp := fst a (encPair r w)
  have hv := snd a (encPair r w)
  let e := pivotInputEncoding q
  have hs := (bubblePair_polyTime pad).comp (encIn := e) (hv.snd'.prod hv.fst')
  have h := (SourceBuckets.vector_polyTime pad b t hq).comp (encIn := e) (hp.fst'.prod hs)
  have hn := (SourceHashChoice.width_polyTime q b t hq).comp (encIn := e) hp.fst'
  have hrun := SourceSpectrum.applyRows_polyTime.comp (encIn := e) (encMid := SourceSpectrum.applyEncoding)
    ((hn.prod hp.snd').prod h)
  exact hrun.of_enc_eq (fun _ => rfl)

abbrev bucketValuesEncoding (q : ℕ) := encPair (encPair encUnary rowsEncoding)
  (encPair (recordEncoding q) rowEncoding)

theorem bucketValues_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : (ℕ × Rows) × (Record q × Row) => bucketValues pad b t p.1.1 p.1.2 p.2.1 p.2.2)
      (bucketValuesEncoding q) (encList (wordEncoding q)) := by
  let r := recordEncoding q
  let m := OrderedCatalogue.bubbleEncoding q
  let w := wordEncoding q
  let a := encPair encUnary rowsEncoding
  have hp := fst a (encPair r rowEncoding)
  have hv := snd a (encPair r rowEncoding)
  have hs := (SourceReplayFamily.shape_polyTime q).comp hv.fst'
  have h := (SourceBuckets.bucket_polyTime pad b t hq).comp ((hp.fst'.prod hs).prod (hp.snd'.prod hv.snd'))
  exact (ComputableInPolyTime.map (fst w m)).comp h

theorem pivotDigit_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : (ℕ × Rows) × (Record q × QWord q) =>
      pivotDigit pad b t p.1.1 p.1.2 p.2.1 p.2.2) (pivotInputEncoding q) encNat := by
  let e := pivotInputEncoding q
  let w := wordEncoding q
  let r := recordEncoding q
  let a := encPair encUnary rowsEncoding
  let u := encPair r w
  have hp := fst a u
  have hv := snd a u
  have hh := recordHash_polyTime pad b t hq
  have hb := (bucketValues_polyTime pad b t hq).comp (hp.prod (hv.fst'.prod hh))
  have hlen := (length_list w).comp hb
  have hs := (SourceReplayFamily.values_polyTime pad).comp (hv.snd'.prod hv.fst'.snd'.snd'.fst')
  have hi := (idxOf?_polyTime ([] : QWord q) w).comp (hb.prod hs)
  have h := optionGetDWithInput hi hlen
  exact (unary_to_binary.comp h).of_enc_eq (fun p => by
    simp [pivotDigit, Function.comp_def, idxOf_eq_getD])

abbrev restoreEncoding (q : ℕ) := encPair (bucketValuesEncoding q) (encPair encNat (wordEncoding q))

theorem restoreWithHash_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : ((ℕ × Rows) × (Record q × Row)) × (ℕ × QWord q) =>
      restoreWithHash pad b t p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2.1 p.2.2)
      (restoreEncoding q) (encOption (wordEncoding q)) := by
  let e := restoreEncoding q
  let w := wordEncoding q
  let r := recordEncoding q
  let a := bucketValuesEncoding q
  have hp := fst a (encPair encNat w)
  have hx := snd a (encPair encNat w)
  have hb := (bucketValues_polyTime pad b t hq).comp hp
  have hn := (length_list w).comp hb
  have hi := binary_to_unary_bounded (binary_min' hx.fst' (unary_to_binary.comp hn)) hn
    (fun _ => Nat.min_le_right ..)
  have hd := ((getElem?_polyTime ([] : QWord q) w).comp (hb.prod hi)).of_enc_eq
    (g := fun p : ((ℕ × Rows) × (Record q × Row)) × (ℕ × QWord q) =>
      (bucketValues pad b t p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2)[p.2.1]?) (fun p => by
      simp only [Function.comp_def]
      by_cases h : p.2.1 < (bucketValues pad b t p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2).length
      · rw [Nat.min_eq_left (Nat.le_of_lt h)]
      · have hle := Nat.le_of_not_gt h
        simp only [Nat.min_eq_right hle, List.getElem?_eq_none hle, List.getElem?_eq_none le_rfl])
  have hsrc := fst e w
  have hv := snd e w
  have hl := hp.fst'.fst'.comp hsrc
  have hkeys := (SourceReplayPayload.keys_polyTime q).comp (hp.snd'.fst'.comp hsrc)
  have hlit := (SourceSmallCodec.outside_polyTime).comp (hl.prod hkeys)
  have hold := (SourceSmallCodec.select_polyTime pad).comp (hlit.prod (hx.snd'.comp hsrc))
  have hout := (SourceSmallCodec.assemble_polyTime pad).comp ((hl.prod hkeys).prod (hv.prod hold))
  have htest := ((length_list (ExceptionalRecords.letterEncoding q)).comp hv).decide_eq'
    ((length_list encUnary).comp hkeys)
  have hresult := htest.ite' ((optionSome w).comp hout) (const none)
  exact optionBindWithInput (f := fun p vals =>
    let keys := SourceReplayPayload.keys p.1.2.1
    if vals.length = keys.length then some (SourceSmallCodec.assemble pad p.1.1.1 keys vals
      (SourceSmallCodec.select pad (SourceSmallCodec.outside p.1.1.1 keys) p.2.2)) else none) hd (hresult.of_enc_eq (fun _ => by
      simp [Function.comp_def]
      rfl))

private def negativeSum (n : ℕ) (rows : Rows) : Row :=
  (List.range n).map fun j => -((rows.map fun row => row.getD j 0).sum)

private theorem negativeSum_polyTime : ComputableInPolyTime
    (fun p : ℕ × Rows => negativeSum p.1 p.2) matrixEncoding rowEncoding := by
  let e := matrixEncoding
  let a := encPair e encUnary
  let h := encPair a rowEncoding
  have hl := fst encUnary rowsEncoding
  have hr := snd encUnary rowsEncoding
  have hx := fst e encUnary
  have hrow := snd a rowEncoding
  have hj := (snd e encUnary).comp (fst a rowEncoding)
  have hv := listGetDWithInput (encIn := h) hrow hj (0 : F₃)
  have hs := mapWithInput (encIn := a) (encA := rowEncoding) (encB := tritEncoding)
    (f := fun p row => row.getD p.2 0) (hr.comp hx) hv
  have hn := (of_finite (encIn := tritEncoding) (encOut := tritEncoding) (fun a : F₃ => -a)).comp
    (tritSum_polyTime.comp (encIn := a) hs)
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := tritEncoding)
    (f := fun p j => -((p.2.map fun row => row.getD j 0).sum)) (unary_range' hl) hn

def neededHash (pad : Fin q) (b t l : ℕ) (H : Rows) (other : List (Record q)) (word : QWord q) : Row :=
  negativeSum H.length (other.map fun record => recordHash pad b t l H record word)

theorem neededHash_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q)
    (H : TernaryMatrix θ (q^gram q b t ℓ)) {d s : ℕ}
    (record : Fin d × Fin s → ReplayGrammar.DecodedEntry q × ReplayEntry.Completed ℓ (Fin q))
    (pivot : Fin d × Fin s) (word : Fin ℓ → Fin q) :
    neededHash pad b t ℓ (matrixRows H)
      (((List.finRange s).filter (· ≠ pivot.2)).map fun j =>
        let p := record (pivot.1,j)
        (decodedData p.1, SourceDictionary.store p.2)) (List.ofFn word) =
      List.ofFn (PeelingBuckets.neededHash (gram q b t ℓ) pad H
        (fun e => ((record e).1.entry,(record e).2)) pivot word) := by
  let ks := (List.finRange s).filter (· ≠ pivot.2)
  have hks : ks.toFinset = Finset.univ.erase pivot.2 := by
    ext i
    simp [ks]
  have hn : ks.Nodup := (List.nodup_finRange s).filter _
  unfold neededHash negativeSum
  rw [show (matrixRows H).length = θ by simp [matrixRows], SourceLists.range_map_eq]
  congr 1
  funext i
  simp only [List.map_map, Function.comp_def, recordHash_eq pad b t hq, BooleanFibres.ofFn_getD]
  unfold PeelingBuckets.neededHash
  simp only [Pi.neg_apply, Finset.sum_apply]
  congr 1
  rw [← List.sum_toFinset _ hn, hks]

abbrev neededEncoding (q : ℕ) := encPair (encPair encUnary rowsEncoding)
  (encPair (encList (recordEncoding q)) (wordEncoding q))

theorem neededHash_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : (ℕ × Rows) × (List (Record q) × QWord q) =>
      neededHash pad b t p.1.1 p.1.2 p.2.1 p.2.2) (neededEncoding q) rowEncoding := by
  let e := neededEncoding q
  let r := recordEncoding q
  let z := encPair (encList r) (wordEncoding q)
  let a := encPair encUnary rowsEncoding
  have hp := fst a z
  have hx := snd a z
  have hf := fst e r
  have hbody := (recordHash_polyTime pad b t hq).comp (encIn := encPair e r) (encMid := pivotInputEncoding q)
    ((hp.comp hf).prod ((snd e r).prod (hx.snd'.comp hf)))
  have hs := mapWithInput (encIn := e) (encA := r) (encB := rowEncoding)
    (f := fun p r => recordHash pad b t p.1.1 p.1.2 r p.2.2) hx.fst' hbody
  have hn := (length_list rowEncoding).comp hp.snd'
  exact negativeSum_polyTime.comp (encIn := e) (encMid := matrixEncoding) (hn.prod hs)

#print axioms recordHash_eq
#print axioms recordHash_polyTime
#print axioms pivotDigit_eq
#print axioms pivotDigit_polyTime
#print axioms restoreWithHash_eq
#print axioms restoreWithHash_polyTime
#print axioms neededHash_eq
#print axioms neededHash_polyTime

end DeletionCode.Explicit.Machine.SourcePeelingBuckets
