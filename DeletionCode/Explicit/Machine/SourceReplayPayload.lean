import DeletionCode.Explicit.Machine.SourcePayloadIndex
import DeletionCode.Explicit.Machine.SourceSmallCodec

/-! One-anchor replay and the small-family compression branch's payload. -/
namespace DeletionCode.Explicit.Machine.SourceReplayPayload

open SourceLists SourceGrammar SourceDescriptionIndex SourcePayloadIndex SourceReplay
open SourceDictionary (store Stored historyData)
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open DeletionCode.Explicit.UniformParameters
open ReplayGrammar
open private samePatch final headerBound header readHeader from DeletionCode.Explicit.ReplayPayload
open private originalNames_eq_activeOrder from DeletionCode.Explicit.ReplayFamily

variable {q ℓ E L b : ℕ}

abbrev Record (q : ℕ) := Decoded q × Stored q
abbrev recordEncoding (q : ℕ) := SourceCoreReplay.materialPairEncoding q

def clearFlags (d : Decoded q) : Decoded q := {d with finalBubble := false, finalRule := false}

def recordData (r : ReplayEntry.Entry (Fin q) × ReplayEntry.Completed ℓ (Fin q)) : Record q :=
  (decodedData ⟨r.1,false,false⟩,store r.2)

def oneAnchor (patch root : ℕ) : Anchors :=
  List.replicate patch none ++ [some root]

theorem oneAnchor_eq (p : ℕ) (root : Fin ℓ) (i : ℕ) :
    anchorAt (oneAnchor p root.val) i =
      (if i = p then some root else none : Option (Fin ℓ)).map Fin.val := by
  unfold anchorAt oneAnchor
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < p
  · simp [List.getElem?_append_left,h,Ne.symm (Nat.ne_of_lt h)]
    omega
  · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt h)]
    by_cases he : i = p
    · simp [he]
    · have hn : 1 ≤ i-p := by omega
      simp [he,List.getElem?_eq_none (l := [some root.val]) (by simpa using hn)]

def marked (ds : List (Decoded q)) : Option (Decoded q) :=
  match ds.filter (·.finalBubble) with
  | [d] => some d
  | _ => none

theorem marked_eq (ds : List (ReplayGrammar.DecodedEntry q)) :
    marked (ds.map decodedData) = (final ds).map decodedData := by
  unfold marked final
  rw [List.filter_map]
  change (match (ds.filter (·.finalBubble)).map decodedData with
    | [d] => some d | _ => none) = _
  cases List.filter (·.finalBubble) ds with
  | nil => rfl
  | cons a as => cases as <;> rfl

def materialize (pad : Fin q) (ℓ E L b : ℕ) (code : Description q) (anchor : ℕ) :
    Option (Record q) := do
  let ds ← SourceGrammar.decodeDescription E L b code
  let d ← marked ds
  if ds.all (fun p => p.patch == d.patch) then
    let ws ← SourceReplay.replay pad ((ℓ,L),oneAnchor d.patch anchor) ds
    let i := (ds.map Decoded.finalBubble).idxOf true
    let w ← ws[i]?
    some (clearFlags d,w)
  else none

theorem materialize_eq (pad : Fin q) (code : DescriptionCode E L b q) (anchor : Fin ℓ) :
    materialize pad ℓ E L b (descriptionData code) anchor.val =
      (ReplayPayload.materialize code anchor).map recordData := by
  unfold materialize ReplayPayload.materialize
  rw [SourceGrammar.decodeDescription_eq]
  cases h : ReplayGrammar.decodeDescription code with
  | none => rfl
  | some ds =>
    simp only [Option.map_some,bind,Option.bind,marked_eq]
    cases hd : final ds with
    | none => rfl
    | some d =>
      simp only [Option.map_some,Option.bind,List.all_map,Function.comp_def,decodedData]
      change (if samePatch d.entry.patch ds then _ else none) =
        (if samePatch d.entry.patch ds then _ else none).map recordData
      by_cases hs : samePatch d.entry.patch ds = true
      · rw [if_pos hs,if_pos hs]
        have hr := replay_eq pad L ds (oneAnchor d.entry.patch anchor.val)
          (fun p => if p = d.entry.patch then some anchor else none) (fun p _ => oneAnchor_eq _ _ _)
        rw [hr]
        cases hw : ReplayEntry.replay L
            (fun p => if p = d.entry.patch then some anchor else none)
            (ds.map (·.entry)) with
        | none => rfl
        | some ws =>
          simp only [Option.map_some,Option.bind,historyData,List.getElem?_map,List.map_map,Function.comp_def]
          change (Option.map store ws.toList[(ds.map ReplayGrammar.DecodedEntry.finalBubble).idxOf true]?).bind _ =
            (ws[(ds.map ReplayGrammar.DecodedEntry.finalBubble).idxOf true]?.bind _).map recordData
          rw [Array.getElem?_toList]
          cases ws[(ds.map ReplayGrammar.DecodedEntry.finalBubble).idxOf true]? <;> rfl
      · rw [if_neg hs,if_neg hs]
        rfl

def keys (r : Record q) : List ℕ := SourceReplayFamily.positions r.2.2.1

theorem keys_eq (d : ReplayGrammar.DecodedEntry q) (v : ReplayEntry.Completed ℓ (Fin q)) :
    keys (decodedData d,store v) = SourceSmallCodec.names (BubbleFamilies.active v.negative.2) := by
  unfold keys store
  rw [SourceReplayFamily.positions_eq,originalNames_eq_activeOrder,List.map_ofFn,SourceSmallCodec.names_eq]
  rfl

def bound (q ℓ E L b : ℕ) : ℕ := descriptionBound E L b q*ℓ

def writeHeader (pad : Fin q) (ℓ E L b : ℕ) (code : Description q) (root : ℕ) : QWord q :=
  writeIndex pad (bound q ℓ E L b) (SourceDescriptionIndex.pack E L b code*ℓ+root)

theorem writeHeader_eq (pad : Fin q) (hq : 2 ≤ q) (c : DescriptionCode E L b q) (anchor : Fin ℓ) :
    writeHeader pad ℓ E L b (descriptionData c) anchor.val =
      List.ofFn (header (by omega) c anchor) := by
  unfold writeHeader header
  rw [pack_eq]
  have h := writeIndex_eq pad hq (finProdFinEquiv (packDescription c,anchor))
  simpa only [bound,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using h

abbrev Header (q : ℕ) := Description q × ℕ × QWord q
abbrev headerEncoding (q : ℕ) := encPair (descriptionEncoding q) (encPair encUnary (wordEncoding q))

def readSmallHeader (pad : Fin q) (ℓ E L b : ℕ) (w : QWord q) : Option (Header q) := do
  let (packed,tail) ← SourcePayloadIndex.readIndex q (bound q ℓ E L b) w
  let c ← SourceDescriptionIndex.unpack pad E L b (packed/ℓ)
  some (c,packed%ℓ,tail)

theorem readSmallHeader_eq (pad : Fin q) (hq : 2 ≤ q) (w : QWord q) :
    readSmallHeader pad ℓ E L b w =
      (readHeader (E := E) (L := L) (b := b) (ℓ := ℓ) w).map
        (fun (c,anchor,tail) => (descriptionData c,anchor.val,tail)) := by
  unfold readSmallHeader readHeader
  rw [SourcePayloadIndex.readIndex_eq]
  change _ = (do
    let (i,rest) ← ReplayPayload.readIndex (bound q ℓ E L b) w
    let (packed,anchor) := finProdFinEquiv.symm i
    let c ← unpackDescription packed
    some (c,anchor,rest)).map (fun (x : DescriptionCode E L b q × Fin ℓ × QWord q) =>
      (descriptionData x.1,x.2.1.val,x.2.2))
  cases h : ReplayPayload.readIndex (bound q ℓ E L b) w with
  | none => rfl
  | some p =>
    obtain ⟨i,tail⟩ := p
    simp only [Option.map_some,bind,Option.bind]
    let pair := finProdFinEquiv.symm i
    change (SourceDescriptionIndex.unpack pad E L b pair.1.val).bind _ = _
    rw [unpack_eq pad hq]
    cases ReplayGrammar.unpackDescription pair.1 <;> rfl

def encode (pad : Fin q) (b t ℓ : ℕ) (code : Description q) (root : ℕ) (x : QWord q) :
    Option (QWord q) := do
  let E := edits t*witnessLimit q b t ℓ
  let L := gram q b t ℓ
  let (d,v) ← materialize pad ℓ E L b code root
  let p ← SourceSmallCodec.encode pad (keys (d,v)) (SourceReplayFamily.assignments pad b t ℓ d v) x
  some (writeHeader pad ℓ E L b code root ++ p)

theorem encode_eq (pad : Fin q) (hq : 2 ≤ q) (b t : ℕ) (x : Fin ℓ → Fin q)
    (c : DescriptionCode (edits t*witnessLimit q b t ℓ) (gram q b t ℓ) b q) (root : Fin ℓ) :
    encode pad b t ℓ (descriptionData c) root.val (List.ofFn x) =
      ReplayPayload.encode (by omega) (windowLength q ℓ) b (gram q b t ℓ)
        (omittedLetters q b t ℓ) pad c root x := by
  unfold encode ReplayPayload.encode
  dsimp only
  rw [materialize_eq]
  cases ReplayPayload.materialize c root with
  | none => rfl
  | some p =>
    obtain ⟨d,v⟩ := p
    simp only [Option.map_some,bind,Option.bind,recordData,keys_eq,SourceReplayFamily.assignments_eq]
    rw [SourceSmallCodec.encode_eq pad hq,writeHeader_eq pad hq]
    cases SmallFamilyCodec.encode (by omega : 1 < q) (BubbleFamilies.active v.negative.2)
      (BubbleFamilies.replayAssignments (windowLength q ℓ) b (gram q b t ℓ)
        (omittedLetters q b t ℓ) pad (d,v)) x <;> rfl

def decode (pad : Fin q) (b t ℓ : ℕ) (w : QWord q) : Option (QWord q) := do
  let E := edits t*witnessLimit q b t ℓ
  let L := gram q b t ℓ
  let (c,root,tail) ← readSmallHeader pad ℓ E L b w
  let (d,v) ← materialize pad ℓ E L b c root
  let s := keys (d,v)
  let members := SourceReplayFamily.assignments pad b t ℓ d v
  let (r,_) ← SourcePayloadIndex.split (Nat.clog q (SourceSmallCodec.bound q ℓ s members)) tail
  SourceSmallCodec.decode pad ℓ s members r

theorem decode_eq (pad : Fin q) (hq : 2 ≤ q) (b t ℓ : ℕ) (w : QWord q) :
    decode pad b t ℓ w =
      (ReplayPayload.decode ℓ (edits t*witnessLimit q b t ℓ) (windowLength q ℓ) b (gram q b t ℓ)
        (omittedLetters q b t ℓ) pad w).map List.ofFn := by
  unfold decode ReplayPayload.decode
  dsimp only
  rw [readSmallHeader_eq pad hq]
  cases readHeader (E := edits t*witnessLimit q b t ℓ) (L := gram q b t ℓ) (b := b) (ℓ := ℓ) w with
  | none => rfl
  | some h =>
    obtain ⟨c,root,tail⟩ := h
    simp only [Option.map_some,bind,Option.bind]
    rw [materialize_eq]
    cases ReplayPayload.materialize c root with
    | none => rfl
    | some p =>
      obtain ⟨d,v⟩ := p
      simp only [Option.map_some,Option.bind,recordData,keys_eq,SourceReplayFamily.assignments_eq,
        SourceSmallCodec.bound,SourceSmallCodec.outside_eq,SourceSmallCodec.names_length,List.length_map]
      rw [split_eq]
      simp only [SmallFamilyCodec.payloadLength]
      cases ReplayPayload.readPrefix (Nat.clog q
          (q^(BubbleFamilies.active v.negative.2)ᶜ.card *
            (BubbleFamilies.replayAssignments (windowLength q ℓ) b (gram q b t ℓ)
              (omittedLetters q b t ℓ) pad (d,v)).length)) tail with
      | none => rfl
      | some p =>
        obtain ⟨data,rest⟩ := p
        exact SourceSmallCodec.decode_eq pad hq _ _ data

abbrev grammarInput (q : ℕ) := encPair encUnary (encPair sizesEncoding (encPair (descriptionEncoding q) encUnary))

private theorem anchor_polyTime :
    ComputableInPolyTime (fun x : ℕ × ℕ => oneAnchor x.1 x.2)
      (encPair encUnary encUnary) anchorsEncoding := by
  let a := encOption encUnary
  have hs := (optionSome encUnary).comp (snd encUnary encUnary)
  have ht := cons' hs (const (encOut := anchorsEncoding) [])
  have hu := replicate (encA := a) (fst encUnary encUnary) (const none)
  exact listAppend' hu ht

theorem marked_polyTime (q : ℕ) :
    ComputableInPolyTime (marked (q := q)) (decodedListEncoding q) (encOption (decodedEncoding q)) := by
  let e := decodedListEncoding q
  let d := decodedEncoding q
  let fallback : Decoded q := ⟨0,0,0,0,[],[],[],false,false⟩
  have hf := filterWithInput (encIn := e) (encA := d) (test := fun _ (x : Decoded q) => x.finalBubble)
    id' (decodedEncoding_finalBubble_polyTime q (snd e d))
  have hn := (length_list d).comp hf
  have h := (hn.decide_eq' (const 1)).ite'
    ((optionSome d).comp (listGetDWithInput hf (const 0) fallback)) (const none)
  exact h.of_enc_eq (fun x => by
    apply congrArg (encOption d)
    unfold marked
    simp only [Function.comp_def,decide_eq_true_eq]
    change _ = if (x.filter (·.finalBubble)).length = 1 then
      some ((x.filter (·.finalBubble)).getD 0 fallback) else none
    cases x.filter (·.finalBubble) with
    | nil => rfl
    | cons a xs => cases xs <;> rfl)

abbrev replayMarkedEncoding (q : ℕ) :=
  encPair (encPair (encPair encUnary encUnary) encUnary)
    (encPair (decodedListEncoding q) (decodedEncoding q))

private theorem idxTrue_polyTime :
    ComputableInPolyTime (fun xs : List Bool => xs.idxOf true)
      PatchGraph.flagsEncoding encUnary := by
  let e := PatchGraph.flagsEncoding
  have hf := (idxOf?_polyTime false encBool).comp ((id' (encIn := e)).prod (const true))
  exact (optionElimWithInput (encA := e) (encB := encUnary) (encC := encUnary)
    (body := fun _ i => i) hf (length_list encBool) (snd e encUnary)).of_enc_eq (fun x => by
      rw [idxOf_eq_getD]
      simp only [Function.comp_def]
      cases x.idxOf? true <;> rfl)

private def replayMarked (pad : Fin q) (ℓ L root : ℕ) (ds : List (Decoded q)) (d : Decoded q) :
    Option (Record q) :=
  if ds.all (fun p => p.patch == d.patch) then
    (SourceReplay.replay pad ((ℓ,L),oneAnchor d.patch root) ds).bind fun ws =>
      (ws[(ds.map Decoded.finalBubble).idxOf true]?).map (fun w => (clearFlags d,w))
  else none

private theorem replayMarked_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : ((ℕ × ℕ) × ℕ) × (List (Decoded q) × Decoded q) =>
      replayMarked pad x.1.1.1 x.1.1.2 x.1.2 x.2.1 x.2.2)
      (replayMarkedEncoding q) (encOption (recordEncoding q)) := by
  let c := encPair (encPair encUnary encUnary) encUnary
  let d := decodedEncoding q
  let ds := decodedListEncoding q
  let e := replayMarkedEncoding q
  let h := SourceDictionary.historyEncoding q
  let r := recordEncoding q
  have hf := fst c (encPair ds d)
  have hp := snd c (encPair ds d)
  have hd := decodedEncoding_patch_polyTime q hp.snd'
  let a := encPair e d
  have hsame := allWithInput (encIn := e) (encA := d) (test := fun x z => z.patch == x.2.2.patch)
    hp.fst' ((decodedEncoding_patch_polyTime q (snd e d)).decide_eq' (hd.comp (fst e d)))
  have hroots := anchor_polyTime.comp (hd.prod hf.snd')
  have hrun := (SourceReplay.replay_polyTime pad).comp ((hf.fst'.prod hroots).prod hp.fst')
  have hm := mapWithInput (encIn := e) (encA := d) (encB := encBool)
    (f := fun _ x => x.finalBubble) hp.fst' (decodedEncoding_finalBubble_polyTime q (snd e d))
  have hi := idxTrue_polyTime.comp hm
  have hread := (getElem?_polyTime ((0,([],[])) : Stored q) (SourceDictionary.storedEncoding q)).comp
    ((snd e h).prod (hi.comp (fst e h)))
  have hc := decodedEncoding_mk_polyTime q
    (decodedEncoding_rule_polyTime q hp.snd') hd (decodedEncoding_left_polyTime q hp.snd')
    (decodedEncoding_right_polyTime q hp.snd') (decodedEncoding_removed_polyTime q hp.snd')
    (decodedEncoding_replacement_polyTime q hp.snd') (decodedEncoding_refs_polyTime q hp.snd')
    (const false) (const false)
  have hc' : ComputableInPolyTime (fun x : ((ℕ × ℕ) × ℕ) × (List (Decoded q) × Decoded q) =>
      clearFlags x.2.2) e d := hc
  have hout := optionMapWithInput (encA := encPair e h) (encB := SourceDictionary.storedEncoding q) (encC := r)
    (f := fun x z => (clearFlags x.1.2.2,z)) hread
    ((hc'.comp ((fst e h).comp (fst (encPair e h) (SourceDictionary.storedEncoding q)))).prod
      (snd (encPair e h) (SourceDictionary.storedEncoding q)))
  have hb := optionBindWithInput (ea := e) (eb := h) (ec := r)
    (f := fun x ws => (ws[(x.2.1.map Decoded.finalBubble).idxOf true]?).map
      (fun v => (clearFlags x.2.2,v))) hrun (hout.of_enc_eq (fun _ => rfl))
  exact (hsame.ite' hb (const none)).of_enc_eq (fun _ => rfl)

theorem materialize_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : ℕ × ((ℕ × (ℕ × ℕ)) × (Description q × ℕ)) =>
      materialize pad x.1 x.2.1.1 x.2.1.2.1 x.2.1.2.2 x.2.2.1 x.2.2.2)
      (grammarInput q) (encOption (recordEncoding q)) := by
  let e := grammarInput q
  let code := descriptionEncoding q
  let ds := decodedListEncoding q
  let d := decodedEncoding q
  let data := encPair sizesEncoding (encPair code encUnary)
  let a := encPair e ds
  have hl := fst encUnary data
  have hp := snd encUnary data
  have hc := (SourceGrammar.decodeDescription_polyTime q).comp (hp.fst'.prod hp.snd'.fst')
  have hg := (marked_polyTime q).comp (snd e ds)
  let k := encPair a d
  have hx := (fst e ds).comp (fst a d)
  have hf := hp.comp hx
  have harg := (((hl.comp hx).prod hf.fst'.snd'.fst').prod hf.snd'.snd').prod
    (((snd e ds).comp (fst a d)).prod (snd a d))
  have hf' := (replayMarked_polyTime pad).comp (encIn := k) harg
  have hm := optionBindWithInput (ea := a) (eb := d) (ec := recordEncoding q)
    (f := fun x d => replayMarked pad x.1.1 x.1.2.1.2.1 x.1.2.2.2 x.2 d)
    hg (hf'.of_enc_eq (fun _ => rfl))
  exact (optionBindWithInput (ea := e) (eb := ds) (ec := recordEncoding q)
    (f := fun x ds => (marked ds).bind fun d =>
      replayMarked pad x.1 x.2.1.2.1 x.2.2.2 ds d) hc hm).of_enc_eq (fun x => by
    apply congrArg (encOption (recordEncoding q))
    dsimp only [materialize,Function.comp_def]
    cases SourceGrammar.decodeDescription x.2.1.1 x.2.1.2.1 x.2.1.2.2 x.2.2.1 <;>
      simp [Option.map_eq_bind,bind,Option.bind,replayMarked,Function.comp_def])

abbrev headerInput (q : ℕ) := encPair (encPair encUnary sizesEncoding) (wordEncoding q)

theorem readSmallHeader_polyTime (pad : Fin q) (hq : 2 ≤ q) (b : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × (ℕ × (ℕ × ℕ))) × QWord q =>
      readSmallHeader pad x.1.1 x.1.2.1 x.1.2.2.1 b x.2)
      (headerInput q) (encOption (headerEncoding q)) := by
  let w := wordEncoding q
  let a := encPair encUnary sizesEncoding
  let e := headerInput q
  let h := readEncoding q
  let dc := descriptionEncoding q
  let p := encPair e h
  have hp := fst a w
  have hl := hp.fst'
  have hD := (descriptionBound_polyTime q b).comp (hp.snd'.fst'.prod hp.snd'.snd'.fst')
  have hcap := binary_mul' hD (unary_to_binary.comp hl)
  have hi := (readIndex_polyTime q hq).comp (hcap.prod (snd a w))
  have hx := fst e h
  have hz := snd e h
  have hl' := hl.comp hx
  have hb := unary_to_binary.comp hl'
  have hrem := binary_mod' hz.fst' hb
  have hroot := binary_to_unary_bounded (binary_min' hrem hb) hl' (fun _ => Nat.min_le_right ..)
  have hcode := (unpack_polyTime pad).comp (((hp.snd'.fst'.comp hx).prod
    ((hp.snd'.snd'.fst'.comp hx).prod (const b))).prod (binary_div' hz.fst' hb))
  let p' := encPair p dc
  have hout := optionMapWithInput (encA := p) (encB := dc) (encC := headerEncoding q)
    (f := fun x c => (c,min (x.2.1%x.1.1.1) x.1.1.1,x.2.2)) hcode
    ((snd p dc).prod ((hroot.comp (fst p dc)).prod (hz.snd'.comp (fst p dc))))
  have htotal := optionBindWithInput
    (f := fun x v =>
      (unpack pad x.1.2.1 x.1.2.2.1 b (v.1/x.1.1)).map
        (fun c => (c,min (v.1%x.1.1) x.1.1,v.2))) hi hout
  refine htotal.of_enc_eq ?_
  intro x
  have hr := SourcePayloadIndex.readIndex_bound q (bound q x.1.1 x.1.2.1 x.1.2.2.1 b) x.2
  unfold readSmallHeader
  simp only [Function.comp_def] at *
  cases he : SourcePayloadIndex.readIndex q (bound q x.1.1 x.1.2.1 x.1.2.2.1 b) x.2 with
  | none => simp [bound] at he; simp [he,bind,Option.bind]
  | some p =>
    have hs := hr p he
    have hl : 0 < x.1.1 := by
      by_contra! h
      simpa [bound,Nat.eq_zero_of_le_zero h] using hs
    have hm := Nat.min_eq_left (Nat.mod_lt p.1 hl).le
    unfold bound at he
    simp only [Function.comp_def,he,bind,Option.bind,hm]
    cases unpack pad x.1.2.1 x.1.2.2.1 b (p.1/x.1.1) <;> rfl

theorem keys_polyTime (q : ℕ) : ComputableInPolyTime (keys (q := q))
    (recordEncoding q) SourceSmallCodec.keyEncoding :=
  (SourcePrepare.positions_polyTime q).comp
    (snd (decodedEncoding q) (SourceDictionary.storedEncoding q)).snd'.fst'

abbrev headerWriter (q : ℕ) := encPair (encPair encUnary sizesEncoding) (encPair (descriptionEncoding q) encUnary)

theorem writeHeader_polyTime (pad : Fin q) (hq : 2 ≤ q) (b : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × (ℕ × (ℕ × ℕ))) × (Description q × ℕ) =>
      writeHeader pad x.1.1 x.1.2.1 x.1.2.2.1 b x.2.1 x.2.2)
      (headerWriter q) (wordEncoding q) := by
  let e := headerWriter q
  let ds := descriptionEncoding q
  let s := encPair encUnary sizesEncoding
  have hp := fst s (encPair ds encUnary)
  have hx := snd s (encPair ds encUnary)
  have hE := hp.snd'.fst'
  have hL := hp.snd'.snd'.fst'
  have hl := unary_to_binary.comp hp.fst'
  have hr := unary_to_binary.comp hx.snd'
  have hb := (descriptionBound_polyTime q b).comp (hE.prod hL)
  have hc := (pack_polyTime q hq).comp ((hE.prod (hL.prod (const b))).prod hx.fst')
  exact (writeIndex_polyTime pad hq).comp ((binary_mul' hb hl).prod (binary_add' (binary_mul' hc hl) hr))

private theorem uniformSizes_polyTime (q b t : ℕ) :
    ComputableInPolyTime (fun l => (l,edits t*witnessLimit q b t l,gram q b t l,b))
      encUnary (encPair encUnary sizesEncoding) := by
  have hD := unary_add' (unary_mul' (const (8*edits t))
    (Machine.UniformParameters.cutoff_machine q b t)) (const 1)
  exact id'.prod ((unary_mul' (const (edits t)) hD).prod
    ((Machine.UniformParameters.gram_machine q b t).prod (const b)))

abbrev encodeInput (q : ℕ) := encPair (encPair encUnary (encPair (descriptionEncoding q) encUnary)) (wordEncoding q)

theorem encode_polyTime (pad : Fin q) (hq : 2 ≤ q) (b t : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × (Description q × ℕ)) × QWord q =>
      encode pad b t x.1.1 x.1.2.1 x.1.2.2 x.2) (encodeInput q) (encOption (wordEncoding q)) := by
  let e := encodeInput q
  let w := wordEncoding q
  let r := recordEncoding q
  let p := encPair encUnary (encPair (descriptionEncoding q) encUnary)
  let a := encPair e r
  have hf := fst p w
  have hx := fst e r
  have hr := snd e r
  have hs := (uniformSizes_polyTime q b t).comp hf.fst'
  have hhead := (writeHeader_polyTime pad hq b).comp (hs.prod hf.snd')
  have hm := (materialize_polyTime pad).comp (hs.fst'.prod (hs.snd'.prod hf.snd'))
  have hkeys := (keys_polyTime q).comp hr
  have hmem := (SourceReplayFamily.assignments_polyTime pad b t hq).comp ((hf.fst'.comp hx).prod hr)
  have henc := (SourceSmallCodec.encode_polyTime pad hq).comp ((hkeys.prod hmem).prod ((snd p w).comp hx))
  have hb := optionMapWithInput (encA := a) (encB := w) (encC := w)
    (f := fun x z => writeHeader pad x.1.1.1 (edits t*witnessLimit q b t x.1.1.1)
      (gram q b t x.1.1.1) b x.1.1.2.1 x.1.1.2.2 ++ z)
    henc (listAppend' (hhead.comp (hx.comp (fst a w))) (snd a w))
  have h := optionBindWithInput (ea := e) (eb := r) (ec := w)
    (f := fun x r => (SourceSmallCodec.encode pad (keys r)
      (SourceReplayFamily.assignments pad b t x.1.1 r.1 r.2) x.2).map (fun z =>
        writeHeader pad x.1.1 (edits t*witnessLimit q b t x.1.1) (gram q b t x.1.1)
          b x.1.2.1 x.1.2.2 ++ z)) hm hb
  exact h.of_enc_eq (fun x => by
    apply congrArg (encOption w)
    simp only [encode,Function.comp_def,Option.map_eq_bind,bind,Option.bind])

abbrev decodeInput (q : ℕ) := encPair encUnary (wordEncoding q)
abbrev memberPayloadInput (q : ℕ) := encPair encUnary (encPair (wordEncoding q) (recordEncoding q))

private def decodeMember (pad : Fin q) (b t ℓ : ℕ) (rest : QWord q) (r : Record q) :
    Option (QWord q) :=
  let s := keys r
  let members := SourceReplayFamily.assignments pad b t ℓ r.1 r.2
  (SourcePayloadIndex.split (Nat.clog q (SourceSmallCodec.bound q ℓ s members)) rest).bind
    (fun p => SourceSmallCodec.decode pad ℓ s members p.1)

private theorem decodeMember_polyTime (pad : Fin q) (hq : 2 ≤ q) (b t : ℕ) :
    ComputableInPolyTime (fun x : ℕ × (QWord q × Record q) => decodeMember pad b t x.1 x.2.1 x.2.2)
      (memberPayloadInput q) (encOption (wordEncoding q)) := by
  let w := wordEncoding q
  let r := recordEncoding q
  let e := memberPayloadInput q
  let s := splitOutput q
  have hl := fst encUnary (encPair w r)
  have hr := snd encUnary (encPair w r)
  have hk := (keys_polyTime q).comp hr.snd'
  have hm := (SourceReplayFamily.assignments_polyTime pad b t hq).comp (hl.prod hr.snd')
  have hpack := (hl.prod hk).prod hm
  have hb := (SourceSmallCodec.bound_polyTime q).comp hpack
  have hn := (SourceMixedRadix.widthAt_polyTime q).comp hb
  have hs := (split_polyTime q).comp (hn.prod hr.fst')
  have hd := (SourceSmallCodec.decode_polyTime pad hq).comp
    ((hpack.comp (fst e s)).prod (snd e s).fst')
  have h := optionBindWithInput (ea := e) (eb := s) (ec := w)
    (f := fun x p => SourceSmallCodec.decode pad x.1 (keys x.2.2)
      (SourceReplayFamily.assignments pad b t x.1 x.2.2.1 x.2.2.2) p.1)
    hs (hd.of_enc_eq (fun _ => rfl))
  exact h.of_enc_eq (fun x => by
    unfold decodeMember
    simp only [Function.comp_def,SourceMixedRadix.widthAt_eq hq]
    rfl)

theorem decode_polyTime (pad : Fin q) (hq : 2 ≤ q) (b t : ℕ) :
    ComputableInPolyTime (fun x : ℕ × QWord q => decode pad b t x.1 x.2)
      (decodeInput q) (encOption (wordEncoding q)) := by
  let w := wordEncoding q
  let e := decodeInput q
  let h := headerEncoding q
  let r := recordEncoding q
  let a := encPair e h
  have hs := (uniformSizes_polyTime q b t).comp (fst encUnary w)
  have hh := (readSmallHeader_polyTime pad hq b).comp (hs.prod (snd encUnary w))
  have hg := hs.comp (fst e h)
  have hp := snd e h
  have hm := (materialize_polyTime pad).comp (hg.fst'.prod (hg.snd'.prod (hp.fst'.prod hp.snd'.fst')))
  have hx := ((fst encUnary w).comp (fst e h)).comp (fst a r)
  have hd := (decodeMember_polyTime pad hq b t).comp
    (hx.prod ((hp.snd'.snd'.comp (fst a r)).prod (snd a r)))
  have hb := optionBindWithInput (ea := a) (eb := r) (ec := w)
    (f := fun x r => decodeMember pad b t x.1.1 x.2.2.2 r) hm (hd.of_enc_eq (fun _ => rfl))
  have h := optionBindWithInput (ea := e) (eb := h) (ec := w)
    (f := fun x p => (materialize pad x.1 (edits t*witnessLimit q b t x.1) (gram q b t x.1) b p.1 p.2.1).bind
      (decodeMember pad b t x.1 p.2.2)) hh hb
  exact h.of_enc_eq (fun x => by
    apply congrArg (encOption w)
    simp only [decode,Function.comp_def,bind,Option.bind]
    cases readSmallHeader pad x.1 (edits t*witnessLimit q b t x.1) (gram q b t x.1) b x.2 with
    | none => rfl
    | some p =>
      obtain ⟨c,root,tail⟩ := p
      cases materialize pad x.1 (edits t*witnessLimit q b t x.1) (gram q b t x.1) b c root <;> rfl)

#print axioms encode_polyTime
#print axioms decode_polyTime

#print axioms materialize_polyTime
#print axioms readSmallHeader_polyTime
#print axioms materialize_eq
#print axioms writeHeader_eq
#print axioms readSmallHeader_eq
#print axioms encode_eq
#print axioms decode_eq

end DeletionCode.Explicit.Machine.SourceReplayPayload
