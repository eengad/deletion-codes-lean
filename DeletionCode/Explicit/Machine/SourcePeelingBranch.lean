import DeletionCode.Explicit.Machine.SourcePeelingFrame
import DeletionCode.Explicit.Machine.SourcePeelingPayload
import DeletionCode.Explicit.Machine.SourcePeel
import DeletionCode.Explicit.Machine.SourceSmallBranch
import DeletionCode.Explicit.PeelingCompression
import Batteries.Tactic.OpenPrivate

/-! Run the concrete reverse-peeling compressor and inverse on serialized data. -/
namespace DeletionCode.Explicit.Machine.SourcePeelingBranch

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Ternary CataloguePrefix SourceGrammar SourcePeelingFrame SourceLists
open _root_.DeletionCode.Explicit.UniformParameters
open Recognizer LetterGraphCuts RulePatch
open private number_left from DeletionCode.Explicit.Machine.PatchGraph
open private isSmall_eq isSmall_polyTime from DeletionCode.Explicit.Machine.SourceSmallBranch
set_option maxHeartbeats 500000

variable {q l s : ℕ}

private abbrev WitnessInput (q : ℕ) := SourceSmallBranch.WitnessInput q × Rows
private abbrev witnessEncoding (q : ℕ) := encPair (SourceSmallBranch.witnessEncoding q) rowsEncoding

private def compactStarts (pad : Fin q) (history : SourceRecognition.History q) (root : ℕ) : List ℕ :=
  (PatchGraph.patchIds (SourceRecognition.graph pad history) root).map fun j =>
    (SourceWitness.patchStarts pad history).getD j 0

private theorem compactStarts_eq (pad : Fin q) (h : 0 < l)
    (hs : History l q (gram q b t l) s) (root : RuleVertex hs) (p : ℕ) :
    (compactStarts pad (SourceRecognition.historyData hs) (PatchGraph.vertexNumber root)).getD p 0 =
      ((witnessAnchor hs root p).getD ⟨0,h⟩).val := by
  let a := PatchTable.incidence (gates hs)
  let S := componentPatches a root
  unfold compactStarts
  rw [SourceRecognition.graph_eq, PatchGraph.patchIds_eq, SourceWitness.filter_finRange_eq_sort]
  have he : (S.sort.map Fin.val).map (fun j => (SourceWitness.patchStarts pad
    (SourceRecognition.historyData hs)).getD j 0) =
      List.ofFn (fun i : Fin S.card => (patchAnchor hs (originalPatch a root i).val).val) := by
    change (SourceSmallCodec.names S).map _ = _
    rw [SourceSmallCodec.names_eq S, List.map_ofFn]
    congr 1
    funext i
    exact SourceWitness.patchStarts_eq pad hs _
  change ((S.sort.map Fin.val).map _).getD p 0 = _
  rw [he]
  unfold witnessAnchor
  by_cases hp : p < S.card
  · rw [dite_eq_left hp, Option.getD_some]
    exact BooleanFibres.ofFn_getD _ ⟨p,hp⟩ 0
  · rw [dite_eq_right hp, Option.getD_none]
    simp [List.getD_eq_getElem?_getD, hp]

private def rootTable (E : ℕ) (keys starts : List ℕ) : SourceReplay.Anchors :=
  (List.range E).map fun j => if keys.contains j then some (starts.getD j 0) else none

private theorem rootTable_eq {E : ℕ} (P : Finset (Fin E)) (roots : ↥P → Fin l)
    (starts : List ℕ) (h : ∀ j : ↥P, starts.getD j.val.val 0 = (roots j).val) :
    rootTable E (P.sort.map Fin.val) starts = anchorsData P roots := by
  unfold rootTable anchorsData
  rw [SourceLists.range_map_eq]
  congr 1
  funext j
  have hj : (P.sort.map Fin.val).contains j.val = decide (j ∈ P) := by
    apply Bool.eq_iff_iff.mpr
    change (SourceSmallCodec.names P).contains j.val = true ↔ _
    rw [List.contains_iff_mem, SourceSmallCodec.names_mem_iff, decide_eq_true_eq]
  rw [hj]
  unfold CoreWeight.anchorLookup
  rw [dite_eq_left j.isLt]
  by_cases hm : j ∈ P
  · simp only [hm, decide_true, ite_true, dite_true, Option.map_some]
    exact congrArg some (h ⟨j,hm⟩)
  · simp [hm]

private def peelInput (l s d : ℕ) (rows : Rows) (records : Records q) : SourcePeelingPayload.Input q :=
  ⟨l,s,rows,records,(SourcePeel.run (programGraph d s records) s).1⟩

private theorem peelInput_eq {d θ : ℕ} (H : FieldHash.TernaryMatrix θ (q^gram q b t l))
    (p : PeelingFrame.Program l q d s) (hp : ∀ e, (p.record e).1.patch = (p.incidence e).val) :
    peelInput l s d (matrixRows H) (programRecords p) =
      ⟨l,s,matrixRows H,SourcePeelingPayload.recordsData p.record,SourcePeelingPayload.traceData (PeelingFrame.trace p)⟩ := by
  unfold peelInput
  rw [programGraph_eq p hp, SourcePeel.run_eq]
  rfl

private def allLarge (pad : Fin q) (b t l : ℕ) (rs : Records q) (trace : List ℕ) : Bool :=
  trace.all (fun i => !SourceSmallBranch.isSmall pad b t l (SourcePeelingPayload.recordAt rs i))

private theorem allLarge_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hl : minLength q b t ≤ l) {d : ℕ} (p : PeelingFrame.Program l q d s) :
    allLarge pad b t l (programRecords p) (SourcePeelingPayload.traceData (PeelingFrame.trace p)) =
      (PeelingFrame.trace p).all (fun e => !SmallCompression.isSmall (b := b) (t := t) pad (p.record e)) := by
  unfold allLarge SourcePeelingPayload.traceData
  rw [List.all_map]
  apply List.all_congr rfl
  intro e
  change (!SourceSmallBranch.isSmall pad b t l
    (SourcePeelingPayload.recordAt (SourcePeelingPayload.recordsData p.record) (finProdFinEquiv e).val)) = _
  rw [SourcePeelingPayload.recordAt_eq]
  obtain ⟨entry,v⟩ := p.record e
  exact congrArg Bool.not (isSmall_eq pad b t hq hb ht hl ⟨entry,false,false⟩ v)

private theorem flags_all_eq (S : Finset (Fin l)) :
    ((SourceSlice.flags S).all (!·)) = decide (S = ∅) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true]
  constructor
  · intro h
    apply decide_eq_true
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hm : decide (i ∈ S) ∈ SourceSlice.flags S := List.mem_ofFn.mpr ⟨i,rfl⟩
    simpa [hi] using h _ hm
  · intro h a ha
    have he : S = ∅ := of_decide_eq_true h
    subst S
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    simp

private def packProgram (pad : Fin q) (b t l d : ℕ) (rows : Rows) (records : Records q)
    (code : Description q) (roots : List ℕ) (word : QWord q) : Option (QWord q) :=
  let state := SourcePeel.run (programGraph d (edits t) records) (edits t)
  if state.2.all (!·) && allLarge pad b t l records state.1 then
    (SourcePeelingPayload.encode pad b t ⟨l,edits t,rows,records,state.1⟩ word).map
      (fun payload => writeHeader pad b t l d code roots ++ payload)
  else none

private def packCode (pad : Fin q) (b t l d : ℕ) (rows : Rows) (code : Description q)
    (starts : List ℕ) (word : QWord q) : Option (QWord q) := do
  let E := edits t*d
  let L := gram q b t l
  let ds ← SourceGrammar.decodeDescription E L b code
  let keys := SourceCoreReplay.patchKeys E ds
  let rs ← materialize pad l L (edits t) d ds (rootTable E keys starts)
  packProgram pad b t l d rows rs code (keys.map (fun j => starts.getD j 0)) word

private def packWitness (pad : Fin q) (b t : ℕ) (x : WitnessInput q) : Option (QWord q) := do
  let (l, root, word, history) := x.1
  let s := edits t
  let graph := SourceRecognition.graph pad history
  let rules := PatchGraph.ruleIds graph root
  let d := rules.length
  if d ≤ witnessLimit q b t l then
    let ids := SourceWitness.retainedIds graph s root
    let es := SourceWitness.entries pad s root word history
    let ds := SourceWitness.describe es rules ids ids
    let c ← SourceGrammar.encodeDescription pad (s*d) (gram q b t l) b ds
    packCode pad b t l d x.2 c (compactStarts pad history root) word
  else none

def encode (pad : Fin q) (b t : ℕ) (input : SourceAcceptance.Input q) : Option (QWord q) := do
  let (l, rows, word) := input
  if 0 < l ∧ minLength q b t ≤ l ∧ AcceptanceWeights.strong pad b t l word = true then
    let out ← SourceRecognition.recognize pad b t (l, rows, word)
    let first ← out.1
    packWitness pad b t ((l, first, word, out.2), rows)
  else none

private def readProgram (pad : Fin q) (b t l : ℕ) (rows : Rows) (h : Header q) : Option (QWord q) := do
  let rs ← materialize pad l (gram q b t l) (edits t) h.count h.entries h.roots
  SourcePeelingPayload.decodePrefix pad b t (peelInput l (edits t) h.count rows rs) h.tail

def decode (pad : Fin q) (b t : ℕ) (input : SourceAcceptance.Input q) : Option (QWord q) :=
  (readHeader pad b t input.1 input.2.2).bind (readProgram pad b t input.1 input.2.1)

private theorem packCode_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hl : minLength q b t ≤ l) (hp : 0 < l) (H : ConcreteSource.Hash q b t l)
    (word : Fin l → Fin q) (d : Fin (witnessLimit q b t l+1))
    (code : ReplayGrammar.DescriptionCode (edits t*d.val) (gram q b t l) b q)
    (ds : List (ReplayGrammar.DecodedEntry q)) (hc : ReplayGrammar.decodeDescription code = some ds)
    (p : PeelingFrame.Program l q d.val (edits t)) (roots : ℕ → Fin l) (starts : List ℕ)
    (hs : ∀ j, starts.getD j 0 = (roots j).val)
    (hm : PeelingFrame.materialize d ds (fun j => roots j.val.val) (gram q b t l) = some p) :
    packCode pad b t l d.val (matrixRows H) (descriptionData code) starts (List.ofFn word) =
      if core p.incidence = ∅ ∧ (PeelingFrame.trace p).all
        (fun e => !SmallCompression.isSmall (b := b) (t := t) pad (p.record e)) = true then
        PeelingFrame.encode (by omega) hp (windowLength q l) b (gram q b t l) (omittedLetters q b t l)
          pad d code roots H word
      else none := by
  let P := CoreWeight.patchKeys (edits t*d.val) ds
  unfold packCode PeelingFrame.encode
  dsimp only
  rw [decodeDescription_eq,hc]
  simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
  rw [SourceCoreReplay.patchKeys_eq]
  rw [rootTable_eq P (fun j => roots j.val.val) starts (fun j => hs _)]
  rw [materialize_eq pad _ d ds _ _ (fun e _ => anchorsData_at P (fun j => roots j.val.val) e.entry.patch), hm]
  simp only [Option.map_some,Option.bind_some]
  have hroots : (P.sort.map Fin.val).map (fun j => starts.getD j 0) =
      List.ofFn (fun i : Fin P.card => (roots (P.orderIsoOfFin rfl i).val.val).val) := by
    change (SourceSmallCodec.names P).map _ = _
    rw [SourceSmallCodec.names_eq P,List.map_ofFn]
    congr 1
    funext i
    exact hs _
  unfold packProgram
  dsimp only
  rw [hroots, programGraph_eq p (materialize_patch hm), SourcePeel.run_eq]
  change (if (SourceSlice.flags (core p.incidence)).all (!·) &&
      allLarge pad b t l (programRecords p) (SourcePeelingPayload.traceData (PeelingFrame.trace p)) then _ else none) = _
  rw [flags_all_eq, allLarge_eq pad b t hq hb ht hl]
  have hwrite := writeHeader_eq pad b t hq hp d code ds (fun j => roots j.val.val)
  dsimp only at hwrite
  by_cases hcore : core p.incidence = ∅ <;>
    cases hlarge : (PeelingFrame.trace p).all (fun e => !SmallCompression.isSmall (b := b) (t := t) pad (p.record e)) <;>
    simp only [hcore, hlarge, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_eq_true,
      and_true, and_false, true_and, false_and, ↓reduceIte]
  change (SourcePeelingPayload.encode pad b t
      ⟨l,edits t,matrixRows H,SourcePeelingPayload.recordsData p.record,
        SourcePeelingPayload.traceData (PeelingFrame.trace p)⟩ (List.ofFn word)).map
      (fun payload => writeHeader pad b t l d.val (descriptionData code)
        (List.ofFn fun i : Fin P.card => (roots (P.orderIsoOfFin rfl i).val.val).val) ++ payload) = _
  rw [SourcePeelingPayload.encode_eq pad b t hq]
  erw [hwrite]
  cases PeelingPayload.encode _ _ _ _ _ _ _ _ _ _ <;> rfl

private theorem packWitness_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hl : minLength q b t ≤ l) (hp : 0 < l) (H : ConcreteSource.Hash q b t l)
    (word : Fin l → Fin q) (hs : History l q (gram q b t l) (edits t)) (i : Fin hs.length)
    (hx : LetterSequence.Strong word (windowLength q l) (omittedLetters q b t l))
    (hr : ConcreteSource.runAt pad H word = some (.firstEvent hs i)) :
    packWitness pad b t ((l, i.val, List.ofFn word, SourceRecognition.historyData hs),matrixRows H) =
      PeelingCompression.packWitness (by omega) hp pad H word hs i := by
  let a := PatchTable.incidence (gates hs)
  let root : RuleVertex hs := .inl i
  let T := retainedEntries hs root
  let R := componentRules a root
  let D := witnessLimit q b t l
  let p := fullProgram hs i word
  let roots := fun j => (witnessAnchor hs root j).getD ⟨0,hp⟩
  have hbasic := basicBounds hq hb ht hl
  obtain ⟨out, ho, hv, records⟩ := recognize_verified (recognizerBounds hbasic) H pad word hx
    (recognizer_window hbasic) hp
  change ConcreteSource.runAt pad H word = some out at ho
  obtain rfl := Option.some.inj (ho.symm.trans hr)
  have hL : 0 < gram q b t l := by have hh := hbasic.local_gram; omega
  have hspos : 0 < edits t := by unfold edits; omega
  have hD : R.card ≤ D := (firstEvent_witnessBounds H pad word hL hspos hv).1
  obtain ⟨_,_,hgraph,_,_⟩ := hv
  let d : Fin (D+1) := ⟨R.card, by omega⟩
  let ds := fullDescription hs i word
  have hwindow : windowLength q l + 2*omittedLetters q b t l ≤ gram q b t l :=
    (Nat.le_succ _).trans (recognizer_window hbasic)
  obtain ⟨code,henc,hdec,_,hprog⟩ := fullDescription_roundtrip records hgraph.chronology hx hgraph.fit
    hwindow hgraph.highWidth i hspos hD
  unfold packWitness
  dsimp only
  rw [← number_left i, SourceRecognition.graph_eq, PatchGraph.ruleIds_eq, SourceWitness.filter_finRange_eq_sort,
    List.length_map, Finset.length_sort, ite_eq_left hD, SourceWitness.retainedIds_eq]
  have hmark (j : Fin (hs.length * edits t)) (hj : j ∈ T) :
      (T.sort.map Fin.val).contains j.val = true := by
    change (SourceSmallCodec.names T).contains j.val = true
    exact List.contains_iff_mem.mpr ((SourceSmallCodec.names_mem_iff T j).mpr hj)
  rw [SourceWitness.describe_eq pad hs root word T _ (fun _ => true) hmark, encodeDescription_eq]
  change ((ReplayGrammar.encodeDescription (edits t*d.val) (gram q b t l) b q pad ds).map descriptionData).bind _ = _
  rw [henc]
  simp only [Option.map_some, Option.bind_some]
  rw [packCode_eq pad b t hq hb ht hl hp H word d code ds hdec p roots _ (compactStarts_eq pad hp hs root) hprog]
  unfold PeelingCompression.packWitness
  dsimp only
  by_cases hcore : core p.incidence = ∅
  · have hn : ¬core (fullProgram hs i word).incidence ≠ ∅ := fun he => he hcore
    rw [ite_eq_right hn]
    cases hlarge : (PeelingFrame.trace p).all (fun e => !SmallCompression.isSmall (b := b) (t := t) pad (p.record e))
    · simp [hcore]
    · simp only [hcore,true_and,↓reduceIte,Bool.not_true,Bool.false_eq_true]
      rw [dite_eq_left hD]
      change _ = (ReplayGrammar.encodeDescription (edits t*d.val) (gram q b t l) b q pad ds).bind _
      rw [henc]
      rfl
  · have hn : core (fullProgram hs i word).incidence ≠ ∅ := hcore
    simp [hn,hcore]

theorem encode_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (H : ConcreteSource.Hash q b t l) (word : Fin l → Fin q) :
    encode pad b t (l, matrixRows H, List.ofFn word) = PeelingCompression.pack (by omega : 1 < q)
      pad (fun x => AcceptanceWeights.strong pad b t l (List.ofFn x)) H word := by
  unfold encode PeelingCompression.pack
  dsimp only
  by_cases h : 0 < l
  · rw [dite_eq_left h]
    by_cases hg : minLength q b t ≤ l ∧ AcceptanceWeights.strong pad b t l (List.ofFn word) = true
    · simp only [h,hg, true_and, ↓reduceIte]
      rw [SourceRecognition.recognize_eq pad b t hq]
      have hx := (AcceptanceWeights.strong_iff pad b t word).mp hg.2
      change ((ConcreteSource.runAt pad H word).map SourceRecognition.resultData).bind _ = _
      cases hr : ConcreteSource.runAt pad H word with
      | none => rfl
      | some result =>
        cases result with
        | complete => rfl
        | firstEvent hs i =>
          simp only [Option.map_some, bind, Option.bind, SourceRecognition.resultData]
          exact packWitness_eq pad b t hq hb ht hg.1 h H word hs i hx hr
    · simp [h,hg]
  · simp [h]

theorem decode_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q)
    (H : ConcreteSource.Hash q b t l) (word : QWord q) :
    decode pad b t (l, matrixRows H, word) = (PeelingCompression.read pad H word).map List.ofFn := by
  unfold decode PeelingCompression.read PeelingFrame.decode
  dsimp only
  rw [readHeader_eq pad b t l hq]
  cases hh : PeelingFrame.readHeader l q (edits t) (witnessLimit q b t l) (gram q b t l) b word with
  | none => rfl
  | some h =>
    simp only [Option.map_some,Option.bind_some,bind,Option.bind]
    unfold readProgram headerData
    dsimp only
    rw [materialize_eq pad _ h.count h.entries h.roots _ (fun e _ => anchorsData_at _ _ _)]
    cases hp : PeelingFrame.materialize h.count h.entries h.roots (gram q b t l) with
    | none => rfl
    | some p =>
      simp only [Option.map_some, Option.bind_some, bind, Option.bind]
      rw [peelInput_eq H p (materialize_patch hp)]
      exact SourcePeelingPayload.decodePrefix_eq pad b t hq H p.record (PeelingFrame.trace p) h.tail

private theorem compactStarts_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun p : SourceRecognition.History q × ℕ => compactStarts pad p.1 p.2)
      (encPair (SourceRecognition.historyEncoding q) encUnary) PatchGraph.rowEncoding := by
  let h := SourceRecognition.historyEncoding q
  let e := encPair h encUnary
  have hh := fst h encUnary
  have hi := snd h encUnary
  have hg := (SourceRecognition.graph_polyTime pad).comp hh
  have hs := (SourceWitness.patchStarts_polyTime pad).comp hh
  have hk := PatchGraph.patchIds_polyTime.comp (hg.prod hi)
  have hi : ComputableInPolyTime (fun p : (SourceRecognition.History q × ℕ) × ℕ =>
      (SourceWitness.patchStarts pad p.1.1).getD p.2 0) (encPair e encUnary) encUnary :=
    (listGetDWithInput (hs.comp (fst e encUnary)) (snd e encUnary) 0).of_enc_eq (fun _ => rfl)
  have hmap := mapWithInput (encIn := e) (encA := encUnary) (encB := encUnary)
    (f := fun p i => (SourceWitness.patchStarts pad p.1).getD i 0) hk hi
  exact hmap.of_enc_eq (fun _ => rfl)

private abbrev startsEncoding := PatchGraph.rowEncoding

private theorem chosenRoots_polyTime :
    ComputableInPolyTime (fun p : List ℕ × List ℕ => p.1.map (fun i => p.2.getD i 0))
      (encPair startsEncoding startsEncoding) startsEncoding := by
  let e := encPair startsEncoding startsEncoding
  exact mapWithInput (f := fun p i => p.2.getD i 0) (fst startsEncoding startsEncoding)
    (listGetDWithInput ((snd startsEncoding startsEncoding).comp (fst e encUnary)) (snd e encUnary) 0)

private theorem rootTable_polyTime :
    ComputableInPolyTime (fun p : ℕ × (List ℕ × List ℕ) => rootTable p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair startsEncoding startsEncoding)) SourceReplay.anchorsEncoding := by
  let a := encPair startsEncoding startsEncoding
  let e := encPair encUnary a
  have hx := fst e encUnary
  have hj := snd e encUnary
  have hu := (snd encUnary a).comp hx
  have hi := (idxOf?_polyTime 0 encUnary).comp (hu.fst'.prod hj)
  have hguard := hi.decide_ne (const none)
  have hz := (optionSome encUnary).comp (listGetDWithInput hu.snd' hj 0)
  exact mapWithInput (encB := encOption encUnary) (f := fun p j => if p.2.1.contains j then some (p.2.2.getD j 0) else none)
    (unary_range' (fst encUnary a)) ((hguard.ite' hz (const none)).of_enc_eq (fun _ => by
      simp [Function.comp_def,List.idxOf?_eq_none_iff]))

private theorem allLarge_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : (ℕ × Records q) × List ℕ => allLarge pad b t p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary (recordsEncoding q)) startsEncoding) encBool := by
  let a := encPair encUnary (recordsEncoding q)
  let e := encPair a startsEncoding
  have hp := (fst a startsEncoding).comp (fst e encUnary)
  have hr := (SourcePeelingPayload.recordAt_polyTime q).comp (hp.snd'.prod (snd e encUnary))
  have hi := bool_not.comp ((isSmall_polyTime pad b t hq).comp (hp.fst'.prod hr))
  have ht : ComputableInPolyTime (fun p : ((ℕ × Records q) × List ℕ) × ℕ =>
      !SourceSmallBranch.isSmall pad b t p.1.1.1 (SourcePeelingPayload.recordAt p.1.1.2 p.2))
      (encPair e encUnary) encBool := hi.of_enc_eq (fun _ => rfl)
  exact allWithInput (encIn := e) (encA := encUnary)
    (test := fun p i => !SourceSmallBranch.isSmall pad b t p.1.1
      (SourcePeelingPayload.recordAt p.1.2 i)) (snd a startsEncoding) ht

private abbrev geometryEncoding (q : ℕ) := encPair (encPair encUnary encUnary) (recordsEncoding q)

private theorem programGraph_polyTime (q : ℕ) :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × Records q => programGraph p.1.1 p.1.2 p.2)
      (geometryEncoding q) PatchGraph.graphEncoding := by
  let r := recordsEncoding q
  let a := encPair encUnary encUnary
  let e := geometryEncoding q
  let f := encPair e encUnary
  have hp := fst a r
  have hs := hp.snd'
  have hd := hp.fst'
  have hx := fst e encUnary
  have hi := snd e encUnary
  have hy := fst f encUnary
  have hj := snd f encUnary
  have hk := unary_add' hj (unary_mul' ((hs.comp hx).comp hy) (hi.comp hy))
  have hr := (SourcePeelingPayload.recordAt_polyTime q).comp ((((snd a r).comp hx).comp hy).prod hk)
  have hu := decodedEncoding_patch_polyTime q hr.fst'
  have hv : ComputableInPolyTime (fun p : (((ℕ × ℕ) × Records q) × ℕ) × ℕ =>
      ((p.1.1.2[p.2+p.1.1.1.2*p.1.2]?).map (fun r => r.1.patch)).getD 0)
      (encPair f encUnary) encUnary := by
    refine hu.of_enc_eq ?_
    intro p
    apply congrArg encUnary
    simp only [Function.comp_def, SourcePeelingPayload.recordAt, List.getD_eq_getElem?_getD]
    cases p.1.1.2[p.2+p.1.1.1.2*p.1.2]? <;> rfl
  have hm := mapWithInput (f := fun p j => ((p.1.2[j+p.1.1.2*p.2]?).map (fun r => r.1.patch)).getD 0)
    (unary_range' (hs.comp hx)) hv
  have hm' : ComputableInPolyTime (fun p : ((ℕ × ℕ) × Records q) × ℕ =>
      (List.range p.1.1.2).map (fun j => ((p.1.2[j+p.1.1.2*p.2]?).map (fun r => r.1.patch)).getD 0))
      (encPair e encUnary) PatchGraph.rowEncoding := hm.of_enc_eq (fun _ => rfl)
  have h := mapWithInput (encIn := e) (encA := encUnary) (encB := PatchGraph.rowEncoding)
    (f := fun p i => (List.range p.1.2).map (fun j =>
      ((p.2[j+p.1.2*i]?).map (fun r => r.1.patch)).getD 0))
    (unary_range' hd) hm'
  exact ((unary_mul' hs hd).prod h).of_enc_eq (fun _ => rfl)

private theorem geometry_polyTime (q : ℕ) :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × Records q => SourcePeel.run (programGraph p.1.1 p.1.2 p.2) p.1.2)
      (geometryEncoding q) SourcePeel.stateEncoding := by
  have h := SourcePeel.run_polyTime.comp ((programGraph_polyTime q).prod
    (fst (encPair encUnary encUnary) (recordsEncoding q)).snd')
  exact h.of_enc_eq (fun _ => rfl)

private abbrev programEncoding (q : ℕ) :=
  encPair (encPair encUnary encUnary) (encPair rowsEncoding (encPair (recordsEncoding q)
    (encPair (descriptionEncoding q) (encPair startsEncoding (wordEncoding q)))))

private theorem packProgram_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × (Rows × (Records q × (Description q × (List ℕ × QWord q)))) =>
      packProgram pad b t p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      (programEncoding q) (encOption (wordEncoding q)) := by
  let e := programEncoding q
  let w := wordEncoding q
  let a := encPair rowsEncoding (encPair (recordsEncoding q)
    (encPair (descriptionEncoding q) (encPair startsEncoding w)))
  have hp := fst (encPair encUnary encUnary) a
  have hu := snd (encPair encUnary encUnary) a
  have hl := hp.fst'
  have hd := hp.snd'
  have hs := const (encIn := e) (encOut := encUnary) (edits t)
  have hR := hu.fst'
  have hr := hu.snd'.fst'
  have hc := hu.snd'.snd'.fst'
  have hk := hu.snd'.snd'.snd'.fst'
  have hw := hu.snd'.snd'.snd'.snd'
  have hg := (geometry_polyTime q).comp ((hd.prod hs).prod hr)
  have hnone := allWithInput (test := fun _ b => !b) hg.snd' (bool_not.comp (snd e encBool))
  have hlarge := (allLarge_polyTime pad b t hq).comp ((hl.prod hr).prod hg.fst')
  have hinput := SourcePeelingPayload.inputEncoding_mk_polyTime q hl hs hR hr hg.fst'
  have hdata := (SourcePeelingPayload.encode_polyTime pad b t hq).comp (hinput.prod hw)
  have hh := (writeHeader_polyTime pad b t hq).comp (hp.prod (hc.prod hk))
  have htail := listAppend' (hh.comp (fst e w)) (snd e w)
  have hb : ComputableInPolyTime (fun p => writeHeader pad b t p.1.1.1 p.1.1.2
      p.1.2.2.2.1 p.1.2.2.2.2.1 ++ p.2) (encPair e w) w := htail.of_enc_eq (fun _ => rfl)
  have hbody := optionMapWithInput (encA := e) (encB := w) (encC := w) (f := fun p tail =>
    writeHeader pad b t p.1.1 p.1.2 p.2.2.2.1 p.2.2.2.2.1 ++ tail) hdata hb
  exact ((bool_and' hnone hlarge).ite' hbody (const none)).of_enc_eq (fun _ => rfl)

private abbrev codeInputEncoding (q : ℕ) :=
  encPair (encPair encUnary encUnary) (encPair rowsEncoding
    (encPair (descriptionEncoding q) (encPair startsEncoding (wordEncoding q))))

private theorem packCode_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × (Rows × (Description q × (List ℕ × QWord q))) =>
      packCode pad b t p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (codeInputEncoding q) (encOption (wordEncoding q)) := by
  let e := codeInputEncoding q
  let w := wordEncoding q
  let a := encPair rowsEncoding (encPair (descriptionEncoding q) (encPair startsEncoding w))
  let v := decodedListEncoding q
  let r := recordsEncoding q
  let z := encPair e v
  have hp := fst (encPair encUnary encUnary) a
  have hu := snd (encPair encUnary encUnary) a
  have hl := hp.fst'
  have hd := hp.snd'
  have hs := const (encIn := e) (encOut := encUnary) (edits t)
  have hR := hu.fst'
  have hc := hu.snd'.fst'
  have hstarts := hu.snd'.snd'.fst'
  have hw := hu.snd'.snd'.snd'
  have hE := unary_mul' hs hd
  have hL := (UniformParameters.gram_machine q b t).comp hl
  have hdec := (decodeDescription_polyTime q).comp ((hE.prod (hL.prod (const (encOut := encUnary) b))).prod hc)
  have hx := fst e v
  have hv := snd e v
  have hkeys := (SourceCoreReplay.patchKeys_polyTime q).comp ((hE.comp hx).prod hv)
  have hroot := rootTable_polyTime.comp ((hE.comp hx).prod (hkeys.prod (hstarts.comp hx)))
  have hmat := (materialize_polyTime pad).comp
    (materializeEncoding_mk_polyTime q (hl.comp hx) (hL.comp hx) (hs.comp hx) (hd.comp hx) hv hroot)
  have hy := fst z r
  have hr := snd z r
  have hsrc := hx.comp hy
  have hchosen := chosenRoots_polyTime.comp (hkeys.prod (hstarts.comp hx))
  have hpack := (packProgram_polyTime pad b t hq).comp ((hp.comp hsrc).prod
    ((hR.comp hsrc).prod (hr.prod ((hc.comp hsrc).prod
      ((hchosen.comp hy).prod (hw.comp hsrc))))))
  have hn := optionBindWithInput (ea := z) (eb := r) (ec := w)
    (f := fun p rs => packProgram pad b t p.1.1.1 p.1.1.2 p.1.2.1 rs p.1.2.2.1
      ((SourceCoreReplay.patchKeys (edits t*p.1.1.2) p.2).map (fun i => p.1.2.2.2.1.getD i 0)) p.1.2.2.2.2)
    hmat hpack
  have h := optionBindWithInput (ea := e) (eb := v) (ec := w)
    (f := fun p ds =>
      let E := edits t*p.1.2
      let keys := SourceCoreReplay.patchKeys E ds
      (materialize pad p.1.1 (gram q b t p.1.1) (edits t) p.1.2 ds (rootTable E keys p.2.2.2.1)).bind fun rs =>
        packProgram pad b t p.1.1 p.1.2 p.2.1 rs p.2.2.1 (keys.map fun i => p.2.2.2.1.getD i 0) p.2.2.2.2)
    hdec hn
  exact h.of_enc_eq (fun _ => rfl)

private theorem packWitness_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (packWitness pad b t) (witnessEncoding q) (encOption (wordEncoding q)) := by
  let e := witnessEncoding q
  let w := wordEncoding q
  let c := descriptionEncoding q
  let a := SourceSmallBranch.witnessEncoding q
  let z := encPair e c
  have h := fst a rowsEncoding
  have hR := snd a rowsEncoding
  have hl := h.fst'
  have hi := h.snd'.fst'
  have hw := h.snd'.snd'.fst'
  have hh := h.snd'.snd'.snd'
  have hs := const (encIn := e) (encOut := encUnary) (edits t)
  have hg := (SourceRecognition.graph_polyTime pad).comp hh
  have hr := PatchGraph.ruleIds_polyTime.comp (hg.prod hi)
  have hd := (length_list encUnary).comp hr
  have hids := SourceWitness.retainedIds_polyTime.comp (hg.prod (hs.prod hi))
  have he := (SourceWitness.entries_polyTime pad).comp ((hs.prod hi).prod (hw.prod hh))
  have hds := (SourceWitness.describe_polyTime q).comp (he.prod (hr.prod (hids.prod hids)))
  have hL := (UniformParameters.gram_machine q b t).comp hl
  have hE := unary_mul' hs hd
  have hc := (encodeDescription_polyTime pad).comp ((hE.prod (hL.prod (const (encOut := encUnary) b))).prod hds)
  have hstarts := (compactStarts_polyTime pad).comp (hh.prod hi)
  have hx := fst e c
  have hpack := (packCode_polyTime pad b t hq).comp (((hl.prod hd).comp hx).prod
    ((hR.comp hx).prod ((snd e c).prod ((hstarts.comp hx).prod (hw.comp hx)))))
  have hb := optionBindWithInput (ea := e) (eb := c) (ec := w) (f := fun x code =>
    packCode pad b t x.1.1 (PatchGraph.ruleIds (SourceRecognition.graph pad x.1.2.2.2) x.1.2.1).length x.2 code
      (compactStarts pad x.1.2.2.2 x.1.2.1) x.1.2.2.1) hc hpack
  have hD := unary_add' (unary_mul' (const (8*edits t)) ((UniformParameters.cutoff_machine q b t).comp hl)) (const 1)
  have h := (unary_le' hd hD).ite' hb (const none)
  exact h.of_enc_eq (fun p => by
    apply congrArg (encOption w)
    simp [packWitness, Function.comp_def, witnessLimit, Nat.mul_assoc])

theorem encode_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (encode pad b t) (SourceAcceptance.inputEncoding q) (encOption (wordEncoding q)) := by
  let e := SourceAcceptance.inputEncoding q
  let w := wordEncoding q
  let a := SourceRecognition.resultEncoding q
  let o := encOption (wordEncoding q)
  let z := encPair e a
  have hl := fst encUnary (encPair rowsEncoding w)
  have hR := (snd encUnary (encPair rowsEncoding w)).fst'
  have hw := (snd encUnary (encPair rowsEncoding w)).snd'
  have hgood := (Machine.AcceptanceWeights.strong_polyTime pad hq hb ht).comp (hl.prod hw)
  have hguard := bool_and' (unary_lt' (const 0) hl) (bool_and' (unary_le' (const (minLength q b t)) hl) hgood)
  have hr := SourceRunBounds.recognize_polyTime pad b t hq
  have hx := fst e a
  have ha := snd e a
  have hy := fst z encUnary
  have hp := hx.comp hy
  have hc := (packWitness_polyTime pad b t hq).comp (((hl.comp hp).prod ((snd z encUnary).prod
    ((hw.comp hp).prod (ha.snd'.comp hy)))).prod (hR.comp hp))
  have hf := optionBindWithInput (ea := z) (eb := encUnary) (ec := w)
    (f := fun x i => packWitness pad b t ((x.1.1,i,x.1.2.2,x.2.2),x.1.2.1)) ha.fst' hc
  have h := optionBindWithInput (ea := e) (eb := a) (ec := w)
    (f := fun x res => res.1.bind (fun i => packWitness pad b t ((x.1,i,x.2.2,res.2), x.2.1))) hr hf
  exact (hguard.ite' h (const (encOut := o) none)).of_enc_eq (fun _ => by
    simp [encode, Function.comp_def, and_assoc] <;> rfl)

private theorem readProgram_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : (ℕ × Rows) × Header q => readProgram pad b t p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary rowsEncoding) (headerEncoding q)) (encOption (wordEncoding q)) := by
  let a := encPair encUnary rowsEncoding
  let u := headerEncoding q
  let e := encPair a u
  let v := recordsEncoding q
  let z := encPair e v
  let w := wordEncoding q
  have hp := fst a u
  have hh := snd a u
  have hl := hp.fst'
  have hs := const (encIn := e) (encOut := encUnary) (edits t)
  have hL := (UniformParameters.gram_machine q b t).comp hl
  have hd := headerEncoding_count_polyTime q hh
  have hes := headerEncoding_entries_polyTime q hh
  have hroots := headerEncoding_roots_polyTime q hh
  have ht := headerEncoding_tail_polyTime q hh
  have hm := (materialize_polyTime pad).comp (materializeEncoding_mk_polyTime q hl hL hs hd hes hroots)
  have hx := fst e v
  have hr := snd e v
  have hg := (geometry_polyTime q).comp (((hd.prod hs).comp hx).prod hr)
  have hi := SourcePeelingPayload.inputEncoding_mk_polyTime q (hl.comp hx) (hs.comp hx)
    (hp.snd'.comp hx) hr hg.fst'
  have hd := (SourcePeelingPayload.decodePrefix_polyTime pad b t hq).comp (hi.prod (ht.comp hx))
  exact optionBindWithInput (ea := e) (eb := v) (ec := w) (f := fun p rs =>
    SourcePeelingPayload.decodePrefix pad b t (peelInput p.1.1 (edits t) p.2.count p.1.2 rs) p.2.tail) hm hd

theorem decode_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (decode pad b t) (SourceAcceptance.inputEncoding q) (encOption (wordEncoding q)) := by
  let e := SourceAcceptance.inputEncoding q
  let w := wordEncoding q
  let u := headerEncoding q
  have hl := fst encUnary (encPair rowsEncoding w)
  have hr := (snd encUnary (encPair rowsEncoding w)).fst'
  have hw := (snd encUnary (encPair rowsEncoding w)).snd'
  have hh := (readHeader_polyTime pad b t hq).comp (hl.prod hw)
  have h := (readProgram_polyTime pad b t hq).comp (((hl.prod hr).comp (fst e u)).prod (snd e u))
  exact optionBindWithInput (ea := e) (eb := u) (ec := w)
    (f := fun p hd => readProgram pad b t p.1 p.2.1 hd) hh h

#print axioms encode_eq
#print axioms encode_polyTime
#print axioms decode_eq
#print axioms decode_polyTime

end DeletionCode.Explicit.Machine.SourcePeelingBranch
