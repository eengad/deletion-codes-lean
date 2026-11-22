import DeletionCode.Explicit.Machine.SourceReplayPayload
import DeletionCode.Explicit.PeelingFrame
import Batteries.Tactic.OpenPrivate

/-! Read the reverse-peeling header and reconstruct its chronological replay. -/
namespace DeletionCode.Explicit.Machine.SourcePeelingFrame

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open SourceReplay SourceCoreReplay SourceGrammar SourceLists
open SourcePayloadIndex SourceDescriptionIndex
open SourceReplayPayload (Record recordEncoding recordData clearFlags)
open _root_.DeletionCode.Explicit.UniformParameters
open scoped BigOperators
open private ofDigits_ofFn from DeletionCode.Explicit.Machine.GramOrder
open private table_eq from DeletionCode.Explicit.Machine.SourceCoreReplay
set_option maxHeartbeats 1300000

variable {q l E d s D : ℕ}

abbrev Records (q : ℕ) := List (Record q)
abbrev recordsEncoding (q : ℕ) := encList (recordEncoding q)

def programRecords (p : PeelingFrame.Program l q d s) : Records q :=
  List.ofFn fun j => recordData (p.record (finProdFinEquiv.symm j))

def programGraph (d s : ℕ) (rows : Records q) : PatchGraph.Graph :=
  (s*d, (List.range d).map fun i => (List.range s).map fun j =>
    ((rows[j+s*i]?).map (fun p => p.1.patch)).getD 0)

theorem programGraph_eq (p : PeelingFrame.Program l q d s)
    (h : ∀ e, (p.record e).1.patch = (p.incidence e).val) :
    programGraph d s (programRecords p) = PatchGraph.graphData p.incidence := by
  unfold programGraph PatchGraph.graphData
  congr 1
  rw [SourceLists.range_map_eq]
  congr 1
  funext i
  rw [SourceLists.range_map_eq]
  congr 1
  funext j
  let a := finProdFinEquiv (i,j)
  have ha : a.val < (programRecords p).length := by simp [programRecords]
  change (((programRecords p)[a.val]?).map (fun r => r.1.patch)).getD 0 = _
  rw [List.getElem?_eq_getElem ha]
  simp only [Option.map_some, Option.getD_some, programRecords, List.getElem_ofFn]
  change (p.record (finProdFinEquiv.symm (finProdFinEquiv (i,j)))).1.patch = _
  rw [Equiv.symm_apply_apply, h]

def materialize (pad : Fin q) (l L s d : ℕ) (ds : List (Decoded q)) (roots : Anchors) : Option (Records q) := do
  let es ← SourceReplay.replay pad ((l,L), roots) ds
  let pairs := ds.zip es
  if pairs.length = d*s && pairs.all (fun p => decide (p.1.patch < s*d)) then
    some (pairs.map fun p => (clearFlags p.1,p.2))
  else none

private theorem validate_pairs {A : Type} (pairs : List A) (hlen : pairs.length = d*s) (f : A → ℕ) :
    (pairs.all fun p => decide (f p < s*d)) = true ↔
      ∀ e : Fin d × Fin s, f (pairs.get (Fin.cast hlen.symm (finProdFinEquiv e))) < s*d := by
  simp only [List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h e
    exact h _ (List.get_mem ..)
  · intro h p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
    let j : Fin (d*s) := ⟨i, hlen ▸ hi⟩
    have hh := h (finProdFinEquiv.symm j)
    rwa [Equiv.apply_symm_apply] at hh

theorem materialize_eq (pad : Fin q) (L : ℕ) (d : Fin (D+1))
    (ds : List (ReplayGrammar.DecodedEntry q)) (roots : ↥(CoreWeight.patchKeys (s*d.val) ds) → Fin l)
    (rootData : Anchors)
    (hroot : ∀ entry ∈ ds, rootData.getD entry.entry.patch none =
      (CoreWeight.anchorLookup (CoreWeight.patchKeys (s*d.val) ds) roots entry.entry.patch).map Fin.val) :
    materialize pad l L s d.val (ds.map decodedData) rootData =
      (PeelingFrame.materialize d ds roots L).map programRecords := by
  unfold materialize PeelingFrame.materialize
  rw [SourceReplay.replay_eq pad L ds rootData _ hroot]
  cases hr : ReplayEntry.replay L (CoreWeight.anchorLookup (CoreWeight.patchKeys (s*d.val) ds) roots) (ds.map (·.entry)) with
  | none => rfl
  | some out =>
    let pairs := ds.zip out.toList
    have hpairs : (ds.map decodedData).zip (SourceDictionary.historyData out) =
        pairs.map (fun p => (decodedData p.1, SourceDictionary.store p.2)) := by
      unfold SourceDictionary.historyData pairs
      rw [List.zip_map_left, List.zip_map_right, List.map_map]
      rfl
    simp only [Option.map_some, bind, Option.bind, hpairs, List.length_map, List.all_map, Function.comp_def]
    let built (h : pairs.length = d.val*s) : Option (PeelingFrame.Program l q d.val s) :=
      let get (e : Fin d.val × Fin s) := pairs.get (Fin.cast h.symm (finProdFinEquiv e))
      if hp : ∀ e, (get e).1.entry.patch < s*d.val then
        some ⟨fun e => ((get e).1.entry,(get e).2), fun e => ⟨(get e).1.entry.patch,hp e⟩⟩
      else none
    change (if decide (pairs.length = d.val*s) && (pairs.all fun p => decide (p.1.entry.patch < s*d.val)) then
      some ((pairs.map fun p => (decodedData p.1,SourceDictionary.store p.2)).map
        (fun p => (clearFlags p.1,p.2))) else none) =
      (if h : pairs.length = d.val*s then built h else none).map programRecords
    by_cases hlen : pairs.length = d.val*s
    · have hbool := validate_pairs pairs hlen (fun p => p.1.entry.patch)
      rw [dite_eq_left hlen]
      simp only [hlen, decide_true, Bool.true_and]
      unfold built
      by_cases hcheck : (pairs.all fun p => decide (p.1.entry.patch < s*d.val)) = true
      · rw [ite_eq_left hcheck, dite_eq_left (hbool.mp hcheck), Option.map_some]
        apply congrArg some
        apply List.ext_getElem (by simp [hlen, programRecords])
        intro i hi hj
        simp only [List.getElem_map, programRecords, List.getElem_ofFn, Equiv.apply_symm_apply]
        rfl
      · rw [ite_eq_right hcheck, dite_eq_right (mt hbool.mpr hcheck)]
        rfl
    · rw [dite_eq_right hlen]
      simp [hlen]

theorem materialize_patch {d : Fin (D+1)} {ds : List (ReplayGrammar.DecodedEntry q)}
    {roots : ↥(CoreWeight.patchKeys (s*d.val) ds) → Fin l} {L : ℕ}
    {p : PeelingFrame.Program l q d.val s} (h : PeelingFrame.materialize d ds roots L = some p) :
    ∀ e, (p.record e).1.patch = (p.incidence e).val := by
  unfold PeelingFrame.materialize at h
  cases hr : ReplayEntry.replay L (CoreWeight.anchorLookup (CoreWeight.patchKeys (s*d.val) ds) roots)
      (ds.map (·.entry)) with
  | none => simp [hr] at h
  | some out =>
    simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · split at h
      · obtain rfl := Option.some.inj h
        exact fun _ => rfl
      · contradiction
    · contradiction

structure MaterializeInput (q : ℕ) where
  length : ℕ
  gram : ℕ
  arity : ℕ
  count : ℕ
  entries : List (Decoded q)
  roots : Anchors

enc_structure materializeEncoding (q : ℕ) : MaterializeInput q where
  length : encUnary, gram : encUnary, arity : encUnary, count : encUnary,
  entries : (decodedListEncoding q), roots : anchorsEncoding

theorem materialize_polyTime (pad : Fin q) : ComputableInPolyTime
    (fun p : MaterializeInput q => materialize pad p.length p.gram p.arity p.count p.entries p.roots)
    (materializeEncoding q) (encOption (recordsEncoding q)) := by
  let e := materializeEncoding q
  let es := SourceDictionary.historyEncoding q
  let r := recordEncoding q
  let a := encPair e es
  have h := id' (encIn := e)
  have hl := materializeEncoding_length_polyTime q h
  have hL := materializeEncoding_gram_polyTime q h
  have hs := materializeEncoding_arity_polyTime q h
  have hc := materializeEncoding_count_polyTime q h
  have hr := materializeEncoding_roots_polyTime q h
  have hd := materializeEncoding_entries_polyTime q h
  have hreplay := (SourceReplay.replay_polyTime pad).comp (encIn := e)
    (((hl.prod hL).prod hr).prod hd)
  have hp := fst e es
  have hz := (ComputableInPolyTime.zip (decodedEncoding q) (SourceDictionary.storedEncoding q)).comp
    ((hd.comp hp).prod (snd e es))
  have hcount := (length_list r).comp hz
  have htotal := (unary_mul' hc hs).comp hp
  have hsize := hcount.decide_eq' htotal
  have htest := (unary_lt' (decodedEncoding_patch_polyTime q (snd a r).fst')
    ((unary_mul' hs hc).comp (hp.comp (fst a r))))
  have hvalid := allWithInput (encIn := a) (encA := r)
    (test := fun p v => decide (v.1.patch < p.1.arity*p.1.count)) hz htest
  have hu := (fst (decodedEncoding q) (SourceDictionary.storedEncoding q))
  have hclear := decodedEncoding_mk_polyTime q (decodedEncoding_rule_polyTime q hu)
    (decodedEncoding_patch_polyTime q hu) (decodedEncoding_left_polyTime q hu)
    (decodedEncoding_right_polyTime q hu) (decodedEncoding_removed_polyTime q hu)
    (decodedEncoding_replacement_polyTime q hu) (decodedEncoding_refs_polyTime q hu) (const false) (const false)
  have hout := (ComputableInPolyTime.map (hclear.prod (snd (decodedEncoding q) (SourceDictionary.storedEncoding q)))).comp hz
  have hb := (bool_and' hsize hvalid).ite' ((optionSome (recordsEncoding q)).comp hout) (const none)
  exact optionBindWithInput (ea := e) (eb := es) (ec := recordsEncoding q)
    (f := fun p es => let pairs := p.entries.zip es
      if pairs.length = p.count*p.arity && pairs.all (fun v => decide (v.1.patch < p.arity*p.count)) then
        some (pairs.map fun p => (clearFlags p.1, p.2)) else none)
    hreplay (hb.of_enc_eq (fun p => by simp [clearFlags, Function.comp_def]))

structure Header (q : ℕ) where
  count : ℕ
  entries : List (Decoded q)
  roots : Anchors
  tail : QWord q

enc_structure headerEncoding (q : ℕ) : Header q where
  count : encUnary, entries : (decodedListEncoding q), roots : anchorsEncoding, tail : (wordEncoding q)

private def readEntries (pad : Fin q) (E L b : ℕ) (w : QWord q) : Option (List (Decoded q) × QWord q) :=
  (SourcePayloadIndex.readIndex q (ReplayGrammar.descriptionBound E L b q) w).bind fun i =>
    (SourceDescriptionIndex.unpack pad E L b i.1).bind fun code =>
      (SourceGrammar.decodeDescription E L b code).map fun ds => (ds,i.2)

private abbrev entriesInputEncoding (q : ℕ) := encPair (encPair encUnary encUnary) (wordEncoding q)
private abbrev entriesOutputEncoding (q : ℕ) := encPair (decodedListEncoding q) (wordEncoding q)

private theorem readEntries_polyTime (pad : Fin q) (b : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × QWord q => readEntries pad p.1.1 p.1.2 b p.2)
      (entriesInputEncoding q) (encOption (entriesOutputEncoding q)) := by
  let e := entriesInputEncoding q
  let w := wordEncoding q
  let a := SourcePayloadIndex.readEncoding q
  let c := descriptionEncoding q
  let ds := decodedListEncoding q
  let z := encPair e a
  have hd := fst (encPair encUnary encUnary) w
  have hγ := (descriptionBound_polyTime q b).comp hd
  have hidx := (readIndex_polyTime q hq).comp (hγ.prod (snd (encPair encUnary encUnary) w))
  have p := fst e a
  have hdim := hd.comp p
  have hsizes := hdim.fst'.prod (hdim.snd'.prod (const (encOut := encUnary) b))
  have hc := (unpack_polyTime pad).comp (encIn := z) (hsizes.prod (snd e a).fst')
  have he := (decodeDescription_polyTime q).comp (encIn := encPair z c)
    ((hsizes.comp (fst z c)).prod (snd z c))
  have hf := optionMapWithInput (encA := encPair z c) (encB := ds) (encC := entriesOutputEncoding q)
    (f := fun p ds => (ds,p.1.2.2)) he
    ((snd (encPair z c) ds).prod (((snd e a).snd'.comp (fst z c)).comp (fst (encPair z c) ds)))
  have h := optionBindWithInput (ea := z) (eb := c) (ec := entriesOutputEncoding q)
    (f := fun p c => (SourceGrammar.decodeDescription p.1.1.1 p.1.1.2 b c).map (fun ds => (ds,p.2.2))) hc hf
  have ht := optionBindWithInput (ea := e) (eb := a) (ec := entriesOutputEncoding q)
    (f := fun p data => (SourceDescriptionIndex.unpack pad p.1.1 p.1.2 b data.1).bind fun c =>
      (SourceGrammar.decodeDescription p.1.1 p.1.2 b c).map (fun ds => (ds,data.2))) hidx h
  exact ht.of_enc_eq (fun _ => rfl)

private def readAnchors (l E : ℕ) (ds : List (Decoded q)) (w : QWord q) : Option (Anchors × QWord q) :=
  let keys := SourceCoreReplay.patchKeys E ds
  (SourcePayloadIndex.readIndex q (l^keys.length) w).bind fun i =>
    (SourceCoreReplay.decodeAnchors l E keys i.1).map fun roots => (roots,i.2)

private abbrev anchorInputEncoding (q : ℕ) := encPair (encPair encUnary encUnary) (entriesOutputEncoding q)
private abbrev anchorOutputEncoding (q : ℕ) := encPair anchorsEncoding (wordEncoding q)

private theorem readAnchors_polyTime (q : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × (List (Decoded q) × QWord q) =>
      readAnchors p.1.1 p.1.2 p.2.1 p.2.2) (anchorInputEncoding q) (encOption (anchorOutputEncoding q)) := by
  let e := anchorInputEncoding q
  let w := wordEncoding q
  let a := SourcePayloadIndex.readEncoding q
  let z := encPair e a
  have hp := fst (encPair encUnary encUnary) (entriesOutputEncoding q)
  have hd := snd (encPair encUnary encUnary) (entriesOutputEncoding q)
  have hk := (patchKeys_polyTime q).comp (hp.snd'.prod hd.fst')
  have hn := (length_list encUnary).comp hk
  have hbound := binary_pow.comp ((unary_to_binary.comp hp.fst').prod hn)
  have hi := (readIndex_polyTime q hq).comp (encIn := e) (hbound.prod hd.snd')
  have h := fst e a
  have hu := snd e a
  have hr := decodeAnchors_polyTime.comp (encIn := z) ((hp.comp h).prod ((hk.comp h).prod hu.fst'))
  have hout := optionMapWithInput (encA := z) (encB := anchorsEncoding) (encC := anchorOutputEncoding q)
    (f := fun p roots => (roots,p.2.2)) hr
    ((snd z anchorsEncoding).prod (hu.snd'.comp (fst z anchorsEncoding)))
  have ht := optionBindWithInput (ea := e) (eb := a) (ec := anchorOutputEncoding q)
    (f := fun p data => (SourceCoreReplay.decodeAnchors p.1.1 p.1.2 (SourceCoreReplay.patchKeys p.1.2 p.2.1)
      data.1).map (fun roots => (roots,data.2))) hi hout
  exact ht.of_enc_eq (fun _ => rfl)

private def readBody (pad : Fin q) (b t l count : ℕ) (w : QWord q) : Option (Header q) :=
  let E := edits t*count
  (readEntries pad E (gram q b t l) b w).bind fun d =>
    (readAnchors l E d.1 d.2).map fun a => ⟨count,d.1,a.1,a.2⟩

private theorem readBody_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × QWord q => readBody pad b t p.1.1 p.1.2 p.2)
      (entriesInputEncoding q) (encOption (headerEncoding q)) := by
  let e := entriesInputEncoding q
  let a := entriesOutputEncoding q
  let u := anchorOutputEncoding q
  let z := encPair e a
  let w := wordEncoding q
  have hp := fst (encPair encUnary encUnary) w
  have hl := hp.fst'
  have hc := hp.snd'
  have hE := unary_mul' (const (edits t)) hc
  have hL := (UniformParameters.gram_machine q b t).comp hl
  have he := (readEntries_polyTime pad b hq).comp (encIn := e) ((hE.prod hL).prod
    (snd (encPair encUnary encUnary) w))
  have hx := fst e a
  have hz := snd e a
  have hroots := (readAnchors_polyTime q hq).comp (encIn := z) (((hl.prod hE).comp hx).prod hz)
  have d := fst z u
  have f := snd z u
  have hbuild := headerEncoding_mk_polyTime q ((hc.comp hx).comp d) (hz.fst'.comp d) f.fst' f.snd'
  have h := optionMapWithInput (encA := z) (encB := u) (encC := headerEncoding q)
    (f := fun p roots => ⟨p.1.1.2,p.2.1,roots.1,roots.2⟩) hroots hbuild
  have ht := optionBindWithInput (ea := e) (eb := a) (ec := headerEncoding q)
    (f := fun p data => (readAnchors p.1.1 (edits t*p.1.2) data.1 data.2).map
      (fun roots => ⟨p.1.2,data.1,roots.1,roots.2⟩)) he h
  exact ht.of_enc_eq (fun _ => rfl)

def readHeader (pad : Fin q) (b t l : ℕ) (w : QWord q) : Option (Header q) := do
  let D := witnessLimit q b t l
  let (d, rest) ← SourcePayloadIndex.readIndex q (D+1) w
  readBody pad b t l (min d D) rest

theorem readHeader_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : ℕ × QWord q => readHeader pad b t p.1 p.2)
      (encPair encUnary (wordEncoding q)) (encOption (headerEncoding q)) := by
  let w := wordEncoding q
  let e := encPair encUnary w
  let a := SourcePayloadIndex.readEncoding q
  let z := encPair e a
  have hl := fst encUnary w
  have hw := snd encUnary w
  have hD := unary_add' (unary_mul' (const (8*edits t)) ((UniformParameters.cutoff_machine q b t).comp hl)) (const 1)
  have hbound := unary_to_binary.comp (unary_add' hD (const 1))
  have hhead := (readIndex_polyTime q hq).comp (encIn := e) (hbound.prod hw)
  have hf := fst e a
  have hd := snd e a
  have hm := hD.comp hf
  have hc := binary_to_unary_bounded (binary_min' hd.fst' (unary_to_binary.comp hm)) hm
    (fun _ => Nat.min_le_right ..)
  have h := (readBody_polyTime pad b t hq).comp (encIn := z) (((hl.comp hf).prod hc).prod hd.snd')
  exact optionBindWithInput (ea := e) (eb := a) (ec := headerEncoding q)
    (f := fun p d => readBody pad b t p.1 (min d.1 (witnessLimit q b t p.1)) d.2) hhead h

def writeHeader (pad : Fin q) (b t l count : ℕ) (code : Description q) (roots : List ℕ) : QWord q :=
  let E := edits t * count
  let L := gram q b t l
  SourcePayloadIndex.writeIndex pad (witnessLimit q b t l+1) count ++
    SourcePayloadIndex.writeIndex pad (ReplayGrammar.descriptionBound E L b q) (SourceDescriptionIndex.pack E L b code) ++
    SourcePayloadIndex.writeIndex pad (l^roots.length) (SourceRadix.littleValue l roots)

theorem writeHeader_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hl : 0 < l)
    (count : Fin (witnessLimit q b t l+1))
    (code : ReplayGrammar.DescriptionCode (edits t*count.val) (gram q b t l) b q) (ds : List (ReplayGrammar.DecodedEntry q))
    (roots : ↥(CoreWeight.patchKeys (edits t*count.val) ds) → Fin l) :
    let P := CoreWeight.patchKeys (edits t*count.val) ds
    writeHeader pad b t l count.val (descriptionData code) (List.ofFn fun i : Fin P.card =>
      (roots (P.orderIsoOfFin rfl i)).val) = PeelingFrame.writeHeader (by omega) hl count code ds roots := by
  dsimp only
  let P := CoreWeight.patchKeys (edits t*count.val) ds
  unfold writeHeader PeelingFrame.writeHeader
  dsimp only
  rw [SourcePayloadIndex.writeIndex_eq pad hq, SourceDescriptionIndex.pack_eq,
    SourcePayloadIndex.writeIndex_eq pad hq, List.length_ofFn, SourceRadix.littleValue_eq, ofDigits_ofFn]
  have he : (RulePatch.packAnchors hl P le_rfl roots).val = ∑ i : Fin P.card,
      (roots (P.orderIsoOfFin rfl i)).val*l^i.val := by
    unfold RulePatch.packAnchors
    simp only [Fin.val_castLE, finFunctionFinEquiv_apply]
  rw [← he, SourcePayloadIndex.writeIndex_eq pad hq]

abbrev writeEncoding (q : ℕ) :=
  encPair (encPair encUnary encUnary) (encPair (descriptionEncoding q) (encList encUnary))

theorem writeHeader_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × (Description q × List ℕ) =>
      writeHeader pad b t p.1.1 p.1.2 p.2.1 p.2.2) (writeEncoding q) (wordEncoding q) := by
  let e := writeEncoding q
  let w := wordEncoding q
  let a := encPair (descriptionEncoding q) (encList encUnary)
  have hl := (fst (encPair encUnary encUnary) a).fst'
  have hc := (fst (encPair encUnary encUnary) a).snd'
  have hcode := (snd (encPair encUnary encUnary) a).fst'
  have hroots := (snd (encPair encUnary encUnary) a).snd'
  have hD := unary_add' (unary_mul' (const (8*edits t)) ((UniformParameters.cutoff_machine q b t).comp hl)) (const 1)
  have hb := unary_to_binary.comp (unary_add' hD (const 1))
  have hcword := (writeIndex_polyTime pad hq).comp (hb.prod (unary_to_binary.comp hc))
  have hE := unary_mul' (const (edits t)) hc
  have hL := (UniformParameters.gram_machine q b t).comp hl
  have hbound := (descriptionBound_polyTime q b).comp (hE.prod hL)
  have he := (pack_polyTime q hq).comp ((hE.prod (hL.prod (const (encOut := encUnary) b))).prod hcode)
  have hw := (writeIndex_polyTime pad hq).comp (hbound.prod he)
  have hn := (length_list encUnary).comp hroots
  have hpow := binary_pow.comp ((unary_to_binary.comp hl).prod hn)
  have hrank := SourceRadix.littleValue_polyTime.comp
    ((unary_to_binary.comp hl).prod ((ComputableInPolyTime.map unary_to_binary).comp hroots))
  have hr := (writeIndex_polyTime pad hq).comp (hpow.prod hrank)
  have h := listAppend' (listAppend' hcword hw) hr
  refine h.of_enc_eq ?_
  intro p
  apply congrArg (wordEncoding q)
  simp [writeHeader, Function.comp_def, witnessLimit, Nat.mul_assoc]

def anchorsData (P : Finset (Fin E)) (roots : ↥P → Fin l) : Anchors :=
  List.ofFn (fun i : Fin E => (CoreWeight.anchorLookup P roots i.val).map Fin.val)

theorem anchorsData_at (P : Finset (Fin E)) (roots : ↥P → Fin l) (i : ℕ) :
    anchorAt (anchorsData P roots) i = (CoreWeight.anchorLookup P roots i).map Fin.val := by
  by_cases h : i < E
  · exact BooleanFibres.ofFn_getD _ ⟨i,h⟩ _
  · simp [anchorAt, anchorsData, CoreWeight.anchorLookup, h, List.getD_eq_getElem?_getD,
]

theorem decodeAnchors_data_eq (P : Finset (Fin E)) (k : Fin (l^P.card)) :
    decodeAnchors l E (P.sort.map Fin.val) k.val =
      (RulePatch.unpackAnchors P k).map (anchorsData P) := by
  unfold decodeAnchors RulePatch.unpackAnchors
  simp only [List.length_map, Finset.length_sort, k.isLt, ↓reduceIte, ↓reduceDIte, Option.map_some]
  congr 1
  apply List.ext_getElem
  · simp [anchorTable, anchorsData]
  · intro i hi hj
    have h := (table_eq P k i).trans (anchorsData_at P _ i).symm
    simpa only [anchorAt, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using h

def headerData {s D : ℕ} (h : PeelingFrame.Header l q s D) : Header q :=
  ⟨h.count.val, h.entries.map decodedData, anchorsData _ h.roots, h.tail⟩

theorem readHeader_eq (pad : Fin q) (b t l : ℕ) (hq : 2 ≤ q) (w : QWord q) :
    readHeader pad b t l w =
      (PeelingFrame.readHeader l q (edits t) (witnessLimit q b t l) (gram q b t l) b w).map headerData := by
  unfold readHeader PeelingFrame.readHeader
  dsimp only
  rw [readIndex_eq]
  cases h₀ : ReplayPayload.readIndex (witnessLimit q b t l+1) w with
  | none => rfl
  | some i =>
    obtain ⟨d,rest⟩ := i
    simp only [Option.map_some, bind, Option.bind]
    rw [Nat.min_eq_left (Nat.le_of_lt_succ d.isLt)]
    unfold readBody readEntries
    dsimp only
    rw [readIndex_eq]
    cases h₁ : ReplayPayload.readIndex (ReplayGrammar.descriptionBound
        (edits t*d.val) (gram q b t l) b q) rest with
    | none => rfl
    | some i =>
      obtain ⟨a,rest⟩ := i
      simp only [Option.map_some, bind, Option.bind]
      rw [unpack_eq pad hq]
      cases h₂ : ReplayGrammar.unpackDescription a with
      | none => rfl
      | some c =>
        simp only [Option.map_some, bind, Option.bind]
        rw [decodeDescription_eq]
        cases h₃ : ReplayGrammar.decodeDescription c with
        | none => rfl
        | some ds =>
          simp only [Option.map_some, bind, Option.bind]
          unfold readAnchors
          dsimp only
          rw [patchKeys_eq, List.length_map, Finset.length_sort, readIndex_eq]
          cases h₄ : ReplayPayload.readIndex (l^(CoreWeight.patchKeys (edits t*d.val) ds).card) rest with
          | none => rfl
          | some i =>
            obtain ⟨k,tail⟩ := i
            simp only [Option.map_some, bind, Option.bind]
            rw [decodeAnchors_data_eq]
            cases RulePatch.unpackAnchors (CoreWeight.patchKeys (edits t*d.val) ds) k <;> rfl

#print axioms materialize_eq
#print axioms materialize_polyTime
#print axioms programGraph_eq
#print axioms readHeader_polyTime
#print axioms readHeader_eq
#print axioms writeHeader_polyTime
#print axioms writeHeader_eq

end DeletionCode.Explicit.Machine.SourcePeelingFrame
