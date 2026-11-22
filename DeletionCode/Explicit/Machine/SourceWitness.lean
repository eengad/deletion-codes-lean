import DeletionCode.Explicit.Machine.SourceCompact
import DeletionCode.Explicit.Machine.SourceRecognition
import DeletionCode.Explicit.WitnessSlice
import DeletionCode.Explicit.WitnessMarks

/-! Serialize the dictionary selections on first-event witness gates. -/
namespace DeletionCode.Explicit.Machine.SourceWitness

open LetterGraphCuts LetterSequence LiftDictionary ReplayEntry
open SourceDictionary SourceGrammar SourceLetters SourcePrepare SourceReference
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {q ℓ L : ℕ}

private def relativeReference (anchor : ℕ) (location : LocationData) : Ref :=
  location.2.elim ((location.1 : ℤ) - (anchor : ℤ), none)
    (fun supplier => (0, some (location.1, supplier)))

private theorem relativeReference_eq (anchor : Fin ℓ) (location : Location) :
    relativeReference anchor.val (locationData location) = referenceData (location.reference anchor) := by
  cases location <;> rfl

private theorem relativeReference_polyTime :
    ComputableInPolyTime (fun p : ℕ × LocationData => relativeReference p.1 p.2)
      (encPair encUnary locationEncoding) refEncoding := by
  let e := encPair encUnary locationEncoding
  let s := encPair encBool encUnary
  have ha := fst encUnary locationEncoding
  have hl := snd encUnary locationEncoding
  have hz := intBin_sub' (intBin_natCast.comp (unary_to_binary.comp hl.fst'))
    (intBin_natCast.comp (unary_to_binary.comp ha))
  have hs := (optionSome supplierEncoding).comp ((hl.fst'.comp (fst e s)).prod (snd e s))
  exact optionElimWithInput (encA := e) (encB := s) (encC := refEncoding)
    (body := fun x value => (0, some (x.2.1, value))) hl.snd'
    (hz.prod (const none)) ((const 0).prod hs)

abbrev gateInputEncoding (q : ℕ) :=
  encPair (encPair (wordEncoding q) (encPair encUnary encUnary)) (preparedEncoding q)

def gateEntry (pad : Fin q) (word : QWord q) (patch anchor : ℕ) (gate : Prepared q) : Decoded q :=
  ⟨gate.rule, patch, gate.left, gate.right,
    spell pad word (window gate.negative gate.left gate.removed), gate.replacement,
    gate.windows.map (fun occ => relativeReference anchor occ.1), false, false⟩

theorem gateEntry_eq (pad : Fin q) (word : Fin ℓ → Fin q) (patch : ℕ) (anchor : Fin ℓ)
    (gate : PreparedBubble ℓ L (Fin q)) :
    gateEntry pad (List.ofFn word) patch anchor.val (preparedData gate) =
      decodedData ⟨gate.replayEntry word patch anchor, false, false⟩ := by
  have h : gate.left + gate.removed ≤ gate.left + gate.removed + gate.right := by omega
  have hr : spell pad (List.ofFn word) (window (liftData gate.gate.negative) gate.left gate.removed) =
      List.ofFn (fun i : Fin gate.removed =>
        gate.gate.negative.spelling word ⟨gate.left + i.val, by have := i.isLt; omega⟩) := by
    rw [window_eq _ _ _ h, spell_eq]
    rfl
  simp [gateEntry, preparedData, decodedData, PreparedBubble.replayEntry, hr,
    List.map_map, Function.comp_def, occurrenceData, relativeReference_eq]

theorem gateEntry_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun p : (QWord q × (ℕ × ℕ)) × Prepared q =>
      gateEntry pad p.1.1 p.1.2.1 p.1.2.2 p.2) (gateInputEncoding q) (decodedEncoding q) := by
  let w := wordEncoding q
  let e := gateInputEncoding q
  let a := occurrenceEncoding q
  let d := encPair w (encPair encUnary encUnary)
  have hx := fst d (preparedEncoding q)
  have hg := snd d (preparedEncoding q)
  have hl := preparedEncoding_left_polyTime q hg
  have hu := preparedEncoding_removed_polyTime q hg
  have hn := preparedEncoding_negative_polyTime q hg
  have hv := (window_polyTime q).comp (encIn := e) (hn.prod (hl.prod hu))
  have hr := (spell_polyTime pad).comp (hx.fst'.prod hv)
  have ha := hx.snd'.snd'.comp (fst e a)
  have ho := (snd e a).fst'
  have hloc := relativeReference_polyTime.comp (encIn := encPair e a) (ha.prod ho)
  have hrefs := mapWithInput (encIn := e) (encA := a) (encB := refEncoding)
    (f := fun p occ => relativeReference p.1.2.2 occ.1)
    (preparedEncoding_windows_polyTime q hg) hloc
  exact decodedEncoding_mk_polyTime q (preparedEncoding_rule_polyTime q hg) hx.snd'.fst' hl
    (preparedEncoding_right_polyTime q hg) hr (preparedEncoding_replacement_polyTime q hg)
    hrefs (const false) (const false)

def suppliers (entry : Decoded q) : List ℕ :=
  entry.refs.filterMap fun ref => ref.2.map Prod.fst

theorem suppliers_eq (entry : ReplayGrammar.DecodedEntry q) :
    (suppliers (decodedData entry)).toFinset = entry.entry.suppliers := by
  unfold suppliers decodedData Entry.suppliers
  rw [List.filterMap_map]
  congr 1
  apply List.filterMap_congr
  intro ref _
  cases ref <;> rfl

theorem suppliers_polyTime (q : ℕ) :
    ComputableInPolyTime (suppliers (q := q)) (decodedEncoding q) PatchGraph.rowEncoding := by
  let e := decodedEncoding q
  let a := encPair e refEncoding
  have h := (snd e refEncoding).snd'
  have hp := optionMapWithInput (encA := a) (encB := supplierEncoding) (encC := encUnary)
    (f := fun _ supplier => supplier.1) h (snd a supplierEncoding).fst'
  have hf := flatMapWithInput (encIn := e) (encA := refEncoding) (encB := encUnary)
    (f := fun _ ref => (ref.2.map Prod.fst).toList) (decodedEncoding_refs_polyTime q id')
    ((SourceLists.optionToList_polyTime encUnary).comp hp)
  exact hf.of_enc_eq (fun entry => congrArg _ (List.filterMap_eq_flatMap_toList _ entry.refs))

def relabel (entries rules : List ℕ) (entry : Decoded q) : Decoded q :=
  { entry with
    rule := SourceCompact.index rules entry.rule
    refs := entry.refs.map (SourceCompact.rename entries) }

theorem relabel_eq {N M : ℕ} (entries : Finset (Fin N)) (rules : Finset (Fin M))
    (entry : ReplayGrammar.DecodedEntry q) :
    relabel (entries.sort.map Fin.val) (rules.sort.map Fin.val) (decodedData entry) =
      decodedData { entry with entry := entry.entry.relabel (compactIndex entries) (compactIndex rules) } := by
  simp only [relabel, decodedData, Entry.relabel, SourceCompact.index_eq, List.map_map, Function.comp_def,
    SourceCompact.rename_eq]

abbrev relabelEncoding (q : ℕ) :=
  encPair (encPair PatchGraph.rowEncoding PatchGraph.rowEncoding) (decodedEncoding q)

theorem relabel_polyTime (q : ℕ) :
    ComputableInPolyTime (fun p : (List ℕ × List ℕ) × Decoded q => relabel p.1.1 p.1.2 p.2)
      (relabelEncoding q) (decodedEncoding q) := by
  let k := PatchGraph.rowEncoding
  let e := relabelEncoding q
  let d := decodedEncoding q
  have hkeys := fst (encPair k k) d
  have hentry := snd (encPair k k) d
  have hr := SourceCompact.index_polyTime.comp (hkeys.snd'.prod (decodedEncoding_rule_polyTime q hentry))
  have hm := SourceCompact.rename_polyTime.comp ((hkeys.fst'.comp (fst e refEncoding)).prod (snd e refEncoding))
  have hrefs := mapWithInput (encIn := e) (encA := refEncoding) (encB := refEncoding)
    (f := fun p ref => SourceCompact.rename p.1.1 ref) (decodedEncoding_refs_polyTime q hentry) hm
  exact decodedEncoding_mk_polyTime q hr (decodedEncoding_patch_polyTime q hentry)
    (decodedEncoding_left_polyTime q hentry) (decodedEncoding_right_polyTime q hentry)
    (decodedEncoding_removed_polyTime q hentry) (decodedEncoding_replacement_polyTime q hentry)
    hrefs (decodedEncoding_finalBubble_polyTime q hentry) (decodedEncoding_finalRule_polyTime q hentry)

theorem filter_finRange_eq_sort {N : ℕ} (keys : Finset (Fin N)) :
    ((List.finRange N).filter (fun i => decide (i ∈ keys))) = keys.sort := by
  have hn := (List.nodup_finRange N).filter (fun i => decide (i ∈ keys))
  have hs : ((List.finRange N).filter (fun i => decide (i ∈ keys))).Pairwise (· ≤ ·) :=
    ((List.pairwise_lt_finRange N).imp le_of_lt).filter _
  apply List.Perm.eq_of_pairwise' hs (keys.pairwise_sort _)
  apply (List.perm_ext_iff_of_nodup hn (keys.sort_nodup _)).mpr
  simp

private theorem patches_eq (pad : Fin q) {s : ℕ} (hs : Recognizer.History ℓ q L s) :
    SourcePatchTable.patches (SourceRecognition.gates pad (SourceRecognition.historyData hs)) =
      (CreationInterval.coalesce (PatchTable.intervals (Recognizer.gates hs))).map PatchMerge.data := by
  let gate := fun e : Fin hs.length × Fin s => preparedData ((hs.get e.1).bubbles e.2)
  let ms := fun e => SourcePrepare.marks (gate e)
  let stock := fun e => SourcePrepare.stock pad (gate e)
  have h : SourceRecognition.gates pad (SourceRecognition.historyData hs) =
      SourcePatchTable.tabulate (Recognizer.gates hs) ms stock := by
    unfold SourceRecognition.gates SourceRecognition.historyData SourcePatchTable.tabulate
    rw [List.map_map]
    have hh : List.ofFn (fun i : Fin hs.length => hs.get i) = hs := by simp
    conv_lhs => rw [← hh, List.map_ofFn]
    simp only [show List.finRange hs.length = List.ofFn (fun i : Fin hs.length => i) from rfl,
      show List.finRange s = List.ofFn (fun i : Fin s => i) from rfl,
      SourceRecognition.batchData, List.map_ofFn, Function.comp_def]
    congr 1
    funext i
    congr 1
    funext j
    exact SourcePrepare.record_eq pad ((hs.get i).bubbles j)
  rw [h, SourcePatchTable.patches_eq]

def patchStarts (pad : Fin q) (hs : SourceRecognition.History q) : List ℕ :=
  (SourcePatchTable.patches (SourceRecognition.gates pad hs)).map Prod.fst

theorem patchStarts_eq (pad : Fin q) {s : ℕ} (hs : Recognizer.History ℓ q L s)
    (p : Fin (PatchTable.patchCount (Recognizer.gates hs))) :
    (patchStarts pad (SourceRecognition.historyData hs)).getD p.val 0 = (Recognizer.patchAnchor hs p).val := by
  unfold patchStarts
  rw [patches_eq, List.map_map]
  have h : p.val < ((CreationInterval.coalesce (PatchTable.intervals (Recognizer.gates hs))).map
      (Prod.fst ∘ PatchMerge.data)).length := by simp [PatchTable.patchCount]
  rw [List.getD_eq_getElem _ _ h, List.getElem_map]
  rfl

private def emptyPrepared (q : ℕ) : Prepared q := ⟨0, 0, 0, 0, 0, [], [], []⟩

private def preparedAt (hs : SourceRecognition.History q) (i j : ℕ) : Prepared q :=
  ((hs.getD i ([], [])).2).getD j (emptyPrepared q)

private theorem preparedAt_eq {s : ℕ} (hs : Recognizer.History ℓ q L s) (i : Fin hs.length) (j : Fin s) :
    preparedAt (SourceRecognition.historyData hs) i.val j.val = preparedData ((hs.get i).bubbles j) := by
  have hi : i.val < (hs.map SourceRecognition.batchData).length := by simp
  unfold preparedAt SourceRecognition.historyData
  rw [List.getD_eq_getElem _ _ hi, List.getElem_map]
  exact BooleanFibres.ofFn_getD _ j _

def patchOfEntry (graph : PatchGraph.Graph) (s j : ℕ) : ℕ :=
  (graph.2.getD (j / s) []).getD (j % s) 0

theorem patchOfEntry_eq {d s c : ℕ} (a : RulePatch.Incidence d s c) (j : Fin (d*s)) :
    patchOfEntry (PatchGraph.graphData a) s j.val = (a (finProdFinEquiv.symm j)).val := by
  let e := finProdFinEquiv.symm j
  change ((List.ofFn (fun i : Fin d => List.ofFn (fun k : Fin s => (a (i,k)).val))).getD e.1.val []).getD e.2.val 0 = _
  rw [BooleanFibres.ofFn_getD _ e.1 [], BooleanFibres.ofFn_getD _ e.2 0]

abbrev patchOfEntryEncoding := encPair PatchGraph.graphEncoding (encPair encUnary encUnary)

theorem patchOfEntry_polyTime : ComputableInPolyTime
    (fun p : PatchGraph.Graph × (ℕ × ℕ) => patchOfEntry p.1 p.2.1 p.2.2)
    patchOfEntryEncoding encUnary := by
  let n := encPair encUnary encUnary
  have hg := fst PatchGraph.graphEncoding n
  have hp := snd PatchGraph.graphEncoding n
  have hrow := listGetDWithInput hg.snd' (unary_div' hp.snd' hp.fst') ([] : List ℕ)
  exact listGetDWithInput hrow (unary_mod' hp.snd' hp.fst') 0

def entries (pad : Fin q) (s root : ℕ) (word : QWord q) (hs : SourceRecognition.History q) : List (Decoded q) :=
  let graph := SourceRecognition.graph pad hs
  let keys := PatchGraph.patchIds graph root
  let starts := patchStarts pad hs
  (List.range (hs.length * s)).map fun j =>
    let patch := patchOfEntry graph s j
    gateEntry pad word (SourceCompact.index keys patch) (starts.getD patch 0) (preparedAt hs (j / s) (j % s))

theorem entries_eq (pad : Fin q) {s : ℕ} (hs : Recognizer.History ℓ q L s)
    (root : Recognizer.RuleVertex hs) (word : Fin ℓ → Fin q) :
    entries pad s (PatchGraph.vertexNumber root) (List.ofFn word) (SourceRecognition.historyData hs) =
      List.ofFn fun j : Fin (hs.length * s) => decodedData ⟨Recognizer.witnessEntry hs root word j, false, false⟩ := by
  unfold entries
  simp only [SourceRecognition.historyData_length, SourceRecognition.graph_eq]
  rw [SourceLists.range_map_eq]
  congr 1
  funext j
  let e := finProdFinEquiv.symm j
  change gateEntry pad (List.ofFn word) _ _ (preparedAt (SourceRecognition.historyData hs) e.1.val e.2.val) = _
  rw [patchOfEntry_eq, patchStarts_eq, preparedAt_eq, PatchGraph.patchIds_eq, filter_finRange_eq_sort,
    SourceCompact.index_eq, gateEntry_eq]
  rfl

theorem patchStarts_polyTime (pad : Fin q) :
    ComputableInPolyTime (patchStarts pad) (SourceRecognition.historyEncoding q) PatchGraph.rowEncoding := by
  have hp := (SourcePatchTable.patches_polyTime (SourceLetters.letterEncoding q)).comp
    (SourceRecognition.gates_polyTime pad)
  exact (ComputableInPolyTime.map (fst encUnary encUnary)).comp hp

abbrev entriesEncoding (q : ℕ) :=
  encPair (encPair encUnary encUnary) (encPair (wordEncoding q) (SourceRecognition.historyEncoding q))

theorem entries_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × (QWord q × SourceRecognition.History q) =>
      entries pad p.1.1 p.1.2 p.2.1 p.2.2) (entriesEncoding q) (decodedListEncoding q) := by
  let e := entriesEncoding q
  let a := encPair e encUnary
  let b := SourceRecognition.batchEncoding q
  let c := encPair encUnary encUnary
  let w := encPair (wordEncoding q) (SourceRecognition.historyEncoding q)
  have hparams := fst c w
  have hdata := snd c w
  have hh := hdata.snd'
  have hlen := unary_mul' ((length_list b).comp hh) hparams.fst'
  have he := fst e encUnary
  have hj := snd e encUnary
  have hs := hparams.fst'.comp he
  have hi := unary_div' hj hs
  have hk := unary_mod' hj hs
  have hg := (SourceRecognition.graph_polyTime pad).comp hh
  have hp := patchOfEntry_polyTime.comp ((hg.comp he).prod (hs.prod hj))
  have hkeys := PatchGraph.patchIds_polyTime.comp (hg.prod hparams.snd')
  have hc := SourceCompact.index_polyTime.comp ((hkeys.comp he).prod hp)
  have hstart := listGetDWithInput (((patchStarts_polyTime pad).comp hh).comp he) hp 0
  have hpairs := listGetDWithInput (hh.comp he) hi (([], []) : SourceRecognition.Batch q)
  have hgate := listGetDWithInput hpairs.snd' hk (emptyPrepared q)
  have h := (gateEntry_polyTime pad).comp (encIn := a)
    (((hdata.fst'.comp he).prod (hc.prod hstart)).prod hgate)
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := decodedEncoding q)
    (f := fun p j =>
      let graph := SourceRecognition.graph pad p.2.2
      let patch := patchOfEntry graph p.1.1 j
      gateEntry pad p.2.1 (SourceCompact.index (PatchGraph.patchIds graph p.1.2) patch)
        ((patchStarts pad p.2.2).getD patch 0) (preparedAt p.2.2 (j / p.1.1) (j % p.1.1)))
    (unary_range' hlen) (h.of_enc_eq (fun _ => rfl))

def retainedIds (graph : PatchGraph.Graph) (s root : ℕ) : List ℕ :=
  let rules := PatchGraph.ruleIds graph root
  (List.range (graph.2.length * s)).filter fun j => rules.contains (j / s)

theorem retainedIds_eq {s : ℕ} (hs : Recognizer.History ℓ q L s) (root : Recognizer.RuleVertex hs) :
    retainedIds (PatchGraph.graphData (PatchTable.incidence (Recognizer.gates hs))) s
      (PatchGraph.vertexNumber root) = (Recognizer.retainedEntries hs root).sort.map Fin.val := by
  unfold retainedIds
  rw [PatchGraph.ruleIds_eq, filter_finRange_eq_sort, ← filter_finRange_eq_sort (Recognizer.retainedEntries hs root)]
  simp only [PatchGraph.graphData, List.length_ofFn]
  rw [show List.range (hs.length * s) = (List.finRange (hs.length * s)).map Fin.val by simp, List.filter_map]
  congr 1
  apply List.filter_congr
  intro j _
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_def, List.contains_iff_mem, List.mem_map, Finset.mem_sort,
    decide_eq_true_eq, Recognizer.retainedEntries, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨r, hr, he⟩ => (show r = (finProdFinEquiv.symm j).1 from Fin.ext he) ▸ hr,
    fun h => ⟨_, h, rfl⟩⟩

abbrev retainedInputEncoding := encPair PatchGraph.graphEncoding (encPair encUnary encUnary)

theorem retainedIds_polyTime : ComputableInPolyTime
    (fun p : PatchGraph.Graph × (ℕ × ℕ) => retainedIds p.1 p.2.1 p.2.2)
    retainedInputEncoding PatchGraph.rowEncoding := by
  let e := retainedInputEncoding
  let n := encPair encUnary encUnary
  have hg := fst PatchGraph.graphEncoding n
  have hp := snd PatchGraph.graphEncoding n
  have hr := PatchGraph.ruleIds_polyTime.comp (hg.prod hp.snd')
  have hlen := unary_mul' ((length_list PatchGraph.rowEncoding).comp hg.snd') hp.fst'
  let a := encPair e encUnary
  have h := contains (hr.comp (fst e encUnary)) (unary_div' (snd e encUnary) (hp.fst'.comp (fst e encUnary)))
  exact filterWithInput (encIn := e) (encA := encUnary) (test := fun p j =>
    (PatchGraph.ruleIds p.1 p.2.2).contains (j / p.2.1)) (unary_range' hlen) (h.of_enc_eq (fun _ => rfl))

private def emptyDecoded (q : ℕ) : Decoded q := ⟨0, 0, 0, 0, [], [], [], false, false⟩

def supplierTable (es : List (Decoded q)) (kept : List ℕ) : SourceSlice.Suppliers :=
  (List.range es.length).map fun j =>
    if kept.contains j then
      (List.range es.length).filter (fun i => (suppliers (es.getD j (emptyDecoded q))).contains i)
    else []

private theorem supplierTable_eq {s : ℕ} (hs : Recognizer.History ℓ q L s)
    (root : Recognizer.RuleVertex hs) (word : Fin ℓ → Fin q) :
    supplierTable (List.ofFn fun j => decodedData ⟨Recognizer.witnessEntry hs root word j, false, false⟩)
      ((Recognizer.retainedEntries hs root).sort.map Fin.val) =
      SourceSlice.supplierData (Recognizer.witnessSuppliers hs root word) := by
  unfold supplierTable SourceSlice.supplierData
  simp only [List.length_ofFn]
  rw [SourceLists.range_map_eq]
  congr 1
  funext j
  have hm : ((Recognizer.retainedEntries hs root).sort.map Fin.val).contains j.val =
      decide (j ∈ Recognizer.retainedEntries hs root) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem, List.mem_map, Finset.mem_sort, decide_eq_true_eq]
    exact ⟨fun ⟨k,hk,he⟩ => (show k = j from Fin.ext he) ▸ hk, fun h => ⟨j,h,rfl⟩⟩
  rw [hm, BooleanFibres.ofFn_getD _ j (emptyDecoded q)]
  by_cases h : j ∈ Recognizer.retainedEntries hs root
  · simp only [h, decide_true, ↓reduceIte, Recognizer.witnessSuppliers]
    rw [show List.range (hs.length*s) = (List.finRange (hs.length*s)).map Fin.val by simp,
      List.filter_map]
    congr 1
    apply List.filter_congr
    intro k _
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_def, List.contains_iff_mem, decide_eq_true_eq, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [← List.mem_toFinset, suppliers_eq]
  · simp [h, Recognizer.witnessSuppliers]

abbrev supplierTableEncoding (q : ℕ) := encPair (decodedListEncoding q) PatchGraph.rowEncoding

theorem supplierTable_polyTime (q : ℕ) : ComputableInPolyTime
    (fun p : List (Decoded q) × List ℕ => supplierTable p.1 p.2)
    (supplierTableEncoding q) SourceSlice.suppliersEncoding := by
  let e := supplierTableEncoding q
  let d := decodedEncoding q
  let a := encPair e encUnary
  have hes := fst (decodedListEncoding q) PatchGraph.rowEncoding
  have hkept := snd (decodedListEncoding q) PatchGraph.rowEncoding
  have hids := unary_range' ((length_list d).comp hes)
  have hx := fst e encUnary
  have hj := snd e encUnary
  have hs := (suppliers_polyTime q).comp (listGetDWithInput (hes.comp hx) hj (emptyDecoded q))
  have hm := contains (hs.comp (fst a encUnary)) (snd a encUnary)
  have hf := filterWithInput (encIn := a) (encA := encUnary)
    (test := fun p i => (suppliers (p.1.1.getD p.2 (emptyDecoded q))).contains i) (hids.comp hx) hm
  have hr := contains (hkept.comp hx) hj
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := PatchGraph.rowEncoding)
    (f := fun p j => if p.2.contains j then (List.range p.1.length).filter
      (fun i => (suppliers (p.1.getD j (emptyDecoded q))).contains i) else [])
    hids ((hr.ite' hf (const [])).of_enc_eq (fun _ => rfl))

def sliceIds (es : List (Decoded q)) (kept ends : List ℕ) : List ℕ :=
  SourceSlice.retained (supplierTable es kept) ((List.range es.length).map ends.contains)

theorem sliceIds_eq (pad : Fin q) {s : ℕ} (hs : Recognizer.History ℓ q L s)
    (root : Recognizer.RuleVertex hs) (word : Fin ℓ → Fin q) (ends : Finset (Fin (hs.length*s))) :
    sliceIds (entries pad s (PatchGraph.vertexNumber root) (List.ofFn word) (SourceRecognition.historyData hs))
      ((Recognizer.retainedEntries hs root).sort.map Fin.val) (ends.sort.map Fin.val) =
      (Recognizer.witnessSlice hs root word ends).sort.map Fin.val := by
  unfold sliceIds Recognizer.witnessSlice
  rw [entries_eq, supplierTable_eq, List.length_ofFn, SourceLists.range_map_eq]
  have h : (List.ofFn (fun j : Fin (hs.length*s) => (ends.sort.map Fin.val).contains j.val)) =
      SourceSlice.flags ends := by
    congr 1
    funext j
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem, List.mem_map, Finset.mem_sort, decide_eq_true_eq]
    exact ⟨fun ⟨k,hk,he⟩ => (show k = j from Fin.ext he) ▸ hk, fun h => ⟨j,h,rfl⟩⟩
  rw [h, SourceSlice.retained_eq, filter_finRange_eq_sort]

abbrev sliceInputEncoding (q : ℕ) :=
  encPair (decodedListEncoding q) (encPair PatchGraph.rowEncoding PatchGraph.rowEncoding)

private theorem seed_polyTime :
    ComputableInPolyTime (fun p : List ℕ × ℕ => (List.range p.2).map p.1.contains)
      (encPair PatchGraph.rowEncoding encUnary) PatchGraph.flagsEncoding := by
  let e := encPair PatchGraph.rowEncoding encUnary
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := encBool) (f := fun p j => p.1.contains j)
    (unary_range' (snd PatchGraph.rowEncoding encUnary))
    (contains ((fst PatchGraph.rowEncoding encUnary).comp (fst e encUnary)) (snd e encUnary))

set_option maxHeartbeats 800000 in
theorem sliceIds_polyTime (q : ℕ) :
    ComputableInPolyTime (fun p : List (Decoded q) × (List ℕ × List ℕ) => sliceIds p.1 p.2.1 p.2.2)
      (sliceInputEncoding q) PatchGraph.rowEncoding := by
  let e := sliceInputEncoding q
  let k := PatchGraph.rowEncoding
  have hes := fst (decodedListEncoding q) (encPair k k)
  have hp := snd (decodedListEncoding q) (encPair k k)
  have hf := seed_polyTime.comp (encIn := e) (hp.snd'.prod ((length_list (decodedEncoding q)).comp hes))
  have ht := (supplierTable_polyTime q).comp (encIn := e) (encMid := supplierTableEncoding q) (hes.prod hp.fst')
  have h := SourceSlice.retained_polyTime.comp (encIn := e) (encMid := SourceSlice.sliceEncoding) (ht.prod hf)
  exact h.of_enc_eq (fun _ => rfl)

def describe (es : List (Decoded q)) (rules slice marked : List ℕ) : List (Decoded q) :=
  slice.map fun j =>
    let d := relabel slice rules (es.getD j (emptyDecoded q))
    { d with finalBubble := marked.contains j, finalRule := marked.contains j }

theorem describe_eq (pad : Fin q) {s : ℕ} (hs : Recognizer.History ℓ q L s)
    (root : Recognizer.RuleVertex hs) (word : Fin ℓ → Fin q) (slice : Finset (Fin (hs.length*s)))
    (marked : List ℕ) (mark : Fin (hs.length*s) → Bool) (hmark : ∀ j ∈ slice, marked.contains j.val = mark j) :
    describe (entries pad s (PatchGraph.vertexNumber root) (List.ofFn word) (SourceRecognition.historyData hs))
      ((RulePatch.componentRules (PatchTable.incidence (Recognizer.gates hs)) root).sort.map Fin.val)
      (slice.sort.map Fin.val) marked = (Recognizer.descriptions hs root word slice mark mark).map decodedData := by
  unfold describe
  rw [entries_eq, Recognizer.descriptions_eq_sorted, List.map_map, List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_def]
  rw [BooleanFibres.ofFn_getD _ j (emptyDecoded q), relabel_eq, hmark j ((Finset.mem_sort _).mp hj)]
  rfl

abbrev describeEncoding (q : ℕ) := encPair (decodedListEncoding q)
  (encPair PatchGraph.rowEncoding (encPair PatchGraph.rowEncoding PatchGraph.rowEncoding))

theorem describe_polyTime (q : ℕ) :
    ComputableInPolyTime (fun p : List (Decoded q) × (List ℕ × (List ℕ × List ℕ)) =>
      describe p.1 p.2.1 p.2.2.1 p.2.2.2) (describeEncoding q) (decodedListEncoding q) := by
  let e := describeEncoding q
  let d := decodedEncoding q
  let k := PatchGraph.rowEncoding
  let a := encPair e encUnary
  let x := encPair k (encPair k k)
  have hes := fst (decodedListEncoding q) x
  have hp := snd (decodedListEncoding q) x
  have hx := fst e encUnary
  have hj := snd e encUnary
  have hs := hp.snd'.fst'
  have hm := contains (hp.snd'.snd'.comp hx) hj
  have hr := (relabel_polyTime q).comp (encIn := a)
    (((hs.comp hx).prod (hp.fst'.comp hx)).prod (listGetDWithInput (hes.comp hx) hj (emptyDecoded q)))
  have hd := decodedEncoding_mk_polyTime q (decodedEncoding_rule_polyTime q hr)
    (decodedEncoding_patch_polyTime q hr) (decodedEncoding_left_polyTime q hr)
    (decodedEncoding_right_polyTime q hr) (decodedEncoding_removed_polyTime q hr)
    (decodedEncoding_replacement_polyTime q hr) (decodedEncoding_refs_polyTime q hr) hm hm
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := d)
    (f := fun p j =>
      let d := relabel p.2.2.1 p.2.1 (p.1.getD j (emptyDecoded q))
      { d with finalBubble := p.2.2.2.contains j, finalRule := p.2.2.2.contains j })
    hs (hd.of_enc_eq (fun _ => rfl))

#print axioms gateEntry_eq
#print axioms gateEntry_polyTime
#print axioms suppliers_eq
#print axioms suppliers_polyTime
#print axioms relabel_eq
#print axioms relabel_polyTime
#print axioms entries_eq
#print axioms entries_polyTime
#print axioms retainedIds_eq
#print axioms retainedIds_polyTime
#print axioms supplierTable_polyTime
#print axioms sliceIds_eq
#print axioms sliceIds_polyTime
#print axioms describe_eq
#print axioms describe_polyTime

end DeletionCode.Explicit.Machine.SourceWitness
