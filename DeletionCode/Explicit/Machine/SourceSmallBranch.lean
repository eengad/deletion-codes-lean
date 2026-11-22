import DeletionCode.Explicit.Machine.SourceWitness
import DeletionCode.Explicit.Machine.SourceReplayPayload
import DeletionCode.Explicit.Machine.SourceAcceptance
import DeletionCode.Explicit.SmallCompression
import DeletionCode.Explicit.Machine.SourceFamilyEnumeration
import Batteries.Tactic.OpenPrivate

/-! The one-anchor compression branch on the serialized first-event history. -/
namespace DeletionCode.Explicit.Machine.SourceSmallBranch
set_option maxHeartbeats 600000

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open ConcreteSource SourceGrammar Ternary CataloguePrefix
open _root_.DeletionCode.Explicit.UniformParameters
open FieldHash SourceLists
open private uniformSizes_polyTime from DeletionCode.Explicit.Machine.SourceReplayPayload
open private count_machine from DeletionCode.Explicit.Machine.UniformParameters
open private number_left from DeletionCode.Explicit.Machine.PatchGraph

variable {q ℓ : ℕ}

abbrev WitnessInput (q : ℕ) := ℕ × (ℕ × (QWord q × SourceRecognition.History q))
abbrev witnessEncoding (q : ℕ) := encPair encUnary (encPair encUnary
  (encPair (wordEncoding q) (SourceRecognition.historyEncoding q)))

def isSmall (pad : Fin q) (b t l : ℕ) (record : SourceReplayPayload.Record q) : Bool :=
  let s := SourceReplayFamily.shape record.1 record.2
  let members := SourceFamilyMembers.members pad b t l s
  let families := SourceFamilyEnumeration.families pad b t l
  decide (members.length < 12 * families.length * (hashCount q b t l)^2)

private theorem isSmall_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : minLength q b t ≤ ℓ) (d : ReplayGrammar.DecodedEntry q)
    (v : ReplayEntry.Completed ℓ (Fin q)) :
    isSmall pad b t ℓ (decodedData d, SourceDictionary.store v) =
      SmallCompression.isSmall (b := b) (t := t) pad (d.entry, v) := by
  have hf := congrArg List.length (SourceFamilyEnumeration.families_eq pad b t ℓ hq hb ht hstart)
  simp only [List.length_map] at hf
  simp only [isSmall, SmallCompression.isSmall, SmallCompression.familyCount,
    SourceReplayFamily.shape_eq, SourceFamilyMembers.members_eq, List.length_map, hf]
  rfl

private def encodeGate (pad : Fin q) (b t l : ℕ) (code : Description q) (anchor : ℕ) (word : QWord q) :
    Option (QWord q) := do
  let record ← SourceReplayPayload.materialize pad l (edits t * witnessLimit q b t l) (gram q b t l) b code anchor
  if isSmall pad b t l record then SourceReplayPayload.encode pad b t l code anchor word else none

def tryGate (pad : Fin q) (b t : ℕ) (args : WitnessInput q) (id : ℕ) : Option (QWord q) := do
  let (l, root, word, history) := args
  let s := edits t
  let graph := SourceRecognition.graph pad history
  let es := SourceWitness.entries pad s root word history
  let ids := SourceWitness.retainedIds graph s root
  let slice := SourceWitness.sliceIds es ids [id]
  let rules := PatchGraph.ruleIds graph root
  let E := s * witnessLimit q b t l
  let L := gram q b t l
  let code ← encodeDescription pad E L b (SourceWitness.describe es rules slice [id])
  let patch := SourceWitness.patchOfEntry graph s id
  let anchor := (SourceWitness.patchStarts pad history).getD patch 0
  encodeGate pad b t l code anchor word

private theorem tryGate_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : minLength q b t ≤ ℓ) (word : Fin ℓ → Fin q)
    (hs : Recognizer.History ℓ q (gram q b t ℓ) (edits t)) (root : Recognizer.RuleVertex hs)
    (id : Fin (hs.length * edits t)) :
    tryGate pad b t (ℓ, PatchGraph.vertexNumber root, List.ofFn word, SourceRecognition.historyData hs) id.val =
      SmallCompression.tryGate (by omega : 1 < q) pad word hs root id := by
  unfold tryGate encodeGate SmallCompression.tryGate Recognizer.singleDescription
  dsimp only
  rw [SourceRecognition.graph_eq, SourceWitness.retainedIds_eq]
  let ends : Finset (Fin (hs.length * edits t)) := {id}
  have he : [id.val] = ends.sort.map Fin.val := by simp [ends]
  conv_lhs => rw [he]
  rw [SourceWitness.sliceIds_eq]
  rw [PatchGraph.ruleIds_eq, SourceWitness.filter_finRange_eq_sort]
  have hm : ∀ j ∈ Recognizer.witnessSlice hs root word ends, [id.val].contains j.val = decide (j = id) := by
    intro j _
    apply Bool.eq_iff_iff.mpr
    simp [Fin.ext_iff, eq_comm]
  simp only [← he]
  rw [SourceWitness.describe_eq pad hs root word _ [id.val] (fun j => decide (j = id)) hm]
  rw [SourceGrammar.encodeDescription_eq]
  cases hc : ReplayGrammar.encodeDescription (edits t * witnessLimit q b t ℓ) (gram q b t ℓ) b q pad
      (Recognizer.descriptions hs root word (Recognizer.witnessSlice hs root word ends)
        (fun j => decide (j = id)) (fun j => decide (j = id))) with
  | none => rfl
  | some c =>
    simp only [Option.map_some, bind, Option.bind]
    rw [SourceWitness.patchOfEntry_eq, SourceWitness.patchStarts_eq, SourceReplayPayload.materialize_eq]
    cases hr : ReplayPayload.materialize c (Recognizer.patchAnchor hs
        (LetterGraphCuts.PatchTable.incidence (Recognizer.gates hs) (finProdFinEquiv.symm id))) with
    | none => rfl
    | some p =>
      obtain ⟨d, v⟩ := p
      simp only [Option.map_some, SourceReplayPayload.recordData, isSmall_eq pad b t hq hb ht hstart]
      rw [SourceReplayPayload.encode_eq pad hq]

def packWitness (pad : Fin q) (b t : ℕ) (args : WitnessInput q) : Option (QWord q) :=
  (SourceWitness.retainedIds (SourceRecognition.graph pad args.2.2.2) (edits t) args.2.1).findSome?
    (tryGate pad b t args)

private theorem packWitness_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : minLength q b t ≤ ℓ) (word : Fin ℓ → Fin q)
    (hs : Recognizer.History ℓ q (gram q b t ℓ) (edits t)) (first : Fin hs.length) :
    packWitness pad b t (ℓ, first.val, List.ofFn word, SourceRecognition.historyData hs) =
      SmallCompression.packWitness (by omega : 1 < q) pad word hs first := by
  unfold packWitness SmallCompression.packWitness
  let root : Recognizer.RuleVertex hs := .inl first
  have hr : PatchGraph.vertexNumber root = first.val := number_left first
  rw [SourceRecognition.graph_eq, ← hr, SourceWitness.retainedIds_eq, List.findSome?_map]
  congr 1
  funext id
  exact tryGate_eq pad b t hq hb ht hstart word hs (.inl first) id

def encode (pad : Fin q) (b t : ℕ) (input : SourceAcceptance.Input q) : Option (QWord q) := do
  let (l, rows, word) := input
  if minLength q b t ≤ l ∧ AcceptanceWeights.strong pad b t l word = true then
    let out ← SourceRecognition.recognize pad b t (l, rows, word)
    let first ← out.1
    packWitness pad b t (l, first, word, out.2)
  else none

theorem encode_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (H : Hash q b t ℓ) (word : Fin ℓ → Fin q) :
    encode pad b t (ℓ, matrixRows H, List.ofFn word) = SmallCompression.pack (by omega : 1 < q)
      pad (fun x => AcceptanceWeights.strong pad b t ℓ (List.ofFn x)) H word := by
  unfold encode SmallCompression.pack runAt
  dsimp only
  split
  next h =>
    rw [SourceRecognition.recognize_eq pad b t hq]
    simp only [edits]
    cases hr : Recognizer.recognize (K := windowLength q ℓ) (b := b) (s := 2*t) H pad word (componentCutoff q b t ℓ) with
    | none => simp
    | some result =>
      cases result with
      | complete => simp [SourceRecognition.resultData]
      | firstEvent hs first =>
        simp only [Option.map_some, bind, Option.bind, SourceRecognition.resultData]
        exact packWitness_eq pad b t hq hb ht h.1 word hs first
  next => rfl

theorem decode_eq (pad : Fin q) (b t l : ℕ) (hq : 2 ≤ q) (payload : QWord q) :
    SourceReplayPayload.decode pad b t l payload = (SmallCompression.read q b t l pad payload).map List.ofFn :=
  SourceReplayPayload.decode_eq pad hq b t l payload

private theorem isSmall_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : ℕ × SourceReplayPayload.Record q => isSmall pad b t p.1 p.2)
      (encPair encUnary (SourceReplayPayload.recordEncoding q)) encBool := by
  let r := SourceReplayPayload.recordEncoding q
  let e := encPair encUnary r
  let a := encPair (SourceFamilyMembers.familyShapeEncoding q) rowsEncoding
  let m := encPair (wordEncoding q) (OrderedCatalogue.bubbleEncoding q)
  have hl := fst encUnary r
  have hr := snd encUnary r
  have hs := (SourceReplayFamily.shape_polyTime q).comp hr
  have hm := (SourceFamilyMembers.members_polyTime pad b t hq).comp (hl.prod hs)
  have hf := (SourceFamilyEnumeration.families_polyTime pad b t hq).comp hl
  have hcount := unary_to_binary.comp ((length_list a).comp hf)
  have hhash := (count_machine q b t).comp hl
  have hh := binary_pow.comp (hhash.prod (const (encOut := encUnary) 2))
  exact binary_lt' (unary_to_binary.comp ((length_list m).comp hm))
    (binary_mul' (binary_mul' (const 12) hcount) hh)

private theorem encodeGate_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : (ℕ × (Description q × ℕ)) × QWord q =>
      encodeGate pad b t p.1.1 p.1.2.1 p.1.2.2 p.2)
      (SourceReplayPayload.encodeInput q) (encOption (wordEncoding q)) := by
  let e := SourceReplayPayload.encodeInput q
  let a := encPair (descriptionEncoding q) encUnary
  let r := SourceReplayPayload.recordEncoding q
  let w := wordEncoding q
  have hp := fst (encPair encUnary a) w
  have hc := (uniformSizes_polyTime q b t).comp (encIn := e) hp.fst'
  have hm := (SourceReplayPayload.materialize_polyTime pad).comp (encIn := e)
    (encMid := SourceReplayPayload.grammarInput q) (hc.fst'.prod (hc.snd'.prod hp.snd'))
  have he := fst e r
  have h := (isSmall_polyTime pad b t hq).comp (encIn := encPair e r) ((hp.fst'.comp he).prod (snd e r))
  have ha := (SourceReplayPayload.encode_polyTime pad hq b t).comp he
  exact optionBindWithInput (ea := e) (eb := r) (ec := w) (f := fun p record =>
    if isSmall pad b t p.1.1 record then SourceReplayPayload.encode pad b t p.1.1 p.1.2.1 p.1.2.2 p.2
    else none) hm (h.ite' ha (const none))

private theorem tryGate_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : WitnessInput q × ℕ => tryGate pad b t p.1 p.2)
      (encPair (witnessEncoding q) encUnary) (encOption (wordEncoding q)) := by
  let e := encPair (witnessEncoding q) encUnary
  let d := descriptionEncoding q
  let p := encPair e d
  let h := witnessEncoding q
  have hx := fst h encUnary
  have hi := snd h encUnary
  have hl := hx.fst'
  have hr := hx.snd'.fst'
  have hw := hx.snd'.snd'.fst'
  have hh := hx.snd'.snd'.snd'
  have hs := const (encIn := e) (encOut := encUnary) (edits t)
  have hg := (SourceRecognition.graph_polyTime pad).comp hh
  have hes := (SourceWitness.entries_polyTime pad).comp ((hs.prod hr).prod (hw.prod hh))
  have hk := SourceWitness.retainedIds_polyTime.comp (hg.prod (hs.prod hr))
  have hmarks := cons' hi (const [])
  have ht := (SourceWitness.sliceIds_polyTime q).comp (hes.prod (hk.prod hmarks))
  have hu := PatchGraph.ruleIds_polyTime.comp (hg.prod hr)
  have hz := (SourceWitness.describe_polyTime q).comp (hes.prod (hu.prod (ht.prod hmarks)))
  have hp := (uniformSizes_polyTime q b t).comp hl
  have hc := (encodeDescription_polyTime pad).comp (hp.snd'.prod hz)
  have hpId := SourceWitness.patchOfEntry_polyTime.comp (hg.prod (hs.prod hi))
  have ha := listGetDWithInput ((SourceWitness.patchStarts_polyTime pad).comp hh) hpId 0
  have hdata := (((hl.comp (fst e d)).prod ((snd e d).prod (ha.comp (fst e d)))).prod (hw.comp (fst e d)))
  have hfinish := (encodeGate_polyTime pad b t hq).comp (encIn := p) hdata
  exact optionBindWithInput (f := fun p code =>
    let (l, _, word, _) := p.1
    encodeGate pad b t l code ((SourceWitness.patchStarts pad p.1.2.2.2).getD
      (SourceWitness.patchOfEntry (SourceRecognition.graph pad p.1.2.2.2) (edits t) p.2) 0) word) hc hfinish

private theorem packWitness_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (packWitness pad b t) (witnessEncoding q) (encOption (wordEncoding q)) := by
  let e := witnessEncoding q
  have h := id' (encIn := e)
  have hg := (SourceRecognition.graph_polyTime pad).comp h.snd'.snd'.snd'
  have hi := SourceWitness.retainedIds_polyTime.comp (hg.prod ((const (edits t)).prod h.snd'.fst'))
  exact findSomeWithInput_polyTime (enc := e) (encA := encUnary) (encB := wordEncoding q)
    (f := tryGate pad b t) hi (tryGate_polyTime pad b t hq)

theorem encode_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (encode pad b t) (SourceAcceptance.inputEncoding q) (encOption (wordEncoding q)) := by
  let e := SourceAcceptance.inputEncoding q
  let r := SourceRecognition.resultEncoding q
  let a := encPair e r
  let w := wordEncoding q
  let h := SourceRecognition.historyEncoding q
  have hx := fst encUnary (encPair rowsEncoding w)
  have hw := (snd encUnary (encPair rowsEncoding w)).snd'
  have hs := (Machine.AcceptanceWeights.strong_polyTime pad hq hb ht).comp (hx.prod hw)
  have hmin := bool_not.comp (unary_lt' hx (const (minLength q b t)))
  have hp := fst e r
  have hr := snd e r
  have hcode := (packWitness_polyTime pad b t hq).comp (encIn := encPair a encUnary)
    (((hx.comp hp).comp (fst a encUnary)).prod ((snd a encUnary).prod
      (((hw.comp hp).comp (fst a encUnary)).prod (hr.snd'.comp (fst a encUnary)))))
  have hfirst := optionBindWithInput (ea := a) (eb := encUnary) (ec := w)
    (f := fun p i => packWitness pad b t (p.1.1, i, p.1.2.2, p.2.2)) hr.fst' hcode
  have hrec := optionBindWithInput (ea := e) (eb := r) (ec := w)
    (f := fun p out => out.1.bind (fun i => packWitness pad b t (p.1, i, p.2.2, out.2)))
    (SourceRunBounds.recognize_polyTime pad b t hq) hfirst
  exact ((bool_and' hmin hs).ite' hrec (const none)).of_enc_eq (fun p => by
    by_cases hl : minLength q b t ≤ p.1 <;>
      simp [encode, show (¬p.1 < minLength q b t) ↔ minLength q b t ≤ p.1 by omega, hl]
    rfl)

#print axioms encode_eq
#print axioms encode_polyTime
#print axioms decode_eq

end DeletionCode.Explicit.Machine.SourceSmallBranch
