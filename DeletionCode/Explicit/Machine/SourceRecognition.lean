import DeletionCode.Explicit.Machine.SourcePrepare
import DeletionCode.Explicit.Machine.SourceParts
import DeletionCode.Explicit.Machine.AlignedSourceHash
import DeletionCode.Explicit.ConcreteSource
import Mathlib.Data.List.OfFn

/-! The chronological rule scan on polynomially encoded recognizer histories. -/
namespace DeletionCode.Explicit.Machine.SourceRecognition

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open FieldHash Ternary SourceLists
open SourcePrepare (Prepared preparedData)
open SourceRuleRows (RuleRow)
open CataloguePrefix (matrixRows)

variable {q ℓ K b L s θ R : ℕ}

abbrev Batch (q : ℕ) := Row × List (Prepared q)
abbrev History (q : ℕ) := List (Batch q)
abbrev Result (q : ℕ) := Option ℕ × History q
abbrev State (q : ℕ) := Bool × Option (Result q)

abbrev batchEncoding (q : ℕ) := encPair rowEncoding (SourcePrepare.preparedListEncoding q)
abbrev historyEncoding (q : ℕ) := encList (batchEncoding q)
abbrev resultEncoding (q : ℕ) := encPair (encOption encUnary) (historyEncoding q)
abbrev stateEncoding (q : ℕ) := encPair encBool (encOption (resultEncoding q))

structure Config (q : ℕ) where
  length : ℕ
  gram : ℕ
  width : ℕ
  arity : ℕ
  cutoff : ℕ
  hash : Rows
  word : QWord q
  spectrum : Row
  catalogue : List (RuleRow q)

enc_structure configEncoding (q : ℕ) : Config q where
  length : encUnary, gram : encUnary, width : encUnary, arity : encUnary, cutoff : encUnary,
  hash : rowsEncoding, word : (wordEncoding q), spectrum : rowEncoding,
  catalogue : (SourceRuleRows.tableEncoding q)

def batchData (p : Recognizer.Batch ℓ q L s) : Batch q :=
  (List.ofFn p.row,List.ofFn (preparedData ∘ p.bubbles))

def historyData (hs : Recognizer.History ℓ q L s) : History q := hs.map batchData

@[simp] theorem historyData_length (hs : Recognizer.History ℓ q L s) :
    (historyData hs).length = hs.length := by simp [historyData]

def resultData : Recognizer.Result ℓ q L s → Result q
  | .complete hs => (none,historyData hs)
  | .firstEvent hs i => (some i.val,historyData hs)

def completed (pad : Fin q) (hs : History q) : List (SourceDictionary.Stored q) :=
  hs.flatMap fun b => b.2.map (SourcePrepare.completed pad)

theorem completed_eq (pad : Fin q) (hs : Recognizer.History ℓ q L s) :
    completed pad (historyData hs) = SourceDictionary.historyData (Recognizer.completed hs) := by
  unfold completed historyData SourceDictionary.historyData Recognizer.completed
  rw [List.flatMap_map,Array.toList_ofFn,List.map_ofFn,List.ofFn_mul]
  change _ = (List.ofFn (fun i : Fin hs.length => List.ofFn (fun j : Fin s =>
    SourceDictionary.store ((hs.get (finProdFinEquiv.symm ⟨i.val*s+j.val,_⟩).1).bubbles
      (finProdFinEquiv.symm ⟨i.val*s+j.val,_⟩).2).completed))).flatten
  rw [List.flatMap_def]
  congr 1
  have hh : List.ofFn (fun i : Fin hs.length => hs.get i) = hs := by simp
  conv_lhs => rw [← hh,List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_def,batchData,List.map_ofFn,SourcePrepare.completed_eq]
  congr 1
  funext j
  have hi : i.val*s+j.val < hs.length*s := by
    apply (Nat.add_lt_add_left j.isLt (i.val*s)).trans_le
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right s i.isLt
  have he : (⟨i.val*s+j.val,hi⟩ : Fin (hs.length*s)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*s+j.val = j.val+s*i.val
    ac_rfl
  rw [he,Equiv.symm_apply_apply]

def gates (pad : Fin q) (hs : History q) : SourcePatchTable.Table (SourceLetters.LetterData q) :=
  hs.map (fun b => b.2.map (SourcePrepare.record pad))

def graph (pad : Fin q) (hs : History q) : PatchGraph.Graph := SourcePatchTable.graph (gates pad hs)

theorem graph_eq (pad : Fin q) (hs : Recognizer.History ℓ q L s) :
    graph pad (historyData hs) = PatchGraph.graphData (LetterGraphCuts.PatchTable.incidence (Recognizer.gates hs)) := by
  unfold graph
  let p := fun e : Fin hs.length × Fin s => preparedData ((hs.get e.1).bubbles e.2)
  let ms := fun e => SourcePrepare.marks (p e)
  let ins := fun e => SourcePrepare.stock pad (p e)
  have h : gates pad (historyData hs) = SourcePatchTable.tabulate (Recognizer.gates hs) ms ins := by
    unfold gates historyData SourcePatchTable.tabulate
    rw [List.map_map]
    have hh : List.ofFn (fun i : Fin hs.length => hs.get i) = hs := by simp
    conv_lhs => rw [← hh,List.map_ofFn]
    have h₁ : List.finRange hs.length = List.ofFn (fun i : Fin hs.length => i) := rfl
    have h₂ : List.finRange s = List.ofFn (fun j : Fin s => j) := rfl
    simp only [h₁,h₂,List.map_ofFn,Function.comp_def,batchData,List.map_ofFn]
    congr 1
    funext i
    congr 1
    funext j
    exact SourcePrepare.record_eq pad ((hs.get i).bubbles j)
  rw [h,SourcePatchTable.graph_eq]

def oldRows (hs : History q) : Rows := hs.map Prod.fst

theorem oldRows_eq (hs : Recognizer.History ℓ q L s) :
    oldRows (historyData hs) = (Recognizer.oldRows hs).map List.ofFn := by
  simp [oldRows,historyData,Recognizer.oldRows,List.map_map,Function.comp_def,batchData]

def parts (pad : Fin q) (hs : History q) : List Rows := SourceParts.parts (graph pad hs) (oldRows hs)

theorem parts_eq (pad : Fin q) (hs : Recognizer.History ℓ q L s) :
    parts pad (historyData hs) = List.ofFn (fun i => (Recognizer.parts hs i).map List.ofFn) := by
  unfold parts
  rw [graph_eq,oldRows_eq]
  have h : (Recognizer.oldRows hs).map List.ofFn =
      List.ofFn (fun i : Fin hs.length => List.ofFn (hs.get i).row) := by
    unfold Recognizer.oldRows
    conv_lhs =>
      rw [← show List.ofFn (fun i : Fin hs.length => hs.get i) = hs from by simp,List.map_ofFn,List.map_ofFn]
    rfl
  rw [h,SourceParts.parts_eq]
  rfl

def prep (cfg : Config q) (pad : Fin q) (hs : History q) (r : RuleRow q) : Option (History q) :=
  if r.2.all (fun w => decide (0 < w.1.1.length ∧ 0 < w.1.2.length)) then
    (SourcePrepare.prepareRule pad cfg.length cfg.gram hs.length cfg.word (completed pad hs) r.2).bind
      (fun p => if p.length = cfg.arity then some (hs++[(r.1,p)]) else none)
  else none

def ruleData (pad : Fin q) (words : Fin s → Borrowed.BubbleWord (Fin q) K b L) : RuleRow q :=
  (List.ofFn (CatalogueEnumeration.row pad words),List.ofFn (OrderedCatalogue.bubbleData ∘ words))

def config (pad : Fin q) (H : TernaryMatrix θ (q^L)) (x : Fin ℓ → Fin q) (R : ℕ)
    (catalogue : List (Fin s → Borrowed.BubbleWord (Fin q) K b L)) : Config q :=
  ⟨ℓ,L,q^L,s,R,matrixRows H,List.ofFn x,List.ofFn (Recognizer.spectrum pad x L),
    catalogue.map (ruleData pad)⟩

theorem prep_eq (pad : Fin q) (H : TernaryMatrix θ (q^L)) (x : Fin ℓ → Fin q) (root : Fin ℓ)
    (cat : List (Fin s → Borrowed.BubbleWord (Fin q) K b L)) (hs : Recognizer.History ℓ q L s)
    (ws : Fin s → Borrowed.BubbleWord (Fin q) K b L) :
    prep (config pad H x R cat) pad (historyData hs) (ruleData pad ws) =
      (Recognizer.appendRule pad x root hs ws).map historyData := by
  unfold prep Recognizer.appendRule
  have hall : (List.ofFn (OrderedCatalogue.bubbleData ∘ ws)).all
      (fun w => decide (0 < w.1.1.length ∧ 0 < w.1.2.length)) = true ↔
      ∀ j, 0 < (ws j).left.length ∧ 0 < (ws j).right.length := by
    simp [List.all_eq_true,List.mem_ofFn,Function.comp_def,OrderedCatalogue.bubbleData]
  simp only [config,ruleData,historyData_length]
  by_cases hp : ∀ j, 0 < (ws j).left.length ∧ 0 < (ws j).right.length
  · have hb := hall.mpr hp
    rw [ite_eq_left hb,dite_eq_left hp,completed_eq,SourcePrepare.prepareRule_eq pad x (Recognizer.completed hs) ws root
      hs.length (fun j => (hp j).1) (fun j => (hp j).2)]
    cases h : LetterGraphCuts.prepareRule pad x (Recognizer.completed hs) ws root hs.length
      (fun j => (hp j).1) (fun j => (hp j).2) with
    | none => rfl
    | some p =>
      by_cases hl : p.length = s
      · have hw : List.ofFn (fun i : Fin s => preparedData (p.get (Fin.cast hl.symm i))) =
          p.map preparedData := by
            subst s
            have h : List.ofFn (fun i : Fin p.length => p.get i) = p := by simp
            conv_rhs => rw [← h,List.map_ofFn]
            rfl
        simp only [Option.map_some,Option.bind_some,List.length_map,ite_eq_left hl]
        simp only [bind,Option.bind,dite_eq_left hl,Option.map_some,historyData,List.map_append,List.map_cons,
          List.map_nil,batchData,Function.comp_def,hw]
      · simp [hl]
  · have hb : (List.ofFn (OrderedCatalogue.bubbleData ∘ ws)).all
        (fun w => decide (0 < w.1.1.length ∧ 0 < w.1.2.length)) = false :=
        Bool.eq_false_iff.mpr (fun he => hp (hall.mp he))
    rw [ite_eq_right (Bool.eq_false_iff.mp hb),dite_eq_right hp]
    rfl

def candidate (pad : Fin q) (cfg : Config q) (hs : History q) (r : RuleRow q) : Bool :=
  let ρ := r.1
  let hv := SourceSpectrum.applyRows cfg.width cfg.hash ρ
  hv.all (fun z => decide (z = 0)) &&
    !CanonicalSourceColour.inSpan ((cfg.width,oldRows hs),ρ) &&
    SourceExposure.check ((cfg.length,(cfg.width,parts pad hs)),(cfg.spectrum,ρ))

theorem candidate_eq (pad : Fin q) (H : TernaryMatrix θ (q^L)) (x : Fin ℓ → Fin q)
    (cat : List (Fin s → Borrowed.BubbleWord (Fin q) K b L)) (hs : Recognizer.History ℓ q L s)
    (ws : Fin s → Borrowed.BubbleWord (Fin q) K b L)
    (hr : R ≤ Nat.log 2 ℓ) (hbefore : Recognizer.BeforeEvent hs R) :
    candidate pad (config pad H x R cat) (historyData hs) (ruleData pad ws) =
      Recognizer.candidateOK H pad x hs ws := by
  have hlen (i : Fin hs.length) : (Recognizer.parts hs i).length ≤ R := by
    apply RulePatch.partRows_length_le
    intro j
    exact ((FirstEvent.componentEvent_eq_false _ _ _).mp (hbefore j)).1
  have hh (v : Fin θ → F₃) : (List.ofFn v).all (fun z => decide (z = 0)) = (v == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true,List.mem_ofFn,decide_eq_true_eq,beq_iff_eq]
    constructor
    · intro h
      funext j
      exact h _ ⟨j,rfl⟩
    · intro h j hj
      obtain ⟨i,rfl⟩ := hj
      exact congrFun h i
  unfold candidate Recognizer.candidateOK
  simp only [config,ruleData]
  rw [SourceSpectrum.applyRows_matrix_eq,hh,oldRows_eq,CanonicalSourceColour.inSpan_rows,parts_eq]
  exact congrArg (fun z => (_ && z)) (SourceExposure.check_eq
    (Recognizer.parts hs) (Recognizer.spectrum pad x L) (CatalogueEnumeration.row pad ws)
    (fun i => (FibreEnumeration.separating_length _).trans ((hlen i).trans hr)))

def next (pad : Fin q) (cfg : Config q) (hs : History q) : Option (RuleRow q) :=
  cfg.catalogue.find? (candidate pad cfg hs)

theorem next_eq (pad : Fin q) (H : TernaryMatrix θ (q^L)) (x : Fin ℓ → Fin q)
    (cat : List (Fin s → Borrowed.BubbleWord (Fin q) K b L)) (hs : Recognizer.History ℓ q L s)
    (hr : R ≤ Nat.log 2 ℓ) (hbefore : Recognizer.BeforeEvent hs R) :
    next pad (config pad H x R cat) (historyData hs) =
      (Recognizer.nextRule H pad x hs cat).map (ruleData pad) := by
  unfold next Recognizer.nextRule
  simp only [config,List.find?_map]
  congr 1
  apply List.find?_congr
  intro w _
  exact candidate_eq pad H x cat hs w hr hbefore

def failed (q : ℕ) : State q := (false,none)

def advance (pad : Fin q) (cfg : Config q) (old : ℕ) (hs : History q) : State q :=
  if old < hs.length then
    if PatchGraph.event cfg.arity cfg.cutoff (graph pad hs) old then
      (false,some (some old,hs))
    else (true,some (none,hs))
  else failed q

def tryRule (pad : Fin q) (cfg : Config q) (hs : History q) (w : RuleRow q) : State q :=
  (prep cfg pad hs w).elim (failed q) (advance pad cfg hs.length)

def scan (pad : Fin q) (cfg : Config q) (hs : History q) : State q :=
  (next pad cfg hs).elim (false,some (none,hs)) (tryRule pad cfg hs)

def step (pad : Fin q) (cfg : Config q) (st : State q) : State q :=
  if st.1 then st.2.elim (failed q) (fun out => scan pad cfg out.2) else st

def run (pad : Fin q) (cfg : Config q) (fuel : ℕ) (hs : History q) : Option (Result q) :=
  let st := (step pad cfg)^[fuel] (true,some (none,hs))
  if st.1 then none else st.2

theorem stopped_iterate (pad : Fin q) (cfg : Config q) (out : Option (Result q)) (fuel : ℕ) :
    (step pad cfg)^[fuel] (false,out) = (false,out) := by
  induction fuel with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',ih]; rfl

theorem run_eq (pad : Fin q) (H : TernaryMatrix θ (q^L)) (x : Fin ℓ → Fin q) (root : Fin ℓ)
    (cat : List (Fin s → Borrowed.BubbleWord (Fin q) K b L)) (fuel : ℕ) (hs : Recognizer.History ℓ q L s)
    (hr : R ≤ Nat.log 2 ℓ) (hbefore : Recognizer.BeforeEvent hs R) :
    run pad (config pad H x R cat) fuel (historyData hs) =
      (Recognizer.run H pad x root R cat fuel hs).map resultData := by
  induction fuel generalizing hs with
  | zero => rfl
  | succ fuel ih =>
    unfold run
    rw [Function.iterate_succ_apply]
    rw [Recognizer.run]
    have hnext := next_eq pad H x cat hs hr hbefore
    cases hw : Recognizer.nextRule H pad x hs cat with
    | none =>
      simp [step,scan,tryRule,advance,failed,hnext,hw,stopped_iterate,resultData]
    | some w =>
      have hp := prep_eq pad H x root cat hs w (R := R)
      cases hx : Recognizer.appendRule pad x root hs w with
      | none =>
        simp [step,scan,tryRule,advance,failed,hnext,hw,hp,hx,stopped_iterate]
      | some hs' =>
        obtain ⟨p,hshape,_⟩ := Recognizer.appendRule_shape pad x root hx
        have hlt : hs.length < hs'.length := by simp [hshape]
        let last : Fin hs'.length := ⟨hs.length,hlt⟩
        have he := PatchGraph.event_eq
          (LetterGraphCuts.PatchTable.incidence (Recognizer.gates hs')) R last
        have hEvent : PatchGraph.event (config pad H x R cat).arity (config pad H x R cat).cutoff
            (graph pad (historyData hs')) (historyData hs).length =
            FirstEvent.componentEvent (LetterGraphCuts.PatchTable.incidence (Recognizer.gates hs')) R last := by
          rw [graph_eq,historyData_length]
          exact he
        simp only [historyData_length] at hEvent
        cases hv : FirstEvent.componentEvent
            (LetterGraphCuts.PatchTable.incidence (Recognizer.gates hs')) R last with
        | true =>
          simp [step,scan,tryRule,advance,failed,hnext,hw,hp,hx,hlt,hEvent,hv,stopped_iterate,resultData,last]
        | false =>
          have hb : Recognizer.BeforeEvent hs' R := by
            subst hs'
            exact Recognizer.beforeEvent_append hs p R hbefore hv
          have hstep := ih hs' hb
          unfold run at hstep
          simpa [step,scan,tryRule,advance,failed,hnext,hw,hp,hx,hlt,hEvent,hv,last] using hstep


def recognizeWith (pad : Fin q) (cfg : Config q) : Option (Result q) :=
  if 0 < cfg.length then run pad cfg (cfg.width+1) []
  else some (none,[])

theorem recognizeWith_eq (pad : Fin q) (H : TernaryMatrix θ (q^L)) (x : Fin ℓ → Fin q)
    (hr : R ≤ Nat.log 2 ℓ) :
    recognizeWith pad (config pad H x R (CatalogueEnumeration.rules q K b L s pad)) =
      (Recognizer.recognize (K := K) (b := b) (s := s) H pad x R).map resultData := by
  unfold recognizeWith Recognizer.recognize
  by_cases hp : 0 < ℓ
  · rw [ite_eq_left (show 0 < (config pad H x R _).length from hp),dite_eq_left hp]
    exact run_eq pad H x ⟨0,hp⟩ _ (q^L+1) [] hr (fun i => i.elim0)
  · simp [config,hp,resultData,historyData]

abbrev uniformEncoding (q : ℕ) := encPair encUnary (encPair rowsEncoding (wordEncoding q))

def uniform (pad : Fin q) (b t : ℕ) (x : ℕ × (Rows × QWord q)) : Config q :=
  let l := x.1
  ⟨l,UniformParameters.gram q b t l,SourceHashChoice.width q b t l,2*t,
    UniformParameters.componentCutoff q b t l,x.2.1,x.2.2,
    SourceSpectrum.word pad b t (l,x.2.2),SourceRuleRows.table pad b t l⟩

theorem uniform_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (w : Fin ℓ → Fin q)
    (H : TernaryMatrix θ (q^UniformParameters.gram q b t ℓ)) :
    uniform pad b t (ℓ,(matrixRows H,List.ofFn w)) =
      config pad H w (UniformParameters.componentCutoff q b t ℓ)
        (CatalogueEnumeration.rules q (UniformParameters.windowLength q ℓ) b (UniformParameters.gram q b t ℓ)
          (2*t) pad) := by
  unfold uniform config SourceSpectrum.word SourceHashChoice.width
  dsimp only
  rw [SourceSpectrum.spectrum_recognizer pad hq,SourceRuleRows.table_eq pad b t ℓ hq]
  rfl

def recognize (pad : Fin q) (b t : ℕ) (x : ℕ × (Rows × QWord q)) : Option (Result q) :=
  recognizeWith pad (uniform pad b t x)

theorem recognize_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q)
    (H : TernaryMatrix θ (q^UniformParameters.gram q b t ℓ)) (w : Fin ℓ → Fin q) :
    recognize pad b t (ℓ,(matrixRows H,List.ofFn w)) =
      (Recognizer.recognize (K := UniformParameters.windowLength q ℓ) (b := b) (s := 2*t)
        H pad w (UniformParameters.componentCutoff q b t ℓ)).map resultData := by
  unfold recognize
  rw [uniform_eq pad b t hq]
  exact recognizeWith_eq pad H w (Nat.div_le_self _ _)

#print axioms prep_eq
#print axioms candidate_eq
#print axioms run_eq
#print axioms recognize_eq

theorem completed_polyTime (pad : Fin q) :
    ComputableInPolyTime (completed pad) (historyEncoding q) (SourceDictionary.historyEncoding q) := by
  let e := historyEncoding q
  let b := batchEncoding q
  let h := snd rowEncoding (SourcePrepare.preparedListEncoding q)
  have hr := (ComputableInPolyTime.map (SourcePrepare.completed_polyTime pad)).comp
    (h.comp (snd e b))
  exact flatMapWithInput (encIn := e) (encA := b) (encB := SourceDictionary.storedEncoding q)
    (f := fun _ b => b.2.map (SourcePrepare.completed pad)) id' (hr.of_enc_eq (fun _ => rfl))

theorem gates_polyTime (pad : Fin q) :
    ComputableInPolyTime (gates pad) (historyEncoding q)
      (SourcePatchTable.tableEncoding (SourceLetters.letterEncoding q)) := by
  have h := (ComputableInPolyTime.map (SourcePrepare.record_polyTime pad)).comp
    (snd rowEncoding (SourcePrepare.preparedListEncoding q))
  exact ((ComputableInPolyTime.map h)).of_enc_eq (fun _ => rfl)

theorem graph_polyTime (pad : Fin q) :
    ComputableInPolyTime (graph pad) (historyEncoding q) PatchGraph.graphEncoding :=
  (SourcePatchTable.graph_polyTime (SourceLetters.letterEncoding q)).comp (gates_polyTime pad)

theorem oldRows_polyTime (q : ℕ) :
    ComputableInPolyTime (oldRows (q := q)) (historyEncoding q) rowsEncoding :=
  ComputableInPolyTime.map (fst rowEncoding (SourcePrepare.preparedListEncoding q))

theorem parts_polyTime (pad : Fin q) :
    ComputableInPolyTime (parts pad) (historyEncoding q) SourceExposure.componentsEncoding :=
  SourceParts.parts_polyTime.comp ((graph_polyTime pad).prod (oldRows_polyTime q))

abbrev scanEncoding (q : ℕ) := encPair (configEncoding q) (historyEncoding q)
abbrev candidateEncoding (q : ℕ) := encPair (scanEncoding q) (SourceRuleRows.rowEncoding q)

theorem prep_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : (Config q × History q) × RuleRow q => prep x.1.1 pad x.1.2 x.2)
      (candidateEncoding q) (encOption (historyEncoding q)) := by
  let e := candidateEncoding q
  let c := configEncoding q
  let h := historyEncoding q
  let r := SourceRuleRows.rowEncoding q
  let v := SourcePrepare.preparedListEncoding q
  let p := encPair e v
  have hc := (fst c h).comp (fst (scanEncoding q) r)
  have hh := (snd c h).comp (fst (scanEncoding q) r)
  have hrow := snd (scanEncoding q) r
  have hlen := configEncoding_length_polyTime q hc
  have hL := configEncoding_gram_polyTime q hc
  have hs := configEncoding_arity_polyTime q hc
  have hx := configEncoding_word_polyTime q hc
  have hno := (length_list (batchEncoding q)).comp hh
  have hcomp := (completed_polyTime pad).comp (encIn := e) hh
  have hprep := (SourcePrepare.prepareRule_polyTime pad).comp (encIn := e)
    (encMid := SourcePrepare.ruleInputEncoding q)
    (((hlen.prod hL).prod hno).prod (hcomp.prod (hx.prod hrow.snd')))
  have hp := snd e v
  have hpLen := (length_list (SourcePrepare.preparedEncoding q)).comp hp
  have hcheck := hpLen.decide_eq' (hs.comp (fst e v))
  have hn := (hrow.fst'.comp (fst e v)).prod hp
  have hz := hcheck.ite' ((optionSome h).comp
    (listAppend' (hh.comp (fst e v)) (cons' hn (const [])))) (const none)
  have hf := optionBindWithInput (ea := e) (eb := v) (ec := h)
    (f := fun x ps => if ps.length = x.1.1.arity then some (x.1.2++[(x.2.1,ps)]) else none)
    (hprep.of_enc_eq (fun _ => rfl)) (hz.of_enc_eq (fun _ => by simp [Function.comp_def]))
  let u := OrderedCatalogue.bubbleEncoding q
  have hu := snd e u
  have hlenW := length_list (ExceptionalRecords.letterEncoding q)
  have hflanks := decide_and (unary_lt' (const 0) (hlenW.comp hu.fst'.fst'))
    (unary_lt' (const 0) (hlenW.comp hu.fst'.snd'))
  have hvalid := allWithInput (encIn := e) (encA := u)
    (test := fun _ w => decide (0 < w.1.1.length ∧ 0 < w.1.2.length))
    hrow.snd' hflanks
  exact (hvalid.ite' hf (const none)).of_enc_eq (fun _ => rfl)

theorem candidate_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : (Config q × History q) × RuleRow q => candidate pad x.1.1 x.1.2 x.2)
      (candidateEncoding q) encBool := by
  let e := candidateEncoding q
  let c := configEncoding q
  let h := historyEncoding q
  let r := SourceRuleRows.rowEncoding q
  have hc := (fst c h).comp (fst (scanEncoding q) r)
  have hh := (snd c h).comp (fst (scanEncoding q) r)
  have hrow := (snd (scanEncoding q) r).fst'
  have hn := configEncoding_width_polyTime q hc
  have hℓ := configEncoding_length_polyTime q hc
  have hhash := configEncoding_hash_polyTime q hc
  have hv := configEncoding_spectrum_polyTime q hc
  have hs := (oldRows_polyTime q).comp (encIn := e) hh
  have hval := SourceSpectrum.applyRows_polyTime.comp (encIn := e) (encMid := SourceSpectrum.applyEncoding)
    ((hn.prod hhash).prod hrow)
  have hzero : ComputableInPolyTime (fun r : Row => r.all fun a => decide (a = 0)) rowEncoding encBool :=
    allWithInput (encIn := rowEncoding) (encA := tritEncoding) (test := fun _ a => decide (a = 0))
      id' ((snd rowEncoding tritEncoding).decide_eq' (const 0))
  have hspan := CanonicalSourceColour.inSpan_polyTime.comp (encIn := e) (encMid := adjunctionEncoding)
    ((hn.prod hs).prod hrow)
  have hp := (parts_polyTime pad).comp (encIn := e) hh
  have hex := SourceExposure.check_polyTime.comp (encIn := e) (encMid := SourceExposure.exposureEncoding)
    ((hℓ.prod (hn.prod hp)).prod (hv.prod hrow))
  exact (bool_and' (bool_and' (hzero.comp hval) (bool_not.comp hspan)) hex).of_enc_eq (fun _ => rfl)

theorem next_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : Config q × History q => next pad x.1 x.2)
      (scanEncoding q) (encOption (SourceRuleRows.rowEncoding q)) := by
  let e := scanEncoding q
  let r := SourceRuleRows.rowEncoding q
  have ht := configEncoding_catalogue_polyTime q (fst (configEncoding q) (historyEncoding q))
  exact findWithInput (encIn := e) (encA := r)
    (test := fun x rule => candidate pad x.1 x.2 rule) ht (candidate_polyTime pad)

theorem uniform_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (uniform pad b t) (uniformEncoding q) (configEncoding q) := by
  let e := uniformEncoding q
  let p := encPair rowsEncoding (wordEncoding q)
  have hℓ := fst encUnary p
  have hw := snd encUnary p
  have hL := (Machine.UniformParameters.gram_machine q b t).comp (encIn := e) hℓ
  have hn := (SourceHashChoice.width_polyTime q b t hq).comp (encIn := e) hℓ
  have hR := (Machine.UniformParameters.cutoff_machine q b t).comp (encIn := e) hℓ
  have hv := (SourceSpectrum.word_polyTime pad b t hq).comp (encIn := e)
    (encMid := encPair encUnary (wordEncoding q)) (hℓ.prod hw.snd')
  have hc := (SourceRuleRows.table_polyTime pad b t hq).comp (encIn := e) hℓ
  exact (configEncoding_mk_polyTime q hℓ hL hn (const (2*t)) hR hw.fst' hw.snd' hv hc).of_enc_eq
    (fun _ => rfl)

abbrev advanceEncoding (q : ℕ) := encPair (encPair (configEncoding q) encUnary) (historyEncoding q)
abbrev stepEncoding (q : ℕ) := encPair (configEncoding q) (stateEncoding q)

private theorem noneResult_polyTime (q : ℕ) :
    ComputableInPolyTime (fun hs : History q => some ((none : Option ℕ),hs))
      (historyEncoding q) (encOption (resultEncoding q)) :=
  (optionSome (resultEncoding q)).comp ((const none).prod id')

theorem advance_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : (Config q × ℕ) × History q => advance pad x.1.1 x.1.2 x.2)
      (advanceEncoding q) (stateEncoding q) := by
  let e := advanceEncoding q
  let c := configEncoding q
  let h := historyEncoding q
  let p := encPair c encUnary
  have hx := fst p h
  have hh := snd p h
  have ho := hx.snd'
  have hs := configEncoding_arity_polyTime q hx.fst'
  have hR := configEncoding_cutoff_polyTime q hx.fst'
  have hg := (graph_polyTime pad).comp (encIn := e) hh
  have he := PatchGraph.event_polyTime.comp (encIn := e) (encMid := PatchGraph.eventEncoding)
    ((hs.prod hR).prod (hg.prod ho))
  have ha := (const (encOut := encBool) false).prod
    ((optionSome (resultEncoding q)).comp (((optionSome encUnary).comp ho).prod hh))
  have hn := (const (encOut := encBool) true).prod
    ((noneResult_polyTime q).comp (encIn := e) hh)
  have hp := unary_lt' ho ((length_list (batchEncoding q)).comp hh)
  exact (hp.ite' (he.ite' ha hn) (const (failed q))).of_enc_eq (fun _ => by
    simp [advance,Function.comp_def])

theorem tryRule_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : (Config q × History q) × RuleRow q => tryRule pad x.1.1 x.1.2 x.2)
      (candidateEncoding q) (stateEncoding q) := by
  let e := candidateEncoding q
  let h := historyEncoding q
  let p := encPair e h
  have hx := fst e h
  have hc := ((fst (configEncoding q) h).comp (fst (scanEncoding q) (SourceRuleRows.rowEncoding q))).comp hx
  have hold := (length_list (batchEncoding q)).comp
    (((snd (configEncoding q) h).comp (fst (scanEncoding q) (SourceRuleRows.rowEncoding q))).comp hx)
  have ha := (advance_polyTime pad).comp (encIn := p) (encMid := advanceEncoding q)
    ((hc.prod hold).prod (snd e h))
  exact optionElimWithInput (encA := e) (encB := h) (encC := stateEncoding q)
    (body := fun x h => advance pad x.1.1 x.1.2.length h)
    (prep_polyTime pad) (const (failed q)) (ha.of_enc_eq (fun _ => rfl))

theorem scan_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : Config q × History q => scan pad x.1 x.2)
      (scanEncoding q) (stateEncoding q) := by
  let e := scanEncoding q
  let r := SourceRuleRows.rowEncoding q
  let h := historyEncoding q
  have hn := (const (encOut := encBool) false).prod
    ((noneResult_polyTime q).comp (encIn := e) (snd (configEncoding q) h))
  exact optionElimWithInput (encA := e) (encB := r) (encC := stateEncoding q)
    (body := fun x w => tryRule pad x.1 x.2 w)
    (next_polyTime pad) (hn.of_enc_eq (fun _ => rfl)) (tryRule_polyTime pad)

theorem step_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : Config q × State q => step pad x.1 x.2)
      (stepEncoding q) (stateEncoding q) := by
  let c := configEncoding q
  let s := stateEncoding q
  let r := resultEncoding q
  let e := stepEncoding q
  let p := encPair e r
  have hc := fst c s
  have hs := snd c s
  have hg := (scan_polyTime pad).comp (encIn := p) (encMid := scanEncoding q)
    ((hc.comp (fst e r)).prod (snd e r).snd')
  have h := optionElimWithInput (encA := e) (encB := r) (encC := s)
    (body := fun x v => scan pad x.1 v.2) hs.snd' (const (failed q)) (hg.of_enc_eq (fun _ => rfl))
  exact (hs.fst'.ite' h hs).of_enc_eq (fun _ => rfl)

#print axioms step_polyTime
#print axioms uniform_polyTime

end DeletionCode.Explicit.Machine.SourceRecognition
