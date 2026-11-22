import DeletionCode.Explicit.Machine.SourceRunBounds

/-! The complete acceptance and label interpreters on the length, hash and word. -/
namespace DeletionCode.Explicit.Machine.SourceAcceptance

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Ternary FieldHash CataloguePrefix SourceLists
open SourceRecognition (Result resultEncoding uniformEncoding recognize)
open ExceptionalWeight (chronological validRun mem_chronological validRun_iff)

variable {q b t ℓ θ : ℕ}

abbrev Input (q : ℕ) := ℕ × (Rows × QWord q)
abbrev inputEncoding (q : ℕ) := uniformEncoding q

private def partner (pad : Fin q) (b t : ℕ) (x : Input q) (z : QWord q) : Bool :=
  decide (z.length = x.1) && (!decide (z = x.2.2) &&
    decide (SourceSpectrum.hash pad b t (x.1,x.2.1,z) = SourceSpectrum.hash pad b t x))

private theorem partner_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (w : Fin ℓ → Fin q)
    (H : TernaryMatrix θ (q^UniformParameters.gram q b t ℓ)) (z : QWord q) :
    partner pad b t (ℓ,matrixRows H,List.ofFn w) z = true ↔
      z.length = ℓ ∧ z ≠ List.ofFn w ∧
      H.mulVec (ExceptionalWeight.spectrum pad finFunctionFinEquiv.symm z) =
      H.mulVec (ExceptionalWeight.spectrum pad finFunctionFinEquiv.symm (List.ofFn w)) := by
  simp only [partner,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not,
    SourceSpectrum.hash,SourceSpectrum.word,SourceSpectrum.spectrum_eq pad hq,
    SourceSpectrum.applyRows_matrix_eq,List.ofFn_inj]

private def runsToPartner (pad : Fin q) (b t : ℕ) (x : Input q)
    (es : List (Burst.Edit (Fin q))) : Bool :=
  (validRun b x.2.2 es).elim false (partner pad b t x)

/-- Short lengths also admit a polynomial scan of the chronological edit scripts.
    It checks the endpoint hash directly, including a zero spectrum change. -/
def exceptionalDirect (pad : Fin q) (b t : ℕ) (x : Input q) : Bool :=
  AcceptanceWeights.uniqueWindows x.1 (UniformParameters.windowLength q x.1) x.2.2 &&
    (chronological q b t (UniformParameters.gram q b t x.1) x.1).any (runsToPartner pad b t x)

theorem exceptionalDirect_iff (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q)
    (H : TernaryMatrix θ (q^UniformParameters.gram q b t ℓ)) (w : Fin ℓ → Fin q) :
    exceptionalDirect pad b t (ℓ,matrixRows H,List.ofFn w) = true ↔
      ExceptionalWeight.Exceptional pad finFunctionFinEquiv.symm H b t
        (UniformParameters.windowLength q ℓ) w := by
  let L := UniformParameters.gram q b t ℓ
  simp only [exceptionalDirect,Bool.and_eq_true,List.any_eq_true,
    AcceptanceWeights.uniqueWindows_iff pad _ List.length_ofFn,ExceptionalWeight.Exceptional]
  refine and_congr_right_iff.mpr (fun _ => ?_)
  constructor
  · rintro ⟨es,hes,htest⟩
    unfold runsToPartner at htest
    cases hr : validRun b (List.ofFn w) es with
    | none => simp [hr] at htest
    | some z =>
      have ⟨hl,hne,hh⟩ := (partner_eq pad b t hq w H z).mp (by simpa [hr] using htest)
      have hm := mem_chronological.mp hes
      exact ⟨z,hl,hne,⟨es,validRun_iff.mp hr,hm.2.1,hm.2.2.1⟩,hh⟩
  · rintro ⟨z,hl,hne,⟨es,hex,hlen,hbad⟩,hh⟩
    refine ⟨es,mem_chronological.mpr ⟨?_,hlen,hbad,?_⟩,?_⟩
    · cases es with
      | nil => cases hex; exact (hne rfl).elim
      | cons => simp
    · intro e he
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp he
      have hpos := hex.position_le ⟨i,hi⟩
      have hb := (hex.get_valid ⟨i,hi⟩).1
      have hi' := Nat.mul_le_mul_right b (show i ≤ 2*t by omega)
      simp only [List.length_ofFn,List.get_eq_getElem] at hpos hb
      exact ⟨by omega,hb⟩
    · have hr := validRun_iff.mpr hex
      simp only [runsToPartner,hr,Option.elim_some]
      exact (partner_eq pad b t hq w H z).mpr ⟨hl,hne,hh⟩

private theorem partner_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : Input q × QWord q => partner pad b t x.1 x.2)
      (encPair (inputEncoding q) (wordEncoding q)) encBool := by
  let e := inputEncoding q
  let w := wordEncoding q
  let a := encPair e w
  have hl := (fst encUnary (encPair rowsEncoding w)).comp (fst e w)
  have hx := (snd encUnary (encPair rowsEncoding w)).comp (fst e w)
  have hz := snd e w
  have hh := SourceSpectrum.hash_polyTime pad b t hq
  have hhash := hh.comp (encIn := a) (encMid := e) (hl.prod (hx.fst'.prod hz))
  have hhash' := hh.comp (fst e w)
  have hlen := ((length_list (ExceptionalRecords.letterEncoding q)).comp hz).decide_eq' hl
  have hne := bool_not.comp (hz.decide_eq' hx.snd')
  exact bool_and' hlen (bool_and' hne (hhash.decide_eq' hhash'))

set_option maxHeartbeats 1200000 in
private theorem runsToPartner_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : Input q × List (Burst.Edit (Fin q)) => runsToPartner pad b t x.1 x.2)
      (encPair (inputEncoding q) (ExceptionalRecords.recordEncoding q)) encBool := by
  let e := inputEncoding q
  let w := wordEncoding q
  let es := ExceptionalRecords.recordEncoding q
  let a := encPair e es
  let z := encPair a w
  have hx := (snd encUnary (encPair rowsEncoding w)).snd'
  have hrun := (ExceptionalRecords.validRun_polyTime q b).comp (encIn := a)
    ((hx.comp (fst e es)).prod (snd e es))
  have harg : ComputableInPolyTime (fun y : (Input q × List (Burst.Edit (Fin q))) × QWord q =>
      (y.1.1,y.2)) z (encPair e w) := ((fst e es).comp (fst a w)).prod (snd a w)
  have htest := (partner_polyTime pad b t hq).comp (encIn := z) harg
  have h := optionElimWithInput (encA := a) (encB := w) (encC := encBool)
    (body := fun x v => partner pad b t x.1 v) hrun (const false) htest
  exact h.of_enc_eq (g := fun y => runsToPartner pad b t y.1 y.2) (encD := encBool) (fun _ => rfl)

theorem exceptionalDirect_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (exceptionalDirect pad b t) (inputEncoding q) encBool := by
  let e := inputEncoding q
  let w := wordEncoding q
  let es := ExceptionalRecords.recordEncoding q
  have hl := fst encUnary (encPair rowsEncoding w)
  have hx := (snd encUnary (encPair rowsEncoding w)).snd'
  have hgram := (Machine.UniformParameters.gram_machine q b t).comp hl
  have hrecords := (ExceptionalRecords.chronological_polyTime q b t).comp (hgram.prod hl)
  have he := anyWithInput (encIn := e) (encA := es) (test := runsToPartner pad b t)
    hrecords (runsToPartner_polyTime pad b t hq)
  have hK := (Machine.UniformParameters.window_machine q).comp hl
  have hu := (Machine.AcceptanceWeights.uniqueWindows_polyTime q).comp (encIn := e)
    (encMid := Machine.AcceptanceWeights.windowEncoding q) ((hl.prod hK).prod hx)
  exact bool_and' hu he

def exceptionalAt (pad : Fin q) (b t : ℕ) (x : Input q) : Bool :=
  if x.1 < UniformParameters.minLength q b t then exceptionalDirect pad b t x
  else AlignedSourceHash.exceptionalMain pad b t x

theorem exceptionalAt_iff (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (H : TernaryMatrix θ (q^UniformParameters.gram q b t ℓ)) (w : Fin ℓ → Fin q) :
    exceptionalAt pad b t (ℓ,matrixRows H,List.ofFn w) = true ↔
      ExceptionalWeight.Exceptional pad finFunctionFinEquiv.symm H b t
        (UniformParameters.windowLength q ℓ) w := by
  unfold exceptionalAt
  split
  · exact exceptionalDirect_iff pad b t hq H w
  · exact AlignedSourceHash.exceptionalMain_iff pad b t w hq hb ht (by omega) H

theorem exceptionalAt_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (exceptionalAt pad b t) (inputEncoding q) encBool := by
  have h := unary_to_binary.comp (fst encUnary (encPair rowsEncoding (wordEncoding q)))
  exact ((binary_lt' h (const (UniformParameters.minLength q b t))).ite'
    (exceptionalDirect_polyTime pad b t hq)
    (AlignedSourceHash.exceptionalMain_polyTime (b := b) (t := t) pad hq)).of_enc_eq
      (fun x => by simp [exceptionalAt])

def withDeciders (pad : Fin q) (C : ConcreteSource.Procedures q b t) :
    ConcreteSource.Procedures q b t :=
  { C with
    strong := fun l w => AcceptanceWeights.strong pad b t l (List.ofFn w)
    exceptional := fun l H w => exceptionalAt pad b t (l,matrixRows H,List.ofFn w) }

theorem deciderLaws (pad : Fin q) (C : ConcreteSource.Procedures q b t)
    (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ConcreteSource.DeciderLaws (withDeciders pad C) pad :=
  ⟨fun w => AcceptanceWeights.strong_iff pad b t w,
    fun H w _ => exceptionalAt_iff pad b t hq hb ht H w⟩

def isComplete (r : Option (Result q)) : Bool := r.elim false (fun v => !v.1.isSome)

def accepted (pad : Fin q) (b t : ℕ) (x : Input q) : Bool :=
  if AcceptanceWeights.strong pad b t x.1 x.2.2 && !exceptionalAt pad b t x then
    isComplete (recognize pad b t x)
  else false

theorem accepted_eq (pad : Fin q) (C : ConcreteSource.Procedures q b t) (hq : 2 ≤ q)
    (H : ConcreteSource.Hash q b t ℓ) (w : Fin ℓ → Fin q) :
    accepted pad b t (ℓ,matrixRows H,List.ofFn w) =
      ConcreteSource.acceptedAt (withDeciders pad C) pad H w := by
  unfold accepted ConcreteSource.acceptedAt withDeciders
  rw [SourceRecognition.recognize_eq pad b t hq]
  unfold ConcreteSource.runAt UniformParameters.edits
  cases h : Recognizer.recognize (K := UniformParameters.windowLength q ℓ) (b := b)
    (s := 2*t) H pad w (UniformParameters.componentCutoff q b t ℓ) with
  | none => rfl
  | some v => cases v <;> rfl

theorem accepted_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (accepted pad b t) (inputEncoding q) encBool := by
  let e := inputEncoding q
  let r := resultEncoding q
  let w := wordEncoding q
  have hl := fst encUnary (encPair rowsEncoding w)
  have hx := (snd encUnary (encPair rowsEncoding w)).snd'
  have hs := (Machine.AcceptanceWeights.strong_polyTime pad hq hb ht).comp (hl.prod hx)
  have he := (exceptionalAt_polyTime pad b t hq)
  have hc := optionElimWithInput (encA := e) (encB := r) (encC := encBool)
    (body := fun _ v => !v.1.isSome) (SourceRunBounds.recognize_polyTime pad b t hq)
    (const false) (bool_not.comp (optionIsSome ((snd e r).fst')))
  exact ((bool_and' hs (bool_not.comp he)).ite' hc (const false)).of_enc_eq (fun _ => rfl)

def labelData (pad : Fin q) (b t : ℕ) (x : Input q) (res : Result q) : ℕ :=
  if res.1.isSome then 0 else
    (CanonicalSourceColour.labelWord pad b t
      ((x.1,(x.2.1,((SourceRuleRows.table pad b t x.1).map Prod.fst,SourceRecognition.oldRows res.2))),x.2.2)).elim 0 id

def label (pad : Fin q) (b t : ℕ) (x : Input q) : ℕ :=
  (recognize pad b t x).elim 0 (labelData pad b t x)

set_option maxHeartbeats 1000000 in
theorem label_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q)
    (H : ConcreteSource.Hash q b t ℓ) (w : Fin ℓ → Fin q) :
    label pad b t (ℓ,matrixRows H,List.ofFn w) = ConcreteSource.rankAt pad H w := by
  unfold label ConcreteSource.rankAt
  rw [SourceRecognition.recognize_eq pad b t hq]
  unfold ConcreteSource.runAt UniformParameters.edits
  cases hr : Recognizer.recognize (K := UniformParameters.windowLength q ℓ) (b := b)
    (s := 2*t) H pad w (UniformParameters.componentCutoff q b t ℓ) with
  | none => rfl
  | some out =>
    cases out with
    | firstEvent => rfl
    | complete hs =>
      unfold labelData
      simp only [Option.map_some,Option.elim_some,SourceRecognition.resultData,Option.isSome_none,
        Bool.false_eq_true,↓reduceIte,SourceRecognition.oldRows_eq,SourceRuleRows.table_eq pad b t ℓ hq,
        List.map_map,Function.comp_def]
      let cat := Recognizer.catalogueRows q (UniformParameters.windowLength q ℓ) b
        (UniformParameters.gram q b t ℓ) (2*t) pad
      have he := CanonicalSourceColour.labelWord_eq pad b t ℓ hq H cat (Recognizer.oldRows hs) w
      have hm : ((CatalogueEnumeration.rules q (UniformParameters.windowLength q ℓ) b
          (UniformParameters.gram q b t ℓ) (2*t) pad).map
          (fun r => List.ofFn (CatalogueEnumeration.row pad r))) = cat.map List.ofFn := by
        simp [cat,Recognizer.catalogueRows,List.map_map,Function.comp_def]
      rw [hm,he]
      change (Recognizer.labelOf (K := UniformParameters.windowLength q ℓ) (b := b) H pad w hs).elim 0 id =
        (Recognizer.labelOf (K := UniformParameters.windowLength q ℓ) (b := b) H pad w hs).getD 0
      cases Recognizer.labelOf (K := UniformParameters.windowLength q ℓ) (b := b) H pad w hs <;> rfl

theorem label_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (label pad b t) (inputEncoding q) encNat := by
  let e := inputEncoding q
  let r := resultEncoding q
  let w := wordEncoding q
  let a := encPair e r
  have he := fst e r
  have hr := snd e r
  have hl := (fst encUnary (encPair rowsEncoding w)).comp he
  have hx := (snd encUnary (encPair rowsEncoding w)).comp he
  have ho := (SourceRecognition.oldRows_polyTime q).comp hr.snd'
  have hc := (ComputableInPolyTime.map (fst rowEncoding (OrderedCatalogue.ruleEncoding q))).comp
    ((SourceRuleRows.table_polyTime pad b t hq).comp hl)
  have hdata := (hl.prod (hx.fst'.prod (hc.prod ho))).prod hx.snd'
  have hlab := (CanonicalSourceColour.labelWord_polyTime pad b t hq).comp (encIn := a)
    (encMid := CanonicalSourceColour.wordLabelInputEncoding q) hdata
  have hd := optionElimWithInput (encA := a) (encB := encNat) (encC := encNat)
    (body := fun _ v => v) hlab (const 0) (snd a encNat)
  have hf := (optionIsSome hr.fst').ite' (const 0) hd
  exact optionElimWithInput (encA := e) (encB := r) (encC := encNat)
    (body := fun x v => labelData pad b t x v) (SourceRunBounds.recognize_polyTime pad b t hq)
    (const 0) (hf.of_enc_eq (fun x => by simp [labelData,Function.comp_def] <;> rfl))

#print axioms exceptionalDirect_iff
#print axioms exceptionalDirect_polyTime
#print axioms deciderLaws
#print axioms accepted_eq
#print axioms accepted_polyTime
#print axioms label_eq
#print axioms label_polyTime

end DeletionCode.Explicit.Machine.SourceAcceptance
