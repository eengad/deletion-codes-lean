import DeletionCode.Explicit.ExceptionalColumns
import DeletionCode.Explicit.Machine.ExceptionalProvenance
import DeletionCode.Explicit.Machine.ExceptionalConditional
import DeletionCode.Explicit.Machine.MatrixConditionalChooser
import DeletionCode.Explicit.Machine.UniformParameters
import DeletionCode.Explicit.ParameterSavings

/-! A uniform machine generator for the exceptional catalogue. -/
namespace DeletionCode.Explicit.Machine.ExceptionalRecords

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Burst ExceptionalWeight FieldHash _root_.DeletionCode.Explicit.UniformParameters
open scoped BigOperators

variable {q : ℕ}

abbrev Prescriptions (q : ℕ) := List (ℕ × Fin q)

abbrev prescriptionsEncoding (q : ℕ) := encList (encPair encUnary (letterEncoding q))

abbrev SerialEntry (q : ℕ) := Ternary.Row × Prescriptions q
abbrev serialEntryEncoding (q : ℕ) := encPair Ternary.rowEncoding (prescriptionsEncoding q)

def serializeAssignment (a : CoreWeight.Assignment ℓ q) : Prescriptions q :=
  (supportList a.support).attach.map fun i =>
    (i.val.val, a.letter ⟨i.val, mem_supportList.mp i.property⟩)

def serialize (e : Entry ℓ q n) : SerialEntry q :=
  (List.ofFn e.changeVector, serializeAssignment e.assignment)

/-- Extract a row and keep its support size for the affine mean machine. -/
def conditionalRow (e : SerialEntry q) : Ternary.ExceptionalRow :=
  (e.1, e.2.length)

def rowDelta (gs : List (QWord q)) (w z : QWord q) : Ternary.Row :=
  gs.map (fun g => (gramCount z g : F₃) - (gramCount w g : F₃))

theorem rowDelta_eq (pad : Fin q) (L : ℕ) (w z : QWord q) :
    rowDelta (wordsOfLength q L) w z = List.ofFn (delta pad (dictionary q L) w z) := by
  apply List.ext_getElem (by simp [rowDelta, length_wordsOfLength])
  intro i hi hj
  let j : Fin (q^L) := ⟨i,by simpa using hj⟩
  have h := dictionary_at q L j
  simp only [rowDelta, List.getElem_map, List.getElem_ofFn]
  rw [← h, gramCount_field, gramCount_field]
  rfl

theorem gramCount_machine (q : ℕ) :
    ComputableInPolyTime (fun x : QWord q × QWord q => gramCount x.1 x.2)
      (encPair (wordEncoding q) (wordEncoding q)) encUnary := by
  let src := encPair (wordEncoding q) (wordEncoding q)
  have hw := fst (wordEncoding q) (wordEncoding q)
  have hg := snd (wordEncoding q) (wordEncoding q)
  have hlen := length_list (letterEncoding q)
  have hr := range.comp (unary_add' (hlen.comp hw) (const 1))
  exact countPWithInput (test := fun x i =>
    decide (i+x.2.length ≤ x.1.length) && ((x.1.drop i).take x.2.length == x.2)) hr (by
      have hp := fst src encUnary
      have hi := snd src encUnary
      have hww := hw.comp hp
      have hgg := hg.comp hp
      have hlw := hlen.comp hww
      have hlg := hlen.comp hgg
      have hdrop := listDropWithInput hww hi
      have ht := (takeUnary (letterEncoding q)).comp (hdrop.prod hlg)
      have he := ht.decide_eq' hgg
      have hn := unary_le' (unary_add' hi hlg) hlw
      exact (bool_and' hn he).of_enc_eq (fun x => by
        apply congrArg encBool
        simp only [Function.comp_def]
        congr 1
        rw [Bool.eq_iff_iff]
        exact beq_iff_eq.trans decide_eq_true_iff.symm))

theorem tritOfUnary : ComputableInPolyTime (fun m : ℕ => (m : F₃)) encUnary
    Ternary.tritEncoding := by
  let f (i : ℕ) : F₃ := if i = 0 then 0 else if i = 1 then 1 else 2
  have hf : ComputableInPolyTime f encUnary Ternary.tritEncoding :=
    ite_decide (id'.decide_eq' (const 0)) (const 0) (ite_decide (id'.decide_eq' (const 1))
      (const 1) (const 2))
  have hm := hf.comp (unary_mod' id' (const 3))
  exact hm.of_enc_eq (fun m => by
    apply congrArg Ternary.tritEncoding
    have h := Nat.mod_lt m (by decide : 0 < 3)
    conv_lhs => rw [← ZMod.natCast_mod m 3]
    interval_cases k : m%3 <;> simp [f,k])

abbrev dictionaryEncoding (q : ℕ) := encList (wordEncoding q)

abbrev DeltaInput (q : ℕ) := List (QWord q) × (QWord q × QWord q)
abbrev deltaEncoding (q : ℕ) :=
  encPair (dictionaryEncoding q) (encPair (wordEncoding q) (wordEncoding q))

private theorem gramDifference_polyTime (q : ℕ) :
    ComputableInPolyTime
      (fun x : DeltaInput q × QWord q => (gramCount x.1.2.2 x.2 : F₃) - (gramCount x.1.2.1 x.2 : F₃))
      (encPair (deltaEncoding q) (wordEncoding q)) Ternary.tritEncoding := by
  let src := encPair (deltaEncoding q) (wordEncoding q)
  have hsub : ComputableInPolyTime (fun x : F₃ × F₃ => x.1-x.2)
      (encPair Ternary.tritEncoding Ternary.tritEncoding) Ternary.tritEncoding := of_finite _
  have hp := fst (deltaEncoding q) (wordEncoding q)
  have hg := snd (deltaEncoding q) (wordEncoding q)
  have hwords := (snd (dictionaryEncoding q) (encPair (wordEncoding q) (wordEncoding q))).comp hp
  have hc : ComputableInPolyTime (fun x : QWord q × QWord q => (gramCount x.1 x.2 : F₃))
      (encPair (wordEncoding q) (wordEncoding q)) Ternary.tritEncoding :=
    tritOfUnary.comp (gramCount_machine q)
  let words := encPair (wordEncoding q) (wordEncoding q)
  have hzIn : ComputableInPolyTime (fun x : DeltaInput q × QWord q => (x.1.2.2,x.2))
      src words := hwords.snd'.prod hg
  have hwIn : ComputableInPolyTime (fun x : DeltaInput q × QWord q => (x.1.2.1,x.2))
      src words := hwords.fst'.prod hg
  have hz := hc.comp (encIn := src) (encMid := words) hzIn
  have hw := hc.comp (encIn := src) (encMid := words) hwIn
  exact (hsub.comp (hz.prod hw)).of_enc_eq (fun _ => rfl)

theorem rowDelta_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : DeltaInput q => rowDelta x.1 x.2.1 x.2.2)
      (deltaEncoding q) Ternary.rowEncoding := by
  unfold rowDelta
  exact mapWithInput (encA := wordEncoding q) (encIn := deltaEncoding q)
    (list := fun x : DeltaInput q => x.1)
    (f := fun x g => (gramCount x.2.2 g : F₃) - (gramCount x.2.1 g : F₃))
    (fst (dictionaryEncoding q) (encPair (wordEncoding q) (wordEncoding q)))
    (gramDifference_polyTime q)

abbrev FillInput (q : ℕ) := ℕ × (List ℕ × QWord q)
abbrev fillEncoding (q : ℕ) := encPair encUnary (encPair (encList encUnary) (wordEncoding q))

def fill (pad : Fin q) (x : FillInput q) : QWord q :=
  (List.range x.1).map fun i => x.2.2.getD (x.2.1.idxOf i) pad

def assignmentPairs (pad : Fin q) (xs : List ℕ) (letters : QWord q) : Prescriptions q :=
  xs.map fun i => (i, letters.getD (xs.idxOf i) pad)

private theorem fill_polyTime (pad : Fin q) :
    ComputableInPolyTime (fill pad) (fillEncoding q) (wordEncoding q) := by
  let src := fillEncoding q
  have hx := fst encUnary (encPair (encList encUnary) (wordEncoding q))
  have hdata := (snd encUnary (encPair (encList encUnary) (wordEncoding q))).comp (fst src encUnary)
  have hi := idxOfWithInput hdata.fst' (snd src encUnary)
  exact mapWithInput (f := fun x i => x.2.2.getD (x.2.1.idxOf i) pad) (range.comp hx)
    (listGetDWithInput hdata.snd' hi pad)

private theorem assignmentPairs_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : List ℕ × QWord q => assignmentPairs pad x.1 x.2)
      (encPair (encList encUnary) (wordEncoding q)) (prescriptionsEncoding q) := by
  let src := encPair (encList encUnary) (wordEncoding q)
  have hx := fst (encList encUnary) (wordEncoding q)
  have hdata := fst src encUnary
  have hi := idxOfWithInput (hx.comp hdata) (snd src encUnary)
  have hl := (snd (encList encUnary) (wordEncoding q)).comp hdata
  exact mapWithInput (f := fun x i => (i, x.2.getD (x.1.idxOf i) pad)) hx
    ((snd src encUnary).prod (listGetDWithInput hl hi pad))

abbrev Prepared (q : ℕ) := (ℕ × List (QWord q)) × (List (Edit (Fin q)) × List ℕ)
abbrev preparedEncoding (q : ℕ) := encPair (encPair encUnary (dictionaryEncoding q))
  (encPair (recordEncoding q) (encList encUnary))

def serialOne (pad : Fin q) (b : ℕ) (x : Prepared q) (letters : QWord q) : List (SerialEntry q) :=
  let w := fill pad (x.1.1, x.2.2, letters)
  (validRun b w x.2.1).elim [] (fun z =>
    if z.length = x.1.1 then
      let row := rowDelta x.1.2 w z
      if row.any (fun a => decide (a ≠ 0)) then [(row, assignmentPairs pad x.2.2 letters)]
      else []
    else [])

set_option maxHeartbeats 1000000 in
theorem serialOne_polyTime (pad : Fin q) (b : ℕ) :
    ComputableInPolyTime (fun x : Prepared q × QWord q => serialOne pad b x.1 x.2)
      (encPair (preparedEncoding q) (wordEncoding q)) (encList (serialEntryEncoding q)) := by
  let src := encPair (preparedEncoding q) (wordEncoding q)
  let arg := encPair src (wordEncoding q)
  have hp := fst (preparedEncoding q) (wordEncoding q)
  have hw := snd (preparedEncoding q) (wordEncoding q)
  have hi := hp.fst'.fst'
  have hs := hp.snd'.snd'
  have hword := (fill_polyTime pad).comp (hi.prod (hs.prod hw))
  have hz := (validRun_polyTime q b).comp (hword.prod hp.snd'.fst')
  have harg := fst src (wordEncoding q)
  have hret := snd src (wordEncoding q)
  have hd := (rowDelta_polyTime q).comp
    ((hp.fst'.snd'.comp harg).prod ((hword.comp harg).prod hret))
  have hpairs := (assignmentPairs_polyTime pad).comp ((hs.prod hw).comp harg)
  have htest := anyWithInput (test := fun _ (a : F₃) => decide (a ≠ 0))
    hd (bool_not.comp ((snd arg Ternary.tritEncoding).decide_eq' (const 0)))
  have hy := cons' (hd.prod hpairs) (const [])
  have hlen := ((length_list (letterEncoding q)).comp hret).decide_eq' (hi.comp harg)
  have hbranch := ite_decide hlen (ite htest hy (const [])) (const [])
  have h := optionElimWithInput
    (body := fun x z => if z.length = x.1.1.1 then
      if (rowDelta x.1.1.2 (fill pad (x.1.1.1,x.1.2.2,x.2)) z).any (fun a => decide (a ≠ 0))
      then [(rowDelta x.1.1.2 (fill pad (x.1.1.1,x.1.2.2,x.2)) z, assignmentPairs pad x.1.2.2 x.2)]
      else [] else []) hz (const []) hbranch
  exact h

private theorem idxOf_finVal_map (xs : List (Fin ℓ)) (i : Fin ℓ) :
    (xs.map Fin.val).idxOf i.val = xs.idxOf i := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases he : i = a
    · subst a
      simp
    · have hv : i.val ≠ a.val := fun h => he (Fin.ext h)
      simp [List.idxOf_cons, Ne.symm he, Ne.symm hv, ih]

private theorem fill_eq (pad : Fin q) (s : Finset (Fin ℓ)) (letters : QWord q) :
    fill pad (ℓ,(supportList s).map Fin.val,letters) =
      List.ofFn (representative pad s letters) := by
  apply List.ext_getElem (by simp [fill])
  intro i hi hj
  simp only [fill, List.getElem_map, List.getElem_range, List.getElem_ofFn, representative]
  rw [idxOf_finVal_map (supportList s) (⟨i, by simpa using hj⟩ : Fin ℓ)]

private theorem assignmentPairs_eq (pad : Fin q) (s : Finset (Fin ℓ)) (letters : QWord q) :
    assignmentPairs pad ((supportList s).map Fin.val) letters =
      (supportList s).attach.map (fun i =>
        (i.val.val,(prescribe pad s letters).letter ⟨i.val, mem_supportList.mp i.2⟩)) := by
  unfold assignmentPairs
  rw [List.map_map, ← List.attach_map_val]
  apply List.map_congr_left
  intro i _
  simp [prescribe, representative, idxOf_finVal_map]

private theorem row_nonzero (x : Fin n → F₃) :
    (List.ofFn x).any (fun a => decide (a ≠ 0)) = true ↔ x ≠ 0 := by
  simp only [List.any_eq_true, List.mem_ofFn, decide_eq_true_eq, ne_eq]
  constructor
  · rintro ⟨a,⟨i,h⟩,ha⟩ he
    exact ha (h ▸ congrFun he i)
  · intro hn
    by_contra! h
    exact hn (funext fun i => h (x i) ⟨i,rfl⟩)

theorem serialOne_eq (pad : Fin q) (b L ℓ : ℕ) (es : List (Edit (Fin q))) (letters : QWord q) :
    serialOne pad b ((ℓ,wordsOfLength q L),(es,supportPositions ((L,ℓ),es))) letters =
      ((entry? pad (dictionary q L) b es (touched L (initialTokens ℓ q) es) letters).map serialize).toList := by
  let s := touched L (initialTokens ℓ q) es
  let w := List.ofFn (representative pad s letters)
  unfold serialOne entry?
  dsimp only
  rw [supportPositions_eq, fill_eq, assignmentPairs_eq]
  change (validRun b w es).elim _ _ = ((validRun b w es).bind _ |>.map serialize).toList
  cases h : validRun b w es with
  | none => rfl
  | some z =>
    simp only [Option.elim_some, Option.bind_some]
    rw [rowDelta_eq pad L]
    by_cases hz : z.length = ℓ
    · rw [ite_eq_left hz]
      by_cases hd : delta pad (dictionary q L) w z = 0
      · have hb : (List.ofFn (delta pad (dictionary q L) w z)).any (fun a => decide (a ≠ 0)) = false :=
          Bool.eq_false_iff.mpr fun ht => (row_nonzero _).mp ht hd
        rw [ite_eq_right (show ¬ (List.ofFn (delta pad (dictionary q L) w z)).any
          (fun a => decide (a ≠ 0)) = true by rw [hb]; decide)]
        rw [dite_eq_right (fun h : z.length = ℓ ∧ delta pad (dictionary q L) w z ≠ 0 => h.2 hd)]
        rfl
      · rw [ite_eq_left ((row_nonzero _).mpr hd)]
        rw [dite_eq_left (show z.length = ℓ ∧ delta pad (dictionary q L) w z ≠ 0 from ⟨hz,hd⟩)]
        rfl
    · rw [ite_eq_right hz, dite_eq_right (fun h : z.length = ℓ ∧ delta pad (dictionary q L) w z ≠ 0 => hz h.1)]
      rfl

private theorem qpowGram_polyBounded (q b t : ℕ) (hq : 2 ≤ q) :
    PolyBounded (fun l : ℕ => l) (fun l => q^UniformParameters.gram q b t l) := by
  refine .of_forall_le (q^(gramMultiplier t*(b+4)) + q^gram q b t 1)
    (gramMultiplier t) ?_
  intro l
  by_cases h : 1 < l
  · exact (gram_dictionary_bound hq h).trans
      (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_left (Nat.le_succ _) _))
  · have hm : gram q b t l ≤ gram q b t 1 := by
      unfold gram gramLength
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.clog_mono_right _ (by omega)) _) _)
    exact (Nat.pow_le_pow_right (by omega : 1 ≤ q) hm).trans
      ((Nat.le_add_left _ _).trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))))

private theorem slots_polyBounded (q b t : ℕ) (hq : 2 ≤ q) :
    PolyBounded (fun l : ℕ => l) (fun l => q^((2*t)*(2*UniformParameters.gram q b t l+b))) := by
  have h := ((qpowGram_polyBounded q b t hq).pow 2).mul (PolyBounded.const (q^b))
  refine (h.pow (2*t)).mono (fun l => ?_)
  have he : q^((2*t)*(2*UniformParameters.gram q b t l+b)) =
      (((q^UniformParameters.gram q b t l)^2)*(q^b))^(2*t) := by
    simp only [← pow_mul, ← pow_add]
    congr 1
    ring
  exact he.le

theorem gramList_polyTime (q b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun l => wordsOfLength q (UniformParameters.gram q b t l))
      encUnary (dictionaryEncoding q) :=
  wordsOfLength_polyTime hq (Machine.UniformParameters.gram_machine q b t)
    (by simpa [encUnary_apply] using qpowGram_polyBounded q b t hq)

private def serialFor (pad : Fin q) (b t : ℕ) (x : Prepared q) : List (SerialEntry q) :=
  let limit := (2*t)*(2*UniformParameters.gram q b t x.1.1+b)
  (wordsOfLength q (min x.2.2.length limit)).flatMap (serialOne pad b x)

private theorem serialFor_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (serialFor pad b t) (preparedEncoding q) (encList (serialEntryEncoding q)) := by
  let src := preparedEncoding q
  have hw := fst (encPair encUnary (dictionaryEncoding q)) (encPair (recordEncoding q) (encList encUnary))
  have hs := snd (encPair encUnary (dictionaryEncoding q)) (encPair (recordEncoding q) (encList encUnary))
  have hlimit := unary_mul' (const (2*t))
    (unary_add' (unary_mul' (const 2) ((Machine.UniformParameters.gram_machine q b t).comp hw.fst')) (const b))
  have hlen := unary_min.comp (((length_list encUnary).comp hs.snd').prod hlimit)
  have hs' : PolyBounded (fun x : Prepared q => (src x).length) (fun x => x.1.1) := by
    simpa only [encUnary_apply, List.length_replicate] using hw.fst'.polyBounded_length
  have hcap : PolyBounded (fun x : Prepared q => (src x).length)
      (fun x => q ^ min x.2.2.length ((2*t)*(2*UniformParameters.gram q b t x.1.1+b))) :=
    ((slots_polyBounded q b t hq).comp hs').mono
      (fun _ => Nat.pow_le_pow_right (by omega) (Nat.min_le_right _ _))
  exact flatMapWithInput (f := serialOne pad b) (wordsOfLength_polyTime hq hlen hcap)
    (serialOne_polyTime pad b)

def serialized (pad : Fin q) (b t ℓ : ℕ) : List (SerialEntry q) :=
  let L := UniformParameters.gram q b t ℓ
  let gs := wordsOfLength q L
  (chronological q b t L ℓ).flatMap fun es =>
    serialFor pad b t ((ℓ,gs),(es,supportPositions ((L,ℓ),es)))

theorem serialized_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (serialized pad b t) encUnary (encList (serialEntryEncoding q)) := by
  let src := encPair encUnary (recordEncoding q)
  have hL := Machine.UniformParameters.gram_machine q b t
  have he := (chronological_polyTime q b t).comp (hL.prod id')
  apply flatMapWithInput (f := fun l es => serialFor pad b t
    ((l,wordsOfLength q (UniformParameters.gram q b t l)),
      (es,supportPositions ((UniformParameters.gram q b t l,l),es)))) he
  have hl := fst encUnary (recordEncoding q)
  have hrec := snd encUnary (recordEncoding q)
  have hs := (supportPositions_polyTime q).comp (((hL.comp hl).prod hl).prod hrec)
  exact (serialFor_polyTime pad b t hq).comp
    ((hl.prod ((gramList_polyTime q b t hq).comp hl)).prod (hrec.prod hs))

theorem serialized_eq (pad : Fin q) (b t ℓ : ℕ) :
    serialized pad b t ℓ =
      (catalogue pad (dictionary q (UniformParameters.gram q b t ℓ)) b t ℓ).map serialize := by
  let L := UniformParameters.gram q b t ℓ
  unfold serialized catalogue
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro es hes
  have hb := mem_chronological.mp hes
  have hbound := (touched_card_le L b (initialTokens ℓ q) es (fun e he => (hb.2.2.2 e he).2.1)).trans
    (Nat.mul_le_mul_right _ hb.2.1)
  unfold serialFor
  dsimp only
  have hlen : (supportPositions ((L,ℓ),es)).length =
      (supportList (touched L (initialTokens ℓ q) es)).length := by rw [supportPositions_eq, List.length_map]
  rw [Nat.min_eq_left (show (supportPositions ((L,ℓ),es)).length ≤ 2*t*(2*L+b) from
    by simpa only [hlen, supportList_length] using hbound)]
  rw [hlen]
  unfold catalogueFor
  dsimp only
  let make := entry? pad (dictionary q L) b es (touched L (initialTokens ℓ q) es)
  let step := serialOne pad b ((ℓ,wordsOfLength q L),(es,supportPositions ((L,ℓ),es)))
  have hrun (ws : List (QWord q)) : ws.flatMap step = (ws.filterMap make).map serialize := by
    induction ws with
    | nil => rfl
    | cons w ws ih =>
      rw [List.flatMap_cons, show step w = ((make w).map serialize).toList from serialOne_eq .., ih]
      cases hm : make w <;> simp [hm]
  exact hrun _

def conditionalOnPrefix (pad : Fin q) (b t : ℕ) (x : (ℕ × ℕ) × ConditionalChooser.Prefix) : ℚ :=
  let n := q ^ UniformParameters.gram q b t x.1.1
  let p := ConditionalChoice.partialRows ((x.1.2,n),x.2)
  Ternary.exceptionalConditional q ((n,p),(serialized pad b t x.1.1).map conditionalRow)

theorem conditionalOnPrefix_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (conditionalOnPrefix pad b t)
      ConditionalChoice.prefixInputEncoding encRat := by
  have hpar := fst ConditionalChoice.dimensionEncoding ConditionalChoice.prefixEncoding
  have hprefix := snd ConditionalChoice.dimensionEncoding ConditionalChoice.prefixEncoding
  have ncalc := ((length_list (wordEncoding q)).comp (gramList_polyTime q b t hq)).comp hpar.fst'
  have hn : ComputableInPolyTime (fun x : (ℕ × ℕ) × ConditionalChooser.Prefix =>
      q^UniformParameters.gram q b t x.1.1) ConditionalChoice.prefixInputEncoding encUnary :=
    ncalc.of_enc_eq (fun x => congrArg encUnary (length_wordsOfLength ..).symm)
  have hrows := ConditionalChoice.partialRows_polyTime.comp ((hpar.snd'.prod hn).prod hprefix)
  have hc : ComputableInPolyTime (conditionalRow (q := q)) (serialEntryEncoding q)
      Ternary.exceptionalRowEncoding := by
    have hr := fst Ternary.rowEncoding (prescriptionsEncoding q)
    have hs := snd Ternary.rowEncoding (prescriptionsEncoding q)
    exact hr.prod ((length_list (encPair encUnary (letterEncoding q))).comp hs)
  have hcat := (ComputableInPolyTime.map hc).comp ((serialized_polyTime pad b t hq).comp hpar.fst')
  exact (Ternary.exceptionalConditional_polyTime q).comp ((hn.prod hrows).prod hcat)

theorem conditionalOnPrefix_eq (pad : Fin q) (b t ℓ θ : ℕ) (p : ConditionalChooser.Prefix) :
    conditionalOnPrefix pad b t ((ℓ,θ),p) =
      conditionalMass (family pad (dictionary q (UniformParameters.gram q b t ℓ)) b t ℓ)
        (ConditionalChooser.prefixHash θ (q^UniformParameters.gram q b t ℓ) p) := by
  let L := UniformParameters.gram q b t ℓ
  let n := q^L
  let C := family pad (dictionary q L) b t ℓ
  let P := ConditionalChoice.partialRows ((θ,n),p)
  let rs := fun i => conditionalRow (serialize (C i))
  have hcat : (List.ofFn C) = catalogue pad (dictionary q L) b t ℓ := List.ofFn_get _
  have hr (i : Fin (catalogue pad (dictionary q L) b t ℓ).length) :
      Ternary.rowOf n (rs i).1 = (C i).changeVector := by
    funext j
    change (List.ofFn (C i).changeVector).getD j.val 0 = _
    have hj : j.val < (List.ofFn (C i).changeVector).length := by
      rw [List.length_ofFn]
      exact j.isLt
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, List.getElem_ofFn,
      Option.getD_some]
    rfl
  have hs (i : Fin (catalogue pad (dictionary q L) b t ℓ).length) :
      (rs i).2 = (C i).assignment.support.card := by
    simp [rs, conditionalRow, serialize, serializeAssignment]
  have he := Ternary.exceptionalConditional_eq P C rs hr hs
  have hlist : List.ofFn rs = ((catalogue pad (dictionary q L) b t ℓ).map serialize).map conditionalRow := by
    calc
      List.ofFn rs = ((List.ofFn C).map serialize).map conditionalRow := by
        simp only [List.map_ofFn]
        rfl
      _ = _ := congrArg (fun xs => (xs.map serialize).map conditionalRow) hcat
  unfold conditionalOnPrefix
  change Ternary.exceptionalConditional q ((n,P),(serialized pad b t ℓ).map conditionalRow) =
    conditionalMass C (ConditionalChooser.prefixHash θ n p)
  rw [serialized_eq, ← hlist, he]
  have hlen : P.length = θ := ConditionalChoice.partialRows_length _
  have hp : ∀ i j, Ternary.hashOf n P i j = ConditionalChooser.prefixHash θ n p (Fin.cast hlen i) j :=
    ConditionalChoice.partialRows_hash θ n p
  suffices ∀ a (h : P.length = a) (H : PartialHash a n),
      (∀ i j, Ternary.hashOf n P i j = H (Fin.cast h i) j) →
      conditionalMass C (Ternary.hashOf n P) = conditionalMass C H by
    exact this θ hlen _ hp
  intro a h H hh
  subst a
  exact congrArg (conditionalMass C) (funext fun i => funext fun j => hh i j)

abbrev ChooserData (α : Type) := ConditionalChoice.Dimensions × α

/-- Supply the exceptional component directly from the word length. -/
def withExceptional {α : Type} (pad : Fin q) (b t : ℕ)
    (E : ChooserData α → ConditionalChooser.Evaluator) (x : ChooserData α) :
    ConditionalChooser.Evaluator :=
  fun i p => if i = 1 then conditionalOnPrefix pad b t (x.1,p) else E x i p

/-- Use the exceptional mass at the root as its scale. -/
def withExceptionalScale {α : Type} (pad : Fin q) (b t : ℕ)
    (μ : ChooserData α → Fin 3 → ℚ) (x : ChooserData α) (i : Fin 3) : ℚ :=
  if i = 1 then conditionalOnPrefix pad b t (x.1,[]) else μ x i

theorem choose_withExceptional_polyTime {α : Type} {enc : α ↪ List Bool}
    (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q)
    (E : ChooserData α → ConditionalChooser.Evaluator) (μ : ChooserData α → Fin 3 → ℚ)
    (hE : ∀ i, i ≠ 1 → ComputableInPolyTime (fun x : ChooserData α × ConditionalChooser.Prefix => E x.1 i x.2)
      (encPair (encPair ConditionalChoice.dimensionEncoding enc) ConditionalChoice.prefixEncoding) encRat)
    (hμ : ∀ i, i ≠ 1 → ComputableInPolyTime (fun x => μ x i)
      (encPair ConditionalChoice.dimensionEncoding enc) encRat) :
    ComputableInPolyTime (fun x : ChooserData α × ℕ => ConditionalChooser.choose
      (ConditionalChooser.score (withExceptional pad b t E x.1) (withExceptionalScale pad b t μ x.1)) x.2)
      (encPair (encPair ConditionalChoice.dimensionEncoding enc) encUnary) ConditionalChoice.prefixEncoding := by
  let dims := ConditionalChoice.dimensionEncoding
  let data := encPair dims enc
  let ep := ConditionalChoice.prefixEncoding
  have h := conditionalOnPrefix_polyTime pad b t hq
  apply ConditionalChoice.choose_three_polyTime
  · intro i
    by_cases hi : i = 1
    · simpa only [withExceptional, hi, ↓reduceIte, Function.comp_def] using
        h.comp (((fst data ep).fst').prod (snd data ep))
    · simpa only [withExceptional, hi, ↓reduceIte] using hE i hi
  · intro i
    by_cases hi : i = 1
    · simpa only [withExceptionalScale, hi, ↓reduceIte, Function.comp_def] using
        h.comp ((fst dims enc).prod (const []))
    · simpa only [withExceptionalScale, hi, ↓reduceIte] using hμ i hi

#print axioms choose_withExceptional_polyTime

#print axioms serialized_eq
#print axioms serialized_polyTime
#print axioms conditionalOnPrefix_eq
#print axioms conditionalOnPrefix_polyTime

#print axioms rowDelta_eq
#print axioms rowDelta_polyTime
#print axioms serialOne_polyTime

end DeletionCode.Explicit.Machine.ExceptionalRecords
