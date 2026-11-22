import DeletionCode.Explicit.Machine.SourceCoreBounds
import DeletionCode.Explicit.Machine.SourceSmallCodec
import DeletionCode.Explicit.Machine.SourceWitness
import DeletionCode.Explicit.Machine.SourceReplayPayload
import Batteries.Tactic.OpenPrivate
import DeletionCode.Explicit.Machine.SourceHashChoice
import DeletionCode.Explicit.CoreCatalogueList
import DeletionCode.Explicit.SourceHashChoice

/-! Enumerate the active assignments of each compact core replay slot. -/
namespace DeletionCode.Explicit.Machine.SourceCoreCatalogue

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open FieldHash Ternary CataloguePrefix SourceCoreReplay SourceLists
open Machine.SourceHashChoice (coreTableEncoding)
open CoreWeight ReplayGrammar
open _root_.DeletionCode.Explicit.UniformParameters
open private assignments from DeletionCode.Explicit.CoreCatalogueList
open private term_eq from DeletionCode.Explicit.Machine.CataloguePrefix
open private uniformSizes_polyTime from DeletionCode.Explicit.Machine.SourceReplayPayload
open private gamma_machine from DeletionCode.Explicit.Machine.UniformParameters

variable {q l b t : ℕ}

private def supportBudget (q b t l : ℕ) : ℕ := 2*t*coreLimit t*(4 * gram q b t l + 2*b)

private theorem supportBudget_polyTime (q b t : ℕ) :
    ComputableInPolyTime (supportBudget q b t) encUnary encUnary :=
  unary_mul' (const (2*t*coreLimit t)) (unary_add'
    (unary_mul' (const 4) (UniformParameters.gram_machine q b t)) (const (2*b)))

private abbrev E (q b t l : ℕ) := edits t * witnessLimit q b t l
private abbrev ReplayKey (l q b t : ℕ) := ReplaySlot l q (E q b t l) (gram q b t l) b t (coreLimit t)

private def candidateWord (pad : Fin q) (l : ℕ) (keys : List ℕ) (letters : QWord q) : QWord q :=
  SourceSmallCodec.assemble pad l keys letters (List.replicate (SourceSmallCodec.outside l keys).length pad)

private theorem candidateWord_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun p : (ℕ × List ℕ) × QWord q => candidateWord pad p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary PatchGraph.rowEncoding) (wordEncoding q)) (wordEncoding q) := by
  let e := encPair encUnary PatchGraph.rowEncoding
  let w := wordEncoding q
  have hp := fst e w
  have hw := snd e w
  have hout := SourceSmallCodec.outside_polyTime.comp hp
  have hlen := (length_list encUnary).comp hout
  have hf := replicate (encA := ExceptionalRecords.letterEncoding q) hlen (const pad)
  exact (SourceSmallCodec.assemble_polyTime pad).comp (hp.prod (hw.prod hf))

private theorem support_names {N r : ℕ} (v : Materialized l q N r) :
    SourceCoreCheck.support l (materialData v) = SourceSmallCodec.names v.support := by
  rw [SourceCoreCheck.support_eq, SourceWitness.filter_finRange_eq_sort]
  rfl

private theorem candidateWord_eq (pad : Fin q) (k : ReplayKey l q b t)
    (a : ↥(slotSupport k) → Fin q) :
    candidateWord pad l (SourceSmallCodec.names (slotSupport k))
      (List.ofFn (a ∘ ((slotSupport k).orderIsoOfFin rfl))) = List.ofFn (slotWord pad k a) := by
  let S := slotSupport k
  unfold candidateWord
  rw [SourceSmallCodec.outside_eq, SourceSmallCodec.names_length]
  rw [show List.replicate Sᶜ.card pad = List.ofFn (fun _ : Fin Sᶜ.card => pad) by simp]
  rw [SourceSmallCodec.assemble_eq]
  apply congrArg List.ofFn
  funext i
  unfold SmallFamilyCodec.assemble slotWord
  by_cases h : i ∈ S
  · simp [S, h]
  · simp [S, h]

private theorem rank_matrixRows {n m : ℕ} (A : TernaryMatrix m n) :
    rank (n, matrixRows A) = ternaryRank A := by
  rw [rank_eq, ternaryRank_eq, ternaryRank_eq]
  let e : Fin (matrixRows A).length ≃ Fin m := finCongr List.length_ofFn
  have he : matrixOf (n, matrixRows A) = Matrix.reindex e.symm (Equiv.refl _) A := by
    funext i j
    change ((List.ofFn (fun u : Fin m => List.ofFn (A u))).getD (e i).val []).getD j.val 0 = A (e i) j
    rw [BooleanFibres.ofFn_getD (fun u => List.ofFn (A u)) (e i) [],
      BooleanFibres.ofFn_getD (A (e i)) j 0]
  rw [he, Matrix.rank_reindex]

abbrev CandidateInput (q : ℕ) := (ℕ × ℕ) × (Material q × (List ℕ × QWord q))
abbrev candidateEncoding (q : ℕ) := encPair (encPair encUnary encUnary)
  (encPair (materialEncoding q) (encPair PatchGraph.rowEncoding (wordEncoding q)))

def candidate (pad : Fin q) (b t : ℕ) (p : CandidateInput q) : Option (EntryData q) :=
  let (param, m, keys, a) := p
  let (l, count) := param
  let L := gram q b t l
  let x := candidateWord pad l keys a
  if SourceCoreCheck.check pad (windowLength q l) b L (omittedLetters q b t l) (edits t) x m then
    let rows := SourceCoreCheck.rows pad L x m
    if rank (q^L, rows) = count then some (rows, keys.zip a) else none
  else none

private theorem candidate_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (candidate pad b t) (candidateEncoding q) (encOption (entryEncoding q)) := by
  let e := candidateEncoding q
  let m := materialEncoding q
  let k := PatchGraph.rowEncoding
  let w := wordEncoding q
  let f := encPair encUnary encUnary
  let d := encPair k w
  have hf := fst f (encPair m d)
  have hd := snd f (encPair m d)
  have hl := hf.fst'
  have hkeys := hd.snd'.fst'
  have ha := hd.snd'.snd'
  have hx := (candidateWord_polyTime pad).comp (encIn := e) ((hl.prod hkeys).prod ha)
  have hg := (UniformParameters.gram_machine q b t).comp hl
  have hK := (UniformParameters.window_machine q).comp hl
  have hΛ := (UniformParameters.omitted_machine q b t).comp hl
  have htest := (SourceCoreCheck.runCheck_polyTime pad b).comp (encIn := e)
    (SourceCoreCheck.checkInputEncoding_mk_polyTime q hK hg hΛ (const (edits t)) hx hd.fst')
  have hrows := (SourceCoreCheck.uniformRows_polyTime pad b t hq).comp (encIn := e) (hl.prod (hx.prod hd.fst'))
  have hwidth := (SourceHashChoice.width_polyTime q b t hq).comp hl
  have hrank := rank_polyTime.comp (encIn := e) (hwidth.prod hrows)
  have hz := (ComputableInPolyTime.zip encUnary (ExceptionalRecords.letterEncoding q)).comp (hkeys.prod ha)
  have hout := (optionSome (entryEncoding q)).comp (hrows.prod hz)
  have h := htest.ite' ((hrank.decide_eq' hf.snd').ite' hout (const none)) (const none)
  exact h.of_enc_eq (fun p => by
    simp [candidate, SourceCoreCheck.runCheck]
    rfl)

private abbrev numericKeyEncoding := encPair encUnary (encPair encUnary (encPair encNat encNat))

private def numericSlot (q b t : ℕ) (p : ℕ × (ℕ × (ℕ × ℕ))) : SlotInput :=
  ⟨p.1, E q b t p.1, gram q b t p.1, b, t, p.2.1, p.2.2.1, p.2.2.2⟩

private theorem numericSlot_polyTime (q b t : ℕ) :
    ComputableInPolyTime (numericSlot q b t) numericKeyEncoding slotEncoding := by
  let a := encPair encUnary (encPair encNat encNat)
  have hl := fst encUnary a
  have hx := snd encUnary a
  have hs := (uniformSizes_polyTime q b t).comp hl
  exact slotEncoding_mk_polyTime hl hs.snd'.fst' hs.snd'.snd'.fst' (const b) (const t) hx.fst'
    hx.snd'.fst' hx.snd'.snd'

private def slotCandidates (pad : Fin q) (b t l count : ℕ) (m : Material q) : List (EntryData q) :=
  let keys := SourceCoreCheck.support l m
  let n := min keys.length (supportBudget q b t l)
  (GramOrder.mainWords pad n).filterMap (fun a => candidate pad b t ((l, count), m, keys, a))

def objectsInSlot (pad : Fin q) (b t : ℕ) (p : ℕ × (ℕ × (ℕ × ℕ))) : List (EntryData q) :=
  (materializeSlot pad (numericSlot q b t p)).elim [] (slotCandidates pad b t p.1 p.2.1)

private theorem slotWords_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : ℕ × List ℕ => GramOrder.mainWords pad (min p.2.length (supportBudget q b t p.1)))
      (encPair encUnary PatchGraph.rowEncoding) (encList (wordEncoding q)) := by
  let e := encPair encUnary PatchGraph.rowEncoding
  let a := encPair e encUnary
  have hl := fst encUnary PatchGraph.rowEncoding
  have hk := snd encUnary PatchGraph.rowEncoding
  have hn := unary_min' ((length_list encUnary).comp hk) ((supportBudget_polyTime q b t).comp hl)
  have hwidth := (SourceHashChoice.width_polyTime q b t hq).comp hl
  let B := 8*t*coreLimit t
  let A := 4*t*coreLimit t*b
  have hb : ComputableInPolyTime (fun p : ℕ × List ℕ => (q^gram q b t p.1)^B * q^A) e encUnary :=
    unary_mul' ((unary_pow B).comp hwidth) (const (q^A))
  have hPow := binary_pow.comp ((const (encOut := encNat) q).prod hn)
  have hcount := binary_to_unary_bounded hPow hb (fun p => by
    apply (Nat.pow_le_pow_right (by omega : 0 < q) (Nat.min_le_right _ _)).trans_eq
    have he : supportBudget q b t p.1 = gram q b t p.1*B + A := by
      simp only [supportBudget, B, A]
      ring
    change q^supportBudget q b t p.1 = _
    rw [he, pow_add, pow_mul])
  have hdigits := (RareAddress.fixedDigits_polyTime pad).comp (encIn := a)
    ((hn.comp (fst e encUnary)).prod (unary_to_binary.comp (snd e encUnary)))
  have hword := (listReverse (ExceptionalRecords.letterEncoding q)).comp (encIn := a) (encMid := wordEncoding q) hdigits
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := wordEncoding q)
    (f := fun p j => (RareAddress.fixedDigits pad (min p.2.length (supportBudget q b t p.1)) j).reverse)
    (unary_range' hcount) hword

private abbrev slotCandidateEncoding (q : ℕ) := encPair (encPair encUnary encUnary) (materialEncoding q)

private theorem slotCandidates_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × Material q => slotCandidates pad b t p.1.1 p.1.2 p.2)
      (slotCandidateEncoding q) (coreTableEncoding q) := by
  let e := slotCandidateEncoding q
  let f := encPair encUnary encUnary
  let w := wordEncoding q
  let m := materialEncoding q
  let v := entryEncoding q
  have h := fst f m
  have hm := snd f m
  have hl := h.fst'
  have hk := (SourceCoreCheck.support_polyTime q).comp (hl.prod hm)
  have hw := (slotWords_polyTime pad b t hq).comp (hl.prod hk)
  have ha := fst e w
  have hcase := (candidate_polyTime pad b t hq).comp (encIn := encPair e w)
    ((h.comp ha).prod ((hm.comp ha).prod ((hk.comp ha).prod (snd e w))))
  have hflat := flatMapWithInput (encIn := e) (encA := w) (encB := v)
    (f := fun p a => (candidate pad b t (p.1, p.2, SourceCoreCheck.support p.1.1 p.2, a)).toList)
    hw ((optionToList_polyTime v).comp hcase)
  exact hflat.of_enc_eq (fun p => congrArg _ (List.filterMap_eq_flatMap_toList _ _))

theorem objectsInSlot_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (objectsInSlot pad b t) numericKeyEncoding (coreTableEncoding q) := by
  let e := numericKeyEncoding
  let a := encPair encUnary (encPair encNat encNat)
  let m := materialEncoding q
  have hm := (materialize_polyTime pad).comp (numericSlot_polyTime q b t)
  have hp := (fst encUnary a).prod (snd encUnary a).fst'
  exact optionElimWithInput (encA := e) (encB := m) (encC := coreTableEncoding q)
    (body := fun p m => slotCandidates pad b t p.1 p.2.1 m) hm (const [])
    ((slotCandidates_polyTime pad b t hq).comp ((hp.comp (fst e m)).prod (snd e m)))

private abbrev coreData (q b t l : ℕ) (pad : Fin q) :=
  _root_.DeletionCode.Explicit.SourceHashChoice.coreData q b t l pad

private def selected {n r Γ : ℕ} (D : ReplayData l q n t r Γ) (c : D.Candidate) : Option (EntryData q) :=
  if h : D.admissible c = true then some (objectData (D.object ⟨c, h⟩)) else none

private theorem serialize_zip (S : Finset (Fin l)) (a : ↥S → Fin q) :
    (SourceSmallCodec.names S).zip (List.ofFn (a ∘ S.orderIsoOfFin rfl)) =
      ExceptionalRecords.serializeAssignment (⟨S, a⟩ : Assignment l q) := by
  have hsort : ExceptionalWeight.supportList S = S.sort := SourceWitness.filter_finRange_eq_sort S
  unfold ExceptionalRecords.serializeAssignment
  apply List.ext_getElem
  · simp [SourceSmallCodec.names_length]
  · intro i hi hj
    have h : i < S.card := by simpa [SourceSmallCodec.names_length] using hi
    simp only [List.getElem_zip, List.getElem_ofFn, List.getElem_map, List.getElem_attach, Function.comp_def]
    apply Prod.ext
    · simp only [SourceSmallCodec.names, List.getElem_map, hsort]
    · apply congrArg a
      apply Subtype.ext
      simp only [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply, hsort]
      rfl

private theorem oneCandidate_eq (pad : Fin q) (hq : 2 ≤ q) (k : ReplayKey l q b t)
    (m : Materialized l q (E q b t l) (k.1.val+1)) (hm : materialize k = some m)
    (a : ↥(slotSupport k) → Fin q) :
    candidate pad b t ((l, k.1.val+1), materialData m, SourceSmallCodec.names (slotSupport k),
      List.ofFn (a ∘ (slotSupport k).orderIsoOfFin rfl)) = selected (coreData q b t l pad) ⟨k, a⟩ := by
  let x := slotWord pad k a
  let D := coreData q b t l pad
  let pass := coreCheck (windowLength q l) b (gram q b t l) (omittedLetters q b t l) (edits t) pad m x
  let A := m.matrix (gram q b t l) pad x
  have hr : D.rules k a = if pass then some A else none := by
    change ((materialize k).bind fun v => if coreCheck (windowLength q l) b (gram q b t l)
      (omittedLetters q b t l) (edits t) pad v x then some (v.matrix (gram q b t l) pad x) else none) = _
    rw [hm]
    rfl
  unfold candidate
  dsimp only
  rw [candidateWord_eq, SourceCoreCheck.check_eq, SourceCoreCheck.rows_eq pad hq, rank_matrixRows, serialize_zip]
  unfold selected
  change (if pass then if ternaryRank A = k.1.val+1 then some (matrixRows A,
      ExceptionalRecords.serializeAssignment ⟨slotSupport k, a⟩) else none else none) =
    (if h : (D.rules k a).any (fun B => decide (ternaryRank B = k.1.val+1)) = true then
      some (objectData (D.object ⟨⟨k, a⟩, h⟩)) else none)
  cases hp : pass with
  | false => simp [hr, hp]
  | true =>
    have hr' : D.rules k a = some A := by simpa [hp] using hr
    by_cases h : ternaryRank A = k.1.val+1
    · simp only [hr', ↓reduceIte, Option.any_some, decide_eq_true_eq, h, ↓reduceDIte]
      unfold objectData ReplayData.object
      apply congrArg some
      apply Prod.ext
      · exact congrArg (fun r : Option (TernaryMatrix (k.1.val+1) (q^gram q b t l)) => matrixRows (r.getD 0)) hr'.symm
      · rfl
    · simp [hr', h]

theorem objectsInSlot_eq (pad : Fin q) (hq : 2 ≤ q) (k : ReplayKey l q b t) :
    objectsInSlot pad b t (l, k.1.val+1, k.2.1.val, k.2.2.val) =
      (assignments (coreData q b t l pad) k).filterMap (fun a => selected (coreData q b t l pad) ⟨k, a⟩) := by
  unfold objectsInSlot materializeSlot numericSlot
  dsimp only
  rw [materialize_eq pad hq k]
  cases hm : materialize k with
  | none =>
    symm
    apply List.filterMap_eq_nil_iff.mpr
    intro a _
    have hr : (coreData q b t l pad).rules k a = none := by
      simp [coreData, _root_.DeletionCode.Explicit.SourceHashChoice.coreData, coreReplayData, checkedReplayData, hm]
    simp [selected, ReplayData.admissible, hr]
  | some m =>
    let S := slotSupport k
    have hS : S = m.support := by simp [S, slotSupport, hm]
    have hk : SourceCoreCheck.support l (materialData m) = SourceSmallCodec.names S := by
      rw [hS, support_names]
    have hcap : S.card ≤ supportBudget q b t l := by
      rw [hS]
      exact (SourceCoreBounds.materialize_support_le k m hm).trans
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ k.1.isLt))
    simp only [Option.map_some, Option.elim_some]
    rw [slotCandidates, hk, SourceSmallCodec.names_length, Nat.min_eq_left hcap, GramOrder.mainWords_eq pad hq]
    change (List.ofFn (fun j : Fin (q^S.card) => List.ofFn (finFunctionFinEquiv.symm j))).filterMap _ = _
    rw [show List.ofFn (fun j : Fin (q^S.card) => List.ofFn (finFunctionFinEquiv.symm j)) =
      (List.finRange (q^S.card)).map (fun j => List.ofFn (finFunctionFinEquiv.symm j)) by simp [List.finRange, List.map_ofFn, Function.comp_def]]
    unfold assignments
    rw [List.filterMap_map, List.filterMap_map]
    apply List.filterMap_congr
    intro j _
    let a : ↥S → Fin q := finFunctionFinEquiv.symm j ∘ (S.orderIsoOfFin rfl).symm
    have ha : a ∘ S.orderIsoOfFin rfl = finFunctionFinEquiv.symm j := by
      funext i
      simp [a, Function.comp_def]
    simp only [Function.comp_def]
    rw [← ha]
    exact oneCandidate_eq pad hq k m hm a

private def anchorCount (t l r : ℕ) : ℕ := l^(t*min (r+1) (coreLimit t))

private theorem anchorCount_polyTime (t : ℕ) :
    ComputableInPolyTime (fun p : ℕ × ℕ => anchorCount t p.1 p.2) (encPair encUnary encUnary) encUnary := by
  let e := encPair encUnary encUnary
  have hl := fst encUnary encUnary
  have hr := snd encUnary encUnary
  have ha := unary_mul' (const t) (unary_min' (unary_add' hr (const 1)) (const (coreLimit t)))
  have hPow := binary_pow.comp (encIn := e) ((unary_to_binary.comp hl).prod ha)
  have hBound := (unary_pow (t*coreLimit t)).comp (unary_add' hl (const 1))
  exact binary_to_unary_bounded hPow hBound (fun p =>
    (Nat.pow_le_pow_left (Nat.le_succ p.1) _).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.mul_le_mul_left t (Nat.min_le_right ..))))

def keys (q b t l : ℕ) : List (ℕ × (ℕ × (ℕ × ℕ))) :=
  (List.range (coreLimit t)).flatMap fun r =>
    (List.range (min (gamma q b t l) l)).flatMap fun d =>
      (List.range (anchorCount t l r)).map fun a => (l, r+1, d, a)

private theorem keys_polyTime (q b t : ℕ) : ComputableInPolyTime (keys q b t) encUnary
    (encList numericKeyEncoding) := by
  let e := encPair encUnary encUnary
  let p := encPair e encUnary
  let z := encPair p encUnary
  let d := numericKeyEncoding
  have hl := fst encUnary encUnary
  have hr := snd encUnary encUnary
  have hγ := binary_to_unary_bounded (binary_min' (gamma_machine q b t) unary_to_binary) id'
    (fun _ => Nat.min_le_right ..)
  have hn := (anchorCount_polyTime t).comp (fst e encUnary)
  have hp := fst e encUnary
  have ha := fst p encUnary
  have hd := unary_to_binary.comp ((snd e encUnary).comp ha)
  have hi := unary_to_binary.comp (snd p encUnary)
  have hk := ((hl.comp hp).comp ha).prod
    ((unary_add' ((hr.comp hp).comp ha) (const 1)).prod (hd.prod hi))
  have hbyAnchor := mapWithInput (encIn := p) (encA := encUnary) (encB := d)
    (f := fun x a => (x.1.1, x.1.2+1, x.2, a)) (unary_range' hn) hk
  have hbyDescription := flatMapWithInput (encIn := e) (encA := encUnary) (encB := d)
    (f := fun x j => (List.range (anchorCount t x.1 x.2)).map (fun i => (x.1, x.2+1, j, i)))
    (unary_range' (hγ.comp hl)) hbyAnchor
  exact flatMapWithInput (encIn := encUnary) (encA := encUnary) (encB := d)
    (f := fun l r => (List.range (min (gamma q b t l) l)).flatMap (fun j =>
      (List.range (anchorCount t l r)).map (fun i => (l, r+1, j, i))))
    (const (List.range (coreLimit t))) hbyDescription

def table (pad : Fin q) (b t l : ℕ) : List (EntryData q) :=
  (keys q b t l).flatMap (objectsInSlot pad b t)

theorem table_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (table pad b t) encUnary (coreTableEncoding q) :=
  flatMapWithInput (encIn := encUnary) (encA := numericKeyEncoding) (encB := entryEncoding q)
    (f := fun _ p => objectsInSlot pad b t p) (keys_polyTime q b t)
    ((objectsInSlot_polyTime pad b t hq).comp (snd encUnary numericKeyEncoding))

theorem keys_eq (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) (hl : minLength q b t ≤ l) :
    keys q b t l = (ReplayData.slots l t (coreLimit t) (gamma q b t l)).map
      (fun k => (l, k.1.val+1, k.2.1.val, k.2.2.val)) := by
  have hΓ : gamma q b t l ≤ l := by
    have he := (enumerationBounds hq hb ht hl).1
    by_cases hz : gamma q b t l = 0
    · simp [hz]
    · have hp := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hz) (show 1 ≤ 8 by decide)
      exact (by simpa using hp.trans he)
  unfold keys ReplayData.slots
  rw [Nat.min_eq_left hΓ, List.map_flatMap]
  rw [show List.range (coreLimit t) = (List.finRange (coreLimit t)).map Fin.val by simp, List.flatMap_map]
  apply List.flatMap_congr
  intro r _
  simp only [Function.comp_def, List.map_map, anchorCount]
  rw [show min (r.val+1) (coreLimit t) = r.val+1 from min_eq_left r.isLt]
  unfold List.product
  rw [List.map_flatMap, show List.range (gamma q b t l) = (List.finRange (gamma q b t l)).map Fin.val by simp,
    List.flatMap_map]
  apply List.flatMap_congr
  intro a _
  simp only [Function.comp_def, List.map_map]
  rw [show List.range (l^(t*(r.val+1))) = (List.finRange (l^(t*(r.val+1)))).map Fin.val by simp, List.map_map]
  rfl

theorem table_eq (pad : Fin q) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) (hl : minLength q b t ≤ l) :
    table pad b t l = (coreData q b t l pad).table.map objectData := by
  unfold table
  rw [keys_eq hq hb ht hl, List.flatMap_map]
  let D := coreData q b t l pad
  change (ReplayData.slots l t (coreLimit t) (gamma q b t l)).flatMap
    (fun k => objectsInSlot pad b t (l,k.1.val+1,k.2.1.val,k.2.2.val)) = D.table.map objectData
  unfold ReplayData.table ReplayData.indices ReplayData.candidates
  rw [List.map_map, List.map_filterMap, List.filterMap_flatMap]
  apply List.flatMap_congr
  intro k _
  rw [objectsInSlot_eq pad hq k, List.filterMap_map]
  apply List.filterMap_congr
  intro a _
  unfold selected
  simp only [Function.comp_def]
  split <;> rfl

abbrev prefixEncoding (q : ℕ) := encPair encUnary (encPair rowsEncoding (wordEncoding q))

def evaluatePrefix (pad : Fin q) (b t : ℕ) (p : ℕ × (Rows × QWord q)) : ℕ :=
  CataloguePrefix.prefixMass pad ((p.1, (q^gram q b t p.1, p.2.1), p.2.2), table pad b t p.1)

theorem prefix_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (evaluatePrefix pad b t) (prefixEncoding q) encNat := by
  let e := prefixEncoding q
  let w := wordEncoding q
  have hl := fst encUnary (encPair rowsEncoding w)
  have hw := snd encUnary (encPair rowsEncoding w)
  have hn := (SourceHashChoice.width_polyTime q b t hq).comp hl
  have h := (table_polyTime pad b t hq).comp hl
  exact (CataloguePrefix.prefixMass_polyTime pad).comp (encIn := e)
    ((hl.prod ((hn.prod hw.fst').prod hw.snd')).prod h)

theorem prefix_eq (pad : Fin q) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) (hl : minLength q b t ≤ l)
    (H : ConcreteSource.Hash q b t l) {k : ℕ} (u : Fin k → Fin q) :
    evaluatePrefix pad b t (l, matrixRows H, List.ofFn u) = CoreWeight.prefixMass (coreData q b t l pad).object H u := by
  let D := coreData q b t l pad
  unfold evaluatePrefix CataloguePrefix.prefixMass CoreWeight.prefixMass
  simp only [List.length_ofFn, table_eq pad hq hb ht hl, ReplayData.table, List.map_map, Function.comp_def]
  split_ifs
  · rw [← ReplayData.sum_indices D _]
    apply congrArg List.sum
    apply List.map_congr_left
    intro i _
    exact term_eq pad H u (D.object i)
  · rfl

#print axioms objectsInSlot_eq
#print axioms objectsInSlot_polyTime
#print axioms table_eq
#print axioms table_polyTime
#print axioms prefix_eq
#print axioms prefix_polyTime

end DeletionCode.Explicit.Machine.SourceCoreCatalogue
