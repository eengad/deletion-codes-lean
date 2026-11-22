import DeletionCode.Explicit.Machine.SourceReference
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-! The compact replay grammar on fixed fields and serialized description lists. -/
namespace DeletionCode.Explicit.Machine.SourceGrammar

open ReplayEntry ReplayGrammar SourceReference SourceLists
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open private readThree prefixWord encodeNat packFields paddingEntry from DeletionCode.Explicit.ReplayGrammar

variable {q E L b : ℕ}

structure Decoded (q : ℕ) where
  rule : ℕ
  patch : ℕ
  left : ℕ
  right : ℕ
  removed : QWord q
  replacement : QWord q
  refs : List Ref
  finalBubble : Bool
  finalRule : Bool

enc_structure decodedEncoding (q : ℕ) : Decoded q where
  rule : encUnary, patch : encUnary, left : encUnary, right : encUnary,
  removed : (wordEncoding q), replacement : (wordEncoding q), refs : (encList refEncoding),
  finalBubble : encBool, finalRule : encBool

abbrev decodedListEncoding (q : ℕ) := encList (decodedEncoding q)
abbrev Code (q : ℕ) := List ℕ × (QWord q × QWord q)
abbrev Description (q : ℕ) := ℕ × List (Code q)
abbrev codeEncoding (q : ℕ) := encPair PatchGraph.rowEncoding (encPair (wordEncoding q) (wordEncoding q))
abbrev descriptionEncoding (q : ℕ) := encPair encUnary (encList (codeEncoding q))
abbrev sizesEncoding := encPair encUnary (encPair encUnary encUnary)

def decodedData (d : ReplayGrammar.DecodedEntry q) : Decoded q :=
  ⟨d.entry.rule,d.entry.patch,d.entry.left,d.entry.right,d.entry.removed,d.entry.replacement,
    d.entry.references.map referenceData,d.finalBubble,d.finalRule⟩

def codeData (c : EntryCode E L b q) : Code q :=
  (List.ofFn fun i => (c.1 i).val,List.ofFn c.2.1,List.ofFn c.2.2)

def descriptionData (c : DescriptionCode E L b q) : Description q :=
  (c.1.val,List.ofFn (codeData ∘ c.2))

def field (c : Code q) (i : ℕ) : ℕ := c.1.getD i 0

private theorem field_eq (c : EntryCode E L b q) (k : ℕ) (h : k < 11) :
    field (codeData c) k = (c.1 (Fin.ofNat 11 k)).val := by
  change (List.ofFn (fun i => (c.1 i).val)).getD k 0 = _
  have he : Fin.ofNat 11 k = ⟨k,h⟩ := Fin.ext (Nat.mod_eq_of_lt h)
  rw [he]
  exact BooleanFibres.ofFn_getD (fun i => (c.1 i).val) ⟨k,h⟩ 0

def refsFrom (rs : List (Option Ref)) : Option (List Ref) :=
  if (rs.getD 0 none).isSome && (!(rs.getD 2 none).isSome || (rs.getD 1 none).isSome) then
    some (rs.flatMap Option.toList)
  else none

def references (E L : ℕ) (c : Code q) : Option (List Ref) :=
  ([6,7,8].mapM (fun i => decode E L (field c i))).bind refsFrom

private theorem references_eq (c : EntryCode E L b q) :
    references E L (codeData c) = (readThree E L c.1).map (List.map referenceData) := by
  unfold references readThree
  simp only [List.mapM_cons,List.mapM_nil]
  rw [field_eq c 6 (by decide),field_eq c 7 (by decide),field_eq c 8 (by decide)]
  simp only [SourceReference.decode_eq]
  cases ReplayGrammar.decodeReference E L (c.1 6) with
  | none => rfl
  | some x =>
    cases ReplayGrammar.decodeReference E L (c.1 7) with
    | none => rfl
    | some y =>
      cases ReplayGrammar.decodeReference E L (c.1 8) with
      | none => rfl
      | some z => cases x <;> cases y <;> cases z <;> rfl

def finalize (L : ℕ) (c : Code q) (rs : List Ref) : Option (Decoded q) :=
  let d : Decoded q := ⟨field c 0,field c 1,field c 2,field c 3,c.2.1.take (field c 4),
    c.2.2.take (field c 5),rs,decide (field c 9 = 1),decide (field c 10 = 1)⟩
  if rs.length = (selectedStarts L (d.left+d.removed.length+d.right)).length then some d else none

def decodeEntry (E L b : ℕ) (c : Code q) : Option (Decoded q) :=
  if E ≤ field c 0 ∨ E ≤ field c 1 ∨ L ≤ field c 2 ∨ L ≤ field c 3 ∨
      1 < field c 9 ∨ 1 < field c 10 then none
  else if field c 4 ≤ b ∧ field c 5 ≤ b then (references E L c).bind (finalize L c)
  else none

private theorem take_prefix (w : Fin b → Fin q) (n : ℕ) (h : n ≤ b) :
    (List.ofFn w).take n = prefixWord w n h := by
  apply List.ext_getElem (by simp [prefixWord,Nat.min_eq_left h])
  intro i hi hj
  simp [prefixWord]

theorem decodeEntry_eq (c : EntryCode E L b q) :
    decodeEntry E L b (codeData c) = (ReplayGrammar.decodeEntry c).map decodedData := by
  have h0 : field (codeData c) 0 = (c.1 0).val := field_eq c 0 (by decide)
  have h1 : field (codeData c) 1 = (c.1 1).val := field_eq c 1 (by decide)
  have h2 : field (codeData c) 2 = (c.1 2).val := field_eq c 2 (by decide)
  have h3 : field (codeData c) 3 = (c.1 3).val := field_eq c 3 (by decide)
  have h4 : field (codeData c) 4 = (c.1 4).val := field_eq c 4 (by decide)
  have h5 : field (codeData c) 5 = (c.1 5).val := field_eq c 5 (by decide)
  have h9 : field (codeData c) 9 = (c.1 9).val := field_eq c 9 (by decide)
  have h10 : field (codeData c) 10 = (c.1 10).val := field_eq c 10 (by decide)
  unfold decodeEntry ReplayGrammar.decodeEntry
  simp only [h0,h1,h2,h3,h4,h5,h9,h10,gt_iff_lt,ge_iff_le]
  split
  · rfl
  · by_cases hu : (c.1 4).val ≤ b
    · by_cases hv : (c.1 5).val ≤ b
      · simp only [hu,hv,and_self,↓reduceIte,↓reduceDIte,references_eq]
        cases readThree E L c.1 with
        | none => rfl
        | some rs =>
          have h₁ : (codeData c).2.1.take ((c.1 4).val) = prefixWord c.2.1 (c.1 4).val hu :=
            take_prefix _ _ hu
          have h₂ : (codeData c).2.2.take ((c.1 5).val) = prefixWord c.2.2 (c.1 5).val hv :=
            take_prefix _ _ hv
          simp only [Option.map_some,Option.bind_some,bind,Option.bind,finalize,
            List.length_map,Entry.negativeLength,h0,h1,h2,h3,h4,h5,h9,h10,h₁,h₂]
          split <;> simp_all [decodedData]
      · simp [hu,hv]
    · simp [hu]

private def padWord (pad : Fin q) (n : ℕ) (w : QWord q) : QWord q :=
  (List.range n).map (fun i => w.getD i pad)

def numericFields (d : Decoded q) : List ℕ :=
  [d.rule,d.patch,d.left,d.right,d.removed.length,d.replacement.length]

def codeNumbers (E L : ℕ) (ns : List ℕ) : Option (List ℕ) :=
  ns.mapM (fun n => if n < ReplayGrammar.radix E L then some n else none)

def codeRefs (E L : ℕ) (rs : List Ref) : Option (List ℕ) :=
  [0,1,2].mapM (fun i => encode E L rs[i]?)

def encodeEntry (pad : Fin q) (E L b : ℕ) (d : Decoded q) : Option (Code q) := do
  let ns ← codeNumbers E L (numericFields d)
  let rs ← codeRefs E L d.refs
  pure (ns++rs++[d.finalBubble.toNat,d.finalRule.toNat],
    padWord pad b d.removed,padWord pad b d.replacement)

private theorem number_eq (E L n : ℕ) :
    (if n < ReplayGrammar.radix E L then some n else none) =
      (encodeNat E L n).map Fin.val := by
  simp only [encodeNat]
  split <;> rfl

private theorem bool_fits (E L : ℕ) (b : Bool) : b.toNat < ReplayGrammar.radix E L := by
  have hr : 100 ≤ ReplayGrammar.radix E L := by
    unfold ReplayGrammar.radix
    nlinarith
  cases b <;> simp <;> omega

private theorem bool_code (E L : ℕ) (b : Bool) :
    encodeNat E L b.toNat = some ⟨b.toNat,bool_fits E L b⟩ := by
  simp [encodeNat,bool_fits]

theorem encodeEntry_eq (pad : Fin q) (d : ReplayGrammar.DecodedEntry q) :
    encodeEntry pad E L b (decodedData d) =
      (ReplayGrammar.encodeEntry E L b q pad d).map codeData := by
  unfold encodeEntry codeNumbers numericFields codeRefs ReplayGrammar.encodeEntry
  simp only [decodedData,List.mapM_cons,List.mapM_nil,number_eq,List.getElem?_map,SourceReference.encode_eq,
    bool_code]
  generalize h₀ : encodeNat E L d.entry.rule = c₀
  generalize h₁ : encodeNat E L d.entry.patch = c₁
  generalize h₂ : encodeNat E L d.entry.left = c₂
  generalize h₃ : encodeNat E L d.entry.right = c₃
  generalize h₄ : encodeNat E L d.entry.removed.length = c₄
  generalize h₅ : encodeNat E L d.entry.replacement.length = c₅
  generalize h₆ : encodeReference E L d.entry.references[0]? = c₆
  generalize h₇ : encodeReference E L d.entry.references[1]? = c₇
  generalize h₈ : encodeReference E L d.entry.references[2]? = c₈
  cases c₀ <;> try rfl
  cases c₁ <;> try rfl
  cases c₂ <;> try rfl
  cases c₃ <;> try rfl
  cases c₄ <;> try rfl
  cases c₅ <;> try rfl
  cases c₆ <;> try rfl
  cases c₇ <;> try rfl
  cases c₈ <;> try rfl
  simp only [Option.map_some,Option.bind_some,bind,Option.bind,pure,codeData,packFields,
    padWord,SourceLists.range_map_eq]
  congr 1


def decodeDescription (E L b : ℕ) (d : Description q) : Option (List (Decoded q)) :=
  (d.2.take d.1).mapM (decodeEntry E L b)

def encodeDescription (pad : Fin q) (E L b : ℕ) (ds : List (Decoded q)) : Option (Description q) := do
  let codes ← ds.mapM (encodeEntry pad E L b)
  if codes.length ≤ E then
    let padding := (List.replicate 11 0,List.replicate b pad,List.replicate b pad)
    some (codes.length,(List.range E).map (fun i => codes.getD i padding))
  else none

theorem decodeDescription_eq (c : DescriptionCode E L b q) :
    decodeDescription E L b (descriptionData c) =
      (ReplayGrammar.decodeDescription c).map (List.map decodedData) := by
  unfold decodeDescription descriptionData ReplayGrammar.decodeDescription
  have ht : (List.ofFn (codeData ∘ c.2)).take c.1.val =
      List.ofFn (fun i : Fin c.1.val => codeData (c.2 (i.castLE (Nat.le_of_lt_succ c.1.isLt)))) := by
    apply List.ext_getElem (by simp [Nat.min_eq_left (Nat.le_of_lt_succ c.1.isLt)])
    intro i hi hj
    simp [Function.comp_def]
  dsimp only [Prod.fst,Prod.snd]
  rw [ht]
  change (List.ofFn (fun i : Fin c.1.val => codeData (c.2 (i.castLE (Nat.le_of_lt_succ c.1.isLt))))).mapM
    (decodeEntry E L b) = _
  let cs := List.ofFn (fun i : Fin c.1.val => c.2 (i.castLE (Nat.le_of_lt_succ c.1.isLt)))
  have hc : List.ofFn (fun i : Fin c.1.val =>
      codeData (c.2 (i.castLE (Nat.le_of_lt_succ c.1.isLt)))) = cs.map codeData := by
    dsimp only [cs]
    rw [List.map_ofFn]
    rfl
  rw [hc,List.mapM_map]
  simp only [Function.comp_def,decodeEntry_eq]
  exact SourceNegative.mapM_map_result _ _ _

theorem encodeDescription_eq (pad : Fin q) (ds : List (ReplayGrammar.DecodedEntry q)) :
    encodeDescription pad E L b (ds.map decodedData) =
      (ReplayGrammar.encodeDescription E L b q pad ds).map descriptionData := by
  unfold encodeDescription ReplayGrammar.encodeDescription
  rw [List.mapM_map]
  simp only [Function.comp_def,encodeEntry_eq]
  rw [SourceNegative.mapM_map_result]
  cases hs : ds.mapM (ReplayGrammar.encodeEntry E L b q pad) with
  | none => rfl
  | some cs =>
    simp only [Option.map_some,bind,Option.bind,List.length_map]
    by_cases hl : cs.length ≤ E
    · simp only [hl,↓reduceIte,↓reduceDIte,Option.map_some,descriptionData,SourceLists.range_map_eq]
      have hp : (List.replicate 11 0,List.replicate b pad,List.replicate b pad) =
          codeData (paddingEntry E L b q pad) := by
        simp [codeData,paddingEntry,List.ofFn_const]
      rw [hp]
      apply congrArg some
      congr 1
      congr 1
      funext i
      rw [List.getD_eq_getElem?_getD,List.getElem?_map]
      simp only [Function.comp_def,List.getD_eq_getElem?_getD]
      cases cs[i.val]? <;> rfl
    · simp [hl]

theorem radix_polyTime :
    ComputableInPolyTime (fun x : ℕ × ℕ => ReplayGrammar.radix x.1 x.2) fieldsEncoding encUnary := by
  exact unary_mul' (unary_mul' (const 100) (unary_add' (fst encUnary encUnary) (const 1)))
    (unary_add' (snd encUnary encUnary) (const 1))

abbrev decodeInputEncoding (q : ℕ) := encPair sizesEncoding (codeEncoding q)
abbrev refsEncoding := encList refEncoding
abbrev optionRefsEncoding := encList referenceEncoding

theorem field_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : Code q × ℕ => field x.1 x.2)
      (encPair (codeEncoding q) encUnary) encUnary :=
  listGetDWithInput (fst (codeEncoding q) encUnary).fst' (snd (codeEncoding q) encUnary) 0

private theorem refsFrom_polyTime :
    ComputableInPolyTime refsFrom optionRefsEncoding (encOption refsEncoding) := by
  let e := optionRefsEncoding
  let r := referenceEncoding
  have hf n := optionIsSome (listGetDWithInput (id' (encIn := e)) (const (encOut := encUnary) n)
    (none : Option Ref))
  have ht := bool_and' (hf 0) (bool_or' (bool_not.comp (hf 2)) (hf 1))
  have h := flatMapWithInput (encIn := e) (encA := r) (encB := refEncoding)
    (f := fun _ x => x.toList) id' ((optionToList_polyTime refEncoding).comp (snd e r))
  exact (ht.ite' ((optionSome refsEncoding).comp h) (const none)).of_enc_eq (fun _ => rfl)

theorem references_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × Code q => references x.1.1 x.1.2 x.2)
      (encPair fieldsEncoding (codeEncoding q)) (encOption refsEncoding) := by
  let c := codeEncoding q
  let e := encPair fieldsEncoding c
  let a := encPair e encUnary
  have hi := snd e encUnary
  have hx := fst e encUnary
  have hc := (field_polyTime q).comp (((snd fieldsEncoding c).comp hx).prod hi)
  have hd := decode_polyTime.comp (encIn := a) (((fst fieldsEncoding c).comp hx).prod hc)
  have hr := mapMWithInput (ea := encUnary) (eb := referenceEncoding) (ec := e)
    (f := fun x i => decode x.1.1 x.1.2 (field x.2 i)) (const [6,7,8]) (hd.of_enc_eq (fun _ => rfl))
  exact optionBindWithInput (ea := e) (eb := optionRefsEncoding) (ec := refsEncoding)
    (f := fun _ rs => refsFrom rs) hr (refsFrom_polyTime.comp (snd e optionRefsEncoding))

private theorem finalize_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × Code q) × List Ref => finalize x.1.1 x.1.2 x.2)
      (encPair (encPair encUnary (codeEncoding q)) refsEncoding) (encOption (decodedEncoding q)) := by
  let c := codeEncoding q
  let e := encPair (encPair encUnary c) refsEncoding
  let w := wordEncoding q
  let d := decodedEncoding q
  have hx := fst (encPair encUnary c) refsEncoding
  have hr := snd (encPair encUnary c) refsEncoding
  have hz := hx.snd'
  have hf i := (field_polyTime q).comp (encIn := e) (hz.prod (const i))
  have ht := listTakeWithInput hz.snd'.fst' (hf 4)
  have hu := listTakeWithInput hz.snd'.snd' (hf 5)
  have hb i := (hf i).decide_eq' (const 1)
  have hd := decodedEncoding_mk_polyTime q (hf 0) (hf 1) (hf 2) (hf 3) ht hu hr (hb 9) (hb 10)
  have hn := unary_add' (unary_add' (hf 2) ((length_list (ExceptionalRecords.letterEncoding q)).comp ht)) (hf 3)
  have hst := SourceDictionary.selectedStarts_polyTime.comp (hx.fst'.prod hn)
  have hvalid := ((length_list refEncoding).comp hr).decide_eq' ((length_list encUnary).comp hst)
  exact (hvalid.ite' ((optionSome d).comp hd) (const none)).of_enc_eq
    (fun _ => by simp [finalize,Function.comp_def] <;> rfl)

theorem decodeEntry_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × (ℕ × ℕ)) × Code q => decodeEntry x.1.1 x.1.2.1 x.1.2.2 x.2)
      (decodeInputEncoding q) (encOption (decodedEncoding q)) := by
  let c := codeEncoding q
  let e := decodeInputEncoding q
  let hp := fst sizesEncoding c
  let hc := snd sizesEncoding c
  have hf i := (field_polyTime q).comp (hc.prod (const i))
  have hE := hp.fst'
  have hL := hp.snd'.fst'
  have hb := hp.snd'.snd'
  have hbad := bool_or' (unary_le' hE (hf 0)) (bool_or' (unary_le' hE (hf 1))
    (bool_or' (unary_le' hL (hf 2)) (bool_or' (unary_le' hL (hf 3))
      (bool_or' (unary_lt' (const 1) (hf 9)) (unary_lt' (const 1) (hf 10))))))
  have hgood := bool_and' (unary_le' (hf 4) hb) (unary_le' (hf 5) hb)
  have hrs := (references_polyTime q).comp ((hE.prod hL).prod hc)
  have hfin := (finalize_polyTime q).comp (encIn := encPair e refsEncoding)
    (((hL.prod hc).comp (fst e refsEncoding)).prod (snd e refsEncoding))
  have hr := optionBindWithInput (ea := e) (eb := refsEncoding) (ec := decodedEncoding q)
    (f := fun x rs => finalize x.1.2.1 x.2 rs) hrs (hfin.of_enc_eq (fun _ => rfl))
  exact (hbad.ite' (const none) (hgood.ite' hr (const none))).of_enc_eq
    (fun _ => by simp [decodeEntry,Function.comp_def,Bool.or_eq_true_iff,Bool.and_eq_true_iff] <;> rfl)

abbrev decodeDescriptionEncoding (q : ℕ) := encPair sizesEncoding (descriptionEncoding q)

theorem decodeDescription_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × (ℕ × ℕ)) × Description q =>
        decodeDescription x.1.1 x.1.2.1 x.1.2.2 x.2)
      (decodeDescriptionEncoding q) (encOption (decodedListEncoding q)) := by
  let c := codeEncoding q
  let e := decodeDescriptionEncoding q
  let a := encPair e c
  have hx := fst sizesEncoding (descriptionEncoding q)
  have hy := snd sizesEncoding (descriptionEncoding q)
  have ht := listTakeWithInput hy.snd' hy.fst'
  have hd := (decodeEntry_polyTime q).comp (encIn := a)
    ((hx.comp (fst e c)).prod (snd e c))
  exact mapMWithInput (ea := c) (eb := decodedEncoding q) (ec := e)
    (f := fun x v => decodeEntry x.1.1 x.1.2.1 x.1.2.2 v) ht (hd.of_enc_eq (fun _ => rfl))

private theorem numericFields_polyTime (q : ℕ) :
    ComputableInPolyTime (numericFields (q := q)) (decodedEncoding q) PatchGraph.rowEncoding := by
  let d := decodedEncoding q
  have h := id' (encIn := d)
  have hr := decodedEncoding_rule_polyTime q h
  have hp := decodedEncoding_patch_polyTime q h
  have hl := decodedEncoding_left_polyTime q h
  have hk := decodedEncoding_right_polyTime q h
  have hw := length_list (ExceptionalRecords.letterEncoding q)
  have hu := hw.comp (decodedEncoding_removed_polyTime q h)
  have hv := hw.comp (decodedEncoding_replacement_polyTime q h)
  exact cons' hr (cons' hp (cons' hl (cons' hk (cons' hu (cons' hv (const []))))))

set_option maxHeartbeats 800000 in
private theorem codeNumbers_polyTime :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × List ℕ => codeNumbers x.1.1 x.1.2 x.2)
      (encPair fieldsEncoding PatchGraph.rowEncoding) (encOption PatchGraph.rowEncoding) := by
  let e := encPair fieldsEncoding PatchGraph.rowEncoding
  let a := encPair e encUnary
  have hrad := radix_polyTime.comp ((fst fieldsEncoding PatchGraph.rowEncoding).comp (fst e encUnary))
  have h := (unary_lt' (snd e encUnary) hrad).ite' ((optionSome encUnary).comp (snd e encUnary)) (const none)
  have hf : ComputableInPolyTime (fun x : ((ℕ × ℕ) × List ℕ) × ℕ =>
      if x.2 < ReplayGrammar.radix x.1.1.1 x.1.1.2 then some x.2 else none)
      a (encOption encUnary) :=
    h.of_enc_eq (fun _ => by simp [Function.comp_def])
  exact mapMWithInput (ea := encUnary) (eb := encUnary) (ec := e)
    (f := fun x n => if n < ReplayGrammar.radix x.1.1 x.1.2 then some n else none)
    (snd fieldsEncoding PatchGraph.rowEncoding) hf

private theorem codeRefs_polyTime :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × List Ref => codeRefs x.1.1 x.1.2 x.2)
      (encPair fieldsEncoding refsEncoding) (encOption PatchGraph.rowEncoding) := by
  let e := encPair fieldsEncoding refsEncoding
  let a := encPair e encUnary
  have h := Turing.MultiTapeTM.ComputableInPolyTime.getElem? (encA := refEncoding)
    ((snd fieldsEncoding refsEncoding).comp (fst e encUnary)) (snd e encUnary)
  have he := encode_polyTime.comp (encIn := a) (((fst fieldsEncoding refsEncoding).comp (fst e encUnary)).prod h)
  exact mapMWithInput (ea := encUnary) (eb := encUnary) (ec := e)
    (f := fun x i => encode x.1.1 x.1.2 x.2[i]?) (const [0,1,2]) (he.of_enc_eq (fun _ => rfl))

theorem encodeEntry_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : (ℕ × (ℕ × ℕ)) × Decoded q =>
        encodeEntry pad x.1.1 x.1.2.1 x.1.2.2 x.2)
      (encPair sizesEncoding (decodedEncoding q)) (encOption (codeEncoding q)) := by
  let c := codeEncoding q
  let d := decodedEncoding q
  let ns := PatchGraph.rowEncoding
  let e := encPair sizesEncoding d
  let p := encPair e ns
  let z := encPair p ns
  let w := wordEncoding q
  have hpar := fst sizesEncoding d
  have hd := snd sizesEncoding d
  have hEL := hpar.fst'.prod hpar.snd'.fst'
  have hnums := codeNumbers_polyTime.comp (hEL.prod ((numericFields_polyTime q).comp hd))
  have hrefs := codeRefs_polyTime.comp (hEL.prod (decodedEncoding_refs_polyTime q hd))
  have hz := fst p ns
  have henc := (fst e ns).comp hz
  have hx := hd.comp henc
  have hb := hpar.snd'.snd'.comp henc
  have h0 := decodedEncoding_removed_polyTime q hx
  have h1 := decodedEncoding_replacement_polyTime q hx
  have hpad0 := (SourceDictionary.paddedWindow_polyTime pad).comp (encIn := z)
    (h0.prod ((const 0).prod hb))
  have hpad1 := (SourceDictionary.paddedWindow_polyTime pad).comp (encIn := z)
    (h1.prod ((const 0).prod hb))
  have ht : ComputableInPolyTime Bool.toNat encBool encUnary := of_finite _
  have hf := ht.comp (decodedEncoding_finalBubble_polyTime q hx)
  have hg := ht.comp (decodedEncoding_finalRule_polyTime q hx)
  have hflags := cons' hf (cons' hg (const []))
  have hfields := listAppend' (listAppend' ((snd e ns).comp hz) (snd p ns)) hflags
  have hout := (optionSome c).comp (hfields.prod (hpad0.prod hpad1))
  have hr := optionBindWithInput (ea := p) (eb := ns) (ec := c)
    (f := fun x rs => some (x.2++rs++[x.1.2.finalBubble.toNat,x.1.2.finalRule.toNat],
        padWord pad x.1.1.2.2 x.1.2.removed,padWord pad x.1.1.2.2 x.1.2.replacement))
    (hrefs.comp (fst e ns)) (hout.of_enc_eq
      (fun _ => by simp [padWord,SourceDictionary.paddedWindow,Function.comp_def] <;> rfl))
  exact optionBindWithInput (ea := e) (eb := ns) (ec := c)
    (f := fun x ns => (codeRefs x.1.1 x.1.2.1 x.2.refs).bind (fun rs =>
      some (ns++rs++[x.2.finalBubble.toNat,x.2.finalRule.toNat],
        padWord pad x.1.2.2 x.2.removed,padWord pad x.1.2.2 x.2.replacement)))
    hnums hr

abbrev encodeDescriptionEncoding (q : ℕ) := encPair sizesEncoding (decodedListEncoding q)

theorem encodeDescription_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : (ℕ × (ℕ × ℕ)) × List (Decoded q) =>
        encodeDescription pad x.1.1 x.1.2.1 x.1.2.2 x.2)
      (encodeDescriptionEncoding q) (encOption (descriptionEncoding q)) := by
  let e := encodeDescriptionEncoding q
  let d := decodedEncoding q
  let c := codeEncoding q
  let cs := encList c
  let a := encPair e d
  let p := encPair e cs
  let hs := fst sizesEncoding (decodedListEncoding q)
  have h := (encodeEntry_polyTime pad).comp (encIn := a) ((hs.comp (fst e d)).prod (snd e d))
  have hm := mapMWithInput (ea := d) (eb := c) (ec := e)
    (f := fun x v => encodeEntry pad x.1.1 x.1.2.1 x.1.2.2 v)
    (snd sizesEncoding (decodedListEncoding q)) (h.of_enc_eq (fun _ => rfl))
  have hE := hs.fst'.comp (fst e cs)
  have hb := hs.snd'.snd'.comp (fst e cs)
  have hc := snd e cs
  have hlen := (length_list c).comp hc
  have hword := replicate hb (const (encOut := ExceptionalRecords.letterEncoding q) pad)
  have hpad := (const (encOut := PatchGraph.rowEncoding) (List.replicate 11 0)).prod
    (hword.prod hword)
  let v := encPair p encUnary
  have hget := Turing.MultiTapeTM.ComputableInPolyTime.getElem? (encA := c)
    (hc.comp (fst p encUnary)) (snd p encUnary)
  have hg := optionElimWithInput (encA := v) (encB := c) (encC := c)
    (body := fun _ x => x) hget (hpad.comp (fst p encUnary)) (snd v c)
  have hlist := mapWithInput (encIn := p) (encA := encUnary) (encB := c)
    (f := fun x i => x.2.getD i (List.replicate 11 0,List.replicate x.1.1.2.2 pad,List.replicate x.1.1.2.2 pad))
    (unary_range' hE) (hg.of_enc_eq (fun x => by
      simp only [Function.comp_def,List.getD_eq_getElem?_getD]
      cases x.1.2[x.2]? <;> rfl))
  have hout := (unary_le' hlen hE).ite' ((optionSome (descriptionEncoding q)).comp (hlen.prod hlist))
    (const none)
  exact optionBindWithInput (ea := e) (eb := cs) (ec := descriptionEncoding q)
    (f := fun x codes => if codes.length ≤ x.1.1 then some (codes.length,
      (List.range x.1.1).map (fun i =>
        codes.getD i (List.replicate 11 0,List.replicate x.1.2.2 pad,List.replicate x.1.2.2 pad))) else none)
    hm (hout.of_enc_eq (fun _ => by simp [Function.comp_def]))

#print axioms encodeEntry_eq
#print axioms encodeDescription_eq
#print axioms encodeEntry_polyTime
#print axioms encodeDescription_polyTime
#print axioms decodeEntry_eq
#print axioms decodeDescription_eq
#print axioms decodeEntry_polyTime
#print axioms decodeDescription_polyTime

end DeletionCode.Explicit.Machine.SourceGrammar
