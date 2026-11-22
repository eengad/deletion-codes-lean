import DeletionCode.Explicit.Machine.SourceDescriptionIndex
import DeletionCode.Explicit.Machine.SourceReplay
import DeletionCode.Explicit.CoreReplay

/-! Materialize a slot by decoding its keys and replaying its symbolic entries. -/
namespace DeletionCode.Explicit.Machine.SourceCoreReplay

open SourceGrammar SourceReplay SourceDescriptionIndex SourceRadix
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open private boundsChecked belongs from DeletionCode.Explicit.CoreReplay

variable {q ℓ E L b t r r₀ : ℕ}

abbrev Material (q : ℕ) := List (Decoded q × SourceDictionary.Stored q) × List ℕ

def keyList (E : ℕ) (p : ℕ → Bool) : List ℕ := (List.range E).filter p

private theorem keyList_eq (E : ℕ) (p : ℕ → Bool) :
    keyList E p = (((Finset.univ : Finset (Fin E)).filter (fun i : Fin E => p i.val)).sort (· ≤ ·)).map Fin.val := by
  rw [keyList,show List.range E = (List.finRange E).map Fin.val by simp,List.filter_map]
  congr 1
  exact (((Finset.univ : Finset (Fin E)).filter (fun i : Fin E => p i.val)).sortedLT_sort.eq_of_mem_iff
    (((List.sortedLT_finRange E).pairwise.filter _).sortedLT) (by simp [Function.comp_def])).symm

def patchKeys (E : ℕ) (ds : List (Decoded q)) : List ℕ :=
  keyList E (fun p => ds.any (fun d => d.patch == p))

def finalKeys (E : ℕ) (ds : List (Decoded q)) : List ℕ :=
  keyList E (fun p => ds.any (fun d => d.finalRule && d.rule == p))

theorem patchKeys_eq (ds : List (ReplayGrammar.DecodedEntry q)) :
    patchKeys E (ds.map decodedData) = ((CoreWeight.patchKeys E ds).sort (· ≤ ·)).map Fin.val := by
  rw [patchKeys,keyList_eq]
  simp only [CoreWeight.patchKeys,List.any_map,Function.comp_def,decodedData]

theorem finalKeys_eq (ds : List (ReplayGrammar.DecodedEntry q)) :
    finalKeys E (ds.map decodedData) = ((CoreWeight.finalRuleKeys E ds).sort (· ≤ ·)).map Fin.val := by
  rw [finalKeys,keyList_eq]
  simp only [CoreWeight.finalRuleKeys,List.any_map,Function.comp_def,decodedData]

def checked (s : ℕ) (ds : List (Decoded q)) (keys : List ℕ) : Bool :=
  (keys.all fun p => decide ((ds.filter (fun d => d.finalBubble && d.rule == p)).length = s)) &&
    ds.all (fun d => !d.finalBubble || keys.any (fun p => d.rule == p))

theorem checked_eq (s : ℕ) (ds : List (ReplayGrammar.DecodedEntry q)) (keys : Finset (Fin E)) :
    checked s (ds.map decodedData) ((keys.sort (· ≤ ·)).map Fin.val) = boundsChecked s ds keys := by
  simp only [checked,boundsChecked,List.all_map,List.any_map,List.filter_map,Function.comp_def,
    decodedData,List.length_map]
  rfl

def keyAnchor (keys digits : List ℕ) (p : ℕ) : Option ℕ :=
  (keys.idxOf? p).bind (fun j => digits[j]?)

private theorem keyAnchor_apply (keys digits : List ℕ) (p : ℕ) :
    keyAnchor keys digits p = if p ∈ keys then digits[keys.idxOf p]? else none := by
  unfold keyAnchor List.idxOf?
  rw [List.findIdx?_eq_guard_findIdx_lt]
  by_cases hp : p ∈ keys
  · have hlt := List.idxOf_lt_length_of_mem hp
    change keys.findIdx (· == p) < keys.length at hlt
    simp [hlt,hp,List.idxOf]
  · have hlt := mt List.idxOf_lt_length_iff.mp hp
    change ¬ keys.findIdx (· == p) < keys.length at hlt
    simp [hlt,hp]

def anchorTable (E : ℕ) (keys digits : List ℕ) : Anchors :=
  (List.range E).map (keyAnchor keys digits)

private theorem idxOf_val (xs : List (Fin E)) (i : Fin E) :
    (xs.map Fin.val).idxOf i.val = xs.idxOf i := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    by_cases h : a = i
    · subst a
      simp
    · have hh : a.val ≠ i.val := fun e => h (Fin.ext e)
      simp [List.idxOf_cons,h,hh,beq_iff_eq,ih]

private theorem table_eq (P : Finset (Fin E)) (u : Fin (ℓ^P.card)) (p : ℕ) :
    anchorAt (anchorTable E (P.sort.map Fin.val) (smallDigits ℓ P.card u.val)) p =
      (CoreWeight.anchorLookup P
        (fun j => finFunctionFinEquiv.symm u ((P.orderIsoOfFin rfl).symm j)) p).map Fin.val := by
  by_cases hp : p < E
  · let i : Fin E := ⟨p,hp⟩
    unfold anchorAt anchorTable
    rw [SourceLists.range_map_eq,BooleanFibres.ofFn_getD _ i none]
    unfold CoreWeight.anchorLookup
    rw [dite_eq_left hp]
    have hm : p ∈ P.sort.map Fin.val ↔ i ∈ P := by
      simp only [List.mem_map,Finset.mem_sort]
      exact ⟨fun ⟨j,hj,he⟩ => (show j = i from Fin.ext he) ▸ hj,fun h => ⟨i,h,rfl⟩⟩
    by_cases hi : i ∈ P
    · have hmem : p ∈ P.sort.map Fin.val := hm.mpr hi
      have hk : (P.sort.map Fin.val).idxOf p = ((P.orderIsoOfFin rfl).symm ⟨i,hi⟩).val := by
        rw [Finset.orderIsoOfFin_symm_apply]
        exact idxOf_val _ i
      simp only [keyAnchor_apply,hmem,↓reduceIte,show (⟨p,hp⟩ : Fin E) = i from rfl,hi,↓reduceDIte,
        Option.map_some,smallDigits_eq u]
      rw [hk,List.getElem?_ofFn]
      simp
      exact ⟨i,hi,rfl⟩
    · have hm' : p ∉ P.sort.map Fin.val := fun h => hi (hm.mp h)
      simp [keyAnchor_apply,i,hm',hi]
  · have hr : E ≤ p := Nat.le_of_not_gt hp
    have hlen : (anchorTable E (P.sort.map Fin.val) (smallDigits ℓ P.card u.val)).length = E := by
      simp [anchorTable]
    simp [anchorAt,CoreWeight.anchorLookup,hp,List.getD_eq_getElem?_getD,List.getElem?_eq_none
      (hlen ▸ hr)]

def decodeAnchors (ℓ E : ℕ) (keys : List ℕ) (packed : ℕ) : Option Anchors :=
  if packed < ℓ^keys.length then some (anchorTable E keys (smallDigits ℓ keys.length packed)) else none

theorem decodeAnchors_eq (P : Finset (Fin E)) {m : ℕ} (k : Fin (ℓ^m)) (p : ℕ) :
    (decodeAnchors ℓ E (P.sort.map Fin.val) k.val).bind (fun roots => anchorAt roots p) =
      (RulePatch.unpackAnchors P k).bind (fun v => (CoreWeight.anchorLookup P v p).map Fin.val) := by
  unfold decodeAnchors RulePatch.unpackAnchors
  simp only [List.length_map,Finset.length_sort]
  split
  · rename_i hp
    simp only [hp,↓reduceDIte,Option.bind_some]
    exact table_eq P ⟨k.val,hp⟩ p
  · simp_all

def materialData (m : CoreWeight.Materialized ℓ q E r) : Material q :=
  (m.entries.map (fun p => (decodedData p.1,SourceDictionary.store p.2)),m.rules.sort.map Fin.val)

def fromEntries (pad : Fin q) (ℓ E L t count anchor : ℕ) (ds : List (Decoded q)) : Option (Material q) := do
  let rules := finalKeys E ds
  if rules.length = count && checked (2*t) ds rules then
    let patches := patchKeys E ds
    if patches.length ≤ t*count then
      let roots ← decodeAnchors ℓ E patches anchor
      (SourceReplay.replay pad ((ℓ,L),roots) ds).map (fun es => (ds.zip es,rules))
    else none
  else none

def materialize (pad : Fin q) (ℓ E L b t count description anchor : ℕ) : Option (Material q) := do
  let d ← unpack pad E L b description
  let ds ← SourceGrammar.decodeDescription E L b d
  fromEntries pad ℓ E L t count anchor ds

theorem materialize_eq (pad : Fin q) (hq : 2 ≤ q) (k : CoreWeight.ReplaySlot ℓ q E L b t r₀) :
    materialize pad ℓ E L b t (k.1.val+1) k.2.1.val k.2.2.val =
      (CoreWeight.materialize k).map materialData := by
  unfold materialize CoreWeight.materialize
  rw [unpack_eq pad hq k.2.1]
  cases hc : ReplayGrammar.unpackDescription k.2.1 with
  | none => rfl
  | some c =>
    simp only [Option.map_some,bind,Option.bind,decodeDescription_eq]
    cases hs : ReplayGrammar.decodeDescription c with
    | none => rfl
    | some ds =>
      let P := CoreWeight.patchKeys E ds
      let U := CoreWeight.finalRuleKeys E ds
      simp only [Option.map_some,fromEntries,finalKeys_eq,patchKeys_eq,checked_eq,
        List.length_map,Finset.length_sort,Bool.and_eq_true_iff,decide_eq_true_eq]
      by_cases hr : U.card = k.1.val+1
      · by_cases he : boundsChecked (2*t) ds U
        · by_cases hp : P.card ≤ t*(k.1.val+1)
          · simp only [show CoreWeight.finalRuleKeys E ds = U from rfl,show CoreWeight.patchKeys E ds = P from rfl,
              hr,he,hp,and_self,↓reduceIte,↓reduceDIte]
            by_cases hn : k.2.2.val < ℓ^P.card
            · let u : Fin (ℓ^P.card) := ⟨k.2.2.val,hn⟩
              have ha : k.2.2.val < ℓ^(CoreWeight.patchKeys E ds).card := hn
              simp only [decodeAnchors,RulePatch.unpackAnchors,List.length_map,Finset.length_sort,hn,ha,
                ↓reduceIte,↓reduceDIte,Option.bind_some,bind,Option.bind]
              have hh := replay_eq pad L ds (anchorTable E (P.sort.map Fin.val)
                (smallDigits ℓ P.card u.val))
                (CoreWeight.anchorLookup P (fun j => finFunctionFinEquiv.symm u ((P.orderIsoOfFin rfl).symm j)))
                (fun d _ => table_eq P u d.entry.patch)
              rw [hh]
              cases hrp : ReplayEntry.replay L _ (ds.map ReplayGrammar.DecodedEntry.entry) with
              | none => rfl
              | some es =>
                simp only [Option.map_some,SourceDictionary.historyData,materialData]
                rw [List.zip_map_left,List.zip_map_right,List.map_map]
                rfl
            · have ha : ¬ k.2.2.val < ℓ^(CoreWeight.patchKeys E ds).card := hn
              simp [decodeAnchors,RulePatch.unpackAnchors,hn,ha]
          · simp [U,P,hr,he,hp]
        · simp [U,hr,he]
      · simp [U,hr]

abbrev keysEncoding := PatchGraph.rowEncoding
abbrev keyArgsEncoding (q : ℕ) := encPair encUnary (decodedListEncoding q)

private theorem keys_polyTime (q : ℕ) (finalRule : Bool) :
    ComputableInPolyTime (fun x : ℕ × List (Decoded q) =>
      if finalRule then finalKeys x.1 x.2 else patchKeys x.1 x.2) (keyArgsEncoding q) keysEncoding := by
  let e := keyArgsEncoding q
  let d := decodedEncoding q
  let a := encPair e encUnary
  let p := encPair a d
  have hi := (snd e encUnary).comp (fst a d)
  have he := (snd encUnary (decodedListEncoding q)).comp (fst e encUnary)
  have hd := snd a d
  have hr := (decodedEncoding_rule_polyTime q hd).decide_eq' hi
  have hp := (decodedEncoding_patch_polyTime q hd).decide_eq' hi
  have htest := (const (encOut := encBool) finalRule).ite' (bool_and' (decodedEncoding_finalRule_polyTime q hd) hr) hp
  have h := anyWithInput (encIn := a) (encA := d)
    (test := fun x d => if finalRule then d.finalRule && d.rule == x.2 else d.patch == x.2)
    he (htest.of_enc_eq (fun x => by
      apply congrArg encBool
      apply Bool.eq_iff_iff.mpr
      cases finalRule <;> simp [Function.comp_def,beq_iff_eq]))
  have hk := filterWithInput (encIn := e) (encA := encUnary)
    (test := fun x i => x.2.any (fun d => if finalRule then d.finalRule && d.rule == i else d.patch == i))
    (unary_range' (fst encUnary (decodedListEncoding q))) h
  exact hk.of_enc_eq (fun x => by cases finalRule <;> rfl)

theorem patchKeys_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : ℕ × List (Decoded q) => patchKeys x.1 x.2)
      (keyArgsEncoding q) keysEncoding := keys_polyTime q false

theorem finalKeys_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : ℕ × List (Decoded q) => finalKeys x.1 x.2)
      (keyArgsEncoding q) keysEncoding := keys_polyTime q true

abbrev checkedEncoding (q : ℕ) := encPair (keyArgsEncoding q) keysEncoding

theorem checked_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × List (Decoded q)) × List ℕ => checked x.1.1 x.1.2 x.2)
      (checkedEncoding q) encBool := by
  let e := checkedEncoding q
  let k := keyArgsEncoding q
  let d := decodedEncoding q
  let a := encPair e encUnary
  let b := encPair a d
  let c := encPair e d
  have hx := fst k keysEncoding
  have hi := snd k keysEncoding
  have hd := snd a d
  have hp := (snd e encUnary).comp (fst a d)
  have hm := bool_and' (decodedEncoding_finalBubble_polyTime q hd) ((decodedEncoding_rule_polyTime q hd).decide_eq' hp)
  have hf := filterWithInput (encIn := a) (encA := d)
    (test := fun x d => d.finalBubble && d.rule == x.2)
    (hx.snd'.comp (fst e encUnary)) (hm.of_enc_eq (fun x => by
      apply congrArg encBool
      apply Bool.eq_iff_iff.mpr
      simp [Bool.and_eq_true_iff,beq_iff_eq]))
  have hn := (length_list d).comp hf
  have hsize := hn.decide_eq' (hx.fst'.comp (fst e encUnary))
  have ha := allWithInput (encIn := e) (encA := encUnary)
    (test := fun x p => decide ((x.1.2.filter (fun d => d.finalBubble && d.rule == p)).length = x.1.1)) hi hsize
  have ht := snd e d
  have hs := contains (hi.comp (fst e d)) (decodedEncoding_rule_polyTime q ht)
  have htest := bool_or' (bool_not.comp (decodedEncoding_finalBubble_polyTime q ht)) hs
  have hh := allWithInput (encIn := e) (encA := d)
    (test := fun x d => !d.finalBubble || x.2.any (fun p => d.rule == p))
    hx.snd' (htest.of_enc_eq (fun x => by
      apply congrArg encBool
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_def,Bool.or_eq_true_iff,List.any_eq_true,beq_iff_eq,List.contains_iff_mem]
      exact or_congr_right
        ⟨fun ⟨p,hp,he⟩ => he.symm ▸ hp,fun hp => ⟨_,hp,rfl⟩⟩))
  exact bool_and' ha hh

abbrev anchorDataEncoding := encPair keysEncoding keysEncoding
abbrev anchorTableEncoding := encPair encUnary anchorDataEncoding

private theorem keyAnchor_polyTime :
    ComputableInPolyTime (fun x : (List ℕ × List ℕ) × ℕ => keyAnchor x.1.1 x.1.2 x.2)
      (encPair anchorDataEncoding encUnary) (encOption encUnary) := by
  let e := encPair anchorDataEncoding encUnary
  let p := encPair e encUnary
  have h := (SourceLists.idxOf?_polyTime 0 encUnary).comp
    ((fst anchorDataEncoding encUnary).fst'.prod (snd anchorDataEncoding encUnary))
  have hd := ((fst anchorDataEncoding encUnary).snd'.comp (fst e encUnary))
  have hn := Turing.MultiTapeTM.ComputableInPolyTime.getElem? (encA := encUnary) hd (snd e encUnary)
  exact SourceLists.optionBindWithInput (ea := e) (eb := encUnary)
    (f := fun x j => x.1.2[j]?) h hn

theorem anchorTable_polyTime :
    ComputableInPolyTime (fun x : ℕ × (List ℕ × List ℕ) => anchorTable x.1 x.2.1 x.2.2)
      anchorTableEncoding anchorsEncoding := by
  let e := anchorTableEncoding
  have h := keyAnchor_polyTime.comp (((snd encUnary anchorDataEncoding).comp (fst e encUnary)).prod (snd e encUnary))
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := encOption encUnary)
    (f := fun x i => keyAnchor x.2.1 x.2.2 i)
    (unary_range' (fst encUnary anchorDataEncoding)) h

abbrev decodeAnchorsEncoding := encPair (encPair encUnary encUnary) (encPair keysEncoding encNat)

theorem decodeAnchors_polyTime :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × (List ℕ × ℕ) => decodeAnchors x.1.1 x.1.2 x.2.1 x.2.2)
      decodeAnchorsEncoding (encOption anchorsEncoding) := by
  let e := decodeAnchorsEncoding
  let a := encPair encUnary encUnary
  let p := encPair keysEncoding encNat
  have hx := fst a p
  have hy := snd a p
  have hlen := (length_list encUnary).comp hy.fst'
  have hp := binary_pow' (unary_to_binary.comp hx.fst') hlen
  have hd := smallDigits_polyTime.comp ((hx.fst'.prod hy.snd').prod hlen)
  have hf := anchorTable_polyTime.comp (encIn := e) (hx.snd'.prod (hy.fst'.prod hd))
  exact ((binary_lt' hy.snd' hp).ite' ((optionSome anchorsEncoding).comp hf) (const none)).of_enc_eq
    (fun _ => by simp [decodeAnchors,Function.comp_def] <;> rfl)

structure SlotInput where
  length : ℕ
  entries : ℕ
  gram : ℕ
  burst : ℕ
  pairs : ℕ
  count : ℕ
  description : ℕ
  anchor : ℕ

enc_structure slotEncoding : SlotInput where
  length : encUnary, entries : encUnary, gram : encUnary, burst : encUnary, pairs : encUnary,
  count : encUnary, description : encNat, anchor : encNat

abbrev materialPairEncoding (q : ℕ) := encPair (decodedEncoding q) (SourceDictionary.storedEncoding q)
abbrev materialEncoding (q : ℕ) := encPair (encList (materialPairEncoding q)) keysEncoding
abbrev fromEntriesEncoding (q : ℕ) := encPair slotEncoding (decodedListEncoding q)

def fromSlotEntries (pad : Fin q) (x : SlotInput × List (Decoded q)) : Option (Material q) :=
  fromEntries pad x.1.length x.1.entries x.1.gram x.1.pairs x.1.count x.1.anchor x.2

private theorem fromSlotEntries_polyTime (pad : Fin q) :
    ComputableInPolyTime (fromSlotEntries pad) (fromEntriesEncoding q) (encOption (materialEncoding q)) := by
  let ds := decodedListEncoding q
  let e := fromEntriesEncoding q
  let r := anchorsEncoding
  let st := SourceDictionary.storedEncoding q
  let hs := SourceDictionary.historyEncoding q
  let d := decodedEncoding q
  let a := encPair e r
  let v := encPair a hs
  let m := materialEncoding q
  have hx := fst slotEncoding ds
  have hd := snd slotEncoding ds
  have hlen := slotEncoding_length_polyTime hx
  have hE := slotEncoding_entries_polyTime hx
  have hL := slotEncoding_gram_polyTime hx
  have hp := slotEncoding_pairs_polyTime hx
  have hc := slotEncoding_count_polyTime hx
  have hi := slotEncoding_anchor_polyTime hx
  have hkeys := (finalKeys_polyTime q).comp (hE.prod hd)
  have hpatches := (patchKeys_polyTime q).comp (hE.prod hd)
  have hkeyCount := (length_list encUnary).comp hkeys
  have hcheck := (checked_polyTime q).comp (((unary_mul' (const 2) hp).prod hd).prod hkeys)
  have hall := bool_and' (hkeyCount.decide_eq' hc) hcheck
  have hbudget := unary_le' ((length_list encUnary).comp hpatches) (unary_mul' hp hc)
  have hroots := decodeAnchors_polyTime.comp ((hlen.prod hE).prod (hpatches.prod hi))
  have hg := fst e r
  have ha := snd e r
  have hpar := ((hlen.prod hL).comp hg).prod ha
  have hrep := (SourceReplay.replay_polyTime pad).comp (encIn := a) (hpar.prod (hd.comp hg))
  have hsrc := hg.comp (fst a hs)
  have hds := hd.comp hsrc
  have hzip := (ComputableInPolyTime.zip d st).comp (hds.prod (snd a hs))
  have hout := optionMapWithInput (encA := a) (encB := hs) (encC := m)
    (f := fun x es => (x.1.2.zip es,finalKeys x.1.1.entries x.1.2)) hrep
    (hzip.prod (hkeys.comp hsrc))
  have hwith := SourceLists.optionBindWithInput (ea := e) (eb := r) (ec := m)
    (f := fun x roots => (SourceReplay.replay pad ((x.1.length,x.1.gram),roots) x.2).map
      (fun es => (x.2.zip es,finalKeys x.1.entries x.2))) hroots hout
  exact (hall.ite' (hbudget.ite' hwith (const none)) (const none)).of_enc_eq
    (fun _ => by simp [fromSlotEntries,fromEntries,Function.comp_def,bind,Option.bind] <;> rfl)

def materializeSlot (pad : Fin q) (x : SlotInput) : Option (Material q) :=
  materialize pad x.length x.entries x.gram x.burst x.pairs x.count x.description x.anchor

theorem materialize_polyTime (pad : Fin q) :
    ComputableInPolyTime (materializeSlot pad) slotEncoding (encOption (materialEncoding q)) := by
  let h := slotEncoding
  let d := descriptionEncoding q
  let ds := decodedListEncoding q
  let m := materialEncoding q
  let a := encPair h d
  have hm := id' (encIn := h)
  have hE := slotEncoding_entries_polyTime hm
  have hL := slotEncoding_gram_polyTime hm
  have hb := slotEncoding_burst_polyTime hm
  have hi := slotEncoding_description_polyTime hm
  have hsize := hE.prod (hL.prod hb)
  have hc := (unpack_polyTime pad).comp (hsize.prod hi)
  have hd := (decodeDescription_polyTime q).comp (encIn := a)
    ((hsize.comp (fst h d)).prod (snd h d))
  have hr := (fromSlotEntries_polyTime pad).comp (encIn := encPair a ds)
    (((fst h d).comp (fst a ds)).prod (snd a ds))
  have hbody := SourceLists.optionBindWithInput (ea := a) (eb := ds) (ec := m)
    (f := fun x ds => fromSlotEntries pad (x.1,ds)) hd hr
  exact SourceLists.optionBindWithInput (ea := h) (eb := d) (ec := m)
    (f := fun x d => (SourceGrammar.decodeDescription x.entries x.gram x.burst d).bind
      (fun ds => fromSlotEntries pad (x,ds))) hc hbody

#print axioms materialize_polyTime
#print axioms patchKeys_eq
#print axioms finalKeys_eq
#print axioms decodeAnchors_eq
#print axioms materialize_eq
#print axioms checked_polyTime
#print axioms decodeAnchors_polyTime

end DeletionCode.Explicit.Machine.SourceCoreReplay
