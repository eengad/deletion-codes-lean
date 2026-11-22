import DeletionCode.Explicit.Machine.SourceReplayFamily
import DeletionCode.Explicit.CoreReplayCheck

/-! Recover and check the final core rules on one assignment. -/
namespace DeletionCode.Explicit.Machine.SourceCoreCheck

open SourceGrammar SourceCoreReplay SourceReplayFamily SourceFamilyMembers SourceLists
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open FieldHash Ternary CataloguePrefix
open OrderedCatalogue (BubbleData bubbleData)
open private finalRuleValid spelled from DeletionCode.Explicit.CoreReplayCheck
open private belongs from DeletionCode.Explicit.CoreReplay

variable {q ℓ E r : ℕ}

abbrev Pair (q : ℕ) := Decoded q × SourceDictionary.Stored q
abbrev Entries (q : ℕ) := List (Pair q)
abbrev entriesEncoding (q : ℕ) := encList (materialPairEncoding q)

def support (ℓ : ℕ) (m : Material q) : List ℕ :=
  (List.range ℓ).filter fun i => m.1.any (fun p => p.1.finalBubble &&
    ((positions p.2.2.1).contains i || (positions p.2.2.2).contains i))

theorem support_eq (m : CoreWeight.Materialized ℓ q E r) :
    support ℓ (materialData m) =
      ((List.finRange ℓ).filter (· ∈ m.support)).map Fin.val := by
  unfold support
  rw [show List.range ℓ = (List.finRange ℓ).map Fin.val by simp,List.filter_map]
  congr 1
  apply List.filter_congr
  intro i _
  apply Bool.eq_iff_iff.mpr
  simp only [materialData,List.any_map,Function.comp_def,List.any_eq_true,Bool.and_eq_true_iff,
    Bool.or_eq_true_iff,List.contains_iff_mem,decide_eq_true_eq,decodedData,SourceDictionary.store,
    positions,← List.mem_toFinset,SourcePrepare.positions_eq]
  exact CoreWeight.Materialized.mem_support m |>.symm

private theorem freshCount_eq (w : LetterSequence.Lift ℓ n (Fin q)) :
    ((pattern (SourceLetters.liftData w)).filter Option.isSome).length = w.freshOffsets.card := by
  simp only [pattern,SourceLetters.liftData,List.map_ofFn,Function.comp_def]
  have hf (i : Fin n) :
      (((SourceLetters.letterData (w.letters i)).2).map Prod.snd).isSome =
      decide (i ∈ w.freshOffsets) := by
    simp only [LetterSequence.Lift.freshOffsets,Finset.mem_filter,Finset.mem_univ,true_and]
    cases w.letters i <;> rfl
  rw [show (List.ofFn (fun i : Fin n => (SourceLetters.letterData (w.letters i)).2.map Prod.snd)) =
      (List.finRange n).map (fun i => (SourceLetters.letterData (w.letters i)).2.map Prod.snd) by
    rw [show List.finRange n = List.ofFn (fun i : Fin n => i) from rfl,List.map_ofFn]
    rfl]
  rw [List.filter_map,List.length_map]
  have hd : ((List.finRange n).filter (fun i => decide (i ∈ w.freshOffsets))).toFinset =
      w.freshOffsets := by ext; simp
  have hnodup := (List.nodup_finRange n).filter (fun i => decide (i ∈ w.freshOffsets))
  have hc := (List.toFinset_card_of_nodup hnodup).symm
  rw [hd] at hc
  simpa [Function.comp_def,hf] using hc

def recover (pad : Fin q) (K b L Λ : ℕ) (word : QWord q) (p : Pair q) : Option (BubbleData q) :=
  let neg := SourceLetters.spell pad word p.2.2.1
  let pos := SourceLetters.spell pad word p.2.2.2
  if ((pattern p.2.2.1).filter Option.isSome).length ≤ Λ then
    (localBubble K b L p.1.left p.1.removed p.1.replacement neg).bind
      fun w => if OrderedCatalogue.side w true = pos then some w else none
  else none

theorem recover_eq (pad : Fin q) (K b L Λ : ℕ) (word : Fin ℓ → Fin q)
    (p : ReplayGrammar.DecodedEntry q × ReplayEntry.Completed ℓ (Fin q)) :
    recover pad K b L Λ (List.ofFn word) (decodedData p.1,SourceDictionary.store p.2) =
      (CoreWeight.recoveredBubble K b L Λ word p).map bubbleData := by
  unfold recover CoreWeight.recoveredBubble
  simp only [SourceDictionary.store,decodedData,freshCount_eq,SourceLetters.spell_eq,spelled]
  split
  · simp only [local_eq]
    cases h : BubbleFamilies.localWord K b L p.1.entry.left p.1.entry.removed p.1.entry.replacement
        (List.ofFn (p.2.negative.2.spelling word)) with
    | none => rfl
    | some w =>
      simp [h,OrderedCatalogue.side,bubbleData,Borrowed.BubbleWord.positiveWord,bind,Option.bind]
  · rfl

def owned (key : ℕ) (p : Pair q) : Bool := p.1.finalBubble && decide (p.1.rule = key)

def ruleValid (pad : Fin q) (K b L Λ s : ℕ) (word : QWord q) (m : Material q) (id : ℕ) : Bool :=
  ((m.1.filter (owned id)).mapM (recover pad K b L Λ word)).elim false fun ws =>
    decide (ws.length = s) && OrderedCatalogue.valid L ws

theorem ruleValid_eq (pad : Fin q) (K b L Λ s : ℕ) (word : Fin ℓ → Fin q)
    (m : CoreWeight.Materialized ℓ q E r) (i : Fin E) :
    ruleValid pad K b L Λ s (List.ofFn word) (materialData m) i.val =
      finalRuleValid K b L Λ s pad m word i := by
  unfold ruleValid finalRuleValid materialData
  simp only [List.filter_map,List.mapM_map,Function.comp_def,recover_eq]
  have ho : (fun p : ReplayGrammar.DecodedEntry q × ReplayEntry.Completed ℓ (Fin q) =>
      owned i.val (decodedData p.1,SourceDictionary.store p.2)) =
      (fun p => p.1.finalBubble && p.1.entry.rule == i.val) := by
    funext p
    unfold owned decodedData
    congr 1
  rw [ho,SourceNegative.mapM_map_result]
  cases h : (m.entries.filter (fun p => p.1.finalBubble && p.1.entry.rule == i.val)).mapM
      (CoreWeight.recoveredBubble K b L Λ word) with
  | none => rfl
  | some ws =>
    by_cases hl : ws.length = s
    · simp only [Option.map_some,Option.elim_some,List.length_map,hl,decide_true,Bool.true_and,↓reduceDIte]
      let w := fun j : Fin s => ws.get (Fin.cast hl.symm j)
      have hw : List.ofFn (fun j => bubbleData (w j)) = ws.map bubbleData := by
        subst s
        change List.ofFn (bubbleData ∘ w) = _
        rw [← List.map_ofFn]
        exact congrArg (List.map bubbleData) (List.ofFn_get ws)
      rw [← hw,OrderedCatalogue.valid_eq pad w]
    · simp [hl]

def check (pad : Fin q) (K b L Λ s : ℕ) (word : QWord q) (m : Material q) : Bool :=
  m.2.all (ruleValid pad K b L Λ s word m)

theorem check_eq (pad : Fin q) (K b L Λ s : ℕ) (word : Fin ℓ → Fin q)
    (m : CoreWeight.Materialized ℓ q E r) :
    check pad K b L Λ s (List.ofFn word) (materialData m) =
      CoreWeight.coreCheck K b L Λ s pad m word := by
  unfold check CoreWeight.coreCheck
  change (m.rules.sort.map Fin.val).all (ruleValid pad K b L Λ s (List.ofFn word) (materialData m)) = _
  rw [List.all_map]
  simp only [Function.comp_def,ruleValid_eq]

def bubblePair (pad : Fin q) (word : QWord q) (p : Pair q) : BubbleData q :=
  (([],[]),(SourceLetters.spell pad word p.2.2.1,SourceLetters.spell pad word p.2.2.2))

def rows (pad : Fin q) (L : ℕ) (word : QWord q) (m : Material q) : Rows :=
  m.2.map fun i => SourceRuleRows.row pad L ((m.1.filter (owned i)).map (bubblePair pad word))

private theorem bubble_delta_eq (pad : Fin q) (L : ℕ) (x : Fin ℓ → Fin q)
    (p : ReplayGrammar.DecodedEntry q × ReplayEntry.Completed ℓ (Fin q)) (g : Fin L → Fin q) :
    SourceRuleRows.delta (List.ofFn g) (bubblePair pad (List.ofFn x) (decodedData p.1,SourceDictionary.store p.2)) =
      LiftDictionary.bubbleVector pad x p.2 g := by
  have hpad {m : ℕ} (v : Fin m → Fin q) :
      (fun i => (List.ofFn v).getD i pad) = LiftDictionary.paddedLetters pad v := by
    funext i
    by_cases hi : i < m
    · exact (BooleanFibres.ofFn_getD v ⟨i,hi⟩ pad).trans (by simp [LiftDictionary.paddedLetters,hi])
    · simp [List.getD_eq_getElem?_getD,LiftDictionary.paddedLetters,hi]
  unfold SourceRuleRows.delta bubblePair LiftDictionary.bubbleVector
  simp only [OrderedCatalogue.side,SourceDictionary.store,SourceLetters.spell_eq]
  simp only [Bool.false_eq_true,↓reduceIte,List.nil_append,List.append_nil]
  rw [ExceptionalWeight.gramCount_field pad _ L g,ExceptionalWeight.gramCount_field pad _ L g]
  simp only [listFieldSpectrum,List.length_ofFn,hpad]
  rfl

theorem rows_eq (pad : Fin q) (hq : 2 ≤ q) (L : ℕ) (x : Fin ℓ → Fin q)
    (m : CoreWeight.Materialized ℓ q E r) :
    rows pad L (List.ofFn x) (materialData m) = matrixRows (m.matrix L pad x) := by
  have he : m.rules.sort = List.ofFn (m.rules.orderEmbOfFin m.rule_count) := by
    rw [← Finset.listMap_orderEmbOfFin_finRange m.rules m.rule_count]
    rw [show List.finRange r = List.ofFn (fun i : Fin r => i) from rfl,List.map_ofFn]
    rfl
  unfold rows materialData matrixRows
  rw [he,List.map_map,List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_def,SourceRuleRows.row,SourceRuleRows.rowWith,GramOrder.mainWords_eq _ hq,
    List.map_ofFn,CoreWeight.Materialized.matrix]
  congr 1
  funext g
  simp only [Function.comp_def,List.filter_map,List.map_map]
  congr 1
  have hf : (fun p : ReplayGrammar.DecodedEntry q × ReplayEntry.Completed ℓ (Fin q) =>
      owned (m.rules.orderEmbOfFin m.rule_count i).val (decodedData p.1,SourceDictionary.store p.2)) =
      (fun p => belongs (m.rules.orderEmbOfFin m.rule_count i).val p.1) := by
    funext p
    change (p.1.finalBubble && decide (p.1.entry.rule = _)) = (p.1.finalBubble && (p.1.entry.rule == _))
    congr 1
  rw [hf]
  apply List.map_congr_left
  intro p _
  exact bubble_delta_eq pad L x p _

abbrev supportEncoding (q : ℕ) := encPair encUnary (materialEncoding q)

theorem support_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : ℕ × Material q => support x.1 x.2)
      (supportEncoding q) PatchGraph.rowEncoding := by
  let e := supportEncoding q
  let f := encPair e encUnary
  let a := materialPairEncoding q
  let p := encPair f a
  have hi := (snd e encUnary).comp (fst f a)
  have hs := ((snd encUnary (materialEncoding q)).comp (fst e encUnary)).fst'
  have hd := (snd f a).fst'
  have he := (snd f a).snd'.snd'
  have hn := (SourcePrepare.positions_polyTime q).comp he.fst'
  have hp := (SourcePrepare.positions_polyTime q).comp he.snd'
  have h := bool_and' (decodedEncoding_finalBubble_polyTime q hd)
    (bool_or' (contains hn hi) (contains hp hi))
  have hf := anyWithInput (encIn := f) (encA := a)
    (test := fun x p => p.1.finalBubble &&
      ((positions p.2.2.1).contains x.2 || (positions p.2.2.2).contains x.2)) hs
    (h.of_enc_eq (fun _ => rfl))
  exact filterWithInput (encIn := e) (encA := encUnary)
    (test := fun x i => x.2.1.any (fun p => p.1.finalBubble &&
      ((positions p.2.2.1).contains i || (positions p.2.2.2).contains i)))
    (unary_range' (fst encUnary (materialEncoding q))) hf

abbrev recoverEncoding (q : ℕ) :=
  encPair (encPair memberParamsEncoding (wordEncoding q)) (materialPairEncoding q)

theorem recover_polyTime (pad : Fin q) (b : ℕ) :
    ComputableInPolyTime (fun x : ((ℕ × (ℕ × ℕ)) × QWord q) × Pair q =>
        recover pad x.1.1.1 b x.1.1.2.1 x.1.1.2.2 x.1.2 x.2)
      (recoverEncoding q) (encOption (OrderedCatalogue.bubbleEncoding q)) := by
  let e := recoverEncoding q
  let a := materialPairEncoding q
  let w := wordEncoding q
  let u := OrderedCatalogue.bubbleEncoding q
  let p := encPair e u
  have hx := fst (encPair memberParamsEncoding w) a
  have hp := snd (encPair memberParamsEncoding w) a
  have hv := hx.snd'
  have hΛ := hx.fst'.snd'.snd'
  have hK := hx.fst'.fst'
  have hL := hx.fst'.snd'.fst'
  have hneg := (SourceLetters.spell_polyTime pad).comp (hv.prod hp.snd'.snd'.fst')
  have hpos := (SourceLetters.spell_polyTime pad).comp (hv.prod hp.snd'.snd'.snd')
  have hleft := decodedEncoding_left_polyTime q hp.fst'
  have hu := decodedEncoding_removed_polyTime q hp.fst'
  have hv := decodedEncoding_replacement_polyTime q hp.fst'
  have hloc := (localBubble_polyTime q b).comp ((hK.prod hL).prod (hleft.prod ((hu.prod hv).prod hneg)))
  have hpat := (pattern_polyTime q).comp hp.snd'.snd'.fst'
  have hfresh := (count_polyTime q true).comp hpat
  have hbody := ((OrderedCatalogue.side_polyTime q true).comp (snd e u)).decide_eq' (hpos.comp (fst e u))
  have hpass := hbody.ite' ((optionSome u).comp (snd e u)) (const none)
  have hr := optionBindWithInput (ea := e) (eb := u) (ec := u)
    (f := fun x w => if OrderedCatalogue.side w true = SourceLetters.spell pad x.1.2 x.2.2.2.2
        then some w else none) hloc (hpass.of_enc_eq (fun _ => by simp [Function.comp_def] <;> rfl))
  exact ((unary_le' hfresh hΛ).ite' hr (const none)).of_enc_eq
    (fun _ => by simp [recover,Function.comp_def] <;> rfl)

abbrev ownedEncoding (q : ℕ) := encPair encUnary (entriesEncoding q)

theorem filterOwned_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : ℕ × Entries q => x.2.filter (owned x.1))
      (ownedEncoding q) (entriesEncoding q) := by
  let e := ownedEncoding q
  let a := materialPairEncoding q
  have hx := (fst encUnary (entriesEncoding q)).comp (fst e a)
  have hd := (snd e a).fst'
  have hf := decodedEncoding_finalBubble_polyTime q hd
  have hi := decodedEncoding_rule_polyTime q hd
  exact filterWithInput (encIn := e) (encA := a)
    (test := fun x p => owned x.1 p) (snd encUnary (entriesEncoding q)) (bool_and' hf (hi.decide_eq' hx))

structure CheckInput (q : ℕ) where
  window : ℕ
  gram : ℕ
  omitted : ℕ
  arity : ℕ
  word : QWord q
  material : Material q

enc_structure checkInputEncoding (q : ℕ) : CheckInput q where
  window : encUnary, gram : encUnary, omitted : encUnary, arity : encUnary,
  word : (wordEncoding q), material : (materialEncoding q)

def runCheck (pad : Fin q) (b : ℕ) (x : CheckInput q) : Bool :=
  check pad x.window b x.gram x.omitted x.arity x.word x.material

theorem runCheck_polyTime (pad : Fin q) (b : ℕ) :
    ComputableInPolyTime (runCheck pad b) (checkInputEncoding q) encBool := by
  let e := checkInputEncoding q
  let a := encPair e encUnary
  let u := OrderedCatalogue.bubbleEncoding q
  let ws := OrderedCatalogue.ruleEncoding q
  let d := materialPairEncoding q
  let y := encPair a d
  let z := encPair a ws
  have hh := id' (encIn := e)
  have hx := fst e encUnary
  have hm := checkInputEncoding_material_polyTime q hh
  have hflip := (filterOwned_polyTime q).comp ((snd e encUnary).prod (hm.fst'.comp hx))
  have hw := checkInputEncoding_window_polyTime q hx
  have hg := checkInputEncoding_gram_polyTime q hx
  have ho := checkInputEncoding_omitted_polyTime q hx
  have hl := checkInputEncoding_word_polyTime q hx
  have hp := (recover_polyTime pad b).comp (encIn := y)
    ((((hw.prod (hg.prod ho)).prod hl).comp (fst a d)).prod (snd a d))
  have hv := mapMWithInput (ea := d) (eb := u) (ec := a)
    (f := fun x p => recover pad x.1.window b x.1.gram x.1.omitted x.1.word p)
    hflip (hp.of_enc_eq (fun _ => rfl))
  have hs := (checkInputEncoding_arity_polyTime q hx).comp (fst a ws)
  have hu := snd a ws
  have hlen := (length_list u).comp hu
  have hvalid := (OrderedCatalogue.valid_polyTime q).comp ((hg.comp (fst a ws)).prod hu)
  have hc := optionElimWithInput (encA := a) (encB := ws) (encC := encBool)
    (body := fun x ws => decide (ws.length = x.1.arity) && OrderedCatalogue.valid x.1.gram ws)
    hv (const false) (bool_and' (hlen.decide_eq' hs) hvalid)
  exact allWithInput (encIn := e) (encA := encUnary)
    (test := fun x i => ruleValid pad x.window b x.gram x.omitted x.arity x.word x.material i)
    hm.snd' (hc.of_enc_eq (fun _ => rfl))

abbrev uniformRowsEncoding (q : ℕ) := encPair encUnary (encPair (wordEncoding q) (materialEncoding q))

theorem uniformRows_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : ℕ × (QWord q × Material q) =>
        rows pad (UniformParameters.gram q b t x.1) x.2.1 x.2.2)
      (uniformRowsEncoding q) rowsEncoding := by
  let e := uniformRowsEncoding q
  let a := encPair e encUnary
  let d := materialPairEncoding q
  let p := encPair a d
  let w := wordEncoding q
  let m := materialEncoding q
  let bEnc := OrderedCatalogue.bubbleEncoding q
  have h := snd encUnary (encPair w m)
  have hi := snd e encUnary
  have hx := fst e encUnary
  have hls := (filterOwned_polyTime q).comp (hi.prod ((h.snd'.comp hx).fst'))
  have hword := (h.fst'.comp hx).comp (fst a d)
  have hb := (snd a d).snd'.snd'
  have hsp := SourceLetters.spell_polyTime pad
  have hc := (const (encOut := OrderedCatalogue.wordPairEncoding q) ([],[])).prod
    ((hsp.comp (hword.prod hb.fst')).prod (hsp.comp (hword.prod hb.snd')))
  have hmap := mapWithInput (encIn := a) (encA := d) (encB := bEnc)
    (f := fun x v => bubblePair pad x.1.2.1 v) hls (hc.of_enc_eq (fun _ => rfl))
  have hg := (SourceSpectrum.mainWords_polyTime pad b t hq).comp ((fst encUnary (encPair w m)).comp hx)
  have hr := (SourceRuleRows.rowWith_polyTime q).comp (hg.prod hmap)
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := rowEncoding)
    (f := fun x i => SourceRuleRows.row pad (UniformParameters.gram q b t x.1)
      ((x.2.2.1.filter (owned i)).map (bubblePair pad x.2.1))) h.snd'.snd'
    (hr.of_enc_eq (fun _ => rfl))

#print axioms support_polyTime
#print axioms recover_polyTime
#print axioms runCheck_polyTime
#print axioms uniformRows_polyTime

#print axioms support_eq
#print axioms recover_eq
#print axioms check_eq
#print axioms rows_eq

end DeletionCode.Explicit.Machine.SourceCoreCheck
