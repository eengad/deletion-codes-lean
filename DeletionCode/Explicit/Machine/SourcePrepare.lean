import DeletionCode.Explicit.Machine.SourceNegative
import DeletionCode.Explicit.Machine.SourceRuleRows
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-! Prepare one rule against its frozen dictionary, retaining the replay data. -/
namespace DeletionCode.Explicit.Machine.SourcePrepare

open LetterGraphCuts LetterSequence ReplayEntry LiftDictionary
open SourceLetters SourceLists
open SourceDictionary (Stored OccurrenceData occurrenceData historyData store)
open SourceNegative (ReadConfig configEncoding)
open OrderedCatalogue (BubbleData bubbleData side ruleEncoding bubbleEncoding)
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {q ℓ L b K s a u v r : ℕ}

structure Prepared (q : ℕ) where
  rule : ℕ
  entry : ℕ
  left : ℕ
  removed : ℕ
  right : ℕ
  replacement : QWord q
  windows : List (OccurrenceData q)
  negative : LiftData q

enc_structure preparedEncoding (q : ℕ) : Prepared q where
  rule : encUnary, entry : encUnary, left : encUnary, removed : encUnary, right : encUnary,
  replacement : (wordEncoding q), windows : (SourceDictionary.occurrencesEncoding q),
  negative : (liftEncoding q)

def preparedData (p : PreparedBubble ℓ L (Fin q)) : Prepared q :=
  ⟨p.rule,p.gate.entry,p.left,p.removed,p.right,List.ofFn p.gate.replacement,
    p.windows.map occurrenceData,liftData p.gate.negative⟩

def positions (v : LiftData q) : List ℕ := v.filterMap position

theorem positions_eq (w : Lift ℓ a (Fin q)) :
    (positions (liftData w)).toFinset = w.positions := by
  ext j
  rw [Lift.mem_positions]
  simp only [positions,liftData,List.mem_toFinset,List.mem_filterMap,List.mem_ofFn,Function.comp_def]
  constructor
  · rintro ⟨_,⟨i,rfl⟩,hj⟩
    rw [position_eq] at hj
    cases h : (w.letters i).position with
    | none => simp [h] at hj
    | some p => exact ⟨i,p,h,by simpa [h] using hj⟩
  · rintro ⟨i,p,h,rfl⟩
    exact ⟨_,⟨i,rfl⟩,by simp [position_eq,h]⟩

def prepareFrom (cfg : ReadConfig) (a u r : ℕ) (replacement : QWord q)
    (v : List (OccurrenceData q) × LiftData q) : Option (Prepared q) :=
  if (positions v.2).isEmpty then none
  else some ⟨cfg.2.2,cfg.2.1,a,u,r,replacement,v.1,v.2⟩

def prepareBubble (pad : Fin q) (cfg : ReadConfig) (x : QWord q) (es : List (Stored q))
    (bub : BubbleData q) : Option (Prepared q) :=
  (SourceNegative.prepareNegative pad cfg x es (side bub false)).bind
    (prepareFrom cfg bub.1.1.length bub.2.1.length bub.1.2.length bub.2.2)

def prepareRule (pad : Fin q) (ℓ L rule : ℕ) (x : QWord q) (es : List (Stored q))
    (bubbles : List (BubbleData q)) : Option (List (Prepared q)) :=
  (List.range bubbles.length).mapM (fun j =>
    prepareBubble pad ((ℓ,L),(es.length+j,rule)) x es (bubbles.getD j (([],[]),([],[]))))

private theorem prepareNegative_eq (pad : Fin q) (x : Fin ℓ → Fin q)
    (es : Array (Completed ℓ (Fin q))) (L current rule : ℕ) (root : Fin ℓ)
    (rem rep : QWord q) (w : Fin (a+rem.length+r) → Fin q) :
    SourceNegative.prepareNegative pad ((ℓ,L),(current,rule)) (List.ofFn x) (historyData es) (List.ofFn w) =
      (LetterGraphCuts.prepareNegative pad x es L current rule root a rem rep r
        w).map
        (fun p => (p.1.map occurrenceData,liftData p.2)) := by
  unfold SourceNegative.prepareNegative LetterGraphCuts.prepareNegative
  have h := SourceDictionary.select_eq pad x es L w
  rw [h]
  cases he : LiftDictionary.select pad x es L w with
  | none => rfl
  | some os =>
    let entry : Entry (Fin q) :=
      ⟨rule,0,a,rem,rep,r,os.map (fun o => o.location.reference root)⟩
    have hrefs : entry.references = (os.map Occurrence.location).map (Location.reference root) := by
      simp [entry,List.map_map,Function.comp_def]
    have hw := SourceNegative.negativeFrom_eq es L current root entry (os.map Occurrence.location) hrefs
    simp only [Option.map_some,Option.bind_some,List.length_ofFn]
    simp only [List.map_map,Function.comp_def,occurrenceData]
    simp only [entry,Entry.negativeLength,List.map_map,Function.comp_def] at hw
    rw [hw]
    cases hx : negativeLift L current entry (some root) (fun j => es[j]?) <;>
      simp [entry] at hx <;> simp [hx,bind,Option.bind] <;> rfl

private theorem ofFn_negative (w : Borrowed.BubbleWord (Fin q) K b L) :
    List.ofFn (LetterGraphCuts.negativeLetters w) = w.negativeWord := by
  apply List.ext_getElem (by simp [Borrowed.BubbleWord.negativeWord,Nat.add_assoc])
  intro i hi hj
  simp [LetterGraphCuts.negativeLetters,Function.comp_def]

theorem prepareBubble_eq (pad : Fin q) (x : Fin ℓ → Fin q) (es : Array (Completed ℓ (Fin q)))
    (w : Borrowed.BubbleWord (Fin q) K b L) (root : Fin ℓ) (current rule : ℕ)
    (ha : 0 < w.left.length) (hr : 0 < w.right.length) :
    prepareBubble pad ((ℓ,L),(current,rule)) (List.ofFn x) (historyData es) (bubbleData w) =
      (LetterGraphCuts.prepareBubble pad x es w root current rule ha hr).map preparedData := by
  unfold prepareBubble LetterGraphCuts.prepareBubble
  rw [OrderedCatalogue.side_eq]
  change (SourceNegative.prepareNegative pad ((ℓ,L),(current,rule)) (List.ofFn x) (historyData es)
    w.negativeWord).bind (prepareFrom ((ℓ,L),(current,rule))
      w.left.length w.removed.length w.right.length w.replacement) = _
  rw [← ofFn_negative w]
  have h := prepareNegative_eq pad x es L current rule root
    w.removed w.replacement (LetterGraphCuts.negativeLetters w)
  rw [h]
  cases hp : LetterGraphCuts.prepareNegative pad x es L current rule root w.left.length
      w.removed w.replacement w.right.length (LetterGraphCuts.negativeLetters w) with
  | none => rfl
  | some p =>
    rcases p with ⟨os,neg⟩
    have hpos : (positions (liftData neg)).isEmpty = false ↔ neg.positions.Nonempty := by
      rw [← positions_eq neg]
      simp
    by_cases hne : neg.positions.Nonempty
    · have hfalse := hpos.mpr hne
      simp [prepareFrom,LetterGraphCuts.prepareBubbleFrom,hfalse,hne,preparedData,bubbleData]
    · have htrue : (positions (liftData neg)).isEmpty = true := by
        cases hv : (positions (liftData neg)).isEmpty
        · exact (hne (hpos.mp hv)).elim
        · rfl
      simp [prepareFrom,LetterGraphCuts.prepareBubbleFrom,htrue,hne,preparedData,bubbleData]

theorem prepareRule_eq (pad : Fin q) (x : Fin ℓ → Fin q) (es : Array (Completed ℓ (Fin q)))
    (ws : Fin s → Borrowed.BubbleWord (Fin q) K b L) (root : Fin ℓ) (rule : ℕ)
    (ha : ∀ j, 0 < (ws j).left.length) (hr : ∀ j, 0 < (ws j).right.length) :
    prepareRule pad ℓ L rule (List.ofFn x) (historyData es) (List.ofFn (bubbleData ∘ ws)) =
      (LetterGraphCuts.prepareRule pad x es ws root rule ha hr).map (List.map preparedData) := by
  unfold prepareRule LetterGraphCuts.prepareRule
  rw [List.length_ofFn,show List.range s = (List.finRange s).map Fin.val from by simp,List.mapM_map]
  have h : ∀ i : Fin s, (List.ofFn (bubbleData ∘ ws)).getD i.val (([],[]),([],[])) = bubbleData (ws i) :=
    fun i => BooleanFibres.ofFn_getD _ i _
  have hs : (historyData es).length = es.size := by simp [historyData]
  have hbody (i : Fin s) : prepareBubble pad ((ℓ,L),((historyData es).length+i.val,rule))
      (List.ofFn x) (historyData es) ((List.ofFn (bubbleData ∘ ws)).getD i.val (([],[]),([],[]))) =
      (LetterGraphCuts.prepareBubble pad x es (ws i) root (es.size+i.val) rule (ha i) (hr i)).map preparedData := by
    rw [h i,hs]
    exact prepareBubble_eq pad x es _ root _ _ (ha i) (hr i)
  simp only [Function.comp_def] at hbody ⊢
  rw [show (fun i : Fin s => prepareBubble pad ((ℓ,L),((historyData es).length+i.val,rule))
    (List.ofFn x) (historyData es) ((List.ofFn (fun j => bubbleData (ws j))).getD i.val (([],[]),([],[])))) = _
    from funext hbody]
  exact SourceNegative.mapM_map_result _ _ _

def completed (pad : Fin q) (p : Prepared q) : Stored q :=
  (p.rule,(p.negative,install pad p.entry p.left p.removed p.negative p.replacement))

theorem completed_eq (pad : Fin q) (p : PreparedBubble ℓ L (Fin q)) :
    completed pad (preparedData p) = store p.completed := by
  unfold completed preparedData
  rw [install_eq]
  rfl

def marks (p : Prepared q) : List ℕ := positions (window p.negative p.left p.removed)

def stock (pad : Fin q) (p : Prepared q) : LiftData q := inserted pad p.entry p.replacement

def interval (p : Prepared q) : Nat × Nat :=
  let ps := positions p.negative
  (ps.foldl min (ps.getD 0 0),ps.foldl max 0)

def record (pad : Fin q) (p : Prepared q) : SourcePatchTable.GateRecord (LetterData q) :=
  ((p.entry,interval p),(marks p,stock pad p))

theorem marks_eq (p : PreparedBubble ℓ L (Fin q)) :
    (marks (preparedData p)).toFinset = p.data.marks := by
  unfold marks preparedData
  let g := p.gate
  have h : p.left+p.removed ≤ p.left+p.removed+p.right := Nat.le_add_right ..
  rw [window_eq _ _ _ h]
  have hdata : liftData (g.negative.window p.left p.removed h) = g.removed.map letterData := by
    simp [liftData,Lift.window,Gate.removed,List.map_ofFn,Function.comp_def,g]
  rw [hdata]
  change (positions (g.removed.map letterData)).toFinset = g.marks
  simp only [positions,Gate.marks,List.filterMap_map,List.map_filterMap,Function.comp_def,position_eq]

theorem stock_eq (pad : Fin q) (p : PreparedBubble ℓ L (Fin q)) :
    (stock pad (preparedData p)).toFinset = p.data.inserted.image letterData := by
  unfold stock preparedData
  rw [inserted_eq]
  change _ = p.gate.inserted.toFinset.image letterData
  ext a
  simp [Gate.inserted,List.mem_ofFn,letterData]

theorem interval_eq (p : PreparedBubble ℓ L (Fin q)) :
    interval (preparedData p) = PatchMerge.data p.data.interval := by
  let ps := positions (liftData p.gate.negative)
  let S := p.gate.negative.positions
  have hS : ps.toFinset = S := positions_eq _
  have hn : S.Nonempty := p.hasOriginal
  have hmin : ps.min? = some (S.min' hn) := by
    apply List.min?_eq_some_iff.mpr
    refine ⟨List.mem_toFinset.mp ?_,fun i hi => Finset.min'_le S i ?_⟩
    · rw [hS]; exact Finset.min'_mem S hn
    · rw [← hS]; exact List.mem_toFinset.mpr hi
  have hmax : ps.max? = some (S.max' hn) := by
    apply List.max?_eq_some_iff.mpr
    refine ⟨List.mem_toFinset.mp ?_,fun i hi => Finset.le_max' S i ?_⟩
    · rw [hS]; exact Finset.max'_mem S hn
    · rw [← hS]; exact List.mem_toFinset.mpr hi
  have hps : ps ≠ [] := by
    intro h
    simp [h] at hmin
  have hh : ps.getD 0 0 ∈ ps := by
    cases h : ps with
    | nil => exact (hps h).elim
    | cons x xs => simp
  change (ps.foldl min (ps.getD 0 0),ps.foldl max 0) = (S.min' hn,S.max' hn)
  rw [List.foldl_min,List.foldl_max,hmin,hmax]
  simp only [Option.getD_some,zero_max]
  rw [min_eq_right (Finset.min'_le S _ (by rw [← hS]; exact List.mem_toFinset.mpr hh))]

theorem record_eq (pad : Fin q) (p : PreparedBubble ℓ L (Fin q)) :
    record pad (preparedData p) =
      SourcePatchTable.gateRecord p.data (marks (preparedData p)) (stock pad (preparedData p)) := by
  unfold record SourcePatchTable.gateRecord
  rw [interval_eq]
  rfl

theorem positions_polyTime (q : ℕ) :
    ComputableInPolyTime (positions (q := q)) (liftEncoding q) (encList encUnary) := by
  let e := liftEncoding q
  let p := encPair e (letterEncoding q)
  have h := (optionToList_polyTime encUnary).comp (encIn := p)
    ((position_polyTime q).comp (snd e (letterEncoding q)))
  have hf := flatMapWithInput (encIn := e) (encA := letterEncoding q) (encB := encUnary)
    (f := fun _ a => (position a).toList) id' (h.of_enc_eq (fun _ => rfl))
  exact hf.of_enc_eq (fun w => congrArg _ (List.filterMap_eq_flatMap_toList position w))

abbrev flankEncoding := encPair encUnary (encPair encUnary encUnary)
abbrev fromEncoding (q : ℕ) :=
  encPair (encPair configEncoding flankEncoding) (encPair (wordEncoding q)
    (SourceNegative.preparedNegativeEncoding q))

theorem prepareFrom_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ReadConfig × (ℕ × (ℕ × ℕ))) ×
        (QWord q × (List (OccurrenceData q) × LiftData q)) =>
      prepareFrom x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2.1 x.2.2)
      (fromEncoding q) (encOption (preparedEncoding q)) := by
  let e := fromEncoding q
  let a := encPair configEncoding flankEncoding
  let v := encPair (wordEncoding q) (SourceNegative.preparedNegativeEncoding q)
  have hc := fst a v
  have hs := snd a v
  have hv := hs.snd'
  have hp := (positions_polyTime q).comp (encIn := e) hv.snd'
  have hlen := (length_list encUnary).comp hp
  have hzero := hlen.decide_eq' (const 0)
  have h := preparedEncoding_mk_polyTime q hc.fst'.snd'.snd' hc.fst'.snd'.fst'
    hc.snd'.fst' hc.snd'.snd'.fst' hc.snd'.snd'.snd' hs.fst' hv.fst' hv.snd'
  have hout := hzero.ite' (const none) ((optionSome (preparedEncoding q)).comp h)
  refine hout.of_enc_eq ?_
  intro x
  by_cases hh : (positions x.2.2.2).isEmpty
  · have hnil : positions x.2.2.2 = [] := List.isEmpty_iff.mp hh
    simp [prepareFrom,hh,hnil,Function.comp_def]
  · have hne : positions x.2.2.2 ≠ [] := fun hp => hh (List.isEmpty_iff.mpr hp)
    simp [prepareFrom,Bool.eq_false_iff.mpr hh,hne,Function.comp_def]

abbrev bubbleInputEncoding (q : ℕ) :=
  encPair (SourceNegative.inventoryEncoding q) (encPair (wordEncoding q) (bubbleEncoding q))

theorem prepareBubble_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : (ReadConfig × List (Stored q)) × (QWord q × BubbleData q) =>
      prepareBubble pad x.1.1 x.2.1 x.1.2 x.2.2)
      (bubbleInputEncoding q) (encOption (preparedEncoding q)) := by
  let e := bubbleInputEncoding q
  let h := SourceNegative.inventoryEncoding q
  let w := encPair (wordEncoding q) (bubbleEncoding q)
  let v := SourceNegative.preparedNegativeEncoding q
  let p := encPair e v
  have hc := fst h w
  have hs := snd h w
  have hneg := (OrderedCatalogue.side_polyTime q false).comp (encIn := e) hs.snd'
  have hprep := (SourceNegative.prepareNegative_polyTime pad).comp
    (encIn := e) (encMid := SourceNegative.prepareEncoding q) (hc.prod (hs.fst'.prod hneg))
  have hx := fst e v
  have hb := hs.snd'.comp hx
  have hl := length_list (ExceptionalRecords.letterEncoding q)
  have hflank := (hl.comp hb.fst'.fst').prod ((hl.comp hb.snd'.fst').prod (hl.comp hb.fst'.snd'))
  have hr := (prepareFrom_polyTime q).comp (encIn := p) (encMid := fromEncoding q)
    (((hc.fst'.comp hx).prod hflank).prod (hb.snd'.snd'.prod (snd e v)))
  have hf := optionBindWithInput (ea := e) (eb := v) (ec := preparedEncoding q)
    (f := fun x o => prepareFrom x.1.1 x.2.2.1.1.length x.2.2.2.1.length
      x.2.2.1.2.length x.2.2.2.2 o) (hprep.of_enc_eq (fun _ => rfl)) (hr.of_enc_eq (fun _ => rfl))
  exact hf.of_enc_eq (fun _ => rfl)

abbrev preparedListEncoding (q : ℕ) := encList (preparedEncoding q)
abbrev ruleInputEncoding (q : ℕ) :=
  encPair (encPair SourceDictionary.sizesEncoding encUnary)
    (encPair (SourceDictionary.historyEncoding q) (encPair (wordEncoding q) (ruleEncoding q)))

theorem prepareRule_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : ((ℕ × ℕ) × ℕ) × (List (Stored q) × (QWord q × List (BubbleData q))) =>
      prepareRule pad x.1.1.1 x.1.1.2 x.1.2 x.2.2.1 x.2.1 x.2.2.2)
      (ruleInputEncoding q) (encOption (preparedListEncoding q)) := by
  let e := ruleInputEncoding q
  let p := encPair e encUnary
  let d := encPair SourceDictionary.sizesEncoding encUnary
  let v := encPair (SourceDictionary.historyEncoding q) (encPair (wordEncoding q) (ruleEncoding q))
  have hx := fst e encUnary
  have hj := snd e encUnary
  have hd := (fst d v).comp hx
  have hh := (snd d v).comp hx
  have hlen := (length_list (SourceDictionary.storedEncoding q)).comp hh.fst'
  have hf := listGetDWithInput hh.snd'.snd' hj ((([],[]),([],[])) : BubbleData q)
  have hcfg := hd.fst'.prod ((unary_add' hlen hj).prod hd.snd')
  have h := (prepareBubble_polyTime pad).comp (encIn := p) (encMid := bubbleInputEncoding q)
    ((hcfg.prod hh.fst').prod (hh.snd'.fst'.prod hf))
  exact mapMWithInput (ec := e) (ea := encUnary) (eb := preparedEncoding q)
    (f := fun x j => prepareBubble pad (x.1.1,(x.2.1.length+j,x.1.2)) x.2.2.1 x.2.1
      (x.2.2.2.getD j (([],[]),([],[]))))
    (unary_range' ((length_list (bubbleEncoding q)).comp (snd d v).snd'.snd'))
    (h.of_enc_eq (fun _ => rfl))

theorem completed_polyTime (pad : Fin q) :
    ComputableInPolyTime (completed pad) (preparedEncoding q) (SourceDictionary.storedEncoding q) := by
  let e := preparedEncoding q
  have hr := preparedEncoding_rule_polyTime q (id' (encIn := e))
  have he := preparedEncoding_entry_polyTime q (id' (encIn := e))
  have hl := preparedEncoding_left_polyTime q (id' (encIn := e))
  have hu := preparedEncoding_removed_polyTime q (id' (encIn := e))
  have hneg := preparedEncoding_negative_polyTime q (id' (encIn := e))
  have hrep := preparedEncoding_replacement_polyTime q (id' (encIn := e))
  have hp := (install_polyTime pad).comp (encIn := e) (encMid := installEncoding q)
    ((he.prod (hl.prod hu)).prod (hneg.prod hrep))
  exact (hr.prod (hneg.prod hp)).of_enc_eq (fun _ => rfl)

theorem marks_polyTime (q : ℕ) :
    ComputableInPolyTime (marks (q := q)) (preparedEncoding q) (encList encUnary) := by
  let e := preparedEncoding q
  have hl := preparedEncoding_left_polyTime q (id' (encIn := e))
  have hu := preparedEncoding_removed_polyTime q (id' (encIn := e))
  have hneg := preparedEncoding_negative_polyTime q (id' (encIn := e))
  have hcut := (window_polyTime q).comp (encIn := e) (encMid := windowEncoding q) (hneg.prod (hl.prod hu))
  exact ((positions_polyTime q).comp (encIn := e) hcut).of_enc_eq (fun _ => rfl)

theorem stock_polyTime (pad : Fin q) :
    ComputableInPolyTime (stock pad) (preparedEncoding q) (liftEncoding q) := by
  let e := preparedEncoding q
  have he := preparedEncoding_entry_polyTime q (id' (encIn := e))
  have hrep := preparedEncoding_replacement_polyTime q (id' (encIn := e))
  exact ((inserted_polyTime pad).comp (encIn := e) (he.prod hrep)).of_enc_eq (fun _ => rfl)

private theorem foldl_min_le (xs : List ℕ) (init : ℕ) : xs.foldl min init ≤ init := by
  induction xs generalizing init with
  | nil => exact le_rfl
  | cons v vs ih => exact (ih (min init v)).trans (min_le_left ..)

private theorem min_polyTime :
    ComputableInPolyTime (fun ps : List ℕ => ps.foldl min (ps.getD 0 0))
      (encList encUnary) encUnary := by
  let e := encList encUnary
  have h := listGetDWithInput (id' (encIn := e)) (const 0) 0
  have hh : PolyBounded (fun ps : List ℕ => (e ps).length) (fun ps => ps.getD 0 0) := by
    simpa only [encUnary_apply,List.length_replicate] using h.polyBounded_length
  exact foldl' (encIn := e) (encA := encUnary) (encB := encUnary)
    (list := id) (init := fun ps => ps.getD 0 0) (step := min) id' h unary_min hh (by
      intro ps i _
      simp only [encUnary_apply,List.length_replicate]
      exact foldl_min_le ..)

theorem interval_polyTime (q : ℕ) :
    ComputableInPolyTime (interval (q := q)) (preparedEncoding q) PatchMerge.intervalEncoding := by
  let e := preparedEncoding q
  have hneg := preparedEncoding_negative_polyTime q (id' (encIn := e))
  have hp := (positions_polyTime q).comp (encIn := e) hneg
  exact ((min_polyTime.comp (encIn := e) hp).prod
    ((unary_foldl_max 0).comp (encIn := e) hp)).of_enc_eq (fun _ => rfl)

theorem record_polyTime (pad : Fin q) :
    ComputableInPolyTime (record pad) (preparedEncoding q) (SourcePatchTable.gateEncoding (letterEncoding q)) := by
  let e := preparedEncoding q
  have he := preparedEncoding_entry_polyTime q (id' (encIn := e))
  exact ((he.prod (interval_polyTime q)).prod
    ((marks_polyTime q).prod (stock_polyTime pad))).of_enc_eq (fun _ => rfl)

#print axioms prepareBubble_eq
#print axioms prepareRule_eq
#print axioms prepareBubble_polyTime
#print axioms prepareRule_polyTime
#print axioms completed_eq
#print axioms interval_eq
#print axioms marks_eq
#print axioms stock_eq
#print axioms record_polyTime

end DeletionCode.Explicit.Machine.SourcePrepare
