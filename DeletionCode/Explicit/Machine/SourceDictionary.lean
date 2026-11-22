import DeletionCode.Explicit.Machine.SourceLetters

/-! The source-first, negative-before-positive replay dictionary. -/
namespace DeletionCode.Explicit.Machine.SourceDictionary

open LetterSequence ReplayEntry LiftDictionary SourceLetters SourceLists
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open private sourceOccurrences liftOccurrences from DeletionCode.Explicit.LiftDictionary

variable {q ℓ L n : ℕ}

abbrev Stored (q : ℕ) := ℕ × (LiftData q × LiftData q)
abbrev LocationData := ℕ × Option (Bool × ℕ)
abbrev OccurrenceData (q : ℕ) := LocationData × LiftData q

abbrev storedEncoding (q : ℕ) := encPair encUnary (encPair (liftEncoding q) (liftEncoding q))
abbrev historyEncoding (q : ℕ) := encList (storedEncoding q)
abbrev locationEncoding := encPair encUnary (encOption (encPair encBool encUnary))
abbrev occurrenceEncoding (q : ℕ) := encPair locationEncoding (liftEncoding q)

def store (e : Completed ℓ (Fin q)) : Stored q :=
  (e.rule,(liftData e.negative.2,liftData e.positive.2))

def historyData (es : Array (Completed ℓ (Fin q))) : List (Stored q) := es.toList.map store

def side (a : ReplayEntry.Side) : Bool :=
  match a with
  | .negative => false
  | .positive => true

def locationData : Location → LocationData
  | .source start => (start,none)
  | .supplier entry s offset => (entry,some (side s,offset))

def occurrenceData (o : Occurrence ℓ L (Fin q)) : OccurrenceData q :=
  (locationData o.location,liftData o.lift)

def onSide (e : Stored q) (s : Bool) : LiftData q := if s then e.2.2 else e.2.1

theorem onSide_eq (e : Completed ℓ (Fin q)) (s : ReplayEntry.Side) :
    onSide (store e) (side s) = liftData (e.lift s).2 := by cases s <;> rfl

def starts (len L : ℕ) : List ℕ := (List.range (len+1)).filter (fun i => decide (i+L ≤ len))

def sources (q ℓ L : ℕ) : List (OccurrenceData q) :=
  (starts ℓ L).map (fun i => ((i,none),original q i L))

def suppliers (j : ℕ) (s : Bool) (L : ℕ) (w : LiftData q) : List (OccurrenceData q) :=
  (starts w.length L).map (fun i => ((j,some (s,i)),window w i L))

def occurrences (ℓ L : ℕ) (history : List (Stored q)) : List (OccurrenceData q) :=
  sources q ℓ L ++ (List.range history.length).flatMap fun j =>
    let e := history.getD j (0,([],[]))
    suppliers j false L e.2.1 ++ suppliers j true L e.2.2

theorem sources_eq (q ℓ L : ℕ) :
    sources q ℓ L = (sourceOccurrences (α := Fin q) ℓ L).map occurrenceData := by
  unfold sources sourceOccurrences starts
  rw [show List.range (ℓ+1) = (List.finRange (ℓ+1)).map Fin.val from by simp,List.filter_map,
    List.map_map,← List.filterMap_eq_filter,List.map_filterMap,List.map_filterMap]
  apply List.filterMap_congr
  intro i _
  by_cases h : i.val+L ≤ ℓ
  · simp only [Option.guard,Function.comp_def,h,decide_true,↓reduceIte,↓reduceDIte,Option.map_some]
    simp [occurrenceData,locationData,original_eq q _ _ h]
  · simp [Option.guard,Function.comp_def,h]

theorem suppliers_eq (j : ℕ) (s : ReplayEntry.Side) (L : ℕ) (u : StoredLift ℓ (Fin q)) :
    suppliers j (side s) L (liftData u.2) = (liftOccurrences j s L u).map occurrenceData := by
  unfold suppliers liftOccurrences starts
  rw [liftData_length,show List.range (u.1+1) = (List.finRange (u.1+1)).map Fin.val from by simp,
    List.filter_map,List.map_map,← List.filterMap_eq_filter,List.map_filterMap,List.map_filterMap]
  apply List.filterMap_congr
  intro i _
  by_cases h : i.val+L ≤ u.1
  · simp only [Option.guard,Function.comp_def,h,decide_true,↓reduceIte,↓reduceDIte,Option.map_some]
    simp [occurrenceData,locationData,window_eq _ _ _ h]
  · simp [Option.guard,Function.comp_def,h]

theorem history_getD (es : Array (Completed ℓ (Fin q))) (j : Fin es.size) :
    (historyData es).getD j.val (0,([],[])) = store es[j.val] := by
  have hj : j.val < (historyData es).length := by simpa [historyData] using j.isLt
  rw [List.getD_eq_getElem _ _ hj]
  simp [historyData]

theorem occurrences_eq (es : Array (Completed ℓ (Fin q))) (L : ℕ) :
    occurrences ℓ L (historyData es) = (LiftDictionary.occurrences es L).map occurrenceData := by
  unfold occurrences LiftDictionary.occurrences
  rw [List.map_append,sources_eq]
  congr 1
  have hs : (historyData es).length = es.size := by simp [historyData]
  rw [hs,show List.range es.size = (List.finRange es.size).map Fin.val from by simp,
    List.flatMap_map,List.map_flatMap]
  apply List.flatMap_congr
  intro j _
  simp only [Function.comp_def,history_getD,store,List.map_append]
  rw [← suppliers_eq j.val .negative,← suppliers_eq j.val .positive]
  rfl

def lookup (pad : Fin q) (x gram : QWord q) (os : List (OccurrenceData q)) : Option (OccurrenceData q) :=
  os.find? (fun o => decide (spell pad x o.2 = gram))

theorem lookup_eq (pad : Fin q) (x : Fin ℓ → Fin q) (es : Array (Completed ℓ (Fin q)))
    (g : Fin L → Fin q) :
    lookup pad (List.ofFn x) (List.ofFn g) (occurrences ℓ L (historyData es)) =
      (LiftDictionary.lookup x es g).map occurrenceData := by
  rw [lookup,occurrences_eq,LiftDictionary.lookup,List.find?_map]
  congr 1
  apply List.find?_congr
  intro o _
  simp [Function.comp_def,occurrenceData,spell_eq,List.ofFn_inj]

def paddedWindow (pad : Fin q) (w : QWord q) (a L : ℕ) : QWord q :=
  (List.range L).map (fun i => w.getD (a+i) pad)

theorem paddedWindow_eq (pad : Fin q) (w : Fin n → Fin q) (a L : ℕ) :
    paddedWindow pad (List.ofFn w) a L =
      List.ofFn (Qary.SignedSupport.gram (paddedLetters pad w) L a) := by
  rw [paddedWindow,range_map_eq]
  congr 1
  funext i
  change (List.ofFn w).getD (a+i.val) pad = paddedLetters pad w (a+i.val)
  by_cases h : a+i.val < n
  · exact (BooleanFibres.ofFn_getD w ⟨a+i.val,h⟩ pad).trans (by simp [paddedLetters,h])
  · simp [paddedLetters,h,List.getD_eq_getElem?_getD]

def select (pad : Fin q) (ℓ L : ℕ) (x : QWord q) (es : List (Stored q))
    (w : QWord q) : Option (List (OccurrenceData q)) :=
  let os := occurrences ℓ L es
  (selectedStarts L w.length).mapM (fun a => lookup pad x (paddedWindow pad w a L) os)

theorem select_eq (pad : Fin q) (x : Fin ℓ → Fin q)
    (es : Array (Completed ℓ (Fin q))) (L : ℕ) (w : Fin n → Fin q) :
    select pad ℓ L (List.ofFn x) (historyData es) (List.ofFn w) =
      (LiftDictionary.select pad x es L w).map (List.map occurrenceData) := by
  unfold select LiftDictionary.select
  simp only [List.length_ofFn,paddedWindow_eq,lookup_eq]
  induction selectedStarts L n with
  | nil => rfl
  | cons a as ih =>
    simp only [List.mapM_cons]
    cases ha : LiftDictionary.lookup x es (Qary.SignedSupport.gram (paddedLetters pad w) L a) with
    | none => rfl
    | some o =>
      simp only [Option.map_some]
      rw [ih]
      cases as.mapM (fun a => LiftDictionary.lookup x es (Qary.SignedSupport.gram (paddedLetters pad w) L a)) <;> rfl

abbrev sizesEncoding := encPair encUnary encUnary
abbrev occurrencesEncoding (q : ℕ) := encList (occurrenceEncoding q)

theorem starts_polyTime :
    ComputableInPolyTime (fun x : ℕ × ℕ => starts x.1 x.2) sizesEncoding (encList encUnary) := by
  let e := sizesEncoding
  have hn := fst encUnary encUnary
  have hL := snd encUnary encUnary
  have hx := fst e encUnary
  have hi := snd e encUnary
  exact filterWithInput (encIn := e) (encA := encUnary)
    (test := fun x i => decide (i+x.2 ≤ x.1)) (unary_range' (unary_add' hn (const 1)))
    (unary_le' (unary_add' hi (hL.comp hx)) (hn.comp hx))

theorem sources_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : ℕ × ℕ => sources q x.1 x.2)
      sizesEncoding (occurrencesEncoding q) := by
  let e := sizesEncoding
  let p := encPair e encUnary
  have hL := (snd encUnary encUnary).comp (fst e encUnary)
  have hi := snd e encUnary
  have hf := (original_polyTime q).comp (encIn := p) (hi.prod hL)
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := occurrenceEncoding q)
    (f := fun x i => ((i,none),original q i x.2)) starts_polyTime
    ((hi.prod (const none)).prod hf)

abbrev suppliersEncoding (q : ℕ) :=
  encPair (encPair encUnary encBool) (encPair encUnary (liftEncoding q))

theorem suppliers_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × Bool) × (ℕ × LiftData q) =>
      suppliers x.1.1 x.1.2 x.2.1 x.2.2) (suppliersEncoding q) (occurrencesEncoding q) := by
  let e := suppliersEncoding q
  let p := encPair e encUnary
  let v := encPair encUnary (liftEncoding q)
  have hx := fst e encUnary
  have hloc := (fst (encPair encUnary encBool) v).comp hx
  have hLift := snd (encPair encUnary encBool) v
  have hi := snd e encUnary
  have hlen := (length_list (letterEncoding q)).comp hLift.snd'
  have hst := starts_polyTime.comp (encIn := e) (encMid := sizesEncoding) (hlen.prod hLift.fst')
  have hw := (window_polyTime q).comp (encIn := p) (encMid := windowEncoding q)
    ((hLift.snd'.comp hx).prod (hi.prod (hLift.fst'.comp hx)))
  have htag := (optionSome (encPair encBool encUnary)).comp (hloc.snd'.prod hi)
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := occurrenceEncoding q)
    (f := fun x i => ((x.1.1,some (x.1.2,i)),window x.2.2 i x.2.1))
    hst (((hloc.fst'.prod htag).prod hw).of_enc_eq (fun _ => rfl))

abbrev dictionaryEncoding (q : ℕ) := encPair sizesEncoding (historyEncoding q)

theorem occurrences_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × List (Stored q) =>
      occurrences x.1.1 x.1.2 x.2) (dictionaryEncoding q) (occurrencesEncoding q) := by
  let e := dictionaryEncoding q
  let p := encPair e encUnary
  have h := fst sizesEncoding (historyEncoding q)
  have hs := snd sizesEncoding (historyEncoding q)
  have hsrc := (sources_polyTime q).comp (encIn := e) h
  have hi := snd e encUnary
  have hx := fst e encUnary
  have he := listGetDWithInput (hs.comp hx) hi ((0,([],[])) : Stored q)
  have hL := h.snd'.comp hx
  have hn := (suppliers_polyTime q).comp (encIn := p) (encMid := suppliersEncoding q)
    ((hi.prod (const false)).prod (hL.prod he.snd'.fst'))
  have hp := (suppliers_polyTime q).comp (encIn := p) (encMid := suppliersEncoding q)
    ((hi.prod (const true)).prod (hL.prod he.snd'.snd'))
  have hrest := flatMapWithInput (encIn := e) (encA := encUnary) (encB := occurrenceEncoding q)
    (f := fun x j => let e := x.2.getD j (0,([],[]))
      suppliers j false x.1.2 e.2.1 ++ suppliers j true x.1.2 e.2.2)
    (unary_range' ((length_list (storedEncoding q)).comp hs))
    ((listAppend' hn hp).of_enc_eq (fun _ => rfl))
  exact (listAppend' hsrc hrest).of_enc_eq (fun _ => rfl)

abbrev lookupEncoding (q : ℕ) := encPair (encPair (wordEncoding q) (wordEncoding q)) (occurrencesEncoding q)

theorem lookup_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : (QWord q × QWord q) × List (OccurrenceData q) =>
      lookup pad x.1.1 x.1.2 x.2) (lookupEncoding q) (encOption (occurrenceEncoding q)) := by
  let e := lookupEncoding q
  let p := encPair e (occurrenceEncoding q)
  let r := encPair (wordEncoding q) (wordEncoding q)
  have hx := (fst r (occurrencesEncoding q)).comp (fst e (occurrenceEncoding q))
  have hf := (spell_polyTime pad).comp (encIn := p) (hx.fst'.prod (snd e (occurrenceEncoding q)).snd')
  exact findWithInput (encIn := e) (encA := occurrenceEncoding q)
    (test := fun x e => decide (spell pad x.1.1 e.2 = x.1.2))
    (snd r (occurrencesEncoding q)) ((hf.decide_eq' hx.snd').of_enc_eq (fun _ => rfl))

abbrev paddedWindowEncoding (q : ℕ) := encPair (wordEncoding q) sizesEncoding

theorem paddedWindow_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : QWord q × (ℕ × ℕ) => paddedWindow pad x.1 x.2.1 x.2.2)
      (paddedWindowEncoding q) (wordEncoding q) := by
  let e := paddedWindowEncoding q
  have hx := fst (wordEncoding q) sizesEncoding
  have hs := snd (wordEncoding q) sizesEncoding
  have h := fst e encUnary
  have hi := snd e encUnary
  unfold paddedWindow
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := ExceptionalRecords.letterEncoding q)
    (f := fun x i => x.1.getD (x.2.1+i) pad) (unary_range' hs.snd')
    (listGetDWithInput (hx.comp h) (unary_add' (hs.fst'.comp h) hi) pad)

theorem selectedStarts_polyTime :
    ComputableInPolyTime (fun x : ℕ × ℕ => selectedStarts x.1 x.2)
      sizesEncoding (encList encUnary) := by
  have h := unary_sub' (snd encUnary encUnary) (fst encUnary encUnary)
  have hd := unary_div' h (const 2)
  have htwo := cons' (const 0) (cons' h (const []))
  have hthree := cons' (const 0) (cons' hd (cons' h (const [])))
  have hp := (h.decide_eq' (const 0)).ite' (const [0])
    ((h.decide_eq' (const 1)).ite' htwo hthree)
  exact hp.of_enc_eq (fun _ => by simp [selectedStarts,Function.comp_def])

abbrev selectEncoding (q : ℕ) :=
  encPair (encPair sizesEncoding (historyEncoding q)) (encPair (wordEncoding q) (wordEncoding q))

theorem select_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : ((ℕ × ℕ) × List (Stored q)) × (QWord q × QWord q) =>
      select pad x.1.1.1 x.1.1.2 x.2.1 x.1.2 x.2.2)
      (selectEncoding q) (encOption (occurrencesEncoding q)) := by
  let e := selectEncoding q
  let r := encPair (wordEncoding q) (wordEncoding q)
  let p := encPair e encUnary
  have hg := fst (dictionaryEncoding q) r
  have hw := snd (dictionaryEncoding q) r
  have hs := (length_list (ExceptionalRecords.letterEncoding q)).comp hw.snd'
  have hL := hg.fst'.snd'
  have hp := selectedStarts_polyTime.comp (encIn := e) (encMid := sizesEncoding) (hL.prod hs)
  have hx := fst e encUnary
  have hi := snd e encUnary
  have hwin := (paddedWindow_polyTime pad).comp (encIn := p) (encMid := paddedWindowEncoding q)
    ((hw.snd'.comp hx).prod (hi.prod (hL.comp hx)))
  have hdata := (occurrences_polyTime q).comp (encIn := p) (encMid := dictionaryEncoding q) (hg.comp hx)
  have h := (lookup_polyTime pad).comp (encIn := p) (encMid := lookupEncoding q)
    (((hw.fst'.comp hx).prod hwin).prod hdata)
  exact mapMWithInput (f := fun x i => lookup pad x.2.1 (paddedWindow pad x.2.2 i x.1.1.2)
    (occurrences x.1.1.1 x.1.1.2 x.1.2)) hp (h.of_enc_eq (fun _ => rfl))

#print axioms occurrences_eq
#print axioms occurrences_polyTime
#print axioms select_eq
#print axioms select_polyTime

end DeletionCode.Explicit.Machine.SourceDictionary
