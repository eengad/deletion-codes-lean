import DeletionCode.Explicit.Machine.SourceDictionary

/-! Read absolute dictionary locations and assemble the selected negative windows. -/
namespace DeletionCode.Explicit.Machine.SourceNegative

open LetterSequence ReplayEntry LiftDictionary SourceLetters SourceLists
open SourceDictionary (Stored LocationData OccurrenceData locationData occurrenceData side onSide onSide_eq store historyData)
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open private assemble resize length_of_negative from DeletionCode.Explicit.ReplayEntry

variable {q ℓ L n : ℕ}

abbrev ReadConfig := (ℕ × ℕ) × (ℕ × ℕ)
abbrev configEncoding := encPair SourceDictionary.sizesEncoding SourceDictionary.sizesEncoding

def readLocation (cfg : ReadConfig) (history : List (Stored q)) (loc : LocationData) :
    Option (LiftData q) :=
  let (ℓ,L) := cfg.1
  let (current,rule) := cfg.2
  loc.2.elim
    (if loc.1+L ≤ ℓ then some (original q loc.1 L) else none)
    (fun p => if loc.1 < current then do
      let e ← history[loc.1]?
      let v := onSide e p.1
      if e.1 < rule ∧ p.2+L ≤ v.length then some (window v p.2 L) else none
      else none)

theorem readSupplier_eq (es : Array (Completed ℓ (Fin q))) (L current rule : ℕ)
    (anchor : Option (Fin ℓ)) (j : ℕ) (s : Side) (off : ℕ) :
    readLocation ((ℓ,L),(current,rule)) (historyData es) (locationData (.supplier j s off)) =
      (readReference L current rule anchor (fun k => es[k]?) (.supplier j s off)).map liftData := by
  have he : (historyData es)[j]? = (es[j]?).map store := by simp [historyData]
  by_cases hj : j < current
  · have hj' : ¬ current ≤ j := by omega
    simp only [readLocation,locationData,Option.elim_some,he,hj,↓reduceIte,
      readReference,hj']
    cases h : es[j]? with
    | none => rfl
    | some e =>
      simp only [Option.map_some,Option.bind_some]
      have hw' : onSide (store e) (side s) = liftData (e.lift s).2 := onSide_eq e s
      simp only [store] at hw'
      simp only [bind,Option.bind,store]
      by_cases hr : e.rule < rule
      · have hr' : ¬rule ≤ e.rule := by omega
        by_cases hw : off+L ≤ (e.lift s).1
        · simp [hr,hr',hw,hw',window_eq _ _ _ hw]
        · simp [hr,hr',hw,hw']
      · have hr' : rule ≤ e.rule := by omega
        simp [hr,hr']
  · have hj' : current ≤ j := by omega
    simp [readLocation,locationData,readReference,hj,hj']

theorem readLocation_eq (es : Array (Completed ℓ (Fin q))) (L current rule : ℕ)
    (root : Fin ℓ) (loc : Location) :
    readLocation ((ℓ,L),(current,rule)) (historyData es) (locationData loc) =
      (readReference L current rule (some root) (fun k => es[k]?) (loc.reference root)).map liftData := by
  cases loc with
  | source i =>
    have he : (root.val : ℤ) + ((i : ℤ) - (root.val : ℤ)) = i := by ring
    by_cases h : i+L ≤ ℓ
    · simp [readLocation,locationData,Location.reference,readReference,he,h,original_eq q i L h]
    · simp [readLocation,locationData,Location.reference,readReference,he,h]
  | supplier j s off => exact readSupplier_eq es L current rule (some root) j s off

def finish (n : ℕ) (w : LiftData q) : Option (LiftData q) :=
  if w.length = n then some w else none

def assembleSelected (n : ℕ) (starts : List ℕ) (windows : List (LiftData q)) :
    Option (LiftData q) :=
  let first := windows.getD 0 []
  let next := SourceLetters.appendWindow first (starts.getD 1 0) (windows.getD 1 [])
  if starts.length = windows.length ∧ starts.getD 0 1 = 0 then
    if starts.length = 1 then finish n first
    else if starts.length = 2 then next.bind (finish n)
    else if starts.length = 3 then next.bind (fun w =>
      (SourceLetters.appendWindow w (starts.getD 2 0) (windows.getD 2 [])).bind (finish n))
    else none
  else none

def negativeWith (L n : ℕ) (refs : List ρ) (read : ρ → Option (LiftData q)) :
    Option (LiftData q) :=
  let starts := selectedStarts L n
  if L ≤ n ∧ refs.length = starts.length then
    (refs.mapM read).bind (assembleSelected n starts)
  else none

def negativeFrom (cfg : ReadConfig) (history : List (Stored q)) (n : ℕ) (refs : List LocationData) :
    Option (LiftData q) := negativeWith cfg.1.2 n refs (readLocation cfg history)

theorem mapM_map_result {α β γ : Type} (f : α → Option β) (g : β → γ) (xs : List α) :
    xs.mapM (fun x => (f x).map g) = (xs.mapM f).map (List.map g) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.mapM_cons]
    cases h : f a with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      rw [ih]
      cases as.mapM f <;> rfl

private theorem finish_eq {m : ℕ} (w : Lift ℓ m (Fin q)) (n : ℕ) :
    finish n (liftData w) = (if h : m = n then some (resize h w) else none).map liftData := by
  by_cases h : m = n
  · subst n
    simp [finish,resize]
  · simp [finish,h]

/-- Assembly agrees once every reference reader agrees on its symbolic window. -/
theorem negativeWith_eq {ρ : Type} (L current : ℕ) (e : Entry (Fin q))
    (anchor : Option (Fin ℓ)) (get : ℕ → Option (Completed ℓ (Fin q)))
    (refs : List ρ) (read : ρ → Option (LiftData q))
    (hlenRef : refs.length = e.references.length)
    (heq : refs.mapM read =
      (e.references.mapM (readReference L current e.rule anchor get)).map (List.map liftData)) :
    negativeWith L e.negativeLength refs read = (negativeLift L current e anchor get).map liftData := by
  by_cases hb : L ≤ e.negativeLength
  · by_cases hn : refs.length = (selectedStarts L e.negativeLength).length
    · have hmatch : refs.length = (selectedStarts L e.negativeLength).length := hn
      simp only [negativeWith,hb,hmatch,and_self,↓reduceIte,heq]
      have hbn : ¬ L > e.negativeLength := by omega
      unfold negativeLift
      simp only [hbn,↓reduceIte]
      have hsel : selectedStarts L e.negativeLength = [0] ∨
          (∃ a, selectedStarts L e.negativeLength = [0,a]) ∨
          (∃ a b, selectedStarts L e.negativeLength = [0,a,b]) := by
        by_cases h0 : e.negativeLength-L = 0
        · exact Or.inl (by simp [selectedStarts,h0])
        · by_cases h1 : e.negativeLength-L = 1
          · exact Or.inr (Or.inl ⟨1,by simp [selectedStarts,h0,h1]⟩)
          · exact Or.inr (Or.inr ⟨(e.negativeLength-L)/2,e.negativeLength-L,by simp [selectedStarts,h0,h1]⟩)
      have hlen : e.references.length = (selectedStarts L e.negativeLength).length := by simpa only [← hlenRef]
      rcases hsel with hs | ⟨a,hs⟩ | ⟨a,b,hs⟩
      · rw [hs] at hlen
        obtain ⟨p,hp⟩ := List.length_eq_one_iff.mp hlen
        simp only [hs,hp]
        cases h : (readReference L current e.rule anchor get) p with
        | none => simp [h,List.mapM_cons]
        | some w => simpa [h,List.mapM_cons,assembleSelected,assemble] using finish_eq w e.negativeLength
      · rw [hs] at hlen
        obtain ⟨p,o,hp⟩ := List.length_eq_two.mp hlen
        simp only [hs,hp]
        cases h : (readReference L current e.rule anchor get) p with
        | none => simp [h,List.mapM_cons]
        | some w =>
          cases ho : (readReference L current e.rule anchor get) o with
          | none => simp [h,ho,List.mapM_cons,assemble]
          | some z =>
            cases hj : ReplayEntry.appendWindow w a z with
            | none =>
              simp [h,ho,List.mapM_cons,assembleSelected,assemble,appendWindow_eq,hj]
            | some u =>
              simpa [h,ho,List.mapM_cons,assembleSelected,assemble,appendWindow_eq,hj] using finish_eq u e.negativeLength
      · rw [hs] at hlen
        obtain ⟨p,o,k,hp⟩ := List.length_eq_three.mp hlen
        simp only [hs,hp]
        cases h : (readReference L current e.rule anchor get) p with
        | none => simp [h,List.mapM_cons]
        | some w =>
          cases ho : (readReference L current e.rule anchor get) o with
          | none => simp [h,ho,List.mapM_cons,assemble]
          | some z =>
            cases hk : (readReference L current e.rule anchor get) k with
            | none =>
              cases hj : ReplayEntry.appendWindow w a z <;> simp [h,ho,hk,hj,List.mapM_cons,assemble]
            | some v =>
              cases hj : ReplayEntry.appendWindow w a z with
              | none =>
                simp [h,ho,hk,List.mapM_cons,assembleSelected,assemble,appendWindow_eq,hj]
              | some u =>
                cases hj' : ReplayEntry.appendWindow u b v with
                | none =>
                  simp [h,ho,hk,List.mapM_cons,assembleSelected,assemble,appendWindow_eq,hj,hj']
                | some u' =>
                  simpa [h,ho,hk,List.mapM_cons,assembleSelected,assemble,appendWindow_eq,hj,hj'] using
                    finish_eq u' e.negativeLength
    · have he : negativeLift L current e anchor get = none := by
        cases hh : negativeLift L current e anchor get with
        | none => rfl
        | some w => exact False.elim (hn (by simpa only [← hlenRef] using length_of_negative e hh))
      simp [negativeWith,hn,he]
  · have hbn : L > e.negativeLength := Nat.lt_of_not_ge hb
    simp [negativeWith,negativeLift,hb,hbn]

/-- Correctness of the at-most-three selected dictionary windows. -/
theorem negativeFrom_eq (es : Array (Completed ℓ (Fin q))) (L current : ℕ)
    (root : Fin ℓ) (e : Entry (Fin q)) (locs : List Location)
    (hr : e.references = locs.map (Location.reference root)) :
    negativeFrom ((ℓ,L),(current,e.rule)) (historyData es) e.negativeLength (locs.map locationData) =
      (negativeLift L current e (some root) (fun k => es[k]?)).map liftData := by
  apply negativeWith_eq L current e (some root) (fun k => es[k]?)
  · simp [hr]
  · rw [hr,List.mapM_map,List.mapM_map]
    simp only [Function.comp_def]
    have h : (fun z => readLocation ((ℓ,L),(current,e.rule)) (historyData es) (locationData z)) =
        (fun z => ((readReference L current e.rule (some root) (fun k => es[k]?)) (z.reference root)).map liftData) :=
      funext (readLocation_eq es L current e.rule root)
    rw [h]
    exact mapM_map_result _ _ _

def prepareNegative (pad : Fin q) (cfg : ReadConfig) (x : QWord q) (history : List (Stored q))
    (w : QWord q) : Option (List (OccurrenceData q) × LiftData q) :=
  (SourceDictionary.select pad cfg.1.1 cfg.1.2 x history w).bind fun os =>
    (negativeFrom cfg history w.length (os.map Prod.fst)).map (fun v => (os,v))

abbrev inventoryEncoding (q : ℕ) := encPair configEncoding (SourceDictionary.historyEncoding q)
abbrev readEncoding (q : ℕ) := encPair (inventoryEncoding q) SourceDictionary.locationEncoding
abbrev resultEncoding (q : ℕ) := encOption (liftEncoding q)

theorem readLocation_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ReadConfig × List (Stored q)) × LocationData =>
      readLocation x.1.1 x.1.2 x.2) (readEncoding q) (resultEncoding q) := by
  let e := readEncoding q
  let zd := encPair encBool encUnary
  let u := encPair e zd
  let c := inventoryEncoding q
  have hx := fst c SourceDictionary.locationEncoding
  have hl := snd c SourceDictionary.locationEncoding
  have hL := hx.fst'.fst'.snd'
  have hlen := hx.fst'.fst'.fst'
  have hp := hl.fst'
  have hsrc := (original_polyTime q).comp (encIn := e) (hp.prod hL)
  have hvalid := unary_le' (unary_add' hp hL) hlen
  have hbase := hvalid.ite' ((optionSome (liftEncoding q)).comp hsrc) (const none)
  have hu := fst e zd
  have hr := snd e zd
  have hs := hx.snd'.comp hu
  have hj := hp.comp hu
  have hd := Turing.MultiTapeTM.ComputableInPolyTime.getElem?
    (encA := SourceDictionary.storedEncoding q) hs hj
  let se := SourceDictionary.storedEncoding q
  let r := encPair u se
  have he := snd u se
  have ht := fst u se
  have hside := hr.fst'.comp ht
  have hoff := hr.snd'.comp ht
  have hw := hside.ite' he.snd'.snd' he.snd'.fst'
  have hL' := (hL.comp hu).comp ht
  have hrule := ((hx.fst'.snd'.snd'.comp hu).comp ht)
  have hbound := unary_le' (unary_add' hoff hL') ((length_list (letterEncoding q)).comp hw)
  have hshift := (window_polyTime q).comp (encIn := r) (encMid := windowEncoding q)
    (hw.prod (hoff.prod hL'))
  have hchecked := (bool_and' (unary_lt' he.fst' hrule) hbound).ite'
    ((optionSome (liftEncoding q)).comp hshift) (const none)
  have hsupplier := optionBindWithInput (ec := liftEncoding q)
    (f := fun x a => let v := onSide a x.2.1
      if a.1 < x.1.1.1.2.2 ∧ x.2.2+x.1.1.1.1.2 ≤ v.length
        then some (window v x.2.2 x.1.1.1.1.2) else none)
    hd (hchecked.of_enc_eq (fun z => by
      simp [Function.comp_def,SourceDictionary.onSide]
      rfl))
  have ht' := unary_lt' hj (hx.fst'.snd'.fst'.comp hu)
  exact optionElimWithInput (encA := e) (encB := zd) (encC := resultEncoding q) hl.snd'
    (body := fun x p => if x.2.1 < x.1.1.2.1 then do
      let a ← x.1.2[x.2.1]?
      let v := onSide a p.1
      if a.1 < x.1.1.2.2 ∧ p.2+x.1.1.1.2 ≤ v.length
        then some (window v p.2 x.1.1.1.2) else none
      else none) (hbase.of_enc_eq (fun _ => by simp [Function.comp_def]))
    ((ht'.ite' hsupplier (const none)).of_enc_eq (fun _ => by simp [Function.comp_def]))

theorem finish_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : ℕ × LiftData q => finish x.1 x.2)
      (encPair encUnary (liftEncoding q)) (resultEncoding q) := by
  have hn := fst encUnary (liftEncoding q)
  have hw := snd encUnary (liftEncoding q)
  have h := ((length_list (letterEncoding q)).comp hw).decide_eq' hn
  exact (h.ite' ((optionSome (liftEncoding q)).comp hw) (const none)).of_enc_eq
    (fun _ => by simp [finish,Function.comp_def])

abbrev assembleEncoding (q : ℕ) :=
  encPair (encPair encUnary (encList encUnary)) (encList (liftEncoding q))

private theorem addWindow_polyTime {α : Type} {e : α ↪ List Bool}
    {s : α → ℕ} {u w : α → LiftData q}
    (hs : ComputableInPolyTime s e encUnary) (hu : ComputableInPolyTime u e (liftEncoding q))
    (hw : ComputableInPolyTime w e (liftEncoding q)) :
    ComputableInPolyTime (fun x => SourceLetters.appendWindow (u x) (s x) (w x))
      e (resultEncoding q) := by
  have h := (appendWindow_polyTime q).comp (encIn := e) (encMid := appendEncoding q)
    (hs.prod (hu.prod hw))
  exact h.of_enc_eq (fun _ => rfl)

theorem assembleSelected_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × List ℕ) × List (LiftData q) =>
      assembleSelected x.1.1 x.1.2 x.2) (assembleEncoding q) (resultEncoding q) := by
  let e := assembleEncoding q
  let v := liftEncoding q
  let p := encPair e v
  let d := encPair encUnary (encList encUnary)
  have hn := (fst d (encList v)).fst'
  have ha := (fst d (encList v)).snd'
  have hw := snd d (encList v)
  have hs := (length_list encUnary).comp ha
  have hlen := (length_list v).comp hw
  have hstart := listGetDWithInput ha (const 0) 1
  have hvalid := bool_and' (hs.decide_eq' hlen) (hstart.decide_eq' (const 0))
  have hfirst := listGetDWithInput hw (const 0) ([] : LiftData q)
  have hnext := addWindow_polyTime (listGetDWithInput ha (const 1) 0) hfirst
    (listGetDWithInput hw (const 1) ([] : LiftData q))
  have hfinish := (finish_polyTime q).comp (encIn := p) ((hn.comp (fst e v)).prod (snd e v))
  have h1 := (finish_polyTime q).comp (encIn := e) (hn.prod hfirst)
  have h2 := optionBindWithInput (f := fun x w => finish x.1.1 w) hnext
    (hfinish.of_enc_eq (fun _ => rfl))
  have hthird := addWindow_polyTime (listGetDWithInput (ha.comp (fst e v)) (const 2) 0)
    (snd e v) (listGetDWithInput (hw.comp (fst e v)) (const 2) ([] : LiftData q))
  have hfinish' := (finish_polyTime q).comp (encIn := encPair p v)
    ((hn.comp ((fst e v).comp (fst p v))).prod (snd p v))
  have htwice := optionBindWithInput (f := fun x w => finish x.1.1.1 w) hthird
    (hfinish'.of_enc_eq (fun _ => rfl))
  have h3 := optionBindWithInput (f := fun x u =>
    (SourceLetters.appendWindow u (x.1.2.getD 2 0) (x.2.getD 2 [])).bind (finish x.1.1))
    hnext (htwice.of_enc_eq (fun _ => rfl))
  have h := hvalid.ite' ((hs.decide_eq' (const 1)).ite' h1
    ((hs.decide_eq' (const 2)).ite' h2 ((hs.decide_eq' (const 3)).ite' h3 (const none)))) (const none)
  exact h.of_enc_eq (fun _ => by simp [assembleSelected,Function.comp_def])

abbrev refsEncoding := encList SourceDictionary.locationEncoding
abbrev negativeEncoding (q : ℕ) := encPair (inventoryEncoding q) (encPair encUnary refsEncoding)

theorem negativeFrom_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ReadConfig × List (Stored q)) × (ℕ × List LocationData) =>
      negativeFrom x.1.1 x.1.2 x.2.1 x.2.2)
      (negativeEncoding q) (resultEncoding q) := by
  let e := negativeEncoding q
  let z := SourceDictionary.locationEncoding
  let p := encPair e z
  let r := encPair encUnary refsEncoding
  let v := encList (liftEncoding q)
  have hx := fst (inventoryEncoding q) r
  have hd := snd (inventoryEncoding q) r
  have hL := hx.fst'.fst'.snd'
  have hn := hd.fst'
  have hrefs := (length_list z).comp hd.snd'
  have hst := SourceDictionary.selectedStarts_polyTime.comp (encIn := e) (hL.prod hn)
  have hw := (readLocation_polyTime q).comp (encIn := p) (encMid := readEncoding q)
    ((hx.comp (fst e z)).prod (snd e z))
  have hread := mapMWithInput (f := fun x z => readLocation x.1.1 x.1.2 z)
    hd.snd' (hw.of_enc_eq (fun _ => rfl))
  have hu := (assembleSelected_polyTime q).comp (encIn := encPair e v) (encMid := assembleEncoding q)
    (((hn.prod hst).comp (fst e v)).prod (snd e v))
  have ha := optionBindWithInput (f := fun x ws =>
    assembleSelected x.2.1 (selectedStarts x.1.1.1.2 x.2.1) ws) hread
    (hu.of_enc_eq (fun _ => rfl))
  have hcheck := bool_and' (unary_le' hL hn) (hrefs.decide_eq' ((length_list encUnary).comp hst))
  exact (hcheck.ite' ha (const none)).of_enc_eq
    (fun _ => by simp [negativeFrom,negativeWith,Function.comp_def,Bool.and_eq_true_iff])

theorem negativeWith_polyTime {α ρ : Type} {e : α ↪ List Bool} {r : ρ ↪ List Bool}
    {L n : α → ℕ} {refs : α → List ρ} {rd : α → ρ → Option (LiftData q)}
    (hL : ComputableInPolyTime L e encUnary) (hn : ComputableInPolyTime n e encUnary)
    (hr : ComputableInPolyTime refs e (encList r))
    (hread : ComputableInPolyTime (fun x : α × ρ => rd x.1 x.2) (encPair e r) (resultEncoding q)) :
    ComputableInPolyTime (fun x => negativeWith (L x) (n x) (refs x) (rd x)) e (resultEncoding q) := by
  let vs := encList (liftEncoding q)
  have hst := SourceDictionary.selectedStarts_polyTime.comp (hL.prod hn)
  have hv := mapMWithInput hr hread
  have hu := (assembleSelected_polyTime q).comp (encIn := encPair e vs)
    (((hn.prod hst).comp (fst e vs)).prod (snd e vs))
  have ha := optionBindWithInput (f := fun x w => assembleSelected (n x) (selectedStarts (L x) (n x)) w)
    hv (hu.of_enc_eq (fun _ => rfl))
  have hcheck := bool_and' (unary_le' hL hn)
    (((length_list r).comp hr).decide_eq' ((length_list encUnary).comp hst))
  exact (hcheck.ite' ha (const none)).of_enc_eq
    (fun _ => by simp [negativeWith,Function.comp_def,Bool.and_eq_true_iff])

abbrev prepareEncoding (q : ℕ) := encPair (inventoryEncoding q) (encPair (wordEncoding q) (wordEncoding q))
abbrev preparedNegativeEncoding (q : ℕ) :=
  encPair (SourceDictionary.occurrencesEncoding q) (liftEncoding q)

theorem prepareNegative_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : (ReadConfig × List (Stored q)) × (QWord q × QWord q) =>
      prepareNegative pad x.1.1 x.2.1 x.1.2 x.2.2)
      (prepareEncoding q) (encOption (preparedNegativeEncoding q)) := by
  let e := prepareEncoding q
  let v := SourceDictionary.occurrencesEncoding q
  let w := encPair (wordEncoding q) (wordEncoding q)
  let p := encPair e v
  let p' := encPair p (liftEncoding q)
  have hd := fst (inventoryEncoding q) w
  have hw := snd (inventoryEncoding q) w
  have hs := (SourceDictionary.select_polyTime pad).comp (encIn := e)
    (encMid := SourceDictionary.selectEncoding q) ((hd.fst'.fst'.prod hd.snd').prod hw)
  have hos := snd e v
  have hrefs := (ComputableInPolyTime.map
    (fst SourceDictionary.locationEncoding (liftEncoding q))).comp (encIn := p) hos
  have hlen := (length_list (ExceptionalRecords.letterEncoding q)).comp (hw.snd'.comp (fst e v))
  have hn := (negativeFrom_polyTime q).comp (encIn := p) (encMid := negativeEncoding q)
    ((hd.comp (fst e v)).prod (hlen.prod hrefs))
  have h := optionMapWithInput (encA := p) (encB := liftEncoding q) (encC := preparedNegativeEncoding q)
    (f := fun x w => (x.2,w)) (hn.of_enc_eq (fun _ => rfl))
    ((hos.comp (fst p (liftEncoding q))).prod (snd p (liftEncoding q)))
  have hh := optionBindWithInput (ea := e) (eb := v) (ec := preparedNegativeEncoding q)
    (f := fun x os => (negativeFrom x.1.1 x.1.2 x.2.2.length (os.map Prod.fst)).map (fun w => (os,w)))
    (hs.of_enc_eq (fun _ => rfl)) (h.of_enc_eq (fun _ => rfl))
  exact hh.of_enc_eq (fun _ => rfl)

#print axioms readLocation_eq
#print axioms negativeFrom_eq
#print axioms negativeFrom_polyTime
#print axioms prepareNegative_polyTime

end DeletionCode.Explicit.Machine.SourceNegative
