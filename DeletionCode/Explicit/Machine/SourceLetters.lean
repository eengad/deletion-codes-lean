import DeletionCode.Explicit.PrepareRule
import DeletionCode.Explicit.Machine.SourceLists
import Batteries.Tactic.OpenPrivate

/-! Lift letters, original positions, and the splice used in replay and preparation. -/
namespace DeletionCode.Explicit.Machine.SourceLetters

open LetterSequence ReplayEntry
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open SourceLists
open private leftOffset joinedLetters join from DeletionCode.Explicit.LiftSplice
open private resize from DeletionCode.Explicit.ReplayEntry
open private gateLetter from DeletionCode.Explicit.LiftReplay

variable {q ℓ n a k b m : ℕ}

abbrev LetterData (q : ℕ) := ℕ × Option (ℕ × Fin q)
abbrev LiftData (q : ℕ) := List (LetterData q)
abbrev freshEncoding (q : ℕ) := encPair encUnary (ExceptionalRecords.letterEncoding q)
abbrev letterEncoding (q : ℕ) := encPair encUnary (encOption (freshEncoding q))
abbrev liftEncoding (q : ℕ) := encList (letterEncoding q)

def letterData : Letter ℓ (Fin q) → LetterData q
  | .original i => (i.val,none)
  | .fresh entry offset sym => (entry,some (offset,sym))

def liftData (w : Lift ℓ n (Fin q)) : LiftData q := List.ofFn (letterData ∘ w.letters)

@[simp] theorem liftData_length (w : Lift ℓ n (Fin q)) : (liftData w).length = n := by simp [liftData]

def position (x : LetterData q) : Option ℕ := if x.2.isSome then none else some x.1

theorem position_eq (x : Letter ℓ (Fin q)) : position (letterData x) = x.position.map Fin.val := by
  cases x <;> rfl

def symbol (pad : Fin q) (x : QWord q) (a : LetterData q) : Fin q :=
  a.2.elim (x.getD a.1 pad) Prod.snd

def spell (pad : Fin q) (x : QWord q) (w : LiftData q) : QWord q :=
  w.map (symbol pad x)

theorem spell_eq (pad : Fin q) (x : Fin ℓ → Fin q) (w : Lift ℓ n (Fin q)) :
    spell pad (List.ofFn x) (liftData w) = List.ofFn (w.spelling x) := by
  simp only [spell,liftData,List.map_ofFn,Function.comp_def]
  congr 1
  funext i
  change symbol pad (List.ofFn x) (letterData (w.letters i)) = (w.letters i).symbol x
  cases w.letters i with
  | original p => exact BooleanFibres.ofFn_getD x p pad
  | fresh j a s => rfl

def original (q start len : ℕ) : LiftData q :=
  (List.range len).map (fun i => (start+i,none))

theorem original_eq (q start len : ℕ) (h : start+len ≤ ℓ) :
    original q start len = liftData (sourceWindow (α := Fin q) start len h) := by
  rw [original,range_map_eq]
  rfl

def window (w : LiftData q) (start len : ℕ) : LiftData q := (w.drop start).take len

theorem window_eq (w : Lift ℓ n (Fin q)) (start len : ℕ) (h : start+len ≤ n) :
    window (liftData w) start len = liftData (w.window start len h) := by
  unfold window
  apply List.ext_getElem
  · simp [Nat.min_eq_left (show len ≤ n-start by omega)]
  · intro i hi hj
    simp [liftData,Lift.window,Function.comp_def]

def sharedAt (start i : ℕ) (u v : LiftData q) : Bool :=
  let p := position (u.getD (start+i) (0,none))
  p.isSome && decide (p = position (v.getD i (0,none)))

private theorem sharedAt_iff (u : Lift ℓ (a+k) (Fin q)) (v : Lift ℓ (k+b) (Fin q)) (i : Fin k) :
    sharedAt a i.val (liftData u) (liftData v) = true ↔ Shared u v i := by
  have hu := BooleanFibres.ofFn_getD (letterData ∘ u.letters) (leftOffset a i) (0,none)
  have hv := BooleanFibres.ofFn_getD (letterData ∘ v.letters) (Fin.castLE (Nat.le_add_right k b) i) (0,none)
  unfold sharedAt liftData
  change (position ((List.ofFn (letterData ∘ u.letters)).getD (leftOffset a i).val (0,none))).isSome &&
    decide (position ((List.ofFn (letterData ∘ u.letters)).getD (leftOffset a i).val (0,none)) =
      position ((List.ofFn (letterData ∘ v.letters)).getD (Fin.castLE (Nat.le_add_right k b) i).val (0,none))) =
    true ↔ _
  rw [hu,hv]
  simp only [Function.comp_def,position_eq,Bool.and_eq_true_iff,decide_eq_true_eq,Option.isSome_map,Shared]
  have hi : Function.Injective (Fin.val (n := ℓ)) := fun _ _ h => Fin.ext h
  rw [Option.map_inj_right hi]

def firstShared (start count : ℕ) (u v : LiftData q) : Option ℕ :=
  (List.range count).find? (fun i => sharedAt start i u v)

theorem firstShared_eq (u : Lift ℓ (a+k) (Fin q)) (v : Lift ℓ (k+b) (Fin q)) :
    firstShared a k (liftData u) (liftData v) = (splicePivot u v).map (fun i => i.val.val) := by
  unfold firstShared
  cases h : splicePivot u v with
  | none =>
    apply List.find?_eq_none.mpr
    intro j hj ht
    have hlt : j < k := List.mem_range.mp hj
    have hs := (sharedAt_iff u v ⟨j,hlt⟩).mp ht
    have he := splicePivot_isSome hs
    simp [h] at he
  | some i =>
    apply findRange_first _ _ _ i.val.isLt ((sharedAt_iff u v i.val).mpr i.property)
    intro j hj
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hlt : j < k := hj.trans i.val.isLt
    have hs := (sharedAt_iff u v ⟨j,hlt⟩).mp htrue
    have hp := splicePivot_first h hs
    exact (Nat.not_le_of_lt hj) hp

def sharedJoin (start p : ℕ) (u v : LiftData q) : LiftData q :=
  (List.range (start+v.length)).map fun i =>
    if i ≤ start+p then u.getD i (0,none) else v.getD (i-start) (0,none)

private theorem join_eq (u : Lift ℓ (a+k) (Fin q)) (v : Lift ℓ (k+b) (Fin q))
    (p : {i : Fin k // Shared u v i}) :
    sharedJoin a p.val.val (liftData u) (liftData v) = liftData (join u v p) := by
  have hp := p.val.isLt
  rw [sharedJoin,liftData_length,← Nat.add_assoc,range_map_eq]
  unfold liftData
  congr 1
  funext i
  by_cases h : i.val ≤ a+p.val.val
  · simp only [h,↓reduceIte,Function.comp_def,join,joinedLetters,↓reduceDIte]
    exact BooleanFibres.ofFn_getD (letterData ∘ u.letters) ⟨i.val,by omega⟩ _
  · simp only [h,↓reduceIte,Function.comp_def,join,joinedLetters,↓reduceDIte]
    exact BooleanFibres.ofFn_getD (letterData ∘ v.letters) ⟨i.val-a,by omega⟩ _

def splice (start count : ℕ) (u v : LiftData q) : Option (LiftData q) :=
  (firstShared start count u v).map (fun p => sharedJoin start p u v)

theorem splice_eq (u : Lift ℓ (a+k) (Fin q)) (v : Lift ℓ (k+b) (Fin q)) :
    splice a k (liftData u) (liftData v) = (LetterSequence.splice u v).map liftData := by
  rw [splice,firstShared_eq,LetterSequence.splice,Option.map_map,Option.map_map]
  congr 1
  funext p
  exact join_eq u v p

def appendWindow (u : LiftData q) (start : ℕ) (v : LiftData q) : Option (LiftData q) :=
  if start ≤ u.length && u.length ≤ start+v.length then
    splice start (u.length-start) u v
  else none

private theorem resize_data {h h' : ℕ} (he : h = h') (w : Lift ℓ h (Fin q)) :
    liftData (resize he w) = liftData w := by cases he; rfl

theorem appendWindow_eq (u : Lift ℓ n (Fin q)) (start : ℕ) (v : Lift ℓ m (Fin q)) :
    appendWindow (liftData u) start (liftData v) = (ReplayEntry.appendWindow u start v).map liftData := by
  by_cases ha : start ≤ n
  · by_cases hb : n ≤ start+m
    · let x : Lift ℓ (start+(n-start)) (Fin q) := resize (by omega) u
      let y : Lift ℓ ((n-start)+(start+m-n)) (Fin q) := resize (by omega) v
      have he := splice_eq x y
      simp only [x,y,resize_data] at he
      simp only [appendWindow,liftData_length,ha,hb,decide_true,Bool.true_and,↓reduceIte,
        ReplayEntry.appendWindow,↓reduceDIte,Option.map_map,Function.comp_def,resize_data]
      exact he
    · simp [appendWindow,ReplayEntry.appendWindow,ha,hb]
  · simp [appendWindow,ReplayEntry.appendWindow,ha]

def inserted (pad : Fin q) (current : ℕ) (w : QWord q) : LiftData q :=
  (List.range w.length).map (fun j => (current,some (j,w.getD j pad)))

def install (pad : Fin q) (current left removed : ℕ) (neg : LiftData q) (replacement : QWord q) : LiftData q :=
  (List.range (left+replacement.length+(neg.length-(left+removed)))).map fun i =>
    if i < left then neg.getD i (0,none)
    else if i < left+replacement.length then (current,some (i-left,replacement.getD (i-left) pad))
    else neg.getD (i-replacement.length+removed) (0,none)

theorem inserted_eq {v : ℕ} (pad : Fin q) (current : ℕ) (w : Fin v → Fin q) :
    inserted pad current (List.ofFn w) = List.ofFn (fun j : Fin v => (current,some (j.val,w j))) := by
  rw [inserted,List.length_ofFn,range_map_eq]
  congr 1
  funext j
  rw [BooleanFibres.ofFn_getD _ j]

theorem install_eq {u v r : ℕ} (pad : Fin q) (neg : Lift ℓ (a+u+r) (Fin q))
    (current : ℕ) (w : Fin v → Fin q) :
    install pad current a u (liftData neg) (List.ofFn w) = liftData (neg.installGate current w) := by
  rw [install,liftData_length,List.length_ofFn,Nat.add_sub_cancel_left,range_map_eq]
  unfold liftData
  congr 1
  funext i
  by_cases h : i.val < a
  · simp only [h,↓reduceIte,Function.comp_def,Lift.installGate,gateLetter,↓reduceDIte]
    exact BooleanFibres.ofFn_getD (letterData ∘ neg.letters) ⟨i.val,by omega⟩ _
  · by_cases hm : i.val < a+v
    · simp only [h,hm,↓reduceIte,Function.comp_def,Lift.installGate,gateLetter,↓reduceDIte,letterData]
      rw [BooleanFibres.ofFn_getD w (⟨i.val-a,by omega⟩ : Fin v)]
    · simp only [h,hm,↓reduceIte,Function.comp_def,Lift.installGate,gateLetter,↓reduceDIte]
      exact BooleanFibres.ofFn_getD (letterData ∘ neg.letters) ⟨i.val-v+u,by omega⟩ _

theorem position_polyTime (q : ℕ) :
    ComputableInPolyTime (position (q := q)) (letterEncoding q) (encOption encUnary) := by
  have h := fst encUnary (encOption (freshEncoding q))
  have hf := snd encUnary (encOption (freshEncoding q))
  exact ((optionIsSome hf).ite' (const none) ((optionSome encUnary).comp h)).of_enc_eq (fun _ => rfl)

theorem symbol_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : QWord q × LetterData q => symbol pad x.1 x.2)
      (encPair (wordEncoding q) (letterEncoding q)) (ExceptionalRecords.letterEncoding q) := by
  let e := encPair (wordEncoding q) (letterEncoding q)
  have hx := fst (wordEncoding q) (letterEncoding q)
  have ha := snd (wordEncoding q) (letterEncoding q)
  exact optionElimWithInput (encA := e) (encB := freshEncoding q)
    (body := fun _ r => r.2) ha.snd'
    (listGetDWithInput hx ha.fst' pad) (snd e (freshEncoding q)).snd'

theorem spell_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : QWord q × LiftData q => spell pad x.1 x.2)
      (encPair (wordEncoding q) (liftEncoding q)) (wordEncoding q) := by
  let e := encPair (wordEncoding q) (liftEncoding q)
  let p := encPair e (letterEncoding q)
  have hx := (fst (wordEncoding q) (liftEncoding q)).comp (fst e (letterEncoding q))
  have h := (symbol_polyTime pad).comp (encIn := p) (hx.prod (snd e (letterEncoding q)))
  exact mapWithInput (encIn := e) (encA := letterEncoding q) (encB := ExceptionalRecords.letterEncoding q)
    (f := fun x a => symbol pad x.1 a) (snd (wordEncoding q) (liftEncoding q))
    (h.of_enc_eq (fun _ => rfl))

theorem original_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : ℕ × ℕ => original q x.1 x.2)
      (encPair encUnary encUnary) (liftEncoding q) := by
  let e := encPair encUnary encUnary
  have ha := (fst encUnary encUnary).comp (fst e encUnary)
  have hi := snd e encUnary
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := letterEncoding q)
    (f := fun x i => (x.1+i,(none : Option (ℕ × Fin q)))) (unary_range' (snd encUnary encUnary))
    ((unary_add' ha hi).prod (const none))

abbrev windowEncoding (q : ℕ) := encPair (liftEncoding q) (encPair encUnary encUnary)

theorem window_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : LiftData q × (ℕ × ℕ) => window x.1 x.2.1 x.2.2)
      (windowEncoding q) (liftEncoding q) := by
  have hw := fst (liftEncoding q) (encPair encUnary encUnary)
  have hi := snd (liftEncoding q) (encPair encUnary encUnary)
  exact listTakeWithInput (listDropWithInput hw hi.fst') hi.snd'

abbrev spliceEncoding (q : ℕ) := encPair (encPair encUnary encUnary) (encPair (liftEncoding q) (liftEncoding q))

theorem sharedAt_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × (LiftData q × LiftData q) =>
      sharedAt x.1.1 x.1.2 x.2.1 x.2.2) (spliceEncoding q) encBool := by
  let e := spliceEncoding q
  let p := encPair (liftEncoding q) (liftEncoding q)
  have hi := fst (encPair encUnary encUnary) p
  have hw := snd (encPair encUnary encUnary) p
  have hu := listGetDWithInput hw.fst' (unary_add' hi.fst' hi.snd') ((0,none) : LetterData q)
  have hv := listGetDWithInput hw.snd' hi.snd' ((0,none) : LetterData q)
  have h₁ := (position_polyTime q).comp (encIn := e) hu
  have h₂ := (position_polyTime q).comp (encIn := e) hv
  exact (bool_and' (optionIsSome h₁) (h₁.decide_eq' h₂)).of_enc_eq (fun _ => rfl)

theorem firstShared_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × (LiftData q × LiftData q) =>
      firstShared x.1.1 x.1.2 x.2.1 x.2.2) (spliceEncoding q) (encOption encUnary) := by
  let e := spliceEncoding q
  let r := encPair (liftEncoding q) (liftEncoding q)
  let p := encPair e encUnary
  have hx := fst e encUnary
  have hi := snd e encUnary
  have ha := ((fst (encPair encUnary encUnary) r).comp hx).fst'
  have hu := (snd (encPair encUnary encUnary) r).comp hx
  have hh := (sharedAt_polyTime q).comp (encIn := p) (encMid := e) ((ha.prod hi).prod hu)
  exact findWithInput (encIn := e) (encA := encUnary)
    (test := fun x i => sharedAt x.1.1 i x.2.1 x.2.2)
    (unary_range' (fst (encPair encUnary encUnary) r).snd') (hh.of_enc_eq (fun _ => rfl))

theorem sharedJoin_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × (LiftData q × LiftData q) =>
      sharedJoin x.1.1 x.1.2 x.2.1 x.2.2) (spliceEncoding q) (liftEncoding q) := by
  let e := spliceEncoding q
  let r := encPair (liftEncoding q) (liftEncoding q)
  have h := fst (encPair encUnary encUnary) r
  have hw := snd (encPair encUnary encUnary) r
  have hr := unary_range' (unary_add' h.fst' ((length_list (letterEncoding q)).comp hw.snd'))
  have hx := fst e encUnary
  have hi := snd e encUnary
  have ha := h.fst'.comp hx
  have hp := h.snd'.comp hx
  have hu := listGetDWithInput (hw.fst'.comp hx) hi ((0,none) : LetterData q)
  have hv := listGetDWithInput (hw.snd'.comp hx) (unary_sub' hi ha) ((0,none) : LetterData q)
  have hbody := (unary_le' hi (unary_add' ha hp)).ite' hu hv
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := letterEncoding q)
    (f := fun x i => if i ≤ x.1.1+x.1.2 then x.2.1.getD i (0,none)
      else x.2.2.getD (i-x.1.1) (0,none)) hr
    (hbody.of_enc_eq (fun _ => by simp [Function.comp_def]))

theorem splice_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × (LiftData q × LiftData q) =>
      splice x.1.1 x.1.2 x.2.1 x.2.2) (spliceEncoding q) (encOption (liftEncoding q)) := by
  let e := spliceEncoding q
  let r := encPair (liftEncoding q) (liftEncoding q)
  let p := encPair e encUnary
  have hx := fst e encUnary
  have hi := snd e encUnary
  have ha := ((fst (encPair encUnary encUnary) r).comp hx).fst'
  have hu := (snd (encPair encUnary encUnary) r).comp hx
  have hh := (sharedJoin_polyTime q).comp (encIn := p) (encMid := e) ((ha.prod hi).prod hu)
  exact optionMapWithInput (encA := e) (encB := encUnary) (encC := liftEncoding q)
    (f := fun x i => sharedJoin x.1.1 i x.2.1 x.2.2)
    (firstShared_polyTime q) (hh.of_enc_eq (fun _ => rfl))

abbrev appendEncoding (q : ℕ) := encPair encUnary (encPair (liftEncoding q) (liftEncoding q))

theorem appendWindow_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : ℕ × (LiftData q × LiftData q) => appendWindow x.2.1 x.1 x.2.2)
      (appendEncoding q) (encOption (liftEncoding q)) := by
  let e := appendEncoding q
  let r := encPair (liftEncoding q) (liftEncoding q)
  have hi := fst encUnary r
  have hs := snd encUnary r
  have hu := (length_list (letterEncoding q)).comp hs.fst'
  have hv := (length_list (letterEncoding q)).comp hs.snd'
  have hb := bool_and' (unary_le' hi hu) (unary_le' hu (unary_add' hi hv))
  have hh := (splice_polyTime q).comp (encIn := e) (encMid := spliceEncoding q)
    ((hi.prod (unary_sub' hu hi)).prod hs)
  exact (hb.ite' hh (const none)).of_enc_eq (fun _ => rfl)

theorem inserted_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : ℕ × QWord q => inserted pad x.1 x.2)
      (encPair encUnary (wordEncoding q)) (liftEncoding q) := by
  let e := encPair encUnary (wordEncoding q)
  have hi := (fst encUnary (wordEncoding q)).comp (fst e encUnary)
  have hj := snd e encUnary
  have hw := (snd encUnary (wordEncoding q)).comp (fst e encUnary)
  have ha := listGetDWithInput hw hj pad
  have hs := (optionSome (freshEncoding q)).comp (hj.prod ha)
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := letterEncoding q)
    (f := fun x j => (x.1,some (j,x.2.getD j pad)))
    (unary_range' ((length_list (ExceptionalRecords.letterEncoding q)).comp
      (snd encUnary (wordEncoding q)))) (hi.prod hs)

abbrev installEncoding (q : ℕ) := encPair (encPair encUnary (encPair encUnary encUnary))
  (encPair (liftEncoding q) (wordEncoding q))

theorem install_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : (ℕ × (ℕ × ℕ)) × (LiftData q × QWord q) =>
      install pad x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2) (installEncoding q) (liftEncoding q) := by
  let e := installEncoding q
  let p := encPair encUnary (encPair encUnary encUnary)
  let r := encPair (liftEncoding q) (wordEncoding q)
  have h := fst p r
  have hw := snd p r
  have hl := h.snd'.fst'
  have hd := h.snd'.snd'
  have hn := (length_list (letterEncoding q)).comp hw.fst'
  have hv := (length_list (ExceptionalRecords.letterEncoding q)).comp hw.snd'
  have hr := unary_range' (unary_add' (unary_add' hl hv) (unary_sub' hn (unary_add' hl hd)))
  have hx := fst e encUnary
  have hi := snd e encUnary
  have hl' := hl.comp hx
  have hv' := hv.comp hx
  have hu' := hd.comp hx
  have hleft := listGetDWithInput (hw.fst'.comp hx) hi ((0,none) : LetterData q)
  have hi' := unary_sub' hi hl'
  have hletter := listGetDWithInput (hw.snd'.comp hx) hi' pad
  have hmid := (h.fst'.comp hx).prod ((optionSome (freshEncoding q)).comp (hi'.prod hletter))
  have hright := listGetDWithInput (hw.fst'.comp hx) (unary_add' (unary_sub' hi hv') hu')
    ((0,none) : LetterData q)
  have hbody := (unary_lt' hi hl').ite' hleft ((unary_lt' hi (unary_add' hl' hv')).ite' hmid hright)
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := letterEncoding q) hr
    (hbody.of_enc_eq (g := fun x : ((ℕ × (ℕ × ℕ)) × (LiftData q × QWord q)) × ℕ =>
      if x.2 < x.1.1.2.1 then x.1.2.1.getD x.2 (0,none)
      else if x.2 < x.1.1.2.1+x.1.2.2.length then
        (x.1.1.1,some (x.2-x.1.1.2.1,x.1.2.2.getD (x.2-x.1.1.2.1) pad))
      else x.1.2.1.getD (x.2-x.1.2.2.length+x.1.1.2.2) (0,none)) (fun _ => by simp [Function.comp_def]))

#print axioms splice_eq
#print axioms appendWindow_eq
#print axioms appendWindow_polyTime
#print axioms install_eq
#print axioms install_polyTime

end DeletionCode.Explicit.Machine.SourceLetters
