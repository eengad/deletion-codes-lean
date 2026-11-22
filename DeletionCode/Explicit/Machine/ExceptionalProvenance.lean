import DeletionCode.Explicit.Machine.ExceptionalRecords

/-! Serialized provenance and checked execution of a chronological record. -/
namespace DeletionCode.Explicit.Machine.ExceptionalRecords

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Burst ExceptionalWeight

variable {q : ℕ}

def origin : Token ℓ q → Option ℕ := Sum.elim (some ∘ Fin.val) (fun _ => none)

abbrev symbolsEncoding : List (Option ℕ) ↪ List Bool := encList (encOption encUnary)

def originStep (es : List (Option ℕ)) (e : Edit (Fin q)) : List (Option ℕ) :=
  es.take e.pos ++ List.replicate e.replacement.length none ++ es.drop (e.pos+e.removed)

private theorem originStep_eq (e : Edit (Fin q)) (ws : List (Token ℓ q)) :
    originStep (ws.map origin) e = ((editTokens e).apply ws).map origin := by
  simp [originStep, origin, Edit.apply, editTokens, List.map_take, List.map_drop,
    Function.comp_def, List.map_const']

def localTokens (L : ℕ) (es : List (Option ℕ)) (e : Edit (Fin q)) : List (Option ℕ) :=
  (leftFlank L e.pos es ++ ((es.drop e.pos).take e.removed)) ++ rightFlank L e.pos e.removed es

private theorem localTokens_eq (L : ℕ) (e : Edit (Fin q)) (ws : List (Token ℓ q)) :
    localTokens L (ws.map origin) e =
      (((leftFlank L e.pos ws ++ (editTokens e).sourceBlock ws) ++
        rightFlank L e.pos e.removed ws)).map origin := by
  simp [localTokens, leftFlank, rightFlank, Edit.sourceBlock, editTokens,
    List.map_take, List.map_drop]

private theorem active_iff (L : ℕ) (i : Fin ℓ) (ws : List (Token ℓ q)) (e : Edit (Fin q)) :
    some i.val ∈ localTokens L (ws.map origin) e ↔ i ∈ active L ws e := by
  rw [localTokens_eq]
  unfold active
  simp only [List.mem_map, List.mem_toFinset, List.mem_filterMap]
  constructor <;> rintro ⟨a, ha, he⟩ <;> refine ⟨a, ha, ?_⟩
  · cases a <;> simp_all [origin, Function.comp_def, Fin.ext_iff]
  · cases a <;> simp_all [origin, Function.comp_def, Fin.ext_iff]

abbrev TraceInput (q : ℕ) := (ℕ × ℕ) × (ℕ × List (Edit (Fin q)))
abbrev traceEncoding (q : ℕ) := encPair (encPair encUnary encUnary) (encPair encUnary (recordEncoding q))

private def traceStep (par : ℕ × ℕ) (state : List (Option ℕ) × Bool) (e : Edit (Fin q)) :
    List (Option ℕ) × Bool :=
  (originStep state.1 e, state.2 || (localTokens par.1 state.1 e).contains (some par.2))

def readsPosition (x : TraceInput q) : Bool :=
  (x.2.2.foldl (traceStep x.1) (((List.range x.2.1).map some), false)).2

private theorem traceStep_spec (L : ℕ) (i : Fin ℓ) (ws : List (Token ℓ q))
    (seen : Bool) (es : List (Edit (Fin q))) :
    (es.foldl (traceStep (L, i.val)) (ws.map origin, seen)).2 = true ↔
      seen = true ∨ i ∈ touched L ws es := by
  induction es generalizing ws seen with
  | nil => simp [touched]
  | cons e es ih =>
    simp only [List.foldl_cons, traceStep, originStep_eq, ih, Bool.or_eq_true,
      List.contains_iff_mem, active_iff, touched, Finset.mem_union]
    tauto

theorem readsPosition_iff (L : ℕ) (i : Fin ℓ) (es : List (Edit (Fin q))) :
    readsPosition (q := q) ((L,i.val),(ℓ,es)) = true ↔
      i ∈ touched L (initialTokens ℓ q) es := by
  have hinit : (initialTokens ℓ q).map origin = (List.range ℓ).map some := by
    apply List.ext_getElem (by simp [initialTokens])
    intro j hj hj'
    simp [initialTokens, origin, Function.comp_def]
  unfold readsPosition
  rw [← hinit, traceStep_spec]
  simp

def supportPositions (x : (ℕ × ℕ) × List (Edit (Fin q))) : List ℕ :=
  (List.range x.1.2).filter (fun i => readsPosition ((x.1.1,i),(x.1.2,x.2)))

theorem supportPositions_eq (L ℓ : ℕ) (es : List (Edit (Fin q))) :
    supportPositions ((L,ℓ),es) = (supportList (touched L (initialTokens ℓ q) es)).map Fin.val := by
  unfold supportPositions supportList
  have he : (List.range ℓ) = (List.finRange ℓ).map Fin.val := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simp [List.getElem_finRange]
  rw [he, List.filter_map]
  apply congrArg (List.map Fin.val)
  congr 1
  funext i
  rw [Bool.eq_iff_iff, Function.comp_apply, readsPosition_iff, decide_eq_true_eq]

private theorem originStep_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : List (Option ℕ) × Edit (Fin q) => originStep x.1 x.2)
      (encPair symbolsEncoding (editEncoding q)) symbolsEncoding := by
  let enc := encOption encUnary
  have hw := fst symbolsEncoding (editEncoding q)
  have he := snd symbolsEncoding (editEncoding q)
  have hp := (pos_polyTime q).comp he
  have hd := (removed_polyTime q).comp he
  have ha := (length_list (letterEncoding q)).comp ((replacement_polyTime q).comp he)
  have hr := ComputableInPolyTime.replicate ha (const (encOut := enc) none)
  exact listAppend' (listAppend' ((takeUnary enc).comp (hw.prod hp)) hr)
    (listDropWithInput hw (unary_add' hp hd))

private theorem localTokens_polyTime (q : ℕ) :
    ComputableInPolyTime (fun p : (ℕ × List (Option ℕ)) × Edit (Fin q) =>
      localTokens p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary symbolsEncoding) (editEncoding q)) symbolsEncoding := by
  let e := encOption encUnary
  have hw := (fst (encPair encUnary symbolsEncoding) (editEncoding q)).snd'
  have hL := (fst (encPair encUnary symbolsEncoding) (editEncoding q)).fst'
  have he := snd (encPair encUnary symbolsEncoding) (editEncoding q)
  have hp := (pos_polyTime q).comp he
  have hd := (removed_polyTime q).comp he
  have hf := unary_sub' hL (const 1)
  have hleft := listDropWithInput ((takeUnary e).comp (hw.prod hp)) (unary_sub' hp hf)
  have hmid := (takeUnary e).comp ((listDropWithInput hw hp).prod hd)
  have hright := (takeUnary e).comp ((listDropWithInput hw (unary_add' hp hd)).prod hf)
  exact listAppend' (listAppend' hleft hmid) hright

private abbrev traceStateEncoding := encPair symbolsEncoding encBool

private theorem traceStep_polyTime (q : ℕ) :
    ComputableInPolyTime
      (fun x : ((ℕ × ℕ) × (List (Option ℕ) × Bool)) × Edit (Fin q) =>
        traceStep x.1.1 x.1.2 x.2)
      (encPair (encPair (encPair encUnary encUnary) traceStateEncoding) (editEncoding q))
      traceStateEncoding := by
  let src := encPair (encPair encUnary encUnary) traceStateEncoding
  have hp := fst src (editEncoding q)
  have he := snd src (editEncoding q)
  have hw := hp.snd'.fst'
  have hseen := hp.snd'.snd'
  have hl := hp.fst'.fst'
  have hi := (optionSome encUnary).comp hp.fst'.snd'
  have ht := (localTokens_polyTime q).comp ((hl.prod hw).prod he)
  exact ((originStep_polyTime q).comp (hw.prod he)).prod (bool_or' hseen (contains ht hi))

theorem encoded_append {α : Type} (e : α ↪ List Bool) (xs ys : List α) :
    (encList e (xs++ys)).length = (encList e xs).length+(encList e ys).length := by
  simp [length_encList, List.sum_append]

theorem encoded_sublist {α : Type} (e : α ↪ List Bool) {xs ys : List α} (h : List.Sublist xs ys) :
    (encList e xs).length ≤ (encList e ys).length := by
  simp only [length_encList]
  have hs {as bs : List ℕ} (hs : List.Sublist as bs) : as.sum ≤ bs.sum := by
    induction hs with
    | slnil => simp
    | cons _ _ ih => simp; omega
    | cons_cons _ _ ih => simp; omega
  exact hs (h.map (fun a => 2*(e a).length+1))

theorem encoded_cut {α : Type} (e : α ↪ List Bool) (xs : List α) (i d : ℕ) :
    (encList e (xs.take i)).length + (encList e (xs.drop (i+d))).length ≤
      (encList e xs).length := by
  rw [← encoded_append]
  exact encoded_sublist _ (by
    conv_rhs => rw [← List.take_append_drop i xs]
    exact (List.Sublist.refl _).append (List.drop_sublist_drop_left _ (by omega)))

private theorem traceStep_growth (par : ℕ × ℕ) (state : List (Option ℕ) × Bool)
    (e : Edit (Fin q)) :
    (traceStateEncoding (traceStep par state e)).length ≤
      (traceStateEncoding state).length + 2*e.replacement.length := by
  have hcut := encoded_cut (encOption encUnary) state.1 e.pos e.removed
  simp only [traceStateEncoding, length_encPair, traceStep, originStep, encoded_append,
    symbolsEncoding, encBool_apply, List.length_singleton]
  have hr (k : ℕ) :
      (encList (encOption encUnary) (List.replicate k none)).length = k := by
    simp [length_encList, List.map_replicate, encOption_none, List.sum_replicate]
  rw [hr]
  omega

theorem readsPosition_polyTime (q : ℕ) :
    ComputableInPolyTime (readsPosition (q := q)) (traceEncoding q) encBool := by
  let src := traceEncoding q
  have hp := fst (encPair encUnary encUnary) (encPair encUnary (recordEncoding q))
  have hx := snd (encPair encUnary encUnary) (encPair encUnary (recordEncoding q))
  have hl := range.comp hx.fst'
  have hw := (ComputableInPolyTime.map (optionSome encUnary)).comp hl
  have hinit := hw.prod (const (encOut := encBool) false)
  have h := foldlWith_of_bounded_growth hp hx.snd' hinit (traceStep_polyTime q)
    (growth := fun x : TraceInput q => 2*(recordEncoding q x.2.2).length)
    ((PolyBounded.const 2).mul hx.snd'.polyBounded_length) (fun x state e he => by
      have h₁ := length_le_encList_of_mem (editEncoding q) he
      have h₂ := length_le_encPair_right encUnary (encPair encUnary (wordEncoding q))
        (e.pos,e.removed,e.replacement)
      have h₃ := length_le_encPair_right encUnary (wordEncoding q) (e.removed,e.replacement)
      have h₄ : e.replacement.length ≤ (wordEncoding q e.replacement).length := by
        unfold wordEncoding
        exact SizedListEncoding.length_le (encA := letterEncoding q) (encL := encList (letterEncoding q)) e.replacement
      exact (traceStep_growth x.1 state e).trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (h₄.trans (h₃.trans (h₂.trans h₁)))) _))
  exact (snd symbolsEncoding encBool).comp h

set_option maxHeartbeats 3000000 in
theorem supportPositions_polyTime (q : ℕ) :
    ComputableInPolyTime (supportPositions (q := q))
      (encPair (encPair encUnary encUnary) (recordEncoding q)) (encList encUnary) := by
  let src := encPair (encPair encUnary encUnary) (recordEncoding q)
  have hp := fst (encPair encUnary encUnary) (recordEncoding q)
  have he := snd (encPair encUnary encUnary) (recordEncoding q)
  have harg := fst src encUnary
  have hread : ComputableInPolyTime
      (fun x : ((ℕ × ℕ) × List (Edit (Fin q))) × ℕ =>
        readsPosition ((x.1.1.1,x.2),(x.1.1.2,x.1.2))) (encPair src encUnary) encBool :=
    (readsPosition_polyTime q).comp (((hp.fst'.comp harg).prod (snd src encUnary)).prod
      ((hp.snd'.comp harg).prod (he.comp harg)))
  unfold supportPositions
  have hrange : ComputableInPolyTime
      (fun x : (ℕ × ℕ) × List (Edit (Fin q)) => List.range x.1.2) src (encList encUnary) :=
    range.comp hp.snd'
  exact filterWithInput (encA := encUnary) (encIn := src)
    (test := fun x i => readsPosition ((x.1.1,i),(x.1.2,x.2))) hrange hread

private def runStep (b : ℕ) (state : Option (QWord q)) (e : Edit (Fin q)) : Option (QWord q) :=
  state.bind (fun w => if validEdit b e w then some (e.apply w) else none)

private theorem validRun_fold (b : ℕ) (w : QWord q) (es : List (Edit (Fin q))) :
    validRun b w es = es.foldl (runStep b) (some w) := by
  have hnone : ∀ es : List (Edit (Fin q)), es.foldl (runStep b) none = none := by
    intro es
    induction es with
    | nil => rfl
    | cons e es ih => exact ih
  induction es generalizing w with
  | nil => rfl
  | cons e es ih =>
    simp only [validRun, List.foldl_cons, runStep, Option.bind_some]
    split <;> simp [ih, hnone]

private theorem runStep_polyTime (q b : ℕ) :
    ComputableInPolyTime (fun x : Option (QWord q) × Edit (Fin q) => runStep b x.1 x.2)
      (encPair (encOption (wordEncoding q)) (editEncoding q)) (encOption (wordEncoding q)) := by
  let src := encPair (encOption (wordEncoding q)) (editEncoding q)
  have harg := ((snd _ (editEncoding q)).comp (fst src (wordEncoding q))).prod
    (snd src (wordEncoding q))
  have hc := ite ((validEdit_polyTime q b).comp harg)
    ((optionSome (wordEncoding q)).comp ((apply_polyTime q).comp harg)) (const none)
  have h := optionElimWithInput (body := fun x w => if validEdit b x.2 w then some (x.2.apply w) else none)
    (fst _ (editEncoding q)) (const none) hc
  exact h.of_enc_eq (fun x => by rcases x with ⟨_ | w, e⟩ <;> rfl)

set_option maxHeartbeats 800000 in
theorem validRun_polyTime (q b : ℕ) :
    ComputableInPolyTime (fun x : QWord q × List (Edit (Fin q)) => validRun b x.1 x.2)
      (encPair (wordEncoding q) (recordEncoding q)) (encOption (wordEncoding q)) := by
  have hw := fst (wordEncoding q) (recordEncoding q)
  have he := snd (wordEncoding q) (recordEncoding q)
  have hinit := (optionSome (wordEncoding q)).comp hw
  have h := foldl_of_bounded_growth he hinit (runStep_polyTime q b)
    (growth := (2*q+1)*b) (fun state e => by
      cases state with
      | none => simp [runStep]
      | some w =>
        unfold runStep
        simp only [Option.bind_some]
        split
        · rename_i hvalid
          have hb := ((validEdit_iff ..).mp hvalid).1.2
          have hcut := encoded_cut (letterEncoding q) w e.pos e.removed
          have hgain := (encoded_word_length_le e.replacement).trans (Nat.mul_le_mul_left _ hb)
          simp only [encOption_some, List.length_cons, Edit.apply]
          change (encList (letterEncoding q) (_ ++ _ ++ _)).length + 1 ≤ _
          simp only [encoded_append]
          change (encList (letterEncoding q) (w.take e.pos)).length +
            (wordEncoding q e.replacement).length +
            (encList (letterEncoding q) (w.drop (e.pos+e.removed))).length + 1 ≤
            (encList (letterEncoding q) w).length + 1 + (2*q+1)*b
          omega
        · simp only [encOption_none, List.length_nil, Nat.zero_le])
  exact h.of_enc_eq (fun x => congrArg _ (validRun_fold b x.1 x.2))

#print axioms supportPositions_eq
#print axioms supportPositions_polyTime
#print axioms validRun_polyTime

end DeletionCode.Explicit.Machine.ExceptionalRecords
