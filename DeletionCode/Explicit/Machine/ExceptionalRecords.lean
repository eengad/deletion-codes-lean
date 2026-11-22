import DeletionCode.Explicit.ExceptionalCatalogue
import DeletionCode.Explicit.Machine.WordEnumeration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership

/-! Machines for chronological records, word edits and provenance lists. -/
namespace DeletionCode.Explicit.Machine.ExceptionalRecords

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Burst ExceptionalWeight

abbrev letterEncoding (q : ℕ) : Fin q ↪ List Bool :=
  ⟨fun a => encUnary a.val, fun _ _ h => Fin.ext (encUnary.injective h)⟩

private abbrev editFields (q : ℕ) := encPair encUnary (encPair encUnary (wordEncoding q))

def editEncoding (q : ℕ) : Edit (Fin q) ↪ List Bool :=
  ⟨fun e => editFields q (e.pos,e.removed,e.replacement), by
    intro a b h
    have := (editFields q).injective h
    cases a
    cases b
    simpa using this⟩

abbrev recordEncoding (q : ℕ) := encList (editEncoding q)

@[fun_prop] theorem fields_polyTime (q : ℕ) :
    ComputableInPolyTime (fun e : Edit (Fin q) => (e.pos,e.removed,e.replacement))
      (editEncoding q) (editFields q) := of_eq (fun _ => rfl)

@[fun_prop] theorem mkEdit_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : ℕ × (ℕ × QWord q) => Edit.mk x.1 x.2.1 x.2.2)
      (editFields q) (editEncoding q) := of_eq (fun _ => rfl)

@[fun_prop] theorem pos_polyTime (q : ℕ) :
    ComputableInPolyTime (Edit.pos (α := Fin q)) (editEncoding q) encUnary :=
  (fst encUnary _).comp (fields_polyTime q)

@[fun_prop] theorem removed_polyTime (q : ℕ) :
    ComputableInPolyTime (Edit.removed (α := Fin q)) (editEncoding q) encUnary :=
  (snd encUnary _).fst'.comp (fields_polyTime q)

@[fun_prop] theorem replacement_polyTime (q : ℕ) :
    ComputableInPolyTime (Edit.replacement (α := Fin q)) (editEncoding q) (wordEncoding q) :=
  (snd encUnary _).snd'.comp (fields_polyTime q)

theorem tuples_polyTime {α : Type} (enc : α ↪ List Bool) (r : ℕ) :
    ComputableInPolyTime (fun xs => tuples xs r) (encList enc) (encList (encList enc)) := by
  induction r with
  | zero => exact const [[]]
  | succ r ih =>
    change ComputableInPolyTime (fun xs : List α => xs.flatMap fun x =>
      (tuples xs r).map (x :: ·)) (encList enc) (encList (encList enc))
    apply flatMapWithInput (f := fun xs x => (tuples xs r).map (x :: ·)) id'
    have hx := snd (encList enc) enc
    exact mapWithInput (f := fun p ys => p.2 :: ys) (ih.comp (fst _ _))
      (cons' (hx.comp (fst _ _)) (snd _ _))

theorem choices_polyTime (q b : ℕ) :
    ComputableInPolyTime (choices q b) encUnary (encList (editEncoding q)) := by
  unfold choices
  apply flatMapWithInput (f := fun _ j => (payloads q b).map (op j)) range
  apply mapConst
  intro p _
  have hi := snd encUnary encUnary
  exact (mkEdit_polyTime q).comp (hi.prod (const p))

private def separationScan (x : (ℕ × ℕ) × List (Edit (Fin q))) : Bool :=
  let ps := x.2.map Edit.pos
  let (l,d) := x.1
  (ps.all fun j => decide (d ≤ j) && decide (j+d ≤ l)) &&
    (List.range ps.length).all fun i => (List.range ps.length).all fun j =>
      decide (i = j) || decide (d ≤ Nat.dist (ps.getD i 0) (ps.getD j 0))

private theorem separationScan_eq (x : (ℕ × ℕ) × List (Edit (Fin q))) :
    separationScan x = separation x.1.1 x.1.2 x.2 := by
  rw [Bool.eq_iff_iff, separation_eq_true]
  simp only [separationScan, Bool.and_eq_true, List.all_eq_true, List.mem_map, List.mem_range,
    List.length_map, Bool.or_eq_true, decide_eq_true_eq, Separated, PositionsSeparated]
  constructor
  · rintro ⟨hbd,hpair⟩
    refine ⟨fun i => hbd _ ⟨x.2[i], List.getElem_mem i.isLt, rfl⟩, ?_⟩
    intro i j hj
    have h := hpair i.val i.isLt j.val j.isLt
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_map, List.getElem?_eq_getElem i.isLt, List.getElem?_eq_getElem j.isLt] at h
    exact h.resolve_left (fun he => hj (Fin.ext he))
  · rintro ⟨hbd,hpair⟩
    refine ⟨?_, ?_⟩
    · rintro j ⟨e,he,rfl⟩
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp he
      exact hbd ⟨i,hi⟩
    · intro i hi j hj
      by_cases he : i = j
      · exact Or.inl he
      · apply Or.inr
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
        exact hpair ⟨i,hi⟩ ⟨j,hj⟩ (fun h => he (congrArg Fin.val h))

private abbrev separationEncoding (q : ℕ) := encPair (encPair encUnary encUnary) (recordEncoding q)

private theorem separationScan_polyTime (q : ℕ) :
    ComputableInPolyTime (separationScan (q := q)) (separationEncoding q) encBool := by
  let src := separationEncoding q
  have hls := (fst (encPair encUnary encUnary) (recordEncoding q)).fst'
  have hd := (fst (encPair encUnary encUnary) (recordEncoding q)).snd'
  have hs := (ComputableInPolyTime.map (pos_polyTime q)).comp
    (snd (encPair encUnary encUnary) (recordEncoding q))
  have hbd := allWithInput
    (test := fun x j => decide (x.1.2 ≤ j) && decide (j+x.1.2 ≤ x.1.1)) hs (by
      have hj := snd src encUnary
      have hx := fst src encUnary
      exact bool_and' (unary_le' (hd.comp hx) hj)
        (unary_le' (unary_add' hj (hd.comp hx)) (hls.comp hx)))
  have hr := range.comp ((length_list encUnary).comp hs)
  have hpair := allWithInput
    (test := fun x i => (List.range x.2.length).all fun j =>
      decide (i = j) || decide (x.1.2 ≤ Nat.dist ((x.2.map Edit.pos).getD i 0)
        ((x.2.map Edit.pos).getD j 0))) hr (by
      let arg := encPair src encUnary
      apply allWithInput (list := fun x : ((ℕ × ℕ) × List (Edit (Fin q))) × ℕ => List.range x.1.2.length)
        (test := fun x j => decide (x.2 = j) ||
        decide (x.1.1.2 ≤ Nat.dist ((x.1.2.map Edit.pos).getD x.2 0) ((x.1.2.map Edit.pos).getD j 0)))
      · exact (range.comp ((length_list (editEncoding q)).comp (snd _ _))).comp (fst src encUnary)
      · have hx := (fst src encUnary).comp (fst arg encUnary)
        have hi := (snd src encUnary).comp (fst arg encUnary)
        have hj := snd arg encUnary
        have hps := hs.comp hx
        have ha := listGetDWithInput hps hi 0
        have hb := listGetDWithInput hps hj 0
        exact bool_or' (hi.decide_eq' hj) (unary_le' (hd.comp hx)
          (unary_add' (unary_sub' ha hb) (unary_sub' hb ha))))
  exact bool_and' hbd (hpair.of_enc_eq (fun x => by simp))

theorem separation_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × List (Edit (Fin q)) => separation x.1.1 x.1.2 x.2)
      (separationEncoding q) encBool :=
  (separationScan_polyTime q).of_enc_eq (fun x => congrArg encBool (separationScan_eq x).symm)

theorem chronological_polyTime (q b t : ℕ) :
    ComputableInPolyTime (fun x : ℕ × ℕ => chronological q b t x.1 x.2)
      (encPair encUnary encUnary) (encList (recordEncoding q)) := by
  let src := encPair encUnary encUnary
  have hL := fst encUnary encUnary
  have hl := snd encUnary encUnary
  have hc := (choices_polyTime q b).comp (unary_add' hl (const (2*t*b+1)))
  have hall := flatMapConst (encB := recordEncoding q) (List.range (2*t))
    (fun r _ => (tuples_polyTime (editEncoding q) (r+1)).comp hc)
  have htest : ComputableInPolyTime
      (fun x : (ℕ × ℕ) × List (Edit (Fin q)) =>
        decide (x.2.length < 2*t) || !separation x.1.2 (8*(x.1.1+t*b)) x.2)
      (encPair src (recordEncoding q)) encBool := by
    have hdata := fst src (recordEncoding q)
    have hes := snd src (recordEncoding q)
    have hD := unary_mul' (const 8) (unary_add' (hL.comp hdata) (const (t*b)))
    exact bool_or' (unary_lt' ((length_list (editEncoding q)).comp hes) (const (2*t)))
      (bool_not.comp ((separation_polyTime q).comp (((hl.comp hdata).prod hD).prod hes)))
  exact filterWithInput (test := fun x es =>
    decide (es.length < 2*t) || !separation x.2 (8*(x.1+t*b)) es) hall htest

@[fun_prop] theorem sourceBlock_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : Edit (Fin q) × QWord q => x.1.sourceBlock x.2)
      (encPair (editEncoding q) (wordEncoding q)) (wordEncoding q) := by
  have he := fst (editEncoding q) (wordEncoding q)
  have hw := snd (editEncoding q) (wordEncoding q)
  exact (takeUnary (letterEncoding q)).comp
    ((listDropWithInput hw ((pos_polyTime q).comp he)).prod ((removed_polyTime q).comp he))

@[fun_prop] theorem apply_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : Edit (Fin q) × QWord q => x.1.apply x.2)
      (encPair (editEncoding q) (wordEncoding q)) (wordEncoding q) := by
  have he := fst (editEncoding q) (wordEncoding q)
  have hw := snd (editEncoding q) (wordEncoding q)
  have hp := (pos_polyTime q).comp he
  have hd := (removed_polyTime q).comp he
  have ha := (replacement_polyTime q).comp he
  have hpre := (takeUnary (letterEncoding q)).comp (hw.prod hp)
  exact listAppend' (listAppend' hpre ha) (listDropWithInput hw (unary_add' hp hd))

theorem validEdit_polyTime (q b : ℕ) :
    ComputableInPolyTime (fun x : Edit (Fin q) × QWord q => validEdit b x.1 x.2)
      (encPair (editEncoding q) (wordEncoding q)) encBool := by
  have he := fst (editEncoding q) (wordEncoding q)
  have hw := snd (editEncoding q) (wordEncoding q)
  have hp := (pos_polyTime q).comp he
  have hd := (removed_polyTime q).comp he
  have ha := (replacement_polyTime q).comp he
  have hlen := length_list (letterEncoding q)
  have h := bool_and' (unary_le' hd (const b))
    (bool_and' (unary_le' (hlen.comp ha) (const b))
      (bool_and' (unary_le' (unary_add' hp hd) (hlen.comp hw))
        (bool_not.comp ((sourceBlock_polyTime q).decide_eq' ha))))
  exact h

#print axioms chronological_polyTime
#print axioms apply_polyTime
#print axioms validEdit_polyTime

end DeletionCode.Explicit.Machine.ExceptionalRecords
