import DeletionCode.Explicit.PatchIntervals
import DeletionCode.Explicit.Machine.FibreClosure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Prefix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import Batteries.Tactic.OpenPrivate

/-! The patch partition with unary endpoints and ordinary lists. -/
namespace DeletionCode.Explicit.Machine.PatchMerge

open LetterGraphCuts
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open private mergeLeft mergeSorted mergeSorted_partition from DeletionCode.Explicit.PatchIntervals

variable {ℓ : ℕ}

abbrev Interval := ℕ × ℕ
abbrev intervalEncoding := encPair encUnary encUnary
abbrev intervalsEncoding := encList intervalEncoding

def data (i : CreationInterval ℓ) : Interval := (i.first.val,i.last.val)

def hull (a b : Interval) : Interval := (min a.1 b.1,max a.2 b.2)

def isBefore (a b : Interval) : Bool := decide (b.1 < a.1)

def insert (a : Interval) (xs : List Interval) : List Interval :=
  xs.takeWhile (isBefore a) ++ a :: xs.dropWhile (isBefore a)

theorem insert_eq (a : Interval) (xs : List Interval) :
    insert a xs = List.orderedInsert (fun a b : Interval => a.1 ≤ b.1) a xs := by
  rw [List.orderedInsert_eq_take_drop]
  simp [insert,isBefore,Nat.not_le]
  rfl

def sort (xs : List Interval) : List Interval :=
  xs.reverse.foldl (fun s i => insert i s) []

theorem sort_eq (xs : List (CreationInterval ℓ)) :
    sort (xs.map data) = (xs.insertionSort (fun a b => a.first ≤ b.first)).map data := by
  simp only [sort,insert_eq,List.foldl_reverse,List.insertionSort]
  simpa [List.insertionSort] using
    (List.map_insertionSort (fun a b : CreationInterval ℓ => a.first ≤ b.first)
      (fun a b : Interval => a.1 ≤ b.1) data xs (by intro a _ b _; rfl)).symm

def mergeStep (s : Interval × List Interval) (j : Interval) : Interval × List Interval :=
  if s.2.isEmpty && decide (j.1 ≤ s.1.2) then (hull s.1 j,[])
  else (s.1,s.2 ++ [j])

def mergeHead (i : Interval) (xs : List Interval) : List Interval :=
  let s := xs.foldl mergeStep (i,[])
  s.1 :: s.2

private theorem fold_closed (i : Interval) (xs tail : List Interval) (h : tail ≠ []) :
    xs.foldl mergeStep (i,tail) = (i,tail++xs) := by
  induction xs generalizing tail with
  | nil => simp
  | cons j xs ih =>
    have hc : tail.isEmpty = false := List.isEmpty_eq_false_iff.mpr h
    simp only [List.foldl_cons,mergeStep,hc,Bool.false_and,Bool.false_eq_true,↓reduceIte]
    rw [ih (tail++[j]) (by simp)]
    simp

theorem mergeHead_eq (i : CreationInterval ℓ) (xs : List (CreationInterval ℓ)) :
    mergeHead (data i) (xs.map data) = (mergeLeft i xs).map data := by
  induction xs generalizing i with
  | nil => rfl
  | cons j xs ih =>
    by_cases h : j.first ≤ i.last
    · have hh : decide ((data j).1 ≤ (data i).2) = true := decide_eq_true h
      simp only [mergeHead,List.map_cons,List.foldl_cons,mergeStep,List.isEmpty_nil,Bool.true_and,
        hh,↓reduceIte,mergeLeft,h]
      exact ih (i.hull j)
    · have hh : decide ((data j).1 ≤ (data i).2) = false := decide_eq_false h
      simp only [mergeHead,List.map_cons,List.foldl_cons,mergeStep,List.isEmpty_nil,Bool.true_and,
        hh,Bool.false_eq_true,↓reduceIte,List.nil_append,mergeLeft,h]
      rw [fold_closed _ _ _ (by simp)]
      rfl

def merge (xs : List Interval) : List Interval :=
  xs.reverse.foldl (fun out i => mergeHead i out) []

private theorem merge_sorted_eq (xs : List (CreationInterval ℓ)) :
    merge (xs.map data) = (mergeSorted xs).map data := by
  simp only [merge,List.foldl_reverse,mergeSorted]
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.map_cons,List.foldr_cons,ih,mergeHead_eq]

def coalesce (xs : List Interval) : List Interval := merge (sort xs)

theorem coalesce_eq (xs : List (CreationInterval ℓ)) :
    coalesce (xs.map data) = (CreationInterval.coalesce xs).map data := by
  rw [coalesce,sort_eq,merge_sorted_eq]
  congr 1
  let ys := xs.insertionSort (fun a b => a.first ≤ b.first)
  have hs : ys.Pairwise (fun a b => a.first ≤ b.first) := by
    have ht : Std.Total (fun a b : CreationInterval ℓ => a.first ≤ b.first) :=
      ⟨fun _ _ => le_total _ _⟩
    have htr : IsTrans (CreationInterval ℓ) (fun a b : CreationInterval ℓ => a.first ≤ b.first) :=
      ⟨fun _ _ _ => le_trans⟩
    exact List.pairwise_insertionSort _ _
  have h := mergeSorted_partition hs
  have hc := CreationInterval.coalesce_partition xs
  have hp : List.Perm ys xs := List.perm_insertionSort _ _
  apply CreationInterval.eq_of_cover_both h.separated hc.separated
  · apply hc.finest _ h.separated
    intro i hi
    exact h.covers i (hp.mem_iff.mpr hi)
  · apply h.finest _ hc.separated
    intro i hi
    exact hc.covers i (hp.mem_iff.mp hi)

def contains (a b : Interval) : Bool := decide (a.1 ≤ b.1) && decide (b.2 ≤ a.2)

def locate (xs : List Interval) (i : Interval) : Option ℕ :=
  (List.range xs.length).find? (fun j => contains (xs.getD j (0,0)) i)

theorem locate_eq (xs : List (CreationInterval ℓ)) (i : CreationInterval ℓ) :
    locate (xs.map data) (data i) = (CreationInterval.locate xs i).map Fin.val := by
  unfold locate CreationInterval.locate
  rw [List.length_map,show List.range xs.length = (List.finRange xs.length).map Fin.val from by simp,List.find?_map]
  congr 1
  apply List.find?_congr
  intro j _
  have hj : j.val < (xs.map data).length := by simpa only [List.length_map] using j.isLt
  simp only [Function.comp_def,List.getD_eq_getElem _ _ hj,List.getElem_map,contains,
    data,CreationInterval.Contains]
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true_iff]
  constructor
  · rintro ⟨ha,hb⟩
    exact decide_eq_true ⟨of_decide_eq_true ha,of_decide_eq_true hb⟩
  · intro h
    obtain ⟨ha,hb⟩ := of_decide_eq_true h
    exact ⟨decide_eq_true ha,decide_eq_true hb⟩

theorem label_eq (xs : List (CreationInterval ℓ)) (i : CreationInterval ℓ) (hi : i ∈ xs) :
    locate (coalesce (xs.map data)) (data i) = some (CreationInterval.label xs i hi).val := by
  rw [coalesce_eq,locate_eq]
  have hs := CreationInterval.locate_isSome ((CreationInterval.coalesce_partition xs).covers i hi)
  exact (congrArg (Option.map Fin.val) (Option.some_get hs)).symm

abbrev insertEncoding := encPair intervalsEncoding intervalEncoding
abbrev mergeStateEncoding := encPair intervalEncoding intervalsEncoding

private theorem frame_size (i : Interval) :
    (frame (intervalEncoding i)).length = 4*i.1+2*i.2+3 := by
  simp only [length_frame,length_encPair,encUnary_apply,List.length_replicate]
  omega

private theorem append_size (xs ys : List Interval) :
    (intervalsEncoding (xs++ys)).length = (intervalsEncoding xs).length+(intervalsEncoding ys).length := by
  simp [intervalsEncoding,length_encList,List.sum_append]

private theorem cons_size (i : Interval) (xs : List Interval) :
    (intervalsEncoding (i::xs)).length = (frame (intervalEncoding i)).length+(intervalsEncoding xs).length := by
  simp only [intervalsEncoding,encList_cons,List.length_append]

private theorem insert_size (i : Interval) (xs : List Interval) :
    (intervalsEncoding (insert i xs)).length = (intervalsEncoding xs).length+(frame (intervalEncoding i)).length := by
  unfold insert
  rw [append_size,cons_size]
  have h := congrArg (fun z => (intervalsEncoding z).length)
    (List.takeWhile_append_dropWhile (p := isBefore i) (l := xs))
  rw [append_size] at h
  omega

private theorem mergeState_size (s : Interval × List Interval) :
    (mergeStateEncoding s).length = (intervalsEncoding (s.1::s.2)).length := by
  rw [cons_size,length_frame,length_encPair]

private theorem mergeStep_size (s : Interval × List Interval) (j : Interval) :
    (mergeStateEncoding (mergeStep s j)).length ≤
      (mergeStateEncoding s).length + (frame (intervalEncoding j)).length := by
  rcases s with ⟨i,rest⟩
  by_cases he : rest.isEmpty && decide (j.1 ≤ i.2)
  · simp only [mergeStep,he,↓reduceIte,mergeState_size,cons_size,frame_size,hull]
    have hmin := Nat.min_le_left i.1 j.1
    have hmax : max i.2 j.2 ≤ i.2+j.2 := max_le (Nat.le_add_right ..) (Nat.le_add_left ..)
    have hz : (intervalsEncoding []).length = 0 := rfl
    omega
  · have he' := Bool.eq_false_iff.mpr he
    simp only [mergeStep,he',Bool.false_eq_true,↓reduceIte,mergeState_size,cons_size,append_size,
      encList_nil,List.length_nil,add_zero]
    omega

private theorem mergeFold_size (s : Interval × List Interval) (xs : List Interval) :
    (mergeStateEncoding (xs.foldl mergeStep s)).length ≤
      (mergeStateEncoding s).length + (intervalsEncoding xs).length := by
  induction xs generalizing s with
  | nil => simp [intervalsEncoding]
  | cons j js ih =>
    rw [List.foldl_cons,cons_size]
    have h := ih (mergeStep s j)
    have hs := mergeStep_size s j
    omega

private theorem mergeHead_size (i : Interval) (xs : List Interval) :
    (intervalsEncoding (mergeHead i xs)).length ≤
      (intervalsEncoding xs).length + (frame (intervalEncoding i)).length := by
  have h := mergeFold_size (i,[]) xs
  rw [mergeState_size,mergeState_size] at h
  simpa [mergeHead,cons_size,intervalsEncoding,Nat.add_comm] using h

private theorem insert_polyTime :
    ComputableInPolyTime (fun x : List Interval × Interval => insert x.2 x.1)
      insertEncoding intervalsEncoding := by
  let e := insertEncoding
  let p := encPair e intervalEncoding
  have hxs := fst intervalsEncoding intervalEncoding
  have hi := snd intervalsEncoding intervalEncoding
  have hlt := unary_lt' (snd e intervalEncoding).fst' (hi.comp (fst e intervalEncoding)).fst'
  have hpre := takeWhileWithInput (enc := e) (encB := intervalEncoding)
    (pred := fun x j => isBefore x.2 j) hxs (hlt.of_enc_eq (fun _ => rfl))
  have hpost := dropWhileWithInput (enc := e) (encB := intervalEncoding)
    (pred := fun x j => isBefore x.2 j) hxs (hlt.of_enc_eq (fun _ => rfl))
  exact (listAppend' hpre (cons' hi hpost)).of_enc_eq (fun _ => rfl)

private theorem mergeStep_polyTime :
    ComputableInPolyTime (fun x : (Interval × List Interval) × Interval => mergeStep x.1 x.2)
      (encPair mergeStateEncoding intervalEncoding) mergeStateEncoding := by
  let e := encPair mergeStateEncoding intervalEncoding
  have hs := fst mergeStateEncoding intervalEncoding
  have hj := snd mergeStateEncoding intervalEncoding
  have hi := hs.fst'
  have hr := hs.snd'
  have hm := unary_min' hi.fst' hj.fst'
  have hM := unary_max' hi.snd' hj.snd'
  have hz := ((length_list intervalEncoding).comp hr).decide_eq' (const 0)
  have ht := bool_and' hz (unary_le' hj.fst' hi.snd')
  have h := ht.ite' ((hm.prod hM).prod (const []))
    (hi.prod (listAppend' hr (cons' hj (const []))))
  refine h.of_enc_eq ?_
  intro x
  simp only [mergeStep,Function.comp_def,List.length_eq_zero_iff]
  cases x.1.2 <;> rfl

private theorem mergeHead_polyTime :
    ComputableInPolyTime (fun x : List Interval × Interval => mergeHead x.2 x.1)
      insertEncoding intervalsEncoding := by
  let e := insertEncoding
  have hi := snd intervalsEncoding intervalEncoding
  have hx := fst intervalsEncoding intervalEncoding
  have hinit := hi.prod (const (encOut := intervalsEncoding) [])
  have hB := hinit.polyBounded_length.add hx.polyBounded_length
  have h := foldl' (encIn := e) (encA := intervalEncoding) (encB := mergeStateEncoding)
    (list := fun x => x.1) (init := fun x => (x.2,[])) (step := mergeStep)
    hx hinit mergeStep_polyTime hB (by
      intro x i _
      apply (mergeFold_size _ _).trans
      apply Nat.add_le_add_left
      exact length_encList_take_le intervalEncoding x.1 i)
  apply h.of_enc_eq
  intro x
  -- The accumulator encoding is the encoding of its head followed by its tail.
  rfl

private theorem foldIntervals_polyTime (step : Interval → List Interval → List Interval)
    (hs : ComputableInPolyTime (fun x : List Interval × Interval => step x.2 x.1)
      insertEncoding intervalsEncoding)
    (hstep : ∀ i xs, (intervalsEncoding (step i xs)).length ≤
      (intervalsEncoding xs).length + (frame (intervalEncoding i)).length) :
    ComputableInPolyTime (fun xs => xs.reverse.foldl (fun s i => step i s) [])
      intervalsEncoding intervalsEncoding := by
  let e := intervalsEncoding
  have h := foldlWith_of_bounded_growth (encB := e) (encL := e) (encA := intervalEncoding) (encP := encBool)
    (step := fun (_ : Bool) xs i => step i xs)
    (const false) (listReverse intervalEncoding) (const [])
    (hs.comp ((fst (encPair encBool e) intervalEncoding).snd'.prod (snd _ _)))
    (((PolyBounded.const 2).mul .self).add (.const 1))
    (by
      intro xs state i hi
      have hm := SizedListEncoding.length_elem_le (encL := e) (encA := intervalEncoding) xs i
        (List.mem_reverse.mp hi)
      have hf : (frame (intervalEncoding i)).length ≤ 2 * (e xs).length + 1 := by
        rw [length_frame]
        omega
      exact (hstep i state).trans (Nat.add_le_add_left hf _))
  exact h

theorem coalesce_polyTime : ComputableInPolyTime coalesce intervalsEncoding intervalsEncoding := by
  have hs := foldIntervals_polyTime insert insert_polyTime (fun i xs => (insert_size i xs).le)
  have hm := foldIntervals_polyTime mergeHead mergeHead_polyTime mergeHead_size
  exact hm.comp hs

abbrev locateEncoding := encPair intervalsEncoding intervalEncoding

theorem locate_polyTime :
    ComputableInPolyTime (fun x : List Interval × Interval => locate x.1 x.2)
      locateEncoding (encOption encUnary) := by
  let e := locateEncoding
  let p := encPair e encUnary
  have hs := fst intervalsEncoding intervalEncoding
  have hj := snd e encUnary
  have hi := (snd intervalsEncoding intervalEncoding).comp (fst e encUnary)
  have ha := listGetDWithInput (hs.comp (fst e encUnary)) hj (0,0)
  have h := bool_and' (unary_le' ha.fst' hi.fst') (unary_le' hi.snd' ha.snd')
  exact findWithInput (encIn := e) (encA := encUnary)
    (test := fun x j => contains (x.1.getD j (0,0)) x.2)
    (unary_range' ((length_list intervalEncoding).comp hs)) (h.of_enc_eq (fun _ => rfl))

#print axioms coalesce_eq
#print axioms coalesce_polyTime
#print axioms locate_eq
#print axioms locate_polyTime

end DeletionCode.Explicit.Machine.PatchMerge
