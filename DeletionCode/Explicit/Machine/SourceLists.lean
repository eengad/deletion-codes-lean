import DeletionCode.Explicit.Machine.SourcePatchTable

/-! List and option composition shared by the source interpreters. -/
namespace DeletionCode.Explicit.Machine.SourceLists

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {α β γ : Type} {ea : α ↪ List Bool} {eb : β ↪ List Bool} {ec : γ ↪ List Bool}

theorem optionToList_polyTime (ea : α ↪ List Bool) :
    ComputableInPolyTime (Option.toList (α := α)) (encOption ea) (encList ea) := by
  have h := optionElimWithInput (encA := encOption ea) (encB := ea)
    (encC := encList ea) (body := fun _ v => [v]) id' (const [])
    (cons' (snd (encOption ea) ea) (const []))
  exact h.of_enc_eq (fun x => by cases x <;> rfl)

theorem optionBindWithInput {p : α → Option β} {f : α → β → Option γ}
    (hp : ComputableInPolyTime p ea (encOption eb))
    (hf : ComputableInPolyTime (fun x : α × β => f x.1 x.2) (encPair ea eb) (encOption ec)) :
    ComputableInPolyTime (fun x => (p x).bind (f x)) ea (encOption ec) := by
  have h := optionElimWithInput (body := f) hp (const none) hf
  exact h.of_enc_eq (fun x => by cases p x <;> rfl)

def collect (xs : List (Option β)) : Option (List β) :=
  if xs.all Option.isSome then some (xs.flatMap Option.toList) else none

theorem collect_map (f : α → Option β) (xs : List α) :
    collect (xs.map f) = xs.mapM f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases h : f a with
    | none => simp [collect,h]
    | some b =>
      simp only [collect,List.map_cons,List.all_cons,h,Option.isSome_some,Bool.true_and,
        List.flatMap_cons,Option.toList_some,List.singleton_append,List.mapM_cons]
      rw [← ih]
      unfold collect
      split <;> rfl

private theorem collect_polyTime (eb : β ↪ List Bool) :
    ComputableInPolyTime (collect (β := β)) (encList (encOption eb)) (encOption (encList eb)) := by
  let e := encList (encOption eb)
  have h := allWithInput (encIn := e) (encA := encOption eb) (test := fun _ b => b.isSome)
    id' (optionIsSome (snd e (encOption eb)))
  have hf := flatMapWithInput (encIn := e) (encA := encOption eb) (encB := eb)
    (f := fun _ b => b.toList) id' ((optionToList_polyTime eb).comp (snd e (encOption eb)))
  exact (h.ite' ((optionSome (encList eb)).comp hf) (const none)).of_enc_eq (fun _ => rfl)

theorem mapMWithInput {ls : γ → List α} {f : γ → α → Option β}
    (hl : ComputableInPolyTime ls ec (encList ea))
    (hf : ComputableInPolyTime (fun x : γ × α => f x.1 x.2) (encPair ec ea) (encOption eb)) :
    ComputableInPolyTime (fun x => (ls x).mapM (f x)) ec (encOption (encList eb)) := by
  have h := (collect_polyTime eb).comp (encIn := ec) (encMid := encList (encOption eb))
    (mapWithInput (encIn := ec) (encA := ea) (encB := encOption eb) (f := f) hl hf)
  exact h.of_enc_eq (fun x => congrArg _ (collect_map (f x) (ls x)).symm)

theorem range_map_eq {k : ℕ} (f : ℕ → α) :
    (List.range k).map f = List.ofFn (fun i : Fin k => f i.val) := by
  have hr : List.range k = (List.finRange k).map Fin.val := by simp
  rw [hr,List.map_map]
  change (List.ofFn (fun i : Fin k => i)).map (f ∘ Fin.val) = _
  rw [List.map_ofFn]
  rfl

theorem findRange_first (p : ℕ → Bool) (n i : ℕ) (hi : i < n)
    (h : p i = true) (hmin : ∀ j < i, p j = false) :
    (List.range n).find? p = some i := by
  have hi' : i < (List.range n).length := by simpa using hi
  apply List.find?_eq_some_iff_append.mpr
  refine ⟨h,(List.range n).take i,(List.range n).drop (i+1),?_,?_⟩
  · have hh := List.take_append_drop i (List.range n)
    rw [List.drop_eq_getElem_cons hi',List.getElem_range] at hh
    exact hh.symm
  · intro j hj
    obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hj
    have hk' : k < i := by
      simpa [List.length_take,Nat.min_eq_left (Nat.le_of_lt hi)] using hk
    simpa [hmin k hk']

/-- Find an index by scanning only valid positions, retaining the first match. -/
theorem idxOf?_polyTime [DecidableEq α] [BEq α] [LawfulBEq α] (fallback : α) (ea : α ↪ List Bool) :
    ComputableInPolyTime (fun x : List α × α => x.1.idxOf? x.2)
      (encPair (encList ea) ea) (encOption encUnary) := by
  let e := encPair (encList ea) ea
  let a := encPair e encUnary
  have hx := fst (encList ea) ea
  have hy := snd (encList ea) ea
  have he := fst e encUnary
  have hi := snd e encUnary
  have ht := listGetDWithInput (hx.comp he) hi fallback
  have h := findWithInput (encIn := e) (encA := encUnary)
    (test := fun x i => decide (x.1.getD i fallback = x.2))
    (unary_range' ((length_list ea).comp hx)) (ht.decide_eq' (hy.comp he))
  refine h.of_enc_eq (g := fun x => x.1.idxOf? x.2) ?_
  intro x
  apply congrArg (encOption encUnary)
  cases h : x.1.idxOf? x.2 with
  | none =>
    symm
    apply List.find?_eq_none.mpr
    intro i hi
    have hb := List.mem_range.mp hi
    have hn := List.idxOf?_eq_none_iff.mp h
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hb,Option.getD_some]
    simp only [decide_eq_true_eq]
    intro hh
    have hi' : x.1[i] ∈ x.1 := List.getElem_mem hb
    exact hn (by simpa only [hh] using hi')
  | some i =>
    obtain ⟨hi,he,hm⟩ := List.idxOf?_eq_some_iff.mp h
    symm
    apply findRange_first _ _ _ hi
    · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,he]
    · intro j hj
      have hj' := hj.trans hi
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj',Option.getD_some]
      exact decide_eq_false_iff_not.mpr (hm j hj)

theorem getElem?_polyTime (fallback : α) (ea : α ↪ List Bool) :
    ComputableInPolyTime (fun x : List α × ℕ => x.1[x.2]?)
      (encPair (encList ea) encUnary) (encOption ea) := by
  have hl := fst (encList ea) encUnary
  have hi := snd (encList ea) encUnary
  have hn := (length_list ea).comp hl
  have hv := listGetDWithInput hl hi fallback
  refine ((unary_lt' hi hn).ite' ((optionSome ea).comp hv) (const none)).of_enc_eq ?_
  intro x
  by_cases h : x.2 < x.1.length
  · simp [Function.comp_def,h,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
  · simp [Function.comp_def,h,List.getElem?_eq_none (Nat.le_of_not_gt h)]

theorem idxOf_eq_getD {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
    (xs : List α) (a : α) : xs.idxOf a = (xs.idxOf? a).getD xs.length := by
  unfold List.idxOf?
  rw [List.findIdx?_eq_guard_findIdx_lt]
  by_cases h : a ∈ xs
  · have hi := List.idxOf_lt_length_of_mem h
    change xs.findIdx (· == a) < xs.length at hi
    simp [List.idxOf,Option.guard,hi]
  · have hi := mt List.idxOf_lt_length_iff.mp h
    change ¬xs.findIdx (· == a) < xs.length at hi
    simp [List.idxOf,Option.guard,hi]
    exact fun x hx ha => h (ha ▸ hx)

#print axioms getElem?_polyTime
#print axioms idxOf_eq_getD
#print axioms idxOf?_polyTime

end DeletionCode.Explicit.Machine.SourceLists
