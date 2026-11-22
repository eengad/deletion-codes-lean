import DeletionCode.Explicit.LiftReplay

/-! Replay of one recorded bubble using only its patch anchor, earlier
lifts, and the symbols of its own replacement (`d:add-rule`, `d:grammar`). -/

namespace DeletionCode.Explicit.ReplayEntry

open LetterSequence
variable {ℓ : ℕ} {α : Type*}

inductive Side where
  | negative
  | positive
  deriving DecidableEq

inductive Reference where
  | source (delta : ℤ)
  | supplier (entry : ℕ) (side : Side) (offset : ℕ)
  deriving DecidableEq

structure Entry (α : Type*) where
  rule : ℕ
  patch : ℕ
  left : ℕ
  removed : List α
  replacement : List α
  right : ℕ
  references : List Reference

def Entry.negativeLength (e : Entry α) := e.left + e.removed.length + e.right

def Entry.positiveLength (e : Entry α) := e.left + e.replacement.length + e.right

abbrev StoredLift (ℓ : ℕ) (α : Type*) := (n : ℕ) × Lift ℓ n α

structure Completed (ℓ : ℕ) (α : Type*) where
  rule : ℕ
  negative : StoredLift ℓ α
  positive : StoredLift ℓ α

def Completed.lift (e : Completed ℓ α) : Side → StoredLift ℓ α
  | .negative => e.negative
  | .positive => e.positive

/-- The ordered offsets from `d:selected-offsets`, with repetitions removed. -/
def selectedStarts (L h : ℕ) : List ℕ :=
  let last := h-L
  if last = 0 then [0] else if last = 1 then [0,last] else [0,last/2,last]

theorem selectedStarts_mem {L h a : ℕ} :
    a ∈ selectedStarts L h ↔ a = 0 ∨ a = (h-L)/2 ∨ a = h-L := by
  unfold selectedStarts
  dsimp only
  split
  next he => simp [he]
  next hz =>
    split
    next he => simp [he]
    next ho => simp

theorem selectedStarts_last (L h : ℕ) : (selectedStarts L h).getLast? = some (h-L) := by
  unfold selectedStarts
  dsimp only
  split
  next he => simp [he]
  next =>
    split <;> rfl

/-- Consecutive selected windows have at most a half-span shift. Under the
manuscript's overlap bound each such pair has room for `minOverlap` letters. -/
theorem selectedStarts_overlap {L h minOverlap a b : ℕ}
    (hroom : (h-L+1)/2 + minOverlap ≤ L)
    (hm : (a,b) ∈ (selectedStarts L h).zip (selectedStarts L h).tail) :
    a < b ∧ b+minOverlap ≤ a+L := by
  by_cases hz : h-L = 0
  · simp [selectedStarts,hz] at hm
  · by_cases hone : h-L = 1
    · simp [selectedStarts,hone] at hm
      omega
    · simp [selectedStarts,hz,hone] at hm
      rcases hm with hm | hm <;> omega

/-- Decode a patch-relative source reference or copy a window of an earlier
bubble. Invalid ranges, missing anchors and entries, and references to the
same or a later rule fail. -/
def readReference (L current currentRule : ℕ) (anchor : Option (Fin ℓ))
    (get : ℕ → Option (Completed ℓ α)) : Reference → Option (Lift ℓ L α)
  | .source delta =>
    match anchor with
    | none => none
    | some root =>
      let start := (root.val : ℤ) + delta
      if 0 ≤ start then
        if h : start.toNat + L ≤ ℓ then some (sourceWindow start.toNat L h) else none
      else none
  | .supplier j side a => do
    if current ≤ j then none
    else
      let e ← get j
      if currentRule ≤ e.rule then none
      else
        let u := e.lift side
        if h : a+L ≤ u.1 then some (u.2.window a L h) else none

theorem read_source (L current rule : ℕ) (anchor : Fin ℓ) (get : ℕ → Option (Completed ℓ α))
    (delta : ℤ) (hs : 0 ≤ (anchor.val : ℤ)+delta)
    (hb : ((anchor.val : ℤ)+delta).toNat+L ≤ ℓ) :
    readReference L current rule (some anchor) get (.source delta) =
      some (sourceWindow ((anchor.val : ℤ)+delta).toNat L hb) := by
  simp [readReference,hs,hb]

theorem read_supplier (L current rule : ℕ) (anchor : Option (Fin ℓ)) (get : ℕ → Option (Completed ℓ α))
    {j a : ℕ} {side : Side} {e : Completed ℓ α} (hj : j < current) (he : get j = some e)
    (hr : e.rule < rule) (hw : a+L ≤ (e.lift side).1) :
    readReference L current rule anchor get (.supplier j side a) =
      some ((e.lift side).2.window a L hw) := by
  simp [readReference,not_le_of_gt hj,he,not_le_of_gt hr,hw]

theorem read_future (L current rule : ℕ) (anchor : Option (Fin ℓ)) (get : ℕ → Option (Completed ℓ α))
    {j a : ℕ} {side : Side} (hj : current ≤ j) :
    readReference L current rule anchor get (.supplier j side a) = none := by
  simp [readReference,hj]

/-- Rewrite a lift length along an arithmetic equality. -/
private def resize {m n : ℕ} (h : m = n) (u : Lift ℓ m α) : Lift ℓ n α :=
  h ▸ u

/-- Place the next window at `start` in the accumulated lift. The accumulated
lift begins at zero, and the new window must reach at least its old end. -/
def appendWindow {n L : ℕ} (u : Lift ℓ n α) (start : ℕ) (v : Lift ℓ L α) :
    Option (Lift ℓ (start+L) α) :=
  if h₁ : start ≤ n then
    if h₂ : n ≤ start+L then
      let overlap := n-start
      let added := start+L-n
      let u' := resize (m := n) (n := start+overlap) (by dsimp [overlap]; omega) u
      let v' := resize (m := L) (n := overlap+added) (by dsimp [overlap,added]; omega) v
      (splice u' v').map (resize (by dsimp [overlap,added]; omega))
    else none
  else none

private theorem resize_renameEntries {m n : ℕ} (h : m = n) (u : Lift ℓ m α) (f : ℕ → ℕ) :
    resize h (u.renameEntries f) = (resize h u).renameEntries f := by
  cases h
  rfl

theorem appendWindow_renameEntries {n L start : ℕ}
    {u : Lift ℓ n α} {v : Lift ℓ L α} {out : Lift ℓ (start+L) α}
    (f : ℕ → ℕ) (h : appendWindow u start v = some out) :
    appendWindow (u.renameEntries f) start (v.renameEntries f) =
      some (out.renameEntries f) := by
  by_cases hs : start ≤ n
  · by_cases he : n ≤ start+L
    · rw [appendWindow,dite_eq_left hs,dite_eq_left he] at h ⊢
      obtain ⟨w,hw,rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [resize_renameEntries,splice_renameEntries f hw,Option.map_some]
    · simp [appendWindow,hs,he] at h
  · simp [appendWindow,hs] at h

#print axioms appendWindow_renameEntries

private theorem resize_follows {m n : ℕ} (h : m = n) (u : Lift ℓ m α)
    (E : Letter ℓ α → Letter ℓ α → Prop) : (resize h u).Follows E ↔ u.Follows E := by
  cases h
  rfl

theorem appendWindow_follows {E : Letter ℓ α → Letter ℓ α → Prop} {n L start : ℕ}
    {u : Lift ℓ n α} {v : Lift ℓ L α} {out : Lift ℓ (start+L) α}
    (h : appendWindow u start v = some out) (hu : u.Follows E) (hv : v.Follows E) :
    out.Follows E := by
  by_cases hs : start ≤ n
  · by_cases he : n ≤ start+L
    · rw [appendWindow,dite_eq_left hs,dite_eq_left he,Option.map_eq_some_iff] at h
      obtain ⟨w,hw,rfl⟩ := h
      apply (resize_follows _ _ E).mpr
      exact splice_follows hw ((resize_follows _ _ E).mpr hu) ((resize_follows _ _ E).mpr hv)
    · simp [appendWindow,hs,he] at h
  · simp [appendWindow,hs] at h

#print axioms appendWindow_follows

private theorem resize_letters {m n : ℕ} (h : m = n) (u : Lift ℓ m α) (i : Fin n) :
    (resize h u).letters i = u.letters (Fin.cast h.symm i) := by
  cases h
  rfl

private theorem resize_fresh_count {m n : ℕ} (h : m = n) (u : Lift ℓ m α) :
    (resize h u).freshOffsets.card = u.freshOffsets.card := by
  cases h
  rfl

private theorem resize_omission_count {m n : ℕ} (h : m = n) (u : Lift ℓ m α) :
    (resize h u).omissions.card = u.omissions.card := by
  cases h
  rfl

/-- An accumulated lift and the next selected window can be spliced when
their common spelling has the manuscript's minimum overlap and both have
the required fresh and omission bounds. This applies also to the second
splice, with the first splice's result as the accumulated lift. -/
theorem appendWindow_isSome {x : Fin ℓ → α} {K Λ n L start : ℕ} (hx : Strong x K Λ)
    (u : Lift ℓ n α) (v : Lift ℓ L α) (hs : start ≤ n) (he : n ≤ start+L)
    (hk : K+2*Λ ≤ n-start)
    (hspell : ∀ i : Fin (n-start),
      u.spelling x ⟨start+i.val,by omega⟩ = v.spelling x ⟨i.val,by omega⟩)
    (huf : u.freshOffsets.card ≤ Λ) (hvf : v.freshOffsets.card ≤ Λ)
    (huo : u.omissions.card ≤ Λ) (hvo : v.omissions.card ≤ Λ) :
    (appendWindow u start v).isSome = true := by
  let u' := resize (n := start+(n-start)) (by omega) u
  let v' := resize (n := (n-start)+(start+L-n)) (by omega) v
  have hov : (u'.window start (n-start) (by omega)).spelling x =
      (v'.window 0 (n-start) (by omega)).spelling x := by
    funext i
    simpa only [u',v',Lift.spelling,Lift.window,resize_letters,Fin.cast_mk,Nat.zero_add] using hspell i
  have hjoin := splice_isSome hx u' v' hk hov
    (by simpa only [u',resize_fresh_count] using huf)
    (by simpa only [v',resize_fresh_count] using hvf)
    (by simpa only [u',resize_omission_count] using huo)
    (by simpa only [v',resize_omission_count] using hvo)
  rw [appendWindow,dite_eq_left hs,dite_eq_left he,Option.isSome_map]
  exact hjoin

#print axioms appendWindow_isSome

/-- A successful splice at a recorded offset spells both input words on
their placed intervals, provided that the input overlap spells the same word. -/
theorem appendWindow_spelling {x : Fin ℓ → α} {n L start : ℕ}
    {u : Lift ℓ n α} {v : Lift ℓ L α} {out : Lift ℓ (start+L) α}
    (hs : start ≤ n) (he : n ≤ start+L)
    (h : appendWindow u start v = some out)
    (hspell : ∀ i : Fin (n-start),
      u.spelling x ⟨start+i.val,by omega⟩ = v.spelling x ⟨i.val,by omega⟩) :
    (∀ i : Fin n, out.spelling x (Fin.castLE he i) = u.spelling x i) ∧
    (∀ i : Fin L, out.spelling x ⟨start+i.val,by omega⟩ = v.spelling x i) := by
  let u' := resize (n := start+(n-start)) (by omega) u
  let v' := resize (n := (n-start)+(start+L-n)) (by omega) v
  have hov : (u'.window start (n-start) (by omega)).spelling x =
      (v'.window 0 (n-start) (by omega)).spelling x := by
    funext i
    simpa only [u',v',Lift.spelling,Lift.window,resize_letters,Fin.cast_mk,Nat.zero_add] using hspell i
  rw [appendWindow,dite_eq_left hs,dite_eq_left he,Option.map_eq_some_iff] at h
  obtain ⟨w,hw,ho⟩ := h
  have hv : splice u' v' = some w := hw
  obtain ⟨hl,hr⟩ := splice_spelling hv x hov
  rw [← ho]
  constructor
  · intro i
    let j : Fin (start+(n-start)) := ⟨i.val,by omega⟩
    simpa only [j,u',Lift.spelling,resize_letters,Fin.cast,Fin.castLE,Fin.eta] using hl j
  · intro i
    let j : Fin ((n-start)+(start+L-n)) := ⟨i.val,by omega⟩
    simpa only [j,v',Lift.spelling,resize_letters,Fin.cast_mk,Fin.eta] using hr j

/-- Specialize splice existence to consecutive offsets in the manuscript's
selected-window list. The accumulated lift ends at the preceding offset plus
one window length. Its bounds must hold again after the first splice. -/
theorem selected_append_isSome {x : Fin ℓ → α} {K Λ L n a b : ℕ}
    (hx : Strong x K Λ)
    (hroom : (n-L+1)/2 + (K+2*Λ) ≤ L)
    (hm : (a,b) ∈ (selectedStarts L n).zip (selectedStarts L n).tail)
    (u : Lift ℓ (a+L) α) (v : Lift ℓ L α)
    (hspell : ∀ i : Fin (a+L-b), u.spelling x ⟨b+i.val,by omega⟩ =
        v.spelling x ⟨i.val,by
          have := (selectedStarts_overlap hroom hm).1
          omega⟩)
    (huf : u.freshOffsets.card ≤ Λ) (hvf : v.freshOffsets.card ≤ Λ)
    (huo : u.omissions.card ≤ Λ) (hvo : v.omissions.card ≤ Λ) :
    (appendWindow u b v).isSome = true := by
  obtain ⟨hab,ho⟩ := selectedStarts_overlap hroom hm
  exact appendWindow_isSome hx u v (by omega) (by omega) (by omega) hspell huf hvf huo hvo

#print axioms appendWindow_spelling
#print axioms selected_append_isSome

private def assemble {L : ℕ} (read : Reference → Option (Lift ℓ L α))
    (starts : List ℕ) (refs : List Reference) (acc : StoredLift ℓ α) :
    Option (StoredLift ℓ α) :=
  match starts, refs with
  | [], [] => some acc
  | a :: as, ref :: rs => do
    let w ← read ref
    let next ← appendWindow acc.2 a w
    assemble read as rs ⟨a+L,next⟩
  | _, _ => none

private def renameStored (f : ℕ → ℕ) (u : StoredLift ℓ α) : StoredLift ℓ α :=
  ⟨u.1,u.2.renameEntries f⟩

private theorem assemble_renameEntries {L : ℕ}
    (read read' : Reference → Option (Lift ℓ L α)) (f : ℕ → ℕ)
    (starts : List ℕ) (refs refs' : List Reference) (u out : StoredLift ℓ α)
    (h : assemble read starts refs u = some out)
    (hr : List.Forall₂ (fun r r' => read' r' = (read r).map (fun w => w.renameEntries f))
      refs refs') :
    assemble read' starts refs' (renameStored f u) = some (renameStored f out) := by
  induction hr generalizing starts u with
  | nil =>
    cases starts with
    | nil =>
      have he : u = out := Option.some.inj h
      exact congrArg (fun w => some (renameStored f w)) he
    | cons => simp [assemble] at h
  | @cons r r' refs refs' hf hr ih =>
    cases starts with
    | nil => simp [assemble] at h
    | cons a rest =>
      cases hread : read r with
      | none => simp [assemble,hread] at h
      | some w =>
        cases ha : appendWindow u.2 a w with
        | none => simp [assemble,hread,ha] at h
        | some next =>
          have hn : assemble read rest refs ⟨a+L,next⟩ = some out :=
            by simpa [assemble,hread,ha] using h
          have hrename := appendWindow_renameEntries f ha
          simpa [assemble,hf,hread,renameStored,hrename] using ih rest _ hn

theorem assemble_length {L : ℕ} (read : Reference → Option (Lift ℓ L α))
    (starts : List ℕ) (refs : List Reference) (u out : StoredLift ℓ α)
    (he : assemble read starts refs u = some out) :
    starts.length = refs.length ∧ out.1 = (starts.getLast?.map (·+L)).getD u.1 := by
  induction starts generalizing refs u with
  | nil =>
    cases refs with
    | nil => simp [assemble] at he; subst out; exact ⟨rfl,rfl⟩
    | cons => simp [assemble] at he
  | cons a as ih =>
    cases refs with
    | nil => simp [assemble] at he
    | cons ref rs =>
      cases hr : read ref with
      | none => simp [assemble,hr] at he
      | some w =>
        cases hs : appendWindow u.2 a w with
        | none => simp [assemble,hr,hs] at he
        | some next =>
          have hea : assemble read as rs ⟨a+L,next⟩ = some out := by simpa [assemble,hr,hs] using he
          obtain ⟨hlen,hout⟩ := ih rs _ hea
          refine ⟨by simp [hlen],?_⟩
          cases as <;> simpa [List.getLast?_cons] using hout

/-- The first reference is at offset zero. All further references are read
and placed at the remaining offsets in the selected-window order. -/
def negativeLift (L current : ℕ) (e : Entry α) (anchor : Option (Fin ℓ))
    (get : ℕ → Option (Completed ℓ α)) : Option (Lift ℓ e.negativeLength α) := do
  if L > e.negativeLength then none
  else
    match selectedStarts L e.negativeLength, e.references with
    | 0 :: as, first :: rest => do
      let read := readReference L current e.rule anchor get
      let initial ← read first
      let u ← assemble read as rest ⟨L, initial⟩
      if h : u.1 = e.negativeLength then some (resize h u.2) else none
    | _, _ => none

/-- Renumbering the window reads renumbers exactly the fresh identifiers
of the reconstructed negative lift. -/
theorem negativeLift_renameEntries {L current current' : ℕ}
    (e : Entry α) (refs : List Reference) (newRule : ℕ)
    (anchor : Option (Fin ℓ)) (get get' : ℕ → Option (Completed ℓ α))
    (f : ℕ → ℕ) {out : Lift ℓ e.negativeLength α}
    (h : negativeLift L current e anchor get = some out)
    (hr : List.Forall₂ (fun r r' =>
      readReference L current' newRule anchor get' r' =
        (readReference L current e.rule anchor get r).map (fun w => w.renameEntries f))
      e.references refs) :
    negativeLift L current' {e with rule := newRule, references := refs} anchor get' =
      some (out.renameEntries f) := by
  let run (len : ℕ) (read : Reference → Option (Lift ℓ L α)) (refs : List Reference) :
      Option (Lift ℓ len α) :=
    if L > len then none else
      match selectedStarts L len, refs with
      | 0 :: as, first :: rest => do
        let initial ← read first
        let u ← assemble read as rest ⟨L, initial⟩
        if h : u.1 = len then some (resize h u.2) else none
      | _, _ => none
  change run e.negativeLength (readReference L current e.rule anchor get) e.references =
    some out at h
  change run e.negativeLength (readReference L current' newRule anchor get') refs =
    some (out.renameEntries f)
  generalize e.negativeLength = len at out h ⊢
  generalize e.references = oldRefs at h hr
  generalize readReference L current e.rule anchor get = read at h hr
  generalize readReference L current' newRule anchor get' = read' at hr ⊢
  unfold run at h ⊢
  by_cases hn : L > len
  · simp [hn] at h
  · rw [ite_eq_right hn] at h ⊢
    generalize selectedStarts L len = starts at h ⊢
    cases hr with
    | nil => cases starts <;> simp at h
    | @cons r r' rs rs' he hr =>
      rcases starts with _ | ⟨a,as⟩
      · simp at h
      cases a with
      | succ => simp at h
      | zero =>
        cases hread : read r with
        | none => simp [hread] at h
        | some w =>
          cases ha : assemble read as rs ⟨L,w⟩ with
          | none => simp [hread,ha] at h
          | some joined =>
            have hw := assemble_renameEntries read read' f as rs rs' ⟨L,w⟩ joined ha hr
            change assemble read' as rs' ⟨L,w.renameEntries f⟩ = some (renameStored f joined) at hw
            by_cases hlen : joined.1 = len
            · have ho : resize hlen joined.2 = out := by simpa [hread,ha,hlen] using h
              have hr' : read' r' = some (w.renameEntries f) := by simpa [hread] using he
              simp [hr',hw,renameStored,hlen,← ho,resize_renameEntries]
            · simp [hread,ha,hlen] at h

#print axioms negativeLift_renameEntries

/-- The recorded negative lift and the gate determine both replayed lifts. -/
def completedOf (current : ℕ) (e : Entry α) (neg : Lift ℓ e.negativeLength α) : Completed ℓ α :=
  ⟨e.rule,⟨e.negativeLength,neg⟩,⟨e.positiveLength,
    neg.installGate (l := e.left) (u := e.removed.length) (r := e.right)
      current (fun i : Fin e.replacement.length => e.replacement[i])⟩⟩

/-- The evaluator reconstructs both symbolic lifts without querying source letters. -/
def evaluate (L current : ℕ) (anchors : ℕ → Option (Fin ℓ)) (get : ℕ → Option (Completed ℓ α))
    (e : Entry α) : Option (Completed ℓ α) := do
  let neg ← negativeLift L current e (anchors e.patch) get
  pure (completedOf current e neg)

theorem evaluate_lengths {L current : ℕ} {anchors : ℕ → Option (Fin ℓ)} {get : ℕ → Option (Completed ℓ α)}
    {e : Entry α} {out : Completed ℓ α} (h : evaluate L current anchors get e = some out) :
    out.rule = e.rule ∧ out.negative.1 = e.negativeLength ∧ out.positive.1 = e.positiveLength := by
  unfold evaluate at h
  cases he : negativeLift L current e (anchors e.patch) get with
  | none => simp [he] at h
  | some neg => simp [he] at h; subst out; exact ⟨rfl,rfl,rfl⟩

section ReferenceCount

variable {current : ℕ}

private theorem length_of_negative {anchors : Option (Fin ℓ)} {get : ℕ → Option (Completed ℓ α)}
    (e : Entry α) {neg : LetterSequence.Lift ℓ e.negativeLength α}
    (he : negativeLift L current e anchors get = some neg) :
    e.references.length = (selectedStarts L e.negativeLength).length := by
  unfold negativeLift at he
  split at he
  next => contradiction
  next _ =>
    generalize hstarts : selectedStarts L e.negativeLength = starts at he ⊢
    generalize hrefs : e.references = refs at he ⊢
    cases starts with
    | nil => contradiction
    | cons first rest =>
      cases first with
      | succ => contradiction
      | zero =>
        cases refs with
        | nil => contradiction
        | cons ref refs =>
          let read := readReference L current e.rule anchors get
          cases hread : read ref with
          | none =>
            change (read ref >>= _) = _ at he
            rw [hread] at he
            contradiction
          | some initial =>
            change (read ref >>= _) = _ at he
            rw [hread] at he
            cases hass : assemble read rest refs ⟨L,initial⟩ with
            | none => dsimp only [read] at hass; simp [hass] at he
            | some result =>
              simp only [List.length_cons,(assemble_length read _ _ _ _ hass).1]

theorem evaluate_reference_count {anchors : ℕ → Option (Fin ℓ)}
    {get : ℕ → Option (Completed ℓ α)} {e : Entry α} {u : Completed ℓ α}
    (h : evaluate L current anchors get e = some u) :
    e.references.length = (selectedStarts L e.negativeLength).length := by
  cases hneg : negativeLift L current e (anchors e.patch) get with
  | none => simp [evaluate,hneg] at h
  | some _ => exact length_of_negative e hneg

#print axioms evaluate_reference_count

end ReferenceCount

#print axioms selectedStarts_mem
#print axioms assemble_length
#print axioms evaluate_lengths

/-- Which earlier entries are named by the references, independent of the
orientation and offset of each read. -/
def Entry.suppliers (e : Entry α) : Finset ℕ :=
  (e.references.filterMap fun
    | .source _ => none
    | .supplier j _ _ => some j).toFinset

private theorem read_congr (L current rule : ℕ) (anchor : Option (Fin ℓ))
    (get get' : ℕ → Option (Completed ℓ α)) (ref : Reference)
    (h : ∀ j side a, ref = .supplier j side a → get j = get' j) :
    readReference L current rule anchor get ref = readReference L current rule anchor get' ref := by
  cases ref with
  | source => rfl
  | supplier j side a => simp [readReference,h j side a rfl]

private theorem assemble_congr {L : ℕ} (read read' : Reference → Option (Lift ℓ L α))
    (starts : List ℕ) (refs : List Reference) (u : StoredLift ℓ α)
    (h : ∀ ref ∈ refs, read ref = read' ref) :
    assemble read starts refs u = assemble read' starts refs u := by
  induction starts generalizing refs u with
  | nil => cases refs <;> rfl
  | cons a as ih =>
    cases refs with
    | nil => rfl
    | cons ref rs =>
      simp only [assemble,h _ (List.mem_cons_self ..)]
      cases he : read' ref with
      | none => rfl
      | some w =>
        cases hs : appendWindow u.2 a w with
        | none => simp [hs]
        | some v =>
          simpa [hs] using ih rs ⟨a+L,v⟩ (fun j hj => h j (List.mem_cons_of_mem _ hj))

private theorem assemble_reads_congr {L : ℕ} (read read' : Reference → Option (Lift ℓ L α))
    (starts : List ℕ) (refs refs' : List Reference) (u : StoredLift ℓ α)
    (h : List.Forall₂ (fun ref ref' => read ref = read' ref') refs refs') :
    assemble read starts refs u = assemble read' starts refs' u := by
  induction h generalizing starts u with
  | nil => cases starts <;> rfl
  | @cons ref ref' rs rs' he _ ih =>
    cases starts with
    | nil => rfl
    | cons a as =>
      simp only [assemble,he]
      cases hw : read' ref' with
      | none => rfl
      | some w =>
        cases hs : appendWindow u.2 a w with
        | none => simp [hs]
        | some next => simpa [hs] using ih as ⟨a+L,next⟩

/-- Changing the encoding of references preserves the negative lift when
each reference still reads the same symbolic window. -/
theorem negativeLift_reads_congr {L current : ℕ} (e : Entry α) (refs : List Reference)
    (anchor anchor' : Option (Fin ℓ)) (get : ℕ → Option (Completed ℓ α))
    (h : List.Forall₂
      (fun ref ref' => readReference L current e.rule anchor get ref =
        readReference L current e.rule anchor' get ref') e.references refs) :
    negativeLift L current e anchor get =
      negativeLift L current {e with references := refs} anchor' get := by
  let run (len : ℕ) (read : Reference → Option (Lift ℓ L α)) (refs : List Reference) :
      Option (Lift ℓ len α) :=
    if L > len then none else
      match selectedStarts L len, refs with
      | 0 :: as, first :: rest => do
        let initial ← read first
        let u ← assemble read as rest ⟨L, initial⟩
        if h : u.1 = len then some (resize h u.2) else none
      | _, _ => none
  change run e.negativeLength (readReference L current e.rule anchor get) e.references =
    run e.negativeLength (readReference L current e.rule anchor' get) refs
  generalize e.negativeLength = len
  generalize e.references = originalRefs at h ⊢
  generalize readReference L current e.rule anchor get = read at h ⊢
  generalize readReference L current e.rule anchor' get = read' at h ⊢
  unfold run
  by_cases hn : L > len
  · simp [hn]
  · rw [ite_eq_right hn,ite_eq_right hn]
    generalize hs : selectedStarts L len = starts
    cases h with
    | nil =>
      rcases starts with _ | ⟨a,as⟩
      · rfl
      cases a <;> rfl
    | @cons ref ref' rs rs' he hr =>
      rcases starts with _ | ⟨a,as⟩
      · rfl
      cases a with
      | succ => rfl
      | zero =>
        change (do let initial ← read ref
                   let u ← assemble read as rs ⟨L,initial⟩
                   if h : u.1 = len then some (resize h u.2) else none) =
          (do let initial ← read' ref'
              let u ← assemble read' as rs' ⟨L,initial⟩
              if h : u.1 = len then some (resize h u.2) else none)
        rw [he]
        cases hw : read' ref' with
        | none => rfl
        | some initial =>
          have hall := assemble_reads_congr read read' as rs rs' ⟨L,initial⟩ hr
          exact congrArg (fun w => w.bind fun u =>
            if h : u.1 = len then some (resize h u.2) else none) hall

/-- Recorded bubble replay depends on the earlier results of its named
suppliers alone. This is the locality required by backward slicing. -/
theorem evaluate_congr (L current : ℕ) (anchors : ℕ → Option (Fin ℓ))
    (get get' : ℕ → Option (Completed ℓ α)) (e : Entry α)
    (h : ∀ j ∈ e.suppliers, get j = get' j) :
    evaluate L current anchors get e = evaluate L current anchors get' e := by
  have heq (ref : Reference) (hm : ref ∈ e.references) :
      readReference L current e.rule (anchors e.patch) get ref =
      readReference L current e.rule (anchors e.patch) get' ref := by
    apply read_congr
    rintro j side a rfl
    apply h j
    simp only [Entry.suppliers,List.mem_toFinset,List.mem_filterMap]
    exact ⟨.supplier j side a,hm,rfl⟩
  suffices hn : negativeLift L current e (anchors e.patch) get =
      negativeLift L current e (anchors e.patch) get' by simp only [evaluate,hn]
  unfold negativeLift
  split
  next => rfl
  next =>
    generalize hs : selectedStarts L e.negativeLength = starts
    cases starts with
    | nil => rfl
    | cons a as =>
      cases a with
      | succ => rfl
      | zero =>
        cases hr : e.references with
        | nil => rfl
        | cons ref rs =>
          have hfirst : ref ∈ e.references := hr ▸ List.mem_cons_self ..
          have htail (j : Reference) (hm : j ∈ rs) : j ∈ e.references := by
            rw [hr]; exact List.mem_cons_of_mem _ hm
          simp only [heq ref hfirst]
          cases readReference L current e.rule (anchors e.patch) get' ref with
          | none => rfl
          | some initial =>
            have hall := assemble_congr
              (readReference L current e.rule (anchors e.patch) get)
              (readReference L current e.rule (anchors e.patch) get') as rs ⟨L,initial⟩
              (fun j hj => heq j (htail j hj))
            simp [hall]

/-- Replay entries in chronological order. A failed entry invalidates the
description. Successful output is indexed in the same order as the input. -/
def replay (L : ℕ) (anchors : ℕ → Option (Fin ℓ)) (entries : List (Entry α)) :
    Option (Array (Completed ℓ α)) :=
  entries.foldlM (fun done e => do
    let next ← evaluate L done.size anchors (fun j => done[j]?) e
    pure (done.push next)) #[]

private theorem replay_length_from (L : ℕ) (anchors : ℕ → Option (Fin ℓ))
    (entries : List (Entry α)) (initial output : Array (Completed ℓ α))
    (h : entries.foldlM (fun done e => do
      let next ← evaluate L done.size anchors (fun j => done[j]?) e
      pure (done.push next)) initial = some output) :
    output.size = initial.size + entries.length := by
  induction entries generalizing initial with
  | nil => simp at h; simp [← h]
  | cons e es ih =>
    cases he : evaluate L initial.size anchors (fun j => initial[j]?) e with
    | none => simp [he] at h
    | some next =>
      have step : es.foldlM (fun done e => do
        let next ← evaluate L done.size anchors (fun j => done[j]?) e
        pure (done.push next)) (initial.push next) = some output := by simpa [he] using h
      simpa [Nat.add_assoc, Nat.add_comm 1] using ih _ step

theorem replay_length (L : ℕ) (anchors : ℕ → Option (Fin ℓ)) (entries : List (Entry α))
    {out : Array (Completed ℓ α)} (h : replay L anchors entries = some out) :
    out.size = entries.length := by
  simpa using replay_length_from L anchors entries #[] out h

#print axioms evaluate_congr
#print axioms replay_length

/-- Interpret the two lengths at their recorded offsets. A valid splice
shares an original letter in the overlap and uses the earliest shared one. -/
def AppendSpec {n L : ℕ} (u : Lift ℓ n α) (start : ℕ) (v : Lift ℓ L α)
    (out : Lift ℓ (start+L) α) : Prop :=
  ∃ (_ : start ≤ n) (_ : n ≤ start+L),
    SpliceSpec (a := start) (k := n-start) (b := start+L-n)
      (resize (by omega) u) (resize (by omega) v) (resize (by omega) out)

private theorem resize_eq_iff {n m : ℕ} (h : n = m) (u : Lift ℓ n α) (v : Lift ℓ m α) :
    resize h u = v ↔ u = resize h.symm v := by
  cases h
  rfl

theorem appendWindow_eq_some_iff {n L : ℕ} {u : Lift ℓ n α} {start : ℕ}
    {v : Lift ℓ L α} {out : Lift ℓ (start+L) α} :
    appendWindow u start v = some out ↔ AppendSpec u start v out := by
  by_cases hs : start ≤ n
  · by_cases he : n ≤ start+L
    · unfold AppendSpec
      rw [appendWindow,dite_eq_left hs,dite_eq_left he]
      rw [Option.map_eq_some_iff]
      constructor
      · rintro ⟨w,hw,eq⟩
        have hw' := (resize_eq_iff _ _ _).mp eq
        exact ⟨hs,he,by simpa only [hw'] using splice_eq_some_iff.mp hw⟩
      · rintro ⟨_,_,h⟩
        exact ⟨_,splice_eq_some_iff.mpr h,(resize_eq_iff _ _ _).mpr rfl⟩
    · simp [appendWindow,AppendSpec,hs,he]
  · simp [appendWindow,AppendSpec,hs]

/-- A source reference records the signed difference from its patch anchor.
Reading it recovers the actual source window, including starts to the left. -/
theorem read_encoded_source (L current rule start : ℕ) (root : Fin ℓ)
    (get : ℕ → Option (Completed ℓ α)) (h : start+L ≤ ℓ) :
    readReference L current rule (some root) get (.source ((start : ℤ)-(root.val : ℤ))) =
      some (sourceWindow start L h) := by
  have eq : (root.val : ℤ)+((start : ℤ)-(root.val : ℤ)) = (start : ℤ) := by omega
  simp [readReference,eq,h]

/-- The geometric read specified by each kind of reference. The coordinate
and orientation of a supplier refer to the stored chronological history. -/
inductive Reads (L current rule : ℕ) (anchor : Option (Fin ℓ))
    (get : ℕ → Option (Completed ℓ α)) :
    Reference → Lift ℓ L α → Prop where
  | source (root : Fin ℓ) (delta : ℤ) (ha : anchor = some root)
      (hs : 0 ≤ (root.val : ℤ)+delta) (hb : ((root.val : ℤ)+delta).toNat+L ≤ ℓ) :
      Reads L current rule anchor get (.source delta) (sourceWindow ((root.val : ℤ)+delta).toNat L hb)
  | supplier (j : ℕ) (side : Side) (a : ℕ) (e : Completed ℓ α)
      (hj : j < current) (he : get j = some e) (hr : e.rule < rule)
      (hw : a+L ≤ (e.lift side).1) :
      Reads L current rule anchor get (.supplier j side a) ((e.lift side).2.window a L hw)

theorem read_of_reads {L current rule : ℕ} {anchor : Option (Fin ℓ)}
    {get : ℕ → Option (Completed ℓ α)} {ref : Reference} {u : Lift ℓ L α}
    (h : Reads L current rule anchor get ref u) :
    readReference L current rule anchor get ref = some u := by
  cases h with
  | source root delta ha hs hb => rw [ha]; exact read_source L current rule root get delta hs hb
  | supplier j side a e hj he hr hw => exact read_supplier L current rule anchor get hj he hr hw

/-- A witness for the ordered splices, including every intermediate lift.
The relation refers to the least-shared-letter rule and concrete windows. -/
inductive WindowTrace {L : ℕ} (read : Reference → Lift ℓ L α → Prop) :
    List ℕ → List Reference → StoredLift ℓ α → StoredLift ℓ α → Prop where
  | done (u : StoredLift ℓ α) : WindowTrace read [] [] u u
  | step {start : ℕ} {starts : List ℕ} {ref : Reference} {refs : List Reference}
      {u out : StoredLift ℓ α} {v : Lift ℓ L α} {w : Lift ℓ (start+L) α}
      (hv : read ref v) (hw : AppendSpec u.2 start v w)
      (tail : WindowTrace read starts refs ⟨start+L,w⟩ out) :
      WindowTrace read (start::starts) (ref::refs) u out

private theorem assemble_of_trace {L current rule : ℕ} {anchor : Option (Fin ℓ)}
    {get : ℕ → Option (Completed ℓ α)} {starts : List ℕ} {refs : List Reference}
    {u out : StoredLift ℓ α}
    (h : WindowTrace (Reads L current rule anchor get) starts refs u out) :
    assemble (readReference L current rule anchor get) starts refs u = some out := by
  induction h with
  | done => rfl
  | step hv hw tail ih =>
    simpa [assemble,read_of_reads hv,appendWindow_eq_some_iff.mpr hw] using ih

/-- A certificate describes the negative lift of one recorded bubble using a
source or supplier read for each selected window, followed by its splices. -/
def Recorded (L current : ℕ) (anchor : Option (Fin ℓ)) (get : ℕ → Option (Completed ℓ α))
    (e : Entry α) (neg : Lift ℓ e.negativeLength α) : Prop :=
  L ≤ e.negativeLength ∧
    ∃ starts first refs initial,
      selectedStarts L e.negativeLength = 0 :: starts ∧
      e.references = first :: refs ∧
      Reads L current e.rule anchor get first initial ∧
      WindowTrace (Reads L current e.rule anchor get) starts refs ⟨L,initial⟩ ⟨e.negativeLength,neg⟩

theorem negativeLift_of_recorded {L current : ℕ} {anchor : Option (Fin ℓ)}
    {get : ℕ → Option (Completed ℓ α)} {e : Entry α} {neg : Lift ℓ e.negativeLength α}
    (h : Recorded L current anchor get e neg) :
    negativeLift L current e anchor get = some neg := by
  obtain ⟨hlen,starts,first,refs,initial,hstarts,hrefs,hread,hsplices⟩ := h
  simp [negativeLift,not_lt_of_ge hlen,hstarts,hrefs,read_of_reads hread,assemble_of_trace hsplices,resize]

theorem evaluate_of_recorded {L current : ℕ} {anchors : ℕ → Option (Fin ℓ)}
    {get : ℕ → Option (Completed ℓ α)} {e : Entry α} {neg : Lift ℓ e.negativeLength α}
    (h : Recorded L current (anchors e.patch) get e neg) :
    evaluate L current anchors get e = some (completedOf current e neg) := by
  simp [evaluate,negativeLift_of_recorded h,completedOf]

/-- Each entry is certified against just the bubbles already accumulated.
The same rule labels, negative lifts and gate outputs appear in replay. -/
inductive RecordedHistory (L : ℕ) (anchors : ℕ → Option (Fin ℓ)) :
    Array (Completed ℓ α) → List (Entry α) → Array (Completed ℓ α) → Prop where
  | done (done : Array (Completed ℓ α)) : RecordedHistory L anchors done [] done
  | step {done out : Array (Completed ℓ α)} {e : Entry α} {es : List (Entry α)}
      {neg : Lift ℓ e.negativeLength α}
      (h : Recorded L done.size (anchors e.patch) (fun j => done[j]?) e neg)
      (tail : RecordedHistory L anchors (done.push (completedOf done.size e neg)) es out) :
      RecordedHistory L anchors done (e::es) out

private theorem replay_from_history {L : ℕ} {anchors : ℕ → Option (Fin ℓ)}
    {done out : Array (Completed ℓ α)} {es : List (Entry α)}
    (h : RecordedHistory L anchors done es out) :
    es.foldlM (fun done e => do
      let next ← evaluate L done.size anchors (fun j => done[j]?) e
      pure (done.push next)) done = some out := by
  induction h with
  | done => rfl
  | step h tail ih =>
    simpa [evaluate_of_recorded h] using ih

theorem replay_of_recorded_history {L : ℕ} {anchors : ℕ → Option (Fin ℓ)}
    {out : Array (Completed ℓ α)} {es : List (Entry α)}
    (h : RecordedHistory L anchors #[] es out) :
    replay L anchors es = some out :=
  replay_from_history h

theorem reads_of_read {L current rule : ℕ} {anchor : Option (Fin ℓ)}
    {get : ℕ → Option (Completed ℓ α)} {ref : Reference} {u : Lift ℓ L α}
    (h : readReference L current rule anchor get ref = some u) :
    Reads L current rule anchor get ref u := by
  cases ref with
  | source delta =>
    cases ha : anchor with
    | none => simp [readReference,ha] at h
    | some root =>
      by_cases hs : 0 ≤ (root.val : ℤ)+delta
      · by_cases hb : ((root.val : ℤ)+delta).toNat+L ≤ ℓ
        · have e : sourceWindow ((root.val : ℤ)+delta).toNat L hb = u := by
            simpa [readReference,ha,hs,hb] using h
          subst u
          exact .source root delta rfl hs hb
        · simp [readReference,ha,hs,hb] at h
      · simp [readReference,ha,hs] at h
  | supplier j side a =>
    by_cases hj : j < current
    · cases he : get j with
      | none => simp [readReference,not_le_of_gt hj,he] at h
      | some prior =>
        by_cases hr : prior.rule < rule
        · by_cases hw : a+L ≤ (prior.lift side).1
          · have e := read_supplier L current rule anchor get hj he hr hw
            rw [e,Option.some.injEq] at h
            subst u
            exact .supplier j side a prior hj he hr hw
          · simp [readReference,not_le_of_gt hj,he,not_le_of_gt hr,hw] at h
        · simp [readReference,not_le_of_gt hj,he,Nat.le_of_not_gt hr] at h
    · simp [readReference,Nat.le_of_not_gt hj] at h

private theorem trace_of_assemble {L current rule : ℕ} {anchor : Option (Fin ℓ)}
    {get : ℕ → Option (Completed ℓ α)} {starts : List ℕ} {refs : List Reference}
    {u out : StoredLift ℓ α}
    (h : assemble (readReference L current rule anchor get) starts refs u = some out) :
    WindowTrace (Reads L current rule anchor get) starts refs u out := by
  induction starts generalizing refs u with
  | nil =>
    cases refs with
    | nil => simp [assemble] at h; subst out; exact .done u
    | cons => simp [assemble] at h
  | cons a as ih =>
    cases refs with
    | nil => simp [assemble] at h
    | cons ref rs =>
      cases hr : readReference L current rule anchor get ref with
      | none => simp [assemble,hr] at h
      | some v =>
        cases hw : appendWindow u.2 a v with
        | none => simp [assemble,hr,hw] at h
        | some w =>
          have htail : assemble (readReference L current rule anchor get) as rs ⟨a+L,w⟩ = some out := by
            simpa [assemble,hr,hw] using h
          exact .step (reads_of_read hr) (appendWindow_eq_some_iff.mp hw) (ih htail)

theorem recorded_of_negativeLift {L current : ℕ} {anchor : Option (Fin ℓ)}
    {get : ℕ → Option (Completed ℓ α)} {e : Entry α} {neg : Lift ℓ e.negativeLength α}
    (h : negativeLift L current e anchor get = some neg) :
    Recorded L current anchor get e neg := by
  by_cases hlen : e.negativeLength < L
  · simp [negativeLift,hlen] at h
  refine ⟨Nat.le_of_not_gt hlen,?_⟩
  unfold negativeLift at h
  simp only [ite_eq_right hlen] at h
  split at h
  next starts first refs hs hr =>
    let read := readReference L current e.rule anchor get
    cases hfirst : read first with
    | none => simp [read,hfirst] at h
    | some initial =>
      cases htail : assemble read starts refs ⟨L,initial⟩ with
      | none => simp [read,hfirst,htail] at h
      | some out =>
        have hdec : (if eq : out.1 = e.negativeLength then some (resize eq out.2) else none) = some neg := by
          simpa [read,hfirst,htail] using h
        have hout : out = ⟨e.negativeLength,neg⟩ := by
          split at hdec
          next eq =>
            cases out with
            | mk n z =>
              dsimp at eq
              subst n
              simp [resize] at hdec
              simp [hdec]
          next => contradiction
        rw [hout] at htail
        exact ⟨starts,first,refs,initial,hs,hr,reads_of_read hfirst,trace_of_assemble htail⟩
  next => contradiction

private theorem history_from_replay {L : ℕ} {anchors : ℕ → Option (Fin ℓ)}
    {done out : Array (Completed ℓ α)} {es : List (Entry α)}
    (h : es.foldlM (fun done e => do
      let next ← evaluate L done.size anchors (fun j => done[j]?) e
      pure (done.push next)) done = some out) :
    RecordedHistory L anchors done es out := by
  induction es generalizing done with
  | nil => simp at h; subst out; exact .done _
  | cons e es ih =>
    cases hneg : negativeLift L done.size e (anchors e.patch) (fun j => done[j]?) with
    | none => simp [evaluate,hneg] at h
    | some neg =>
      have hn := recorded_of_negativeLift hneg
      have ht : es.foldlM (fun done e => do
        let next ← evaluate L done.size anchors (fun j => done[j]?) e
        pure (done.push next)) (done.push (completedOf done.size e neg)) = some out := by
        simpa [evaluate_of_recorded hn] using h
      exact .step hn (ih ht)

/-- The replay succeeds with exactly the histories specified by the recorded
reads, the earliest-letter splices and the recorded gates. -/
theorem replay_eq_some_iff {L : ℕ} {anchors : ℕ → Option (Fin ℓ)}
    {out : Array (Completed ℓ α)} {es : List (Entry α)} :
    replay L anchors es = some out ↔ RecordedHistory L anchors #[] es out :=
  ⟨history_from_replay,replay_of_recorded_history⟩

/-- A source window matching a selected window can be recorded within
the signed offset range of `d:grammar`. The width hypothesis comes from
the union of the creation intervals in the patch. -/
theorem source_record_in_grammar {x : Fin ℓ → α} {K Λ m L start offset width E current rule : ℕ}
    (hx : Strong x K Λ) (u : Lift ℓ m α) (root : Fin ℓ)
    (hs : start+L ≤ ℓ) (hu : offset+L ≤ m) (hL : K+2*Λ ≤ L)
    (hspell : (sourceWindow start L hs).spelling x = (u.window offset L hu).spelling x)
    (hf : u.freshOffsets.card ≤ Λ) (ho : u.omissions.card ≤ Λ)
    (hpatch : ∀ p ∈ u.positions, root.val ≤ p ∧ p < root.val+width)
    (hE : 0 < E) (hwidth : width ≤ 3*E*L) (get : ℕ → Option (Completed ℓ α)) :
    ∃ delta : ℤ, -(8*(E : ℤ)*L) ≤ delta ∧ delta ≤ 8*(E : ℤ)*L ∧
      Reads L current rule (some root) get (.source delta) (sourceWindow start L hs) := by
  obtain ⟨hl,hr⟩ := source_reference_bounds hx u hs hu hL hspell hf ho hpatch
  have hlow : L ≤ 8*E*L := by
    simpa using Nat.mul_le_mul_right L (show 1 ≤ 8*E by omega)
  have hhigh : width ≤ 8*E*L :=
    hwidth.trans (Nat.mul_le_mul_right L (show 3*E ≤ 8*E by omega))
  refine ⟨(start : ℤ)-(root.val : ℤ),?_,?_,reads_of_read (read_encoded_source L current rule start root get hs)⟩
  · have hlo' : (L : ℤ) ≤ 8*(E : ℤ)*L := by exact_mod_cast hlow
    omega
  · exact hr.le.trans (by exact_mod_cast hhigh)

#print axioms source_record_in_grammar

#print axioms replay_eq_some_iff

#print axioms appendWindow_eq_some_iff
#print axioms replay_of_recorded_history

/-- The spelling of a lift placed at an offset of a prescribed local word. -/
def SpellsAt {m n : ℕ} (u : Lift ℓ m α) (x : Fin ℓ → α) (word : Fin n → α)
    (start : ℕ) : Prop :=
  start+m ≤ n ∧ ∀ (i : Fin m) (j : Fin n), start+i.val = j.val → u.spelling x i = word j

private def AdjacentWindows (L minimum : ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | m, a :: rest =>
    a ≤ m ∧ m ≤ a+L ∧ minimum ≤ m-a ∧ AdjacentWindows L minimum (a+L) rest

private theorem selected_adjacent {L n minimum : ℕ} {starts : List ℕ}
    (hs : selectedStarts L n = 0::starts) (hroom : (n-L+1)/2 + minimum ≤ L) :
    AdjacentWindows L minimum L starts := by
  by_cases hz : n-L = 0
  · have he : starts = [] := by simpa [selectedStarts,hz] using hs.symm
    subst starts
    trivial
  · by_cases h₁ : n-L = 1
    · have he : starts = [1] := by simpa [selectedStarts,h₁] using hs.symm
      subst starts
      have hr : 1 + minimum ≤ L := by simpa [h₁] using hroom
      refine ⟨?_,?_,?_,trivial⟩ <;> omega
    · have he : starts = [(n-L)/2,n-L] := by simpa [selectedStarts,hz,h₁] using hs.symm
      subst starts
      generalize hd : n-L = d at hz h₁ hroom ⊢
      refine ⟨?_,?_,?_,?_,?_,?_,trivial⟩ <;> omega

private theorem selected_end {L n : ℕ} {starts : List ℕ} (hn : L ≤ n)
    (hs : selectedStarts L n = 0::starts) :
    (starts.getLast?.map (·+L)).getD L = n := by
  have hl := selectedStarts_last L n
  rw [hs] at hl
  cases starts with
  | nil => simp at hl; simp; omega
  | cons a as =>
    have ha : (a::as).getLast? = some (n-L) := by simpa [List.getLast?_cons] using hl
    simp [ha, Nat.sub_add_cancel hn]

private theorem assemble_on_graph {K Λ L n : ℕ} {x : Fin ℓ → α} (hx : Strong x K Λ)
    (word : Fin n → α) (E : Letter ℓ α → Letter ℓ α → Prop)
    (hshort : n ≤ 3*L)
    (hbudget : ∀ {m} (u : Lift ℓ m α), L ≤ m → m ≤ 3*L → u.Follows E →
      u.freshOffsets.card ≤ Λ ∧ u.omissions.card ≤ Λ)
    (read : Reference → Option (Lift ℓ L α))
    {starts : List ℕ} {refs : List Reference}
    (hreads : List.Forall₂ (fun a ref => ∃ v, read ref = some v ∧
      SpellsAt v x word a ∧ v.Follows E) starts refs)
    (u : StoredLift ℓ α) (hspell : SpellsAt u.2 x word 0) (hfollow : u.2.Follows E)
    (hminimum : L ≤ u.1) (hfit : AdjacentWindows L (K+2*Λ) u.1 starts) :
    ∃ out : StoredLift ℓ α, assemble read starts refs u = some out ∧
      SpellsAt out.2 x word 0 ∧ out.2.Follows E := by
  induction hreads generalizing u with
  | nil => exact ⟨u,rfl,hspell,hfollow⟩
  | @cons a ref starts refs hnext htail ih =>
    obtain ⟨v,hread,hv,hvPath⟩ := hnext
    obtain ⟨hle,hreach,hmin,hrest⟩ := hfit
    obtain ⟨huf,huo⟩ := hbudget u.2 hminimum (by have := hspell.1; omega) hfollow
    obtain ⟨hvf,hvo⟩ := hbudget v (le_refl _) (by have := hv.1; omega) hvPath
    have hov (i : Fin (u.1-a)) :
        u.2.spelling x ⟨a+i.val,by omega⟩ = v.spelling x ⟨i.val,by omega⟩ := by
      let j : Fin n := ⟨a+i.val,by have := hv.1; omega⟩
      exact (hspell.2 _ j (Nat.zero_add _)).trans (hv.2 _ j rfl).symm
    have hsuccess := appendWindow_isSome hx u.2 v hle hreach hmin hov huf hvf huo hvo
    cases hjoin : appendWindow u.2 a v with
    | none => simp [hjoin] at hsuccess
    | some next =>
      have hnextPath := appendWindow_follows hjoin hfollow hvPath
      obtain ⟨hl,hr⟩ := appendWindow_spelling hle hreach hjoin hov
      have hnextSpell : SpellsAt next x word 0 := by
        refine ⟨by simpa using hv.1,?_⟩
        intro i j he
        by_cases h : i.val < u.1
        · have hcast : Fin.castLE hreach (⟨i.val,h⟩ : Fin u.1) = i := Fin.ext rfl
          have hleft := hl ⟨i.val,h⟩
          rw [hcast] at hleft
          exact hleft.trans (hspell.2 _ j he)
        · let ii : Fin L := ⟨i.val-a,by omega⟩
          have hix : a+ii.val = i.val := Nat.add_sub_of_le (by omega : a ≤ i.val)
          have hcast : (⟨a+ii.val,by omega⟩ : Fin (a+L)) = i := Fin.ext hix
          have hright := hr ii
          rw [hcast] at hright
          exact hright.trans (hv.2 ii j (by omega))
      obtain ⟨out,ho,hs,hp⟩ := ih ⟨a+L,next⟩ hnextSpell hnextPath (by simp) hrest
      exact ⟨out,by simpa [assemble,hread,hjoin] using ho,hs,hp⟩

/-- Replay of the recorded windows succeeds in the old graph. The local
bound is invoked again for each assembled prefix before the next splice. -/
theorem negativeLift_on_graph {K Λ L current : ℕ} {x : Fin ℓ → α} (hx : Strong x K Λ)
    (E : Letter ℓ α → Letter ℓ α → Prop) (e : Entry α)
    (word : Fin e.negativeLength → α) (anchor : Option (Fin ℓ))
    (get : ℕ → Option (Completed ℓ α))
    (hlen : L ≤ e.negativeLength) (hshort : e.negativeLength ≤ 3*L)
    (hroom : (e.negativeLength-L+1)/2 + (K+2*Λ) ≤ L)
    (hbudget : ∀ {m} (u : Lift ℓ m α), L ≤ m → m ≤ 3*L → u.Follows E →
      u.freshOffsets.card ≤ Λ ∧ u.omissions.card ≤ Λ)
    (hreads : List.Forall₂ (fun a ref => ∃ v,
      readReference L current e.rule anchor get ref = some v ∧
      SpellsAt v x word a ∧ v.Follows E) (selectedStarts L e.negativeLength) e.references) :
    ∃ out, negativeLift L current e anchor get = some out ∧
      SpellsAt out x word 0 ∧ out.Follows E := by
  have hs : ∃ starts, selectedStarts L e.negativeLength = 0::starts := by
    unfold selectedStarts
    dsimp only
    split
    · exact ⟨[],rfl⟩
    · split <;> exact ⟨_,rfl⟩
  obtain ⟨starts,hstarts⟩ := hs
  rw [hstarts] at hreads
  cases hrefs : e.references with
  | nil => simp [hrefs] at hreads
  | cons first refs =>
    rw [hrefs] at hreads
    cases hreads with
    | cons hfirst htail =>
      obtain ⟨v,hread,hspell,hpath⟩ := hfirst
      let read := readReference L current e.rule anchor get
      have hfit := selected_adjacent hstarts hroom
      obtain ⟨out,ho,hsp,hfp⟩ := assemble_on_graph hx word E hshort hbudget read
        htail ⟨L,v⟩ hspell hpath (le_refl L) hfit
      have hlenOut := (assemble_length read starts refs ⟨L,v⟩ out ho).2
      rw [selected_end hlen hstarts] at hlenOut
      rcases out with ⟨m,w⟩
      dsimp at hlenOut
      subst m
      refine ⟨w,?_,hsp,hfp⟩
      dsimp only [read] at ho
      simp [negativeLift,hstarts,hrefs,not_lt_of_ge hlen,hread,ho,resize]

#print axioms negativeLift_on_graph

end DeletionCode.Explicit.ReplayEntry
