import DeletionCode.Explicit.PrepareNegative
import DeletionCode.Explicit.Borrowed.BubbleWords

/-! Prepare all bubbles of a rule against the same frozen dictionary. -/

namespace DeletionCode.Explicit.LetterGraphCuts

open LetterSequence LocalBudget RulePatch ReplayEntry LiftDictionary SelectedReplay Borrowed
open Qary.SignedSupport FieldHash

variable {ℓ d s K b L : ℕ} {α : Type*} [DecidableEq α]

/-- A prepared bubble keeps the gate and the selected dictionary occurrences
until the new patch label and anchor are available. -/
structure PreparedBubble (ℓ L : ℕ) (α : Type*) where
  windows : List (Occurrence ℓ L α)
  rule : ℕ
  left : ℕ
  removed : ℕ
  inserted : ℕ
  right : ℕ
  gate : Gate ℓ left removed inserted right α
  hasOriginal : gate.negative.positions.Nonempty

def PreparedBubble.completed (p : PreparedBubble ℓ L α) : Completed ℓ α :=
  ⟨p.rule,⟨_,p.gate.negative⟩,⟨_,p.gate.positive⟩⟩

def PreparedBubble.data (p : PreparedBubble ℓ L α) : GateData ℓ α :=
  p.gate.data p.hasOriginal

def prepareBubbleFrom (L current rule : ℕ) {a u v r : ℕ}
    (replacement : Fin v → α) (windows : List (Occurrence ℓ L α))
    (neg : Lift ℓ (a+u+r) α) (ha : 0 < a) (hr : 0 < r) :
    Option (PreparedBubble ℓ L α) :=
  let g : Gate ℓ a u v r α := ⟨neg,ha,hr,current,replacement⟩
  if h : neg.positions.Nonempty then some ⟨windows,rule,a,u,v,r,g,h⟩ else none

def negativeLetters (w : BubbleWord α K b L) :
    Fin (w.left.length+w.removed.length+w.right.length) → α :=
  w.negativeWord.get ∘ Fin.cast (by simp [BubbleWord.negativeWord,Nat.add_assoc])

/-- Use the paper's local word to prepare a gate and keep the dictionary
selections. Gate ids are supplied in chronological bubble order. -/
def prepareBubble (pad : α) (x : Fin ℓ → α) (history : Array (Completed ℓ α))
    (w : BubbleWord α K b L) (root : Fin ℓ) (current rule : ℕ)
    (ha : 0 < w.left.length) (hr : 0 < w.right.length) : Option (PreparedBubble ℓ L α) := do
  let (windows,neg) ← prepareNegative pad x history L current rule root w.left.length
    w.removed w.replacement w.right.length (negativeLetters w)
  prepareBubbleFrom L current rule w.replacement.get
    windows neg ha hr

/-- The input array is held fixed while selecting every negative lift. -/
def prepareRule (pad : α) (x : Fin ℓ → α) (history : Array (Completed ℓ α))
    (words : Fin s → BubbleWord α K b L) (root : Fin ℓ) (rule : ℕ)
    (ha : ∀ j, 0 < (words j).left.length) (hr : ∀ j, 0 < (words j).right.length) :
    Option (List (PreparedBubble ℓ L α)) :=
  (List.finRange s).mapM fun j => prepareBubble pad x history (words j) root
    (history.size+j.val) rule (ha j) (hr j)

theorem prepareBubble_of_negative (pad : α) (x : Fin ℓ → α) (history : Array (Completed ℓ α))
    (w : BubbleWord α K b L) (root : Fin ℓ) (current rule : ℕ)
    (ha : 0 < w.left.length) (hr : 0 < w.right.length)
    (windows : List (Occurrence ℓ L α))
    (neg : Lift ℓ (w.left.length+w.removed.length+w.right.length) α)
    (hneg : prepareNegative pad x history L current rule root w.left.length w.removed w.replacement
      w.right.length
      (negativeLetters w) =
        some (windows,neg))
    (hleft : neg.freshOffsets.card < w.left.length) :
    ∃ (g : Gate ℓ w.left.length w.removed.length w.replacement.length w.right.length α)
      (hn : g.negative.positions.Nonempty),
      g.negative = neg ∧ g.entry = current ∧ g.replacement = w.replacement.get ∧
      prepareBubble pad x history w root current rule ha hr =
        some ⟨windows,rule,_,_,_,_,g,hn⟩ := by
  let g : Gate ℓ w.left.length w.removed.length w.replacement.length w.right.length α :=
    ⟨neg,ha,hr,current,w.replacement.get⟩
  have hn := g.positions_nonempty hleft
  exact ⟨g,hn,rfl,rfl,rfl,by
    unfold prepareBubble
    rw [hneg]
    simp [prepareBubbleFrom,g,show neg.positions.Nonempty from hn]⟩

/-- Record the saved dictionary occurrences relative to the final patch anchor. -/
def PreparedBubble.replayEntry (p : PreparedBubble ℓ L α) (x : Fin ℓ → α)
    (patch : ℕ) (anchor : Fin ℓ) : Entry α :=
  ⟨p.rule,patch,p.left,List.ofFn (fun i : Fin p.removed =>
    p.gate.negative.spelling x ⟨p.left+i.val,by have := i.isLt; omega⟩),
    List.ofFn p.gate.replacement,p.right,p.windows.map (fun o => o.location.reference anchor)⟩

omit [DecidableEq α] in
theorem removed_from_spelling (x : Fin ℓ → α) (w : BubbleWord α K b L)
    (neg : Lift ℓ (w.left.length+w.removed.length+w.right.length) α)
    (hword : List.ofFn (neg.spelling x) = w.negativeWord) :
    (List.ofFn fun i : Fin w.removed.length =>
      neg.spelling x ⟨w.left.length+i.val,by have := i.isLt; omega⟩) = w.removed := by
  let f := Fin.append (Fin.append w.left.get w.removed.get) w.right.get
  have he : neg.spelling x = f := by
    apply List.ofFn_injective
    rw [hword]
    simp [f,List.ofFn_fin_append,BubbleWord.negativeWord,List.append_assoc]
  have heq : (fun i : Fin w.removed.length => neg.spelling x
      ⟨w.left.length+i.val,by have := i.isLt; omega⟩) = w.removed.get := by
    funext i
    change neg.spelling x (Fin.castAdd w.right.length (Fin.natAdd w.left.length i)) = w.removed.get i
    rw [he]
    simp [f,Fin.append_left,Fin.append_right]
  rw [heq,List.ofFn_get]

/-- A prepared bubble replays exactly at any anchor, using the same
frozen array and the stored dictionary choices. -/
theorem prepareBubble_replay (pad : α) (x : Fin ℓ → α) (history : Array (Completed ℓ α))
    (w : BubbleWord α K b L) (origin anchor : Fin ℓ) (current rule patch : ℕ)
    (ha : 0 < w.left.length) (hr : 0 < w.right.length)
    (hc : history.size ≤ current) (hold : ∀ j : Fin history.size, history[j].rule < rule)
    {p : PreparedBubble ℓ L α} (h : prepareBubble pad x history w origin current rule ha hr = some p)
    (hword : List.ofFn (p.gate.negative.spelling x) = w.negativeWord)
    (anchors : ℕ → Option (Fin ℓ)) (hanchor : anchors patch = some anchor) :
    evaluate L current anchors (fun j => history[j]?) (p.replayEntry x patch anchor) = some p.completed := by
  unfold prepareBubble at h
  cases hn : prepareNegative pad x history L current rule origin w.left.length w.removed w.replacement
      w.right.length (negativeLetters w) with
  | none => simp [hn] at h
  | some res =>
    obtain ⟨os,neg⟩ := res
    have hp : prepareBubbleFrom L current rule w.replacement.get os neg ha hr = some p := by
      simpa [hn] using h
    unfold prepareBubbleFrom at hp
    dsimp only at hp
    split at hp
    next hne =>
      let g : Gate ℓ w.left.length w.removed.length w.replacement.length w.right.length α :=
        ⟨neg,ha,hr,current,w.replacement.get⟩
      have hprep : (⟨os,rule,_,_,_,_,g,hne⟩ : PreparedBubble ℓ L α) = p := Option.some.inj hp
      subst p
      have hcentral := removed_from_spelling x w neg hword
      have he := prepareNegative_reanchor pad x history L current rule origin anchor
        w.left.length w.removed w.replacement w.right.length (negativeLetters w) hc hold hn
      have hentry : (⟨os,rule,_,_,_,_,g,hne⟩ : PreparedBubble ℓ L α).replayEntry x patch anchor =
          ⟨rule,patch,w.left.length,w.removed,w.replacement,w.right.length,
            os.map (fun o => o.location.reference anchor)⟩ := by
        simp [PreparedBubble.replayEntry,g,hcentral]
      rw [hentry]
      unfold evaluate
      have he' : negativeLift L current
          ⟨rule,patch,w.left.length,w.removed,w.replacement,w.right.length,
            os.map (fun o => o.location.reference anchor)⟩ (anchors patch) (fun j => history[j]?) = some neg := by
        rw [hanchor]
        exact he
      rw [he']
      rfl
    next => contradiction

#print axioms prepareBubble_replay

/-- The replay record keeps the exact central words and flank lengths. -/
theorem prepareBubble_entry_fields (pad : α) (x : Fin ℓ → α) (history : Array (Completed ℓ α))
    (w : BubbleWord α K b L) (origin anchor : Fin ℓ) (current rule patch : ℕ)
    (ha : 0 < w.left.length) (hr : 0 < w.right.length)
    {p : PreparedBubble ℓ L α} (h : prepareBubble pad x history w origin current rule ha hr = some p)
    (hword : List.ofFn (p.gate.negative.spelling x) = w.negativeWord) :
    let e := p.replayEntry x patch anchor
    e.left = w.left.length ∧ e.right = w.right.length ∧
      e.removed = w.removed ∧ e.replacement = w.replacement := by
  unfold prepareBubble at h
  cases hn : prepareNegative pad x history L current rule origin w.left.length w.removed w.replacement
      w.right.length (negativeLetters w) with
  | none => simp [hn] at h
  | some res =>
    obtain ⟨os,neg⟩ := res
    have hp : prepareBubbleFrom L current rule w.replacement.get os neg ha hr = some p := by
      simpa [hn] using h
    unfold prepareBubbleFrom at hp
    dsimp only at hp
    split at hp
    next hne =>
      let g : Gate ℓ w.left.length w.removed.length w.replacement.length w.right.length α :=
        ⟨neg,ha,hr,current,w.replacement.get⟩
      have he : (⟨os,rule,_,_,_,_,g,hne⟩ : PreparedBubble ℓ L α) = p := Option.some.inj hp
      subst p
      exact ⟨rfl,rfl,removed_from_spelling x w neg hword,List.ofFn_get _⟩
    next => contradiction

/-- A saved occurrence spells the corresponding window of the final negative lift. -/
theorem prepareBubble_saved_window (pad : α) (x : Fin ℓ → α) (history : Array (Completed ℓ α))
    (w : BubbleWord α K b L) (root anchor : Fin ℓ) (current rule : ℕ)
    (ha : 0 < w.left.length) (hr : 0 < w.right.length)
    {p : PreparedBubble ℓ L α} (h : prepareBubble pad x history w root current rule ha hr = some p)
    (hword : List.ofFn (p.gate.negative.spelling x) = w.negativeWord)
    (hmin : L ≤ w.negativeWord.length) (hc : history.size ≤ current)
    (hold : ∀ j : Fin history.size, history[j].rule < rule) {o : Occurrence ℓ L α} (ho : o ∈ p.windows) :
    ∃ a, ∃ hb : a+L ≤ p.left+p.removed+p.right,
      o.lift.spelling x = (p.gate.negative.window a L hb).spelling x ∧
      readReference L current rule (some anchor) (fun j => history[j]?) (o.location.reference anchor) = some o.lift := by
  unfold prepareBubble at h
  cases hn : prepareNegative pad x history L current rule root w.left.length w.removed w.replacement
      w.right.length (negativeLetters w) with
  | none => simp [hn] at h
  | some res =>
    obtain ⟨os,neg⟩ := res
    have hp : prepareBubbleFrom L current rule w.replacement.get os neg ha hr = some p := by
      simpa [hn] using h
    unfold prepareBubbleFrom at hp
    dsimp only at hp
    split at hp
    next hne =>
      let g : Gate ℓ w.left.length w.removed.length w.replacement.length w.right.length α :=
        ⟨neg,ha,hr,current,w.replacement.get⟩
      have he : (⟨os,rule,_,_,_,_,g,hne⟩ : PreparedBubble ℓ L α) = p := Option.some.inj hp
      subst p
      have hselect : select pad x history L (negativeLetters w) = some os := by
        unfold prepareNegative at hn
        cases hs : select pad x history L (negativeLetters w) with
        | none => simp [hs] at hn
        | some selected =>
          simp only [hs,Option.bind_eq_bind,Option.bind_some] at hn
          generalize negLift : negativeLift L current _ _ _ = opt at hn
          cases opt with
          | none => simp at hn
          | some lift =>
            have h := congrArg Prod.fst (Option.some.inj hn)
            exact congrArg some h
      have hslots := select_lookup_at pad x history L (negativeLetters w) hselect
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp ho
      have hidx : i.val < (selectedStarts L (w.left.length+w.removed.length+w.right.length)).length := by
        rw [hslots.length_eq]
        exact i.isLt
      let a := (selectedStarts L (w.left.length+w.removed.length+w.right.length)).get ⟨i.val,hidx⟩
      have hmem : a ∈ selectedStarts L (w.left.length+w.removed.length+w.right.length) := List.get_mem ..
      have hbound : a+L ≤ w.left.length+w.removed.length+w.right.length := by
        have hl : L ≤ w.left.length+w.removed.length+w.right.length := by
          simpa [BubbleWord.negativeWord,Nat.add_assoc] using hmin
        have hh := selectedStarts_mem.mp hmem
        rcases hh with h | h | h <;> omega
      have hlookup := hslots.get hidx i.isLt
      have hlook : lookup x history (gram (paddedLetters pad (negativeLetters w)) L a) = some o :=
        hlookup.trans (congrArg some hi)
      have hspell : neg.spelling x = negativeLetters w := by
        apply List.ofFn_injective
        rw [hword]
        apply List.ext_getElem
        · simp [BubbleWord.negativeWord,Nat.add_assoc]
        · intro i hi hj
          simp [negativeLetters]
      refine ⟨a,hbound,(lookup_spelling hlook).trans ?_, lookup_reference hlook anchor hc hold⟩
      exact (congrArg (fun z => gram (paddedLetters pad z) L a) hspell.symm).trans
        (lift_gram pad x ⟨_,neg⟩ a hbound)
    next => contradiction

#print axioms prepareBubble_saved_window

private theorem mapM_present {A B : Type*} (f : A → Option B) (xs : List A)
    (h : ∀ a ∈ xs, ∃ b, f a = some b) :
    ∃ ys, xs.mapM f = some ys ∧ List.Forall₂ (fun a b => f a = some b) xs ys := by
  induction xs with
  | nil => exact ⟨[],rfl,.nil⟩
  | cons a rest ih =>
    obtain ⟨y,hy⟩ := h a (List.mem_cons_self ..)
    obtain ⟨ys,hys,hspec⟩ := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    exact ⟨y :: ys,by simp [hy,hys],.cons hy hspec⟩

/-- Any per-bubble preparation theorem for the frozen graph lifts to the
entire rule in its chronological order. -/
theorem prepareRule_of_bubbles (pad : α) (x : Fin ℓ → α) (history : Array (Completed ℓ α))
    (words : Fin s → BubbleWord α K b L) (root : Fin ℓ) (rule : ℕ)
    (ha : ∀ j, 0 < (words j).left.length) (hr : ∀ j, 0 < (words j).right.length)
    (h : ∀ j, ∃ w, prepareBubble pad x history (words j) root (history.size+j.val) rule (ha j) (hr j) =
      some w) :
    ∃ ws, prepareRule pad x history words root rule ha hr = some ws ∧
      List.Forall₂ (fun j w => prepareBubble pad x history (words j) root (history.size+j.val)
        rule (ha j) (hr j) = some w) (List.finRange s) ws :=
  mapM_present _ _ (fun j _ => h j)

/-- Install the prepared gates in order, keeping the old graph available to
every negative lift. These relations are used only in the correctness proof. -/
def installedEdges (E : Letter ℓ α → Letter ℓ α → Prop)
    (ws : List (PreparedBubble ℓ L α)) : Letter ℓ α → Letter ℓ α → Prop :=
  ws.foldl (fun G w => w.gate.edges G) E

def installedMarks (marked : Finset (Fin ℓ)) (ws : List (PreparedBubble ℓ L α)) :
    Finset (Fin ℓ) :=
  ws.foldl (fun M w => M ∪ (w.gate.removed.filterMap Letter.position).toFinset) marked

omit [DecidableEq α] in
private theorem Lift.follows_addGate {a u v r m : ℕ} {E : Letter ℓ α → Letter ℓ α → Prop}
    (w : Lift ℓ m α) (h : w.Follows E) (g : Gate ℓ a u v r α) :
    w.Follows (g.edges E) := fun i j hj => Or.inl (h i j hj)

omit [DecidableEq α] in
private theorem unused_after_gate {a u v r : ℕ} {E : Letter ℓ α → Letter ℓ α → Prop}
    (g : Gate ℓ a u v r α) (hpath : g.negative.Follows E) {id : ℕ} (hne : id ≠ g.entry)
    (h : ∀ k x, ¬ Incident E (.fresh id k x)) :
    ∀ k x, ¬ Incident (g.edges E) (.fresh id k x) := by
  intro k x hi
  rcases g.incident_after hpath hi with hi | hi
  · exact h k x hi
  · obtain ⟨i,he⟩ := g.mem_inserted.mp hi
    exact hne (Letter.fresh.inj he).1

/-- Every prepared negative lift was obtained in the old graph. It stays
valid through the preceding installations in the same rule. -/
theorem install_prepared_rule
    {E : Letter ℓ α → Letter ℓ α → Prop} {marked : Finset (Fin ℓ)}
    (H : History ℓ α E marked) (ws : List (PreparedBubble ℓ L α))
    (hpath : ∀ w ∈ ws, w.gate.negative.Follows E)
    (hids : (ws.map (fun w => w.gate.entry)).Nodup)
    (hnew : ∀ w ∈ ws, ∀ k x, ¬ Incident E (.fresh w.gate.entry k x)) :
    History ℓ α (installedEdges E ws) (installedMarks marked ws) := by
  induction ws generalizing E marked with
  | nil => exact H
  | cons w rest ih =>
    have hn := hpath w (List.mem_cons_self ..)
    have hf := hnew w (List.mem_cons_self ..)
    obtain ⟨hne,hrest⟩ := List.nodup_cons.mp hids
    have hpaths : ∀ p ∈ rest, p.gate.negative.Follows (w.gate.edges E) :=
      fun p hp => Lift.follows_addGate _ (hpath p (List.mem_cons_of_mem _ hp)) _
    apply ih (w.gate.history H hn hf) hpaths hrest
    intro p hp
    have hne' : p.gate.entry ≠ w.gate.entry := by
      intro he
      exact hne (List.mem_map.mpr ⟨p,hp,he⟩)
    exact unused_after_gate w.gate hn hne' (hnew p (List.mem_cons_of_mem _ hp))

/-- All old patch witnesses still refer to the same gate records. The
new graph witnesses can be grouped immediately by the final patch labels. -/
theorem installed_records {d' s' : ℕ} {data : Fin d' × Fin s' → GateData ℓ α}
    {E : Letter ℓ α → Letter ℓ α → Prop} {marked : Finset (Fin ℓ)}
    (hrecords : PatchTable.RecordsGraph data E marked) (ws : List (PreparedBubble ℓ L α))
    (hpath : ∀ w ∈ ws, w.gate.negative.Follows E)
    (hfit : ∀ w ∈ ws, w.gate.negative.freshOffsets.card < w.left ∧
      w.gate.negative.freshOffsets.card < w.right)
    (hdata : ∀ w ∈ ws, ∃ e, data e = w.data) :
    PatchTable.RecordsGraph data (installedEdges E ws) (installedMarks marked ws) := by
  induction ws generalizing E marked with
  | nil => exact hrecords
  | cons w rest ih =>
    have hw : w ∈ w :: rest := List.mem_cons_self
    have hn := hpath w hw
    obtain ⟨hl,hr⟩ := hfit w hw
    have he := PatchTable.RecordsGraph.extend data hrecords w.gate hn w.hasOriginal hl hr
      (new := data) (fun e => ⟨e,rfl⟩) (hdata w hw)
    have hp : ∀ p ∈ rest, p.gate.negative.Follows (w.gate.edges E) :=
      fun p hp => Lift.follows_addGate _ (hpath p (List.mem_cons_of_mem _ hp)) _
    exact ih he hp (fun p hp => hfit p (List.mem_cons_of_mem _ hp))
      (fun p hp => hdata p (List.mem_cons_of_mem _ hp))

#print axioms installed_records

#print axioms install_prepared_rule

#print axioms prepareBubble_of_negative
#print axioms prepareRule_of_bubbles

end DeletionCode.Explicit.LetterGraphCuts
