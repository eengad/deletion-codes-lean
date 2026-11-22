import DeletionCode.Explicit.SelectedReplay

/-! Install the executable replacement in the chronological letter graph. -/

namespace DeletionCode.Explicit.LetterGraphCuts

open LetterSequence
open SelectedReplay (Incident)

variable {ℓ a u v r m : ℕ} {α : Type*}

/-- A gate is installed between the last letter of the left flank and the
first letter of the right flank of the stored negative lift. -/
structure Gate (ℓ a u v r : ℕ) (α : Type*) where
  negative : Lift ℓ (a+u+r) α
  left_pos : 0 < a
  right_pos : 0 < r
  entry : ℕ
  replacement : Fin v → α

def Gate.left (g : Gate ℓ a u v r α) : Letter ℓ α :=
  g.negative.letters ⟨a-1,by have := g.left_pos; omega⟩

def Gate.right (g : Gate ℓ a u v r α) : Letter ℓ α :=
  g.negative.letters ⟨a+u,by have := g.right_pos; omega⟩

def Gate.removed (g : Gate ℓ a u v r α) : List (Letter ℓ α) :=
  List.ofFn (fun i : Fin u => g.negative.letters ⟨a+i.val,by omega⟩)

def Gate.inserted (g : Gate ℓ a u v r α) : List (Letter ℓ α) :=
  List.ofFn (fun i : Fin v => .fresh g.entry i.val (g.replacement i))

def Gate.positive (g : Gate ℓ a u v r α) : Lift ℓ (a+v+r) α :=
  g.negative.installGate g.entry g.replacement

abbrev Gate.edges (g : Gate ℓ a u v r α) (E : Letter ℓ α → Letter ℓ α → Prop) :=
  addGate E g.left g.inserted g.right

@[simp] theorem Gate.length_removed (g : Gate ℓ a u v r α) : g.removed.length = u := by
  simp [Gate.removed]

@[simp] theorem Gate.length_inserted (g : Gate ℓ a u v r α) : g.inserted.length = v := by
  simp [Gate.inserted]

theorem Gate.inserted_nodup (g : Gate ℓ a u v r α) : g.inserted.Nodup := by
  rw [Gate.inserted,List.nodup_ofFn]
  intro i j h
  exact Fin.ext (Letter.fresh.inj h).2.1

theorem Gate.mem_inserted (g : Gate ℓ a u v r α) {w : Letter ℓ α} :
    w ∈ g.inserted ↔ ∃ i : Fin v, w = .fresh g.entry i.val (g.replacement i) := by
  simp [Gate.inserted,List.mem_ofFn,eq_comm]

private theorem mem_liftSegment_iff (w : Lift ℓ m α) {start len : ℕ}
    (h : start+len+1 < m) {x y : Letter ℓ α} :
    (x,y) ∈ segmentEdges (w.letters ⟨start,by omega⟩)
      (List.ofFn (fun i : Fin len => w.letters ⟨start+1+i.val,by omega⟩))
      (w.letters ⟨start+len+1,h⟩) ↔
      ∃ (i : ℕ) (hi : i < len+1), w.letters ⟨start+i,by omega⟩ = x ∧
        w.letters ⟨start+i+1,by omega⟩ = y := by
  let mid := List.ofFn (fun i : Fin len => w.letters ⟨start+1+i.val,by omega⟩)
  let first := w.letters ⟨start,by omega⟩
  let last := w.letters ⟨start+len+1,h⟩
  have hlen : mid.length = len := by simp [mid]
  have hleft (i : ℕ) (hi : i < len+1) :
      (first :: mid)[i]'(by simp [hlen]; omega) = w.letters ⟨start+i,by omega⟩ := by
    cases i with
    | zero => simp [first]
    | succ i => simp [mid,Nat.add_assoc,Nat.add_comm 1]
  have hright (i : ℕ) (hi : i < len+1) :
      (mid ++ [last])[i]'(by simp [hlen]; omega) = w.letters ⟨start+i+1,by omega⟩ := by
    by_cases ht : i < len
    · rw [List.getElem_append_left (by omega : i < mid.length)]
      simp [mid,Nat.add_assoc,Nat.add_comm 1]
    · have he : i = len := by omega
      subst i
      rw [List.getElem_append_right (by omega : mid.length ≤ len)]
      simp [hlen,last]
  change (x,y) ∈ segmentEdges first mid last ↔ _
  rw [mem_segmentEdges_iff]
  constructor
  · rintro ⟨i,hi,hx,hy⟩
    have hi' : i < len+1 := by omega
    exact ⟨i,hi',(hleft i hi').symm.trans hx,(hright i hi').symm.trans hy⟩
  · rintro ⟨i,hi,hx,hy⟩
    exact ⟨i,by omega,(hleft i hi).trans hx,(hright i hi).trans hy⟩

theorem Gate.old_segment (g : Gate ℓ a u v r α) {E : Letter ℓ α → Letter ℓ α → Prop}
    (hneg : g.negative.Follows E) :
    ∀ x y, (x,y) ∈ segmentEdges g.left g.removed g.right → E x y := by
  intro x y hxy
  have ha := g.left_pos
  have hr := g.right_pos
  have he : a-1+u+1 = a+u := by omega
  have hmid : (List.ofFn (fun i : Fin u => g.negative.letters ⟨a-1+1+i.val,by omega⟩)) =
      g.removed := by
    simp [Gate.removed,show a-1+1=a by omega]
  have hlast : g.negative.letters ⟨a-1+u+1,by omega⟩ = g.right :=
    congrArg g.negative.letters (Fin.ext he)
  obtain ⟨i,hi,rfl,rfl⟩ := (mem_liftSegment_iff g.negative
    (start := a-1) (len := u) (by omega)).mp (by rwa [hmid,hlast])
  exact hneg _ _ rfl

private theorem Gate.positive_segment (g : Gate ℓ a u v r α) {i : ℕ}
    (hl : a-1 ≤ i) (hr : i < a+v) :
    (g.positive.letters ⟨i,by omega⟩,g.positive.letters ⟨i+1,by
        have := g.right_pos
        omega⟩) ∈ segmentEdges g.left g.inserted g.right := by
  have ha := g.left_pos
  have hrv := g.right_pos
  have hfirst : g.positive.letters ⟨a-1,by omega⟩ = g.left :=
    g.negative.gate_left_letter g.entry g.replacement (a-1) (by omega)
  have hlast : g.positive.letters ⟨a-1+v+1,by omega⟩ = g.right := by
    have he : (⟨a-1+v+1,by omega⟩ : Fin (a+v+r)) = ⟨a+v+0,by omega⟩ :=
      Fin.ext (show a-1+v+1 = a+v+0 by omega)
    rw [he]
    exact g.negative.gate_right_letter g.entry g.replacement 0 hrv
  have hmid : (List.ofFn (fun j : Fin v => g.positive.letters ⟨a-1+1+j.val,by omega⟩)) =
      g.inserted := by
    unfold Gate.inserted
    congr 1
    funext j
    have he : (⟨a-1+1+j.val,by omega⟩ : Fin (a+v+r)) = ⟨a+j.val,by omega⟩ :=
      Fin.ext (show a-1+1+j.val = a+j.val by omega)
    rw [he]
    exact g.negative.gate_inserted_letter g.entry g.replacement j
  rw [← hfirst,← hlast,← hmid]
  apply (mem_liftSegment_iff g.positive (start := a-1) (len := v) (by omega)).mpr
  have he : a-1+(i-(a-1)) = i := by omega
  refine ⟨i-(a-1),by omega,?_,?_⟩
  · exact congrArg g.positive.letters (Fin.ext he)
  · exact congrArg g.positive.letters (Fin.ext (congrArg (·+1) he))

/-- The executable positive lift follows the enlarged graph. -/
theorem Gate.positive_follows (g : Gate ℓ a u v r α) {E : Letter ℓ α → Letter ℓ α → Prop}
    (hneg : g.negative.Follows E) : g.positive.Follows (g.edges E) := by
  intro i j h
  have ha := g.left_pos
  have hrv := g.right_pos
  by_cases hl : j.val < a
  · rw [show g.positive.letters i = g.negative.letters ⟨i.val,by omega⟩ from
      g.negative.gate_left_letter g.entry g.replacement i.val (by omega),
      show g.positive.letters j = g.negative.letters ⟨j.val,by omega⟩ from
      g.negative.gate_left_letter g.entry g.replacement j.val hl]
    exact Or.inl (hneg _ _ h)
  by_cases hr : a+v ≤ i.val
  · have hi : (⟨a+v+(i.val-(a+v)),by omega⟩ : Fin (a+v+r)) = i :=
      Fin.ext (show a+v+(i.val-(a+v)) = i.val by omega)
    have hj : (⟨a+v+(j.val-(a+v)),by omega⟩ : Fin (a+v+r)) = j :=
      Fin.ext (show a+v+(j.val-(a+v)) = j.val by omega)
    have hi' := g.negative.gate_right_letter g.entry g.replacement (i.val-(a+v)) (by omega)
    have hj' := g.negative.gate_right_letter g.entry g.replacement (j.val-(a+v)) (by omega)
    change g.positive.letters _ = _ at hi' hj'
    rw [hi] at hi'
    rw [hj] at hj'
    rw [hi',hj']
    exact Or.inl (hneg _ _ (by change a+u+(j.val-(a+v)) = a+u+(i.val-(a+v))+1; omega))
  have hj : (⟨i.val+1,by omega⟩ : Fin (a+v+r)) = j := Fin.ext h.symm
  exact Or.inr (hj ▸ g.positive_segment (i := i.val) (by omega) (by omega))

theorem Gate.endpoints_incident (g : Gate ℓ a u v r α)
    {E : Letter ℓ α → Letter ℓ α → Prop} (hneg : g.negative.Follows E) :
    Incident E g.left ∧ Incident E g.right := by
  have ha := g.left_pos
  have hr := g.right_pos
  exact ⟨⟨g.negative.letters ⟨a,by omega⟩,Or.inl (hneg _ _ (show a = (a-1)+1 by omega))⟩,
    ⟨g.negative.letters ⟨a+u-1,by omega⟩,Or.inr (hneg _ _ (show a+u = (a+u-1)+1 by omega))⟩⟩

theorem Gate.incident_after (g : Gate ℓ a u v r α)
    {E : Letter ℓ α → Letter ℓ α → Prop} (hneg : g.negative.Follows E) {w : Letter ℓ α}
    (h : Incident (g.edges E) w) : Incident E w ∨ w ∈ g.inserted := by
  obtain ⟨z,hz⟩ := h
  rcases hz with (he | he) | (he | he)
  · exact Or.inl ⟨z,Or.inl he⟩
  · rcases List.mem_cons.mp (List.of_mem_zip he).1 with rfl | hi
    · exact Or.inl (g.endpoints_incident hneg).1
    · exact Or.inr hi
  · exact Or.inl ⟨z,Or.inr he⟩
  · rcases List.mem_append.mp (List.of_mem_zip he).2 with hi | hi
    · exact Or.inr hi
    · have hw : w = g.right := List.mem_singleton.mp hi
      exact Or.inl (hw ▸ (g.endpoints_incident hneg).2)

/-- A gate uses an entry identifier absent from the old graph. Even a
deletion-only gate produces the new marks and the bypass edge. -/
theorem Gate.history [DecidableEq α] (g : Gate ℓ a u v r α)
    {E : Letter ℓ α → Letter ℓ α → Prop} {marked : Finset (Fin ℓ)}
    (H : History ℓ α E marked) (hneg : g.negative.Follows E)
    (hentry : ∀ offset symbol, ¬ Incident E (.fresh g.entry offset symbol)) :
    History ℓ α (g.edges E) (marked ∪ (g.removed.filterMap Letter.position).toFinset) := by
  have avoids {w : Letter ℓ α} (hw : Incident E w) : w ∉ g.inserted := by
    intro h
    obtain ⟨i,rfl⟩ := g.mem_inserted.mp h
    exact hentry _ _ hw
  have he := g.old_segment hneg
  obtain ⟨hleft,hright⟩ := g.endpoints_incident hneg
  apply History.gate H g.left g.right g.removed g.inserted he
    (avoids hleft) (avoids hright) g.inserted_nodup
  · intro x y h
    exact ⟨avoids ⟨y,Or.inl h⟩,avoids ⟨x,Or.inr h⟩⟩
  · intro i h
    obtain ⟨j,hj⟩ := g.mem_inserted.mp h
    contradiction

#print axioms Gate.positive_follows
#print axioms Gate.history

end DeletionCode.Explicit.LetterGraphCuts
