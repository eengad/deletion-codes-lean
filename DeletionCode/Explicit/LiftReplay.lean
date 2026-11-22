import DeletionCode.Explicit.LiftSplice

/-! Source windows and symbolic gate replacement for manuscript replay. -/

namespace DeletionCode.Explicit.LetterSequence

variable {ℓ : ℕ} {α : Type*}

/-- The lift of a reference into the source is known before reading its symbols. -/
def sourceWindow (start len : ℕ) (h : start+len ≤ ℓ) : Lift ℓ len α where
  letters i := .original ⟨start+i.val,by omega⟩
  increasing := by
    intro i j p q hij hp hq
    have hp' := Option.some.inj hp
    have hq' := Option.some.inj hq
    subst p q
    exact Nat.add_lt_add_left hij start

@[simp] theorem sourceWindow_spelling (x : Fin ℓ → α) (start len : ℕ) (h : start+len ≤ ℓ) (i : Fin len) :
    (sourceWindow start len h).spelling x i = x ⟨start+i.val,by omega⟩ := rfl

@[simp] theorem sourceWindow_mem_positions (start len : ℕ) (h : start+len ≤ ℓ) {p : ℕ} :
    p ∈ (sourceWindow (α := α) start len h).positions ↔ start ≤ p ∧ p < start+len := by
  rw [Lift.mem_positions]
  constructor
  · rintro ⟨i,q,hq,rfl⟩
    have hq' := Option.some.inj hq
    subst q
    change start ≤ start+i.val ∧ start+i.val < start+len
    omega
  · rintro ⟨hl,hr⟩
    refine ⟨⟨p-start,by omega⟩,⟨p,by omega⟩,?_ ,rfl⟩
    exact congrArg some (Fin.ext (Nat.add_sub_of_le hl))

@[simp] theorem sourceWindow_fresh (start len : ℕ) (h : start+len ≤ ℓ) :
    (sourceWindow (α := α) start len h).freshOffsets = ∅ := by
  ext i
  simp [Lift.freshOffsets, sourceWindow, Letter.position]

@[simp] theorem sourceWindow_omissions (start len : ℕ) (h : start+len ≤ ℓ) :
    (sourceWindow (α := α) start len h).omissions = ∅ := by
  ext p
  simp only [Lift.omissions,Finset.mem_filter,Finset.mem_range,
    sourceWindow_mem_positions,Finset.notMem_empty,iff_false]
  rintro ⟨_,hn,⟨lo,hlo,hlo'⟩,⟨hi,hhi,hhi'⟩⟩
  exact hn ⟨by omega,by omega⟩

/-- If a selected source window spells the same word as the window on a
consumer's lift, its start is within one window length to the left of the
patch anchor, and within the patch's width to its right. -/
theorem source_reference_bounds {x : Fin ℓ → α} {K Λ m L start offset anchor width : ℕ}
    (hx : Strong x K Λ) (u : Lift ℓ m α)
    (hs : start+L ≤ ℓ) (hu : offset+L ≤ m) (hL : K+2*Λ ≤ L)
    (hspell : (sourceWindow start L hs).spelling x = (u.window offset L hu).spelling x)
    (hf : u.freshOffsets.card ≤ Λ) (ho : u.omissions.card ≤ Λ)
    (hpatch : ∀ p ∈ u.positions, anchor ≤ p ∧ p < anchor+width) :
    -(L : ℤ) ≤ (start : ℤ)-(anchor : ℤ) ∧ (start : ℤ)-(anchor : ℤ) < (width : ℤ) := by
  have hsf : (sourceWindow (α := α) start L hs).freshOffsets.card ≤ Λ := by simp
  have hso : (sourceWindow (α := α) start L hs).omissions.card ≤ Λ := by simp
  obtain ⟨i,p,_,hl,hr⟩ := aligned hx _ _ hL hspell hsf ((u.window_fresh_le hu).trans hf)
    hso ((Finset.card_le_card (u.window_omissions_subset hu)).trans ho)
  have hp := (sourceWindow_mem_positions (α := α) start L hs).mp
    ((sourceWindow start L hs).mem_positions.mpr ⟨i,p,hl,rfl⟩)
  have hp' := hpatch p.val (u.window_positions_subset hu ((u.window offset L hu).mem_positions.mpr
    ⟨i,p,hr,rfl⟩))
  omega

#print axioms source_reference_bounds

private def gateLetter {l u v r : ℕ} (old : Lift ℓ (l+u+r) α) (entry : ℕ)
    (replacement : Fin v → α) (i : Fin (l+v+r)) : Letter ℓ α :=
  if h : i.val < l then old.letters ⟨i.val,by omega⟩
  else if h' : i.val < l+v then .fresh entry (i.val-l) (replacement ⟨i.val-l,by omega⟩)
  else old.letters ⟨i.val-v+u,by omega⟩

private theorem gateLetter_original {l u v r : ℕ} (old : Lift ℓ (l+u+r) α) (entry : ℕ)
    (replacement : Fin v → α) (i : Fin (l+v+r)) (p : Fin ℓ)
    (hp : (gateLetter old entry replacement i).position = some p) :
    ∃ j : Fin (l+u+r), (old.letters j).position = some p ∧
      (i.val < l ∧ j.val = i.val ∨ l+v ≤ i.val ∧ j.val = i.val-v+u) := by
  by_cases h : i.val < l
  · exact ⟨⟨i.val,by omega⟩,by simpa only [gateLetter,dite_eq_left h] using hp,Or.inl ⟨h,rfl⟩⟩
  · by_cases h' : i.val < l+v
    · simp [gateLetter,h,h',Letter.position] at hp
    · exact ⟨⟨i.val-v+u,by omega⟩,by simpa only [gateLetter,dite_eq_right h,dite_eq_right h'] using hp,
        Or.inr ⟨Nat.le_of_not_lt h',rfl⟩⟩

/-- Install one gate on a negative lift by replacing its middle segment.
The positive lift reuses the two flanks and gives each inserted letter a
fresh identifier recording the entry and the insertion offset. -/
def Lift.installGate {l u v r : ℕ} (old : Lift ℓ (l+u+r) α) (entry : ℕ)
    (replacement : Fin v → α) : Lift ℓ (l+v+r) α where
  letters := gateLetter old entry replacement
  increasing := by
    intro i j p q hij hp hq
    obtain ⟨i',hi,hi'⟩ := gateLetter_original old entry replacement i p hp
    obtain ⟨j',hj,hj'⟩ := gateLetter_original old entry replacement j q hq
    apply old.increasing _ hi hj
    change i'.val < j'.val
    change i.val < j.val at hij
    rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj' <;> omega

theorem Lift.gate_left_letter {a u v r : ℕ} (old : Lift ℓ (a+u+r) α)
    (entry : ℕ) (replacement : Fin v → α) (i : ℕ) (hi : i < a) :
    (old.installGate entry replacement).letters ⟨i,by omega⟩ =
      old.letters ⟨i,by omega⟩ := by
  simp [Lift.installGate,gateLetter,hi]

theorem Lift.gate_inserted_letter {a u v r : ℕ} (old : Lift ℓ (a+u+r) α)
    (entry : ℕ) (replacement : Fin v → α) (i : Fin v) :
    (old.installGate entry replacement).letters ⟨a+i.val,by omega⟩ =
      .fresh entry i.val (replacement i) := by
  have hl : ¬ a+i.val < a := by omega
  have hm : a+i.val < a+v := by omega
  simp [Lift.installGate,gateLetter,hl,hm]

theorem Lift.gate_right_letter {a u v r : ℕ} (old : Lift ℓ (a+u+r) α)
    (entry : ℕ) (replacement : Fin v → α) (i : ℕ) (hi : i < r) :
    (old.installGate entry replacement).letters ⟨a+v+i,by omega⟩ =
      old.letters ⟨a+u+i,by omega⟩ := by
  have hl : ¬ a+v+i < a := by omega
  have hm : ¬ a+v+i < a+v := by omega
  have he : (⟨a+v+i-v+u,by omega⟩ : Fin (a+u+r)) = ⟨a+u+i,by omega⟩ :=
    Fin.ext (by change a+v+i-v+u = a+u+i; omega)
  simp only [Lift.installGate,gateLetter,dite_eq_right hl,dite_eq_right hm,he]

theorem Lift.gate_positions_subset {l u v r : ℕ} (old : Lift ℓ (l+u+r) α) (entry : ℕ)
    (replacement : Fin v → α) : (old.installGate entry replacement).positions ⊆ old.positions := by
  intro p hp
  obtain ⟨i,q,hq,rfl⟩ := (old.installGate entry replacement).mem_positions.mp hp
  obtain ⟨j,hj,_⟩ := gateLetter_original old entry replacement i q hq
  exact old.mem_positions.mpr ⟨j,q,hj,rfl⟩

/-- The gate spells the replacement inside the new segment. This assertion
also holds at either boundary when the deletion or a flank is empty. -/
theorem Lift.gate_middle {l u v r : ℕ} (old : Lift ℓ (l+u+r) α) (entry : ℕ)
    (replacement : Fin v → α) (x : Fin ℓ → α) (i : Fin v) :
    (old.installGate entry replacement).spelling x ⟨l+i.val,by omega⟩ = replacement i := by
  have h : ¬ l+i.val < l := by omega
  have h' : l+i.val < l+v := by omega
  simp [Lift.spelling,Lift.installGate,gateLetter,Letter.symbol,h,h']

/-- Both flanks keep their original spelling, with the right flank shifted
by the change in middle length. -/
theorem Lift.gate_flanks {l u v r : ℕ} (old : Lift ℓ (l+u+r) α) (entry : ℕ)
    (replacement : Fin v → α) (x : Fin ℓ → α) :
    (∀ i : Fin l, (old.installGate entry replacement).spelling x ⟨i.val,by omega⟩ =
      old.spelling x ⟨i.val,by omega⟩) ∧
    (∀ i : Fin r, (old.installGate entry replacement).spelling x ⟨l+v+i.val,by omega⟩ =
      old.spelling x ⟨l+u+i.val,by omega⟩) := by
  constructor
  · intro i
    simp only [Lift.spelling,Lift.installGate,gateLetter,dite_eq_left i.isLt]
  · intro i
    have hl : ¬ l+v+i.val < l := by omega
    have hu : ¬ l+v+i.val < l+v := by omega
    simp only [Lift.spelling,Lift.installGate,gateLetter,dite_eq_right hl,dite_eq_right hu]
    have he : (⟨l+v+i.val-v+u,by omega⟩ : Fin (l+u+r)) = ⟨l+u+i.val,by omega⟩ :=
      Fin.ext (by change l+v+i.val-v+u = l+u+i.val; omega)
    rw [he]

/-- Renumbering commutes with source reads and with restriction to a window. -/
@[simp] theorem sourceWindow_renameEntries {start n : ℕ} (h : start+n ≤ ℓ)
    (f : ℕ → ℕ) :
    (sourceWindow (α := α) start n h).renameEntries f = sourceWindow start n h := rfl

@[simp] theorem Lift.window_renameEntries {m : ℕ} (w : Lift ℓ m α) (a k : ℕ)
    (h : a+k ≤ m) (f : ℕ → ℕ) :
    (w.renameEntries f).window a k h = (w.window a k h).renameEntries f := rfl

theorem Lift.installGate_renameEntries {a u v r : ℕ} (w : Lift ℓ (a+u+r) α)
    (entry : ℕ) (replacement : Fin v → α) (f : ℕ → ℕ) :
    (w.renameEntries f).installGate (f entry) replacement =
      (w.installGate entry replacement).renameEntries f := by
  have hletters : ((w.renameEntries f).installGate (f entry) replacement).letters =
      ((w.installGate entry replacement).renameEntries f).letters := by
    funext i
    by_cases hl : i.val < a
    · simp [Lift.installGate,gateLetter,hl]
    · by_cases hm : i.val < a+v
      · simp [Lift.installGate,gateLetter,hl,hm,Letter.renameEntry]
      · simp [Lift.installGate,gateLetter,hl,hm]
  revert hletters
  generalize (w.renameEntries f).installGate (f entry) replacement = left
  generalize (w.installGate entry replacement).renameEntries f = right
  cases left
  cases right
  simp

#print axioms Lift.installGate_renameEntries

#print axioms Lift.gate_flanks
#print axioms Lift.gate_positions_subset
#print axioms Lift.gate_middle

end DeletionCode.Explicit.LetterSequence
