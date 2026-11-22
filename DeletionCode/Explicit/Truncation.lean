import DeletionCode.Burst.Basic

/-! Manuscript `d:truncation`, with the existing bounded substring edit channel. -/

namespace DeletionCode.Explicit

open Burst

variable {α : Type*} {b t : ℕ}

/-- A single bounded replacement, allowing the two blocks to be equal. -/
private def Replacement (b : ℕ) (x y : List α) : Prop :=
  ∃ a u v s : List α, u.length ≤ b ∧ v.length ≤ b ∧
    x = a ++ u ++ s ∧ y = a ++ v ++ s

private theorem map_edits (f : List α → List α)
    (step : ∀ a u v s : List α, u.length ≤ b → v.length ≤ b →
      Replacement b (f (a ++ u ++ s)) (f (a ++ v ++ s)))
    {x y : List α} (h : WithinBursts b t x y) : WithinBursts b t (f x) (f y) := by
  obtain ⟨r, hr, path⟩ := h
  suffices bound : WithinBursts b r (f x) (f y) by
    obtain ⟨j, hj, p⟩ := bound
    exact ⟨j, Nat.le_trans hj hr, p⟩
  clear hr
  induction path with
  | refl => exact ⟨0, Nat.le_refl _, .refl _⟩
  | @step a s u v r hu hv _ _ ih =>
    obtain ⟨j, hj, p⟩ := ih
    obtain ⟨a', u', v', s', hu', hv', hx, hy⟩ := step a u v s hu hv
    rw [hx] at p
    rw [hy]
    by_cases he : u' = v'
    · subst v'
      exact ⟨j, by omega, p⟩
    · exact ⟨j + 1, by omega, .step hu' hv' he p⟩

/-- Dropping the first symbol of `u ++ s` leaves the common suffix `s.tail`.
The part preceding that suffix uses at most as many symbols as `u`. -/
private theorem tail_split (u s : List α) :
    ∃ v : List α, v.length ≤ u.length ∧ (u ++ s).tail = v ++ s.tail := by
  cases u with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons a u =>
    cases s with
    | nil => exact ⟨u, by simp, by simp⟩
    | cons c s => exact ⟨u ++ [c], by simp, by simp [List.append_assoc]⟩

private theorem tail_edits {x y : List α} (h : WithinBursts b t x y) :
    WithinBursts b t x.tail y.tail := by
  apply map_edits List.tail _ h
  intro a u v s hu hv
  cases a with
  | cons c a => exact ⟨a, u, v, s, hu, hv, rfl, rfl⟩
  | nil =>
    obtain ⟨u', hu', eu⟩ := tail_split u s
    obtain ⟨v', hv', ev⟩ := tail_split v s
    exact ⟨[], u', v', s.tail, Nat.le_trans hu' hu, Nat.le_trans hv' hv, by simpa using eu, by simpa using ev⟩

private theorem reverse_edits {x y : List α} (h : WithinBursts b t x y) :
    WithinBursts b t x.reverse y.reverse := by
  apply map_edits List.reverse _ h
  intro a u v s hu hv
  exact ⟨s.reverse, u.reverse, v.reverse, a.reverse, by simpa using hu, by simpa using hv,
    by simp [List.reverse_append, List.append_assoc], by simp [List.reverse_append, List.append_assoc]⟩

/-- `d:truncation`, left end, including cuts longer than either word. -/
theorem withinBursts_drop (r : ℕ) {x y : List α} (h : WithinBursts b t x y) :
    WithinBursts b t (x.drop r) (y.drop r) := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
    simpa only [← List.drop_one, List.drop_drop] using tail_edits ih

/-- `d:truncation`, right end. Each cut is measured from its own word's end. -/
theorem withinBursts_dropRight (r : ℕ) {x y : List α} (h : WithinBursts b t x y) :
    WithinBursts b t (x.take (x.length - r)) (y.take (y.length - r)) := by
  simpa only [List.reverse_drop, List.reverse_reverse, List.length_reverse] using
    reverse_edits (withinBursts_drop r (reverse_edits h))

#print axioms withinBursts_drop
#print axioms withinBursts_dropRight

end DeletionCode.Explicit
