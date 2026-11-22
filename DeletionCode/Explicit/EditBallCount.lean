import DeletionCode.Explicit.EditBall
import Mathlib.Tactic.Ring

/-! The counting part of manuscript `d:tag-code`. The list counts records
with multiplicity, including empty edits that pad a shorter history. -/

namespace DeletionCode.Explicit

private theorem length_flatMap_const {α β : Type*} (xs : List α) (f : α → List β)
    (c : ℕ) (h : ∀ x ∈ xs, (f x).length = c) :
    (xs.flatMap f).length = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, h x (by simp), ih (by simp_all)]
    simp [Nat.succ_mul, Nat.add_comm]

theorem length_flatMap_bound {α β : Type*} (xs : List α) (f : α → List β)
    (c : ℕ) (h : ∀ x ∈ xs, (f x).length ≤ c) :
    (xs.flatMap f).length ≤ xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h₁ := h x (by simp)
    have h₂ := ih (by intro a ha; exact h a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

@[simp] theorem length_wordsOfLength (q m : ℕ) : (wordsOfLength q m).length = q ^ m := by
  induction m with
  | zero => simp [wordsOfLength]
  | succ m ih =>
    rw [wordsOfLength, length_flatMap_const _ _ (q ^ m) (by simp [ih])]
    simp [Nat.pow_succ, Nat.mul_comm]

def recordChoices (b q maxLen : ℕ) : ℕ := (maxLen + 1) * ((b + 1) * ((b + 1) * q ^ b))

private theorem oneEdit_count {q : ℕ} (hq : 0 < q) (b maxLen : ℕ)
    (x : QWord q) (hx : x.length ≤ maxLen) : (oneEdit b x).length ≤ recordChoices b q maxLen := by
  unfold oneEdit recordChoices
  apply Nat.le_trans (length_flatMap_bound _ _ ((b + 1) * ((b + 1) * q ^ b)) ?_)
  · simp [Nat.mul_le_mul_right _ (Nat.succ_le_succ hx)]
  intro i hi
  apply Nat.le_trans (length_flatMap_bound _ _ ((b + 1) * q ^ b) ?_)
  · simp [Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.min_le_left b (x.length - i)))]
  intro m hm
  apply Nat.le_trans (length_flatMap_bound _ _ (q ^ b) ?_)
  · simp
  intro vlen hv
  simp only [List.length_map, length_wordsOfLength]
  apply Nat.pow_le_pow_right hq
  simpa only [List.mem_range, Nat.lt_succ_iff] using hv

/-- With `s` slots and padding by empty edits, `B^s` already bounds the
enumerated records. The manuscript counts all record lengths separately. -/
theorem editBall_count {q : ℕ} (hq : 0 < q) (b s : ℕ) (x : QWord q) :
    (editBall b s x).length ≤ recordChoices b q (x.length + s * b) ^ s := by
  let B := recordChoices b q (x.length + s * b)
  suffices h : ∀ r ≤ s, (editBall b r x).length ≤ B ^ r from h s (Nat.le_refl _)
  intro r
  induction r with
  | zero => simp [editBall]
  | succ r ih =>
    intro hr
    have hp := ih (by omega)
    rw [editBall, Nat.pow_succ]
    apply Nat.le_trans (length_flatMap_bound _ _ B ?_) (Nat.mul_le_mul_right _ hp)
    intro y hy
    obtain ⟨j, hj, path⟩ := mem_editBall.mp hy
    have hlen := path.length_le
    have hmul := Nat.mul_le_mul_right b (show j ≤ s by omega)
    exact oneEdit_count hq b _ y (by omega)

/-- The exact expression `D_b(m)` from `d:tag-ball`. -/
def tagBallBound (q b s m : ℕ) : ℕ :=
  (s + 1) * (b + 1) ^ (2 * s) * q ^ (b * s) * (m + s * b + 1) ^ s

theorem editBall_le_tagBallBound {q : ℕ} (hq : 0 < q) (b s : ℕ) (x : QWord q) :
    (editBall b s x).length ≤ tagBallBound q b s x.length := by
  apply Nat.le_trans (editBall_count hq b s x)
  let B := recordChoices b q (x.length + s * b) ^ s
  have h : B ≤ (s + 1) * B := by rw [Nat.succ_mul]; omega
  apply Nat.le_trans h
  apply Nat.le_of_eq
  dsimp [B, tagBallBound, recordChoices]
  simp only [Nat.mul_pow, Nat.pow_mul, Nat.pow_two]
  ring

#print axioms editBall_le_tagBallBound

end DeletionCode.Explicit
