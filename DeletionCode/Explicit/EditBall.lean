import DeletionCode.Burst.ChronologicalRecords

/-! The executable edit-record enumeration shared by `d:tag-code` and
`d:wrapper-decoding`. Duplicate records may produce the same endpoint. -/

namespace DeletionCode.Explicit

open Burst

abbrev QWord (q : ℕ) := List (Fin q)

/-- Lexicographic order on the words of a given length. -/
def wordsOfLength (q : ℕ) : ℕ → List (QWord q)
  | 0 => [[]]
  | k + 1 => (List.finRange q).flatMap (fun a => (wordsOfLength q k).map (a :: ·))

@[simp] theorem mem_wordsOfLength {q k : ℕ} {w : QWord q} :
    w ∈ wordsOfLength q k ↔ w.length = k := by
  induction k generalizing w with
  | zero => cases w <;> simp [wordsOfLength]
  | succ k ih => cases w <;> simp [wordsOfLength, List.mem_flatMap, List.mem_map, ih]

/-- Only valid positions and removal lengths are enumerated. Equal replacements
are harmless, including the empty replacement of the empty block. -/
def oneEdit (b : ℕ) {q : ℕ} (x : QWord q) : List (QWord q) :=
  (List.range (x.length + 1)).flatMap fun i =>
    (List.range (min b (x.length - i) + 1)).flatMap fun m =>
      (List.range (b + 1)).flatMap fun vlen =>
        (wordsOfLength q vlen).map fun v => (Edit.mk i m v).apply x

private theorem oneEdit_sound {b q : ℕ} {x y : QWord q} (h : y ∈ oneEdit b x) :
    WithinBursts b 1 x y := by
  simp only [oneEdit, List.mem_flatMap, List.mem_range, List.mem_map, mem_wordsOfLength] at h
  obtain ⟨i, hi, m, hm, vlen, hv, v, hlen, rfl⟩ := h
  let e : Edit (Fin q) := ⟨i, m, v⟩
  have hin : e.InBounds x.length := by change i + m ≤ x.length; omega
  have hs := e.decomposition x
  have he := e.sourceBlock_length x hin
  by_cases eq : e.sourceBlock x = v
  · refine ⟨0, by decide, ?_⟩
    rw [eq] at hs
    change Script b x (x.take i ++ v ++ x.drop (i + m)) 0
    rw [show x.take i ++ v ++ x.drop (i + m) = x from hs]
    exact .refl _
  · have prev : Script b x (x.take i ++ e.sourceBlock x ++ x.drop (i + m)) 0 := by
      rw [show x.take i ++ e.sourceBlock x ++ x.drop (i + m) = x from hs]
      exact .refl _
    have hshort : (e.sourceBlock x).length ≤ b := by rw [he]; change m ≤ b; omega
    exact ⟨1, Nat.le_refl _, .step hshort (by change v.length ≤ b; omega) eq prev⟩

private theorem oneEdit_contains {b q : ℕ} (a u v s : QWord q)
    (hu : u.length ≤ b) (hv : v.length ≤ b) :
    a ++ v ++ s ∈ oneEdit b (a ++ u ++ s) := by
  simp only [oneEdit, List.mem_flatMap, List.mem_range, List.mem_map, mem_wordsOfLength,
    List.length_append]
  exact ⟨a.length, by omega, u.length, by omega, v.length, by omega,
    v, rfl, Edit.apply_split a u v s⟩

/-- All endpoints of at most `r` bounded edits. An empty replacement
at position zero pads a shorter record at its own endpoint. -/
def editBall (b : ℕ) {q : ℕ} : ℕ → QWord q → List (QWord q)
  | 0, x => [x]
  | r + 1, x =>
    (editBall b r x).flatMap (oneEdit b)

theorem mem_editBall {b q r : ℕ} {x y : QWord q} :
    y ∈ editBall b r x ↔ WithinBursts b r x y := by
  induction r generalizing y with
  | zero =>
    constructor
    · intro h
      have hy : y = x := by simpa [editBall] using h
      subst y
      exact ⟨0, Nat.le_refl _, .refl _⟩
    · rintro ⟨j, hj, path⟩
      obtain rfl : j = 0 := by omega
      cases path
      simp [editBall]
  | succ r ih =>
    simp only [editBall, List.mem_flatMap, ih]
    constructor
    · rintro ⟨mid, ⟨j, hj, path⟩, h⟩
      obtain ⟨d, hd, one⟩ := oneEdit_sound h
      exact ⟨j + d, by omega, path.trans one⟩
    · rintro ⟨j, hj, path⟩
      cases path with
      | refl =>
        refine ⟨x, ⟨0, Nat.zero_le _, .refl _⟩, ?_⟩
        simpa using oneEdit_contains (b := b) [] [] [] x (Nat.zero_le _) (Nat.zero_le _)
      | @step a s u v j hu hv hne prev =>
        exact ⟨a ++ u ++ s, ⟨j, by omega, prev⟩, oneEdit_contains a u v s hu hv⟩

/-- Whole transmitted-word candidates, as in `d:wrapper-decoding`. -/
def candidates (n b t : ℕ) {q : ℕ} (z : QWord q) : List (QWord q) :=
  if n - t * b ≤ z.length ∧ z.length ≤ n + t * b then
    (editBall b t z).filter (fun w => w.length == n)
  else []

theorem mem_candidates {n b t q : ℕ} {w z : QWord q} :
    w ∈ candidates n b t z ↔ w.length = n ∧ WithinBursts b t w z := by
  constructor
  · intro h
    unfold candidates at h
    split at h
    · simp only [List.mem_filter, beq_iff_eq, mem_editBall] at h
      obtain ⟨⟨j, hj, path⟩, hw⟩ := h
      exact ⟨hw, j, hj, path.reverse⟩
    · simp at h
  · rintro ⟨rfl, j, hj, path⟩
    have hlo := path.source_length_le
    have hhi := path.length_le
    have hmul := Nat.mul_le_mul_right b hj
    have hrange : w.length - t * b ≤ z.length ∧ z.length ≤ w.length + t * b := by omega
    unfold candidates
    split
    · simp only [List.mem_filter, beq_iff_eq, mem_editBall]
      exact ⟨⟨j, hj, path.reverse⟩, trivial⟩
    · rename_i h
      exact (h hrange).elim

#print axioms mem_editBall
#print axioms mem_candidates

end DeletionCode.Explicit
