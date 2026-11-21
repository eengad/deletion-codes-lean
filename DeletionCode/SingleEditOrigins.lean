import DeletionCode.Windows

/-!
Source positions for an actual single insertion, deletion, or unchanged word.
An inserted bit has no source position. Every other output bit has the stated
source bit, and no source position is duplicated. A block avoiding the edit
has consecutive source positions. Validity and output bounds are explicit,
so unused tails of total letter functions are never treated as word data.
-/

namespace DeletionCode.SingleEditOrigins

open Windows

inductive Edit where
  | unchanged
  | delete (pos : ℕ)
  | insert (pos : ℕ) (bit : Bool)
  | substitute (pos : ℕ)
  deriving DecidableEq, Repr

namespace Edit

def cut : Edit → ℕ
  | .unchanged => 0
  | .delete pos => pos
  | .insert pos _ => pos
  | .substitute pos => pos

def outputLength (e : Edit) (n : ℕ) : ℕ :=
  match e with
  | .unchanged => n
  | .delete _ => n - 1
  | .insert _ _ => n + 1
  | .substitute _ => n

def Valid (e : Edit) (n : ℕ) : Prop :=
  match e with
  | .unchanged => True
  | .delete pos => pos < n
  | .insert pos _ => pos ≤ n
  | .substitute pos => pos < n

def word (e : Edit) (x : Letters) : Letters :=
  match e with
  | .unchanged => x
  | .delete pos => deleteAt x pos
  | .insert pos bit => insertAt x pos bit
  | .substitute pos => flipAt x pos

def origin (e : Edit) (i : ℕ) : Option ℕ :=
  match e with
  | .unchanged => some i
  | .delete pos => some (if i < pos then i else i + 1)
  | .insert pos _ =>
      if i < pos then some i else if i = pos then none else some (i - 1)
  | .substitute pos => if i = pos then none else some i

/-- A source-labelled output bit is precisely the bit at that source position. -/
theorem word_of_origin (e : Edit) (x : Letters) {i r : ℕ}
    (h : e.origin i = some r) : e.word x i = x r := by
  cases e with
  | unchanged => exact congrArg x (Option.some.inj h)
  | delete pos =>
    by_cases hi : i < pos
    · have hir : i = r := by simpa only [origin, ite_eq_left hi, Option.some.injEq] using h
      change (if i < pos then x i else x (i + 1)) = x r
      rw [ite_eq_left hi, hir]
    · have hir : i + 1 = r := by simpa only [origin, ite_eq_right hi, Option.some.injEq] using h
      simp only [word, deleteAt, ite_eq_right hi, hir]
  | insert pos bit =>
    by_cases hi : i < pos
    · have hir : i = r := by simpa only [origin, ite_eq_left hi, Option.some.injEq] using h
      change (if i < pos then x i else if i = pos then bit else x (i - 1)) = x r
      rw [ite_eq_left hi, hir]
    · by_cases heq : i = pos
      · simp only [origin, ite_eq_right hi, ite_eq_left heq, reduceCtorEq] at h
      · have hir : i - 1 = r := by
          simpa only [origin, ite_eq_right hi, ite_eq_right heq, Option.some.injEq] using h
        simp only [word, insertAt, ite_eq_right hi, ite_eq_right heq, hir]
  | substitute pos =>
    by_cases heq : i = pos
    · simp only [origin, ite_eq_left heq, reduceCtorEq] at h
    · have hir : i = r := by simpa only [origin, ite_eq_right heq, Option.some.injEq] using h
      subst hir
      simp only [word, flipAt, ite_eq_right heq]

/-- No original source position survives at two distinct output positions. -/
theorem origin_injective (e : Edit) {i j r : ℕ}
    (hi : e.origin i = some r) (hj : e.origin j = some r) : i = j := by
  cases e with
  | unchanged => exact (Option.some.inj hi).trans (Option.some.inj hj).symm
  | delete pos =>
    by_cases hiCut : i < pos <;> by_cases hjCut : j < pos <;>
      simp only [origin, hiCut, hjCut, ite_true, ite_false, Option.some.injEq] at hi hj <;>
      omega
  | insert pos bit =>
    by_cases hiCut : i < pos <;> by_cases hjCut : j < pos <;>
      by_cases hiEq : i = pos <;> by_cases hjEq : j = pos <;>
      simp_all only [origin, ite_true, ite_false, Option.some.injEq, reduceCtorEq] <;> omega
  | substitute pos =>
    by_cases hiEq : i = pos <;> by_cases hjEq : j = pos <;>
      simp_all only [origin, ite_true, ite_false, Option.some.injEq, reduceCtorEq] <;> omega

/-- Every surviving bit inside the valid output has an in-bounds source label. -/
theorem origin_lt (e : Edit) {n i r : ℕ} (hv : e.Valid n)
    (hi : i < e.outputLength n) (hr : e.origin i = some r) : r < n := by
  cases e with
  | unchanged =>
    have hir := Option.some.inj hr
    change i < n at hi
    omega
  | delete pos =>
    by_cases hcut : i < pos <;>
      simp only [Valid, outputLength, origin, hcut, ite_true, ite_false,
        Option.some.injEq] at hv hi hr <;> omega
  | insert pos bit =>
    by_cases hcut : i < pos <;> by_cases heq : i = pos <;>
      simp_all only [Valid, outputLength, origin, ite_true, ite_false,
        Option.some.injEq, reduceCtorEq] <;> omega
  | substitute pos =>
    by_cases heq : i = pos <;>
      simp_all only [Valid, outputLength, origin, ite_true, ite_false,
        Option.some.injEq, reduceCtorEq] <;> omega

/-- A block lying wholly before or strictly after the cut consists of
consecutive original source positions. This also holds for an empty block. -/
theorem clean_block (e : Edit) (a s k : ℕ)
    (h : a + s + k ≤ e.cut ∨ e.cut < a + s) :
    ∃ r, ∀ i, i < k → e.origin (a + s + i) = some (r + i) := by
  cases e with
  | unchanged => exact ⟨a + s, fun _ _ => rfl⟩
  | delete pos =>
    rcases h with hbefore | hafter
    · change a + s + k ≤ pos at hbefore
      refine ⟨a + s, ?_⟩
      intro i hi
      have hcut : a + s + i < pos := by omega
      simp only [origin, ite_eq_left hcut]
    · change pos < a + s at hafter
      refine ⟨a + s + 1, ?_⟩
      intro i hi
      have hcut : ¬ a + s + i < pos := by omega
      have heq : a + s + i + 1 = a + s + 1 + i := by omega
      simp only [origin, ite_eq_right hcut, heq]
  | insert pos bit =>
    rcases h with hbefore | hafter
    · change a + s + k ≤ pos at hbefore
      refine ⟨a + s, ?_⟩
      intro i hi
      have hcut : a + s + i < pos := by omega
      simp only [origin, ite_eq_left hcut]
    · change pos < a + s at hafter
      refine ⟨a + s - 1, ?_⟩
      intro i hi
      have hcut : ¬ a + s + i < pos := by omega
      have hne : a + s + i ≠ pos := by omega
      have heq : a + s + i - 1 = a + s - 1 + i := by omega
      simp only [origin, ite_eq_right hcut, ite_eq_right hne, heq]
  | substitute pos =>
    refine ⟨a + s, ?_⟩
    intro i hi
    have hne : a + s + i ≠ pos := by
      rcases h with hbefore | hafter
      · change a + s + k ≤ pos at hbefore
        omega
      · change pos < a + s at hafter
        omega
    simp only [origin, ite_eq_right hne]

#print axioms word_of_origin
#print axioms origin_injective
#print axioms origin_lt
#print axioms clean_block

end Edit
end DeletionCode.SingleEditOrigins
