import DeletionCode.Burst.Basic

/-!
Source positions for a bounded substring replacement. All replacement letters
are new, including letters whose values happen to match the removed block.
Surviving source positions remain injective and consecutive on either side.
-/
namespace DeletionCode.Burst.Edit

variable {α : Type*}

theorem word_of_origin [Inhabited α] (e : Edit α) (x : Letters α) {i r : ℕ}
    (h : e.origin i = some r) : e.word x i = x r := by
  by_cases hbefore : i < e.pos
  · simp only [origin, hbefore, ite_true, Option.some.injEq] at h
    subst r
    simp only [word, hbefore, ite_true]
  · by_cases hnew : i < e.pos + e.replacement.length
    · simp only [origin, hbefore, hnew, ite_false, ite_true, reduceCtorEq] at h
    · simp only [origin, hbefore, hnew, ite_false, Option.some.injEq] at h
      simp only [word, hbefore, hnew, ite_false, h]

theorem origin_injective (e : Edit α) {i j r : ℕ}
    (hi : e.origin i = some r) (hj : e.origin j = some r) : i = j := by
  by_cases hib : i < e.pos <;> by_cases hjb : j < e.pos <;>
    by_cases hin : i < e.pos + e.replacement.length <;>
    by_cases hjn : j < e.pos + e.replacement.length <;>
    simp_all only [origin, ite_true, ite_false, Option.some.injEq, reduceCtorEq] <;>
    omega

theorem origin_lt (e : Edit α) {n i r : ℕ} (hv : e.InBounds n)
    (hi : i < e.outputLength n) (hr : e.origin i = some r) : r < n := by
  unfold InBounds at hv
  unfold outputLength at hi
  by_cases hbefore : i < e.pos <;>
    by_cases hnew : i < e.pos + e.replacement.length <;>
    simp_all only [origin, ite_true, ite_false, Option.some.injEq, reduceCtorEq] <;>
    omega

theorem clean_block (e : Edit α) (a s k : ℕ)
    (h : a + s + k ≤ e.pos ∨ e.pos + e.replacement.length ≤ a + s) :
    ∃ r, ∀ i, i < k → e.origin (a + s + i) = some (r + i) := by
  rcases h with hbefore | hafter
  · refine ⟨a + s, ?_⟩
    intro i hi
    have hcut : a + s + i < e.pos := by omega
    simp only [origin, hcut, ite_true]
  · refine ⟨a + s + e.removed - e.replacement.length, ?_⟩
    intro i hi
    have hcut : ¬ a + s + i < e.pos := by omega
    have hnew : ¬ a + s + i < e.pos + e.replacement.length := by omega
    have heq : a + s + i + e.removed - e.replacement.length =
        a + s + e.removed - e.replacement.length + i := by omega
    simp only [origin, hcut, hnew, ite_false, heq]

theorem origin_before_or_after (e : Edit α) {i r : ℕ}
    (h : e.origin i = some r) :
    (i < e.pos ∧ r = i) ∨
      (e.pos + e.replacement.length ≤ i ∧ r = i + e.removed - e.replacement.length) := by
  by_cases hbefore : i < e.pos
  · left
    simpa only [origin, hbefore, ite_true, Option.some.injEq] using And.intro hbefore h.symm
  · by_cases hnew : i < e.pos + e.replacement.length
    · simp only [origin, hbefore, hnew, ite_false, ite_true, reduceCtorEq] at h
    · right
      simp only [origin, hbefore, hnew, ite_false, Option.some.injEq] at h
      exact ⟨by omega, h.symm⟩

#print axioms word_of_origin
#print axioms origin_injective
#print axioms origin_lt
#print axioms clean_block

end DeletionCode.Burst.Edit
