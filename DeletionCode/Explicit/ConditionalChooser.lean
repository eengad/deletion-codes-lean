import DeletionCode.Explicit.FieldHash
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-! Executable ternary conditional-expectation selector, `d:combined-CE`. -/
namespace DeletionCode.Explicit.ConditionalChooser

open FieldHash
open scoped BigOperators

abbrev Prefix := List F₃
abbrev Evaluator := Fin 3 → Prefix → ℚ

/-- The first value whose expectation does not exceed the current value. -/
def next (E : Prefix → ℚ) (p : Prefix) : F₃ :=
  let cur := E p
  if E (p ++ [0]) ≤ cur then 0 else if E (p ++ [1]) ≤ cur then 1 else 2

def step (E : Prefix → ℚ) (p : Prefix) : Prefix := p ++ [next E p]

def choose (E : Prefix → ℚ) (m : ℕ) : Prefix :=
  (step E)^[m] []

theorem step_length (E : Prefix → ℚ) (p : Prefix) : (step E p).length = p.length + 1 := by
  simp [step]

theorem choose_length (E : Prefix → ℚ) (m : ℕ) : (choose E m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [choose, Function.iterate_succ_apply', step_length]
    exact congrArg (· + 1) ih

def Averages (E : Prefix → ℚ) (p : Prefix) : Prop :=
  E (p ++ [0]) + E (p ++ [1]) + E (p ++ [2]) = 3 * E p

theorem step_le {E : Prefix → ℚ} {p : Prefix} (h : Averages E p) :
    E (step E p) ≤ E p := by
  unfold step next
  dsimp only
  split
  · assumption
  split
  · assumption
  unfold Averages at h
  linarith

def score (E : Evaluator) (μ : Fin 3 → ℚ) (p : Prefix) : ℚ :=
  E 0 p / μ 0 + E 1 p / μ 1 + E 2 p / μ 2

lemma score_eq_sum (E : Evaluator) (μ : Fin 3 → ℚ) (p : Prefix) :
    score E μ p = ∑ i, E i p / μ i := by
  rw [Fin.sum_univ_three, score]

theorem score_averages {E : Evaluator} {μ : Fin 3 → ℚ} {p : Prefix}
    (h : ∀ i, Averages (E i) p) : Averages (score E μ) p := by
  simp only [Averages, score_eq_sum] at *
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← add_div, ← add_div, h i, mul_div_assoc]

private theorem zero_step {E : Evaluator} {p : Prefix} (h : ∀ i, Averages (E i) p)
    (hn : ∀ i a, 0 ≤ E i (p ++ [a])) (i : Fin 3) (hz : E i p = 0) (a : F₃) :
    E i (p ++ [a]) = 0 := by
  have ht : ∀ a : F₃, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  have he := h i
  rw [Averages, hz, mul_zero] at he
  obtain rfl | rfl | rfl := ht a <;> linarith [hn i 0, hn i 1, hn i 2]

/-- Upper scales may equal zero or exceed the uniform root means. In the
zero case, nonnegativity and exact averaging force the selected leaf to vanish. -/
theorem choose_three_bounds (E : Evaluator) (μ : Fin 3 → ℚ) (m : ℕ)
    (hn : ∀ i p, p.length ≤ m → 0 ≤ E i p)
    (hr : ∀ i, E i [] ≤ μ i)
    (hs : ∀ i p, p.length < m → Averages (E i) p) :
    ∀ i, E i (choose (score E μ) m) ≤ 3 * μ i := by
  have hμ (i : Fin 3) : 0 ≤ μ i := (hn i [] (Nat.zero_le _)).trans (hr i)
  have hnscore (i : Fin 3) (p : Prefix) (hp : p.length ≤ m) : 0 ≤ E i p / μ i :=
    div_nonneg (hn i p hp) (hμ i)
  have hroot : score E μ [] ≤ 3 := by
    rw [score_eq_sum, ← show (∑ _ : Fin 3, (1 : ℚ)) = 3 by simp]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : μ i = 0
    · simp [hi]
    · apply (div_le_iff₀ (lt_of_le_of_ne (hμ i) (Ne.symm hi))).2
      simpa using hr i
  have hstate (k : ℕ) (hk : k ≤ m) :
      score E μ (choose (score E μ) k) ≤ 3 ∧
        ∀ i, μ i = 0 → E i (choose (score E μ) k) = 0 := by
    induction k with
    | zero =>
      exact ⟨hroot, fun i hi => le_antisymm ((hr i).trans (le_of_eq hi)) (hn i [] hk)⟩
    | succ k ih =>
      let p := choose (score E μ) k
      have hlen : p.length = k := choose_length _ _
      have hp : p.length < m := hlen ▸ Nat.lt_of_succ_le hk
      obtain ⟨hscore, hzero⟩ := ih (Nat.le_of_succ_le hk)
      have hnext : choose (score E μ) (k + 1) = step (score E μ) p := by
        simp only [choose, p, Function.iterate_succ_apply']
      rw [hnext]
      exact ⟨(step_le (score_averages fun i => hs i p hp)).trans hscore,
        fun i hi => zero_step (fun j => hs j p hp)
          (fun j a => hn j (p ++ [a]) (by simpa [hlen] using hk))
          i (hzero i hi) (next (score E μ) p)⟩
  intro i
  obtain ⟨hb, hz⟩ := hstate m le_rfl
  let p := choose (score E μ) m
  by_cases hi : μ i = 0
  · simp [p, hz i hi, hi]
  · have hpart : E i p / μ i ≤ score E μ p := by
      rw [score_eq_sum]
      exact Finset.single_le_sum (fun j _ => hnscore j p (choose_length _ _).le) (Finset.mem_univ i)
    exact (div_le_iff₀ (lt_of_le_of_ne (hμ i) (Ne.symm hi))).mp (hpart.trans hb)

#print axioms step_le
#print axioms choose_three_bounds

end DeletionCode.Explicit.ConditionalChooser
