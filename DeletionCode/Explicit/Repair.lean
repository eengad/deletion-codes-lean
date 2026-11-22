import Mathlib.Data.List.Basic

/-! Manuscript `sec:d-repair`. The accepted-word test and one-step compressor
are supplied by the earlier, length-dependent construction. The inverse may
succeed off the compressor image, just as allowed in `sec:c-setting`. -/

namespace DeletionCode.Explicit

structure RepairData (α : Type*) where
  accepted : List α → Bool
  compress : List α → List α
  expand : List α → Option (List α)
  accepted_nil : accepted [] = true
  shortens : ∀ x, accepted x = false → (compress x).length + 1 = x.length
  expand_compress : ∀ x, accepted x = false → expand (compress x) = some x
  expand_length : ∀ y x, expand y = some x → x.length = y.length + 1

namespace RepairData

variable {α : Type*} (D : RepairData α)

/-- Each unit of fuel permits one compression of a rejected word. -/
def repairAux : ℕ → List α → List α
  | 0, x => x
  | fuel + 1, x => if D.accepted x then x else repairAux fuel (D.compress x)

def repair (x : List α) : List α := D.repairAux x.length x

/-- Undo exactly the requested number of steps, propagating the first failure. -/
def undo : ℕ → List α → Option (List α)
  | 0, y => some y
  | steps + 1, y => (undo steps y).bind D.expand

def inverse (k : ℕ) (y : List α) : Option (List α) :=
  if y.length ≤ k then D.undo (k - y.length) y else none

private theorem repairAux_spec (fuel : ℕ) (x : List α) (hx : x.length ≤ fuel) :
    D.accepted (D.repairAux fuel x) = true ∧
    (D.repairAux fuel x).length ≤ x.length ∧
    D.undo (x.length - (D.repairAux fuel x).length) (D.repairAux fuel x) = some x := by
  induction fuel generalizing x with
  | zero =>
    cases x with
    | nil => simp [repairAux, undo, D.accepted_nil]
    | cons _ _ => simp at hx
  | succ fuel ih =>
    cases h : D.accepted x with
    | true => simp [repairAux, h, undo]
    | false =>
      have hs := D.shortens x h
      obtain ⟨ha, hl, hu⟩ := ih (D.compress x) (by omega)
      simp only [repairAux, h, Bool.false_eq_true, ite_false]
      refine ⟨ha, by omega, ?_⟩
      have changeSteps : x.length - (D.repairAux fuel (D.compress x)).length =
          ((D.compress x).length - (D.repairAux fuel (D.compress x)).length) + 1 := by omega
      rw [changeSteps, undo, hu]
      exact D.expand_compress x h

/-- `d:repair`: the result is accepted and at most as long as the input. -/
theorem repair_accepted (x : List α) : D.accepted (D.repair x) = true :=
  (D.repairAux_spec x.length x (Nat.le_refl _)).1

theorem repair_length_le (x : List α) : (D.repair x).length ≤ x.length :=
  (D.repairAux_spec x.length x (Nat.le_refl _)).2.1

theorem inverse_repair (x : List α) : D.inverse x.length (D.repair x) = some x := by
  simp only [inverse, D.repair_length_le x, ↓reduceIte]
  exact (D.repairAux_spec x.length x (Nat.le_refl _)).2.2

theorem repair_injective_of_length_eq {x y : List α}
    (hlen : x.length = y.length) (heq : D.repair x = D.repair y) : x = y := by
  have h := D.inverse_repair x
  rw [hlen, heq, D.inverse_repair] at h
  exact (Option.some.inj h).symm

private theorem undo_length (steps : ℕ) (y x : List α)
    (h : D.undo steps y = some x) : x.length = y.length + steps := by
  induction steps generalizing x with
  | zero =>
    change some y = some x at h
    cases h
    simp
  | succ steps ih =>
    cases hmid : D.undo steps y with
    | none => simp [undo, hmid] at h
    | some mid =>
      have he : D.expand mid = some x := by simpa [undo, hmid] using h
      have := D.expand_length mid x he
      have := ih mid hmid
      omega

/-- Even off the image, a successful inverse returns a word of length `k`. -/
theorem inverse_length {k : ℕ} {y x : List α} (h : D.inverse k y = some x) :
    x.length = k := by
  unfold inverse at h
  split at h
  · have := D.undo_length _ y x h
    omega
  · contradiction

#print axioms repair_accepted
#print axioms repair_length_le
#print axioms inverse_repair
#print axioms repair_injective_of_length_eq
#print axioms inverse_length

end RepairData
end DeletionCode.Explicit
