import DeletionCode.Explicit.EditBallCount
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith

/-! The executable parameter choices of `d:tag-constant` and `d:tag-length`. -/

namespace DeletionCode.Explicit

def TagConstantOK (b s C : ℕ) : Prop :=
  b * s ≤ C ∧ (s + 1) * (b + 1) ^ (2 * s) * (C + s + 2) ^ s ≤ 2 ^ (C - b * s)

instance (b s C : ℕ) : Decidable (TagConstantOK b s C) := by unfold TagConstantOK; infer_instance

/-- Quadratic growth fits under a power of two from exponent four onward. -/
theorem square_le_two_pow (k : ℕ) (hk : 4 ≤ k) : k * k ≤ 2 ^ k := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction r with
  | zero => decide
  | succ r ih =>
    rw [show 4 + (r + 1) = (4 + r) + 1 by omega, Nat.pow_succ]
    nlinarith

private theorem tagConstant_exists (b s : ℕ) : ∃ C, TagConstantOK b s C := by
  let A := (s + 1) * (b + 1) ^ (2 * s)
  let k := A + b * s + s + 4
  let C := 2 ^ k
  have hks : s + 1 ≤ k := by dsimp [k]; omega
  have hsquare : k * k ≤ C := square_le_two_pow k (by dsimp [k]; omega)
  have hkC : k < C := Nat.lt_pow_self (by decide : 1 < 2)
  have hbC : b * s ≤ C := by dsimp [k] at hkC; omega
  have hsC : s + 2 ≤ C := by omega
  have hh : A + (k + 1) * s + b * s ≤ C := by
    have hprod := Nat.mul_le_mul_left k hks
    have hk : A + b * s + s ≤ k := by dsimp [k]; omega
    nlinarith
  refine ⟨C, hbC, ?_⟩
  change A * (C + s + 2) ^ s ≤ 2 ^ (C - b * s)
  calc
    _ ≤ 2 ^ A * (2 ^ (k + 1)) ^ s := by
      apply Nat.mul_le_mul (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))
      apply Nat.pow_le_pow_left
      rw [Nat.pow_succ]
      change C + s + 2 ≤ C * 2
      omega
    _ = 2 ^ (A + (k + 1) * s) := by rw [Nat.pow_add (2 : ℕ) A ((k + 1) * s), Nat.pow_mul 2 (k + 1) s]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- Sequential search for the first admissible constant, as in the paper.
Only the proof of termination uses the explicit large witness above. -/
def tagConstant (b s : ℕ) : ℕ := Nat.find (tagConstant_exists b s)

theorem tagConstant_spec (b s : ℕ) : TagConstantOK b s (tagConstant b s) :=
  Nat.find_spec (tagConstant_exists b s)

def tagLength (q b s M e : ℕ) : ℕ :=
  let l := Nat.clog q M
  l + s * Nat.clog q (l + e + s * b + 2) + tagConstant b s

/-- `d:tag-length`: the same base length pays for edit balls with up to
`e` extra tag symbols. -/
theorem tagLength_sufficient {q : ℕ} (hq : 2 ≤ q) (b s M e : ℕ) :
    M * tagBallBound q b s (tagLength q b s M e + e) ≤ q ^ tagLength q b s M e := by
  let l := Nat.clog q M
  let v := l + e + s * b + 2
  let r := Nat.clog q v
  let C := tagConstant b s
  let A := (s + 1) * (b + 1) ^ (2 * s)
  let m := tagLength q b s M e
  have hm : m = l + s * r + C := rfl
  obtain ⟨hC, hcost⟩ := tagConstant_spec b s
  change b * s ≤ C at hC
  change A * (C + s + 2) ^ s ≤ 2 ^ (C - b * s) at hcost
  have hM : M ≤ q ^ l := Nat.le_pow_clog hq _
  have hv : v ≤ q ^ r := Nat.le_pow_clog hq _
  have hr : r ≤ v := Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self hq))
  have hlarge : m + e + s * b + 1 ≤ (C + s + 2) * v := by
    have hv1 : 1 ≤ v := by dsimp [v]; omega
    have hCv := Nat.mul_le_mul_left C hv1
    have hsv := Nat.mul_le_mul_left s hr
    have hvdef : v = l + e + s * b + 2 := rfl
    nlinarith
  have hsize : (m + e + s * b + 1) ^ s ≤ (C + s + 2) ^ s * (q ^ r) ^ s := by
    rw [← Nat.mul_pow]
    exact Nat.pow_le_pow_left (Nat.le_trans hlarge (Nat.mul_le_mul_left _ hv)) _
  have hconst : A * (C + s + 2) ^ s ≤ q ^ (C - b * s) :=
    Nat.le_trans hcost (Nat.pow_le_pow_left hq _)
  change M * (A * q ^ (b * s) * (m + e + s * b + 1) ^ s) ≤ q ^ m
  calc
    _ ≤ q ^ l * (A * q ^ (b * s) * ((C + s + 2) ^ s * (q ^ r) ^ s)) :=
      Nat.mul_le_mul hM (Nat.mul_le_mul_left _ hsize)
    _ = (q ^ l * (q ^ r) ^ s * q ^ (b * s)) * (A * (C + s + 2) ^ s) := by ring
    _ ≤ (q ^ l * (q ^ r) ^ s * q ^ (b * s)) * q ^ (C - b * s) :=
      Nat.mul_le_mul_left _ hconst
    _ = q ^ m := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, hm, Nat.mul_comm r s]
      congr 1
      omega

#print axioms tagConstant_spec
#print axioms tagLength_sufficient

end DeletionCode.Explicit
