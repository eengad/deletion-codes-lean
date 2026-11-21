import DeletionCode.DescriptionCount

/-!
A burst header contains four lengths and two blocks of at most b symbols.
Each of the 4ν padded instruction rows carries at most b extension symbols.
Numeric fields use the existing codec at length parameter 2L, accommodating
burst paths of length at most 3L. The alphabet contribution is exactly q^(6bν).
-/
namespace DeletionCode.Burst.DescriptionCount

abbrev fieldBound (L ν : ℕ) := DeletionCode.DescriptionCount.fieldBound (2 * L) ν

abbrev HeaderCode (α : Type*) (L b : ℕ) :=
  (Fin 4 → Fin L) × (Fin b → α) × (Fin b → α)

abbrev Description (α : Type*) (b n L ν c : ℕ) :=
  (Fin c → Fin n) × (Fin ν → HeaderCode α L b) × (Fin c → Fin ν) ×
  (Fin (4 * ν) → (Fin 12 → Fin (fieldBound L ν)) × (Fin b → α))

theorem description_card (α : Type*) [Fintype α] (b n L ν c : ℕ) :
    Fintype.card (Description α b n L ν c) =
      n ^ c * L ^ (4 * ν) * ν ^ c * fieldBound L ν ^ (48 * ν) *
        Fintype.card α ^ (6 * b * ν) := by
  simp only [Description, HeaderCode, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, mul_pow, ← pow_mul]
  rw [show 6 * b * ν = b * ν + b * ν + b * (4 * ν) by ring,
    pow_add, pow_add]
  ring

theorem description_bound (α : Type*) [Fintype α] (b n L ν c : ℕ)
    (hL : 1 ≤ L) (hν : 1 ≤ ν) (hc : c ≤ ν) :
    Fintype.card (Description α b n L ν c) ≤
      n ^ c * fieldBound L ν ^ (53 * ν) * Fintype.card α ^ (6 * b * ν) := by
  let B := fieldBound L ν
  have hmul : ν ≤ L * ν := by
    calc
      ν = 1 * ν := (one_mul ν).symm
      _ ≤ L * ν := Nat.mul_le_mul_right ν hL
  have hB : 1 ≤ B := by dsimp [B, fieldBound, DeletionCode.DescriptionCount.fieldBound]; nlinarith
  have hheader : L ≤ B := by dsimp [B, fieldBound, DeletionCode.DescriptionCount.fieldBound]; nlinarith
  have hname : ν ≤ B := by dsimp [B, fieldBound, DeletionCode.DescriptionCount.fieldBound]; nlinarith
  have hp1 : L ^ (4 * ν) ≤ B ^ (4 * ν) := by gcongr
  have hp2 : ν ^ c ≤ B ^ ν := by
    calc
      ν ^ c ≤ B ^ c := by gcongr
      _ ≤ B ^ ν := by gcongr
  have hpower : B ^ (4 * ν) * B ^ ν * B ^ (48 * ν) = B ^ (53 * ν) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [description_card]
  calc
    _ = n ^ c * (L ^ (4 * ν) * ν ^ c * B ^ (48 * ν)) * Fintype.card α ^ (6 * b * ν) := by ring
    _ ≤ n ^ c * (B ^ (4 * ν) * B ^ ν * B ^ (48 * ν)) * Fintype.card α ^ (6 * b * ν) := by gcongr
    _ = _ := by rw [hpower]

#print axioms description_bound
end DeletionCode.Burst.DescriptionCount
