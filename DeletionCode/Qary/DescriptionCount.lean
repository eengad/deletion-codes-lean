import DeletionCode.DescriptionCount

/-!
The finite reconstruction format keeps alphabet letters separate from numeric fields.
Each of the ν headers stores two symbols. Each of the 4ν padded instruction rows
has one symbol slot, used by starts and ignored by fills and padding. Thus the
alphabet factor is q^(6ν). This intentionally overcounts the manuscript's tighter
q^(3ν) format, without introducing alphabet dependence in the polynomial exponent.
-/
namespace DeletionCode.Qary.DescriptionCount

abbrev fieldBound := DeletionCode.DescriptionCount.fieldBound

abbrev Description (α : Type*) (n L ν c : ℕ) :=
  (Fin c → Fin n) × (Fin ν → Fin (6 * L) × α × α) × (Fin c → Fin ν) ×
  (Fin (4 * ν) → (Fin 12 → Fin (fieldBound L ν)) × α)

theorem description_card (α : Type*) [Fintype α] (n L ν c : ℕ) :
    Fintype.card (Description α n L ν c) =
      Fintype.card (DeletionCode.DescriptionCount.Description n L ν c) *
        Fintype.card α ^ (6 * ν) := by
  simp only [Description, DeletionCode.DescriptionCount.Description,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, mul_pow]
  rw [show 6 * ν = ν + ν + 4 * ν by omega, pow_add, pow_add]
  ring

theorem description_bound (α : Type*) [Fintype α] (n L ν c : ℕ)
    (hL : 1 ≤ L) (hν : 1 ≤ ν) (hc : c ≤ ν) :
    Fintype.card (Description α n L ν c) ≤
      n ^ c * fieldBound L ν ^ (50 * ν) * Fintype.card α ^ (6 * ν) := by
  rw [description_card]
  exact Nat.mul_le_mul_right _
    (DeletionCode.DescriptionCount.description_bound n L ν c hL hν hc)

#print axioms description_bound
end DeletionCode.Qary.DescriptionCount
