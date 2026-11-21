import DeletionCode.CloseAnchorCount
import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum

/-!
A finite edit packet records two Boolean flags and an alphabet letter.
The same close-anchor restriction saves one positional choice; its payload
cost is (4q)^r for r packets. Invalid flag combinations are harmless overcounts.
-/
namespace DeletionCode.Qary.TaggedAnchorCount

variable {α : Type*}

abbrev Record (α : Type*) (n r : ℕ) :=
  (Fin r → Fin n) × (Fin r → (Bool × Bool) × α)

def packets {n r : ℕ} (rec : Record α n r) : List (ℕ × ((Bool × Bool) × α)) :=
  List.ofFn (fun i => ((rec.1 i).val, rec.2 i))

theorem record_card [Fintype α] (n r : ℕ) :
    Fintype.card (Record α n r) = n ^ r * (4 * Fintype.card α) ^ r := by
  simp only [Record, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]

def Bad {n r : ℕ} (m B : ℕ) (rec : Record α n r) : Prop :=
  CloseAnchorCount.Bad m B rec.1

noncomputable def badEquiv (n r m B : ℕ) :
    {rec : Record α n r // Bad m B rec} ≃
      {a : Fin r → Fin n // CloseAnchorCount.Bad m B a} ×
        (Fin r → (Bool × Bool) × α) where
  toFun rec := (⟨rec.val.1, rec.property⟩, rec.val.2)
  invFun p := ⟨(p.1.val, p.2), p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem bad_record_card_le [Fintype α] (n r m B : ℕ) :
    Nat.card {rec : Record α n r // Bad m B rec} ≤
      r * (r + 2) * (2 * B) * n ^ (r - 1) * (4 * Fintype.card α) ^ r := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (badEquiv n r m B),
    Fintype.card_prod, Fintype.card_fun]
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  norm_num only [Nat.reduceMul]
  apply Nat.mul_le_mul_right
  rw [Fintype.card_subtype]
  exact CloseAnchorCount.bad_card_le r n m B

#print axioms record_card
#print axioms bad_record_card_le

end DeletionCode.Qary.TaggedAnchorCount
