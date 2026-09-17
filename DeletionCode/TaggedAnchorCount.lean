import DeletionCode.CloseAnchorCount
import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum

/-!
Finite edit records have one bounded matched anchor and one of four tags per
edit. A close-anchor restriction saves one power of the word length. The
chronological decoder later turns these records into actual partner words.
-/
namespace DeletionCode.TaggedAnchorCount

abbrev Record (n r : ℕ) := (Fin r → Fin n) × (Fin r → Bool × Bool)

def packets {n r : ℕ} (rec : Record n r) : List (ℕ × (Bool × Bool)) :=
  List.ofFn (fun i => ((rec.1 i).val, rec.2 i))

theorem record_card (n r : ℕ) : Fintype.card (Record n r) = n ^ r * 4 ^ r := by
  simp only [Record, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]

def Bad {n r : ℕ} (m B : ℕ) (rec : Record n r) : Prop :=
  CloseAnchorCount.Bad m B rec.1

noncomputable def badEquiv (n r m B : ℕ) :
    {rec : Record n r // Bad m B rec} ≃
      {a : Fin r → Fin n // CloseAnchorCount.Bad m B a} × (Fin r → Bool × Bool) where
  toFun rec := (⟨rec.val.1, rec.property⟩, rec.val.2)
  invFun p := ⟨(p.1.val, p.2), p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem bad_record_card_le (n r m B : ℕ) :
    Nat.card {rec : Record n r // Bad m B rec} ≤
      r * (r + 2) * (2 * B) * n ^ (r - 1) * 4 ^ r := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (badEquiv n r m B),
    Fintype.card_prod, Fintype.card_fun, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin]
  norm_num only [Nat.reduceMul]
  apply Nat.mul_le_mul_right
  rw [Fintype.card_subtype]
  exact CloseAnchorCount.bad_card_le r n m B

#print axioms record_card
#print axioms bad_record_card_le

end DeletionCode.TaggedAnchorCount
