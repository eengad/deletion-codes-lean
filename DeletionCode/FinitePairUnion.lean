import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic

/-!
A finite union bound over actual pairs of distinct ordered positions a < b.
Their number is derived by an explicit equivalence with a triangular sigma
type; no pair-count or union-cardinality inequality is assumed.
-/
namespace DeletionCode.FinitePairUnion

open scoped BigOperators
open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev OrderedPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- Choose the larger position b, then one of its b smaller positions. -/
def orderedPairEquiv (n : ℕ) : OrderedPair n ≃ Σ b : Fin n, Fin b.val where
  toFun p := ⟨p.val.2, ⟨p.val.1.val, p.property⟩⟩
  invFun p := ⟨(⟨p.2.val, p.2.isLt.trans p.1.isLt⟩, p.1), p.2.isLt⟩
  left_inv := by rintro ⟨⟨a, b⟩, hab⟩; rfl
  right_inv := by rintro ⟨b, a⟩; rfl

/-- The number of pairs a < b among n positions is exactly choose n 2,
including the empty cases n = 0 and n = 1. -/
theorem ordered_pair_card (n : ℕ) : Fintype.card (OrderedPair n) = n.choose 2 := by
  rw [Fintype.card_congr (orderedPairEquiv n), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id, Nat.choose_two_right]

/-- A union of events indexed by a < b has at most choose n 2 times the
maximum event size. The counted set contains each outcome only once. -/
theorem ordered_pair_union_bound {α : Type*} [Fintype α] [DecidableEq α]
    (n M : ℕ) (P : Fin n → Fin n → α → Prop)
    (hcount : ∀ a b, a < b → (univ.filter (P a b)).card ≤ M) :
    (univ.filter (fun x => ∃ a b, a < b ∧ P a b x)).card ≤ n.choose 2 * M := by
  let events : OrderedPair n → Finset α := fun p => univ.filter (P p.val.1 p.val.2)
  have hcover : univ.filter (fun x => ∃ a b, a < b ∧ P a b x) =
      (univ : Finset (OrderedPair n)).biUnion events := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, events]
    constructor
    · rintro ⟨a, b, hab, hx⟩
      exact ⟨⟨(a, b), hab⟩, hx⟩
    · rintro ⟨p, hx⟩
      exact ⟨p.val.1, p.val.2, p.property, hx⟩
  rw [hcover]
  calc
    ((univ : Finset (OrderedPair n)).biUnion events).card ≤
        (univ : Finset (OrderedPair n)).card * M :=
      Finset.card_biUnion_le_card_mul _ events M
        (fun p _ => hcount p.val.1 p.val.2 p.property)
    _ = n.choose 2 * M := by rw [Finset.card_univ, ordered_pair_card]

#print axioms ordered_pair_card
#print axioms ordered_pair_union_bound

end

end DeletionCode.FinitePairUnion
