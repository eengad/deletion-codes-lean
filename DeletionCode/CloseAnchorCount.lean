import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Counting tuples with an anchor near an endpoint or another anchor. The count
removes one coordinate, records the remaining tuple, and reconstructs the
omitted entry. Each distance constraint allows at most `2 * B` entries.
The right endpoint test is distance to `m`, so no bound on the anchors by `m`
is required. All cardinalities count actual tuples, including repeated anchors.
-/

namespace DeletionCode.CloseAnchorCount

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

/-- An endpoint-near or mutually close tuple of anchors. -/
def Bad {r n : ℕ} (m B : ℕ) (a : Fin r → Fin n) : Prop :=
  (∃ i, (a i).val < B) ∨
  (∃ i, Nat.dist (a i).val m < B) ∨
  (∃ i j, i ≠ j ∧ Nat.dist (a i).val (a j).val < B)

/-- A natural-number ball, intersected with `Fin n`, contains at most `2 * B` points. -/
theorem near_card_le (n c B : ℕ) :
    (univ.filter (fun x : Fin n => Nat.dist x.val c < B)).card ≤ 2 * B := by
  calc
    (univ.filter (fun x : Fin n => Nat.dist x.val c < B)).card ≤
        (range (2 * B)).card := by
      apply Finset.card_le_card_of_injOn (fun x : Fin n => x.val + B - c)
      · intro x hx
        have hd := (mem_filter.mp hx).2
        change x.val + B - c ∈ range (2 * B)
        rw [mem_range]
        unfold Nat.dist at hd
        omega
      · intro x hx y hy heq
        have hx' := (mem_filter.mp hx).2
        have hy' := (mem_filter.mp hy).2
        change x.val + B - c = y.val + B - c at heq
        unfold Nat.dist at hx' hy'
        apply Fin.ext
        omega
    _ = 2 * B := card_range _

/-- Omitting one coordinate leaves exactly `n^r` possible records; each record
admits at most `M` values of the omitted coordinate. -/
theorem coordinate_constraint_card_le {r n : ℕ} (i : Fin (r + 1))
    (P : (Fin r → Fin n) → Fin n → Prop) (M : ℕ)
    (hM : ∀ b, (univ.filter (P b)).card ≤ M) :
    (univ.filter (fun a : Fin (r + 1) → Fin n => P (i.removeNth a) (a i))).card ≤
      M * n ^ r := by
  let fibers : (Fin r → Fin n) → Finset (Fin (r + 1) → Fin n) :=
    fun b => (univ.filter (P b)).image (fun x => i.insertNth x b)
  have hcover :
      univ.filter (fun a : Fin (r + 1) → Fin n => P (i.removeNth a) (a i)) ⊆
        (univ : Finset (Fin r → Fin n)).biUnion fibers := by
    intro a ha
    apply mem_biUnion.mpr
    refine ⟨i.removeNth a, mem_univ _, ?_⟩
    apply mem_image.mpr
    refine ⟨a i, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ha).2⟩, ?_⟩
    exact Fin.insertNth_self_removeNth i a
  calc
    (univ.filter (fun a : Fin (r + 1) → Fin n => P (i.removeNth a) (a i))).card ≤
        ((univ : Finset (Fin r → Fin n)).biUnion fibers).card := card_le_card hcover
    _ ≤ (univ : Finset (Fin r → Fin n)).card * M :=
      card_biUnion_le_card_mul _ fibers M (fun b _ => (card_image_le).trans (hM b))
    _ = M * n ^ r := by simp [Nat.mul_comm]

/-- The reference point may depend on every coordinate except the constrained one. -/
theorem coordinate_near_card_le {r n : ℕ} (i : Fin (r + 1))
    (c : (Fin r → Fin n) → ℕ) (B : ℕ) :
    (univ.filter (fun a : Fin (r + 1) → Fin n =>
      Nat.dist (a i).val (c (i.removeNth a)) < B)).card ≤ (2 * B) * n ^ r := by
  have h := coordinate_constraint_card_le i (fun b x => Nat.dist x.val (c b) < B) (2 * B)
    (fun b => by
      apply le_of_eq_of_le ?_ (near_card_le n (c b) B)
      apply congrArg Finset.card
      ext x
      simp only [mem_filter, mem_univ, true_and])
  apply le_of_eq_of_le ?_ h
  apply congrArg Finset.card
  ext a
  simp only [mem_filter, mem_univ, true_and]

private abbrev EventIndex (r : ℕ) := Fin r × (Fin r ⊕ Bool)

private def Event {r n : ℕ} (m B : ℕ) (q : EventIndex r) (a : Fin r → Fin n) : Prop :=
  match q.2 with
  | .inl j => q.1 ≠ j ∧ Nat.dist (a q.1).val (a j).val < B
  | .inr false => (a q.1).val < B
  | .inr true => Nat.dist (a q.1).val m < B

private theorem event_card_le {r n : ℕ} (m B : ℕ) (q : EventIndex (r + 1)) :
    (univ.filter (Event (n := n) m B q)).card ≤ (2 * B) * n ^ r := by
  rcases q with ⟨i, s⟩
  cases s with
  | inl j =>
      by_cases hij : i = j
      · have hempty : univ.filter (Event (n := n) m B (i, .inl j)) = ∅ := by
          ext a
          simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty]
          change (i ≠ j ∧ Nat.dist (a i).val (a j).val < B) ↔ False
          simp [hij]
        rw [hempty, card_empty]
        exact Nat.zero_le _
      · obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
        apply le_of_eq_of_le ?_
          (coordinate_near_card_le (n := n) i (fun b => (b j').val) B)
        apply congrArg Finset.card
        ext a
        simp only [mem_filter, mem_univ, true_and]
        change (i ≠ j ∧ Nat.dist (a i).val (a j).val < B) ↔
          Nat.dist (a i).val (a (i.succAbove j')).val < B
        rw [hj']
        exact ⟨And.right, fun h => ⟨hij, h⟩⟩
  | inr b =>
      cases b with
      | false =>
          apply le_of_eq_of_le ?_ (coordinate_near_card_le (n := n) i (fun _ => 0) B)
          apply congrArg Finset.card
          ext a
          simp only [mem_filter, mem_univ, true_and]
          change (a i).val < B ↔ Nat.dist (a i).val 0 < B
          rw [Nat.dist_zero_right]
      | true =>
          apply le_of_eq_of_le ?_ (coordinate_near_card_le (n := n) i (fun _ => m) B)
          apply congrArg Finset.card
          ext a
          simp only [mem_filter, mem_univ, true_and]
          rfl

/-- A union bound over all actual endpoint and pair constraints. The exponent
is `r - 1`, and the theorem also covers `r = 0`, `n = 0`, and `B = 0`. -/
theorem bad_card_le (r n m B : ℕ) :
    (univ.filter (Bad (r := r) (n := n) m B)).card ≤
      r * (r + 2) * (2 * B) * n ^ (r - 1) := by
  cases r with
  | zero => simp [Bad]
  | succ r =>
      let events : EventIndex (r + 1) → Finset (Fin (r + 1) → Fin n) :=
        fun q => univ.filter (Event m B q)
      have hcover : univ.filter (Bad (r := r + 1) (n := n) m B) =
          (univ : Finset (EventIndex (r + 1))).biUnion events := by
        ext a
        simp only [mem_filter, mem_univ, true_and, mem_biUnion, events]
        constructor
        · rintro (⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, j, hij, hd⟩)
          · exact ⟨(i, .inr false), hi⟩
          · exact ⟨(i, .inr true), hi⟩
          · exact ⟨(i, .inl j), hij, hd⟩
        · rintro ⟨⟨i, s⟩, h⟩
          cases s with
          | inl j => exact Or.inr (Or.inr ⟨i, j, h⟩)
          | inr b =>
              cases b with
              | false => exact Or.inl ⟨i, h⟩
              | true => exact Or.inr (Or.inl ⟨i, h⟩)
      rw [hcover]
      calc
        ((univ : Finset (EventIndex (r + 1))).biUnion events).card ≤
            (univ : Finset (EventIndex (r + 1))).card * ((2 * B) * n ^ r) :=
          card_biUnion_le_card_mul _ events _ (fun q _ => event_card_le m B q)
        _ = (r + 1) * (r + 1 + 2) * (2 * B) * n ^ (r + 1 - 1) := by
          simp [EventIndex, Fintype.card_prod, Fintype.card_sum, Nat.mul_assoc]

#print axioms near_card_le
#print axioms coordinate_constraint_card_le
#print axioms coordinate_near_card_le
#print axioms bad_card_le

end

end DeletionCode.CloseAnchorCount
