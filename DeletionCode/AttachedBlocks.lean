import DeletionCode.ComponentBounds
import DeletionCode.SignedRuleCount
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Size accounting for old blocks attached to a newly adjoined rule. Each old
block supplies an actual common support vertex. Pairwise disjointness of the
old support unions makes these chosen vertices distinct, bounding the number
of attached blocks by the new rule's actual support-vertex count.
-/

namespace DeletionCode.AttachedBlocks

open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open scoped BigOperators

/-- Different attached blocks must use different vertices of the new rule. -/
theorem attached_block_count_le_vertices {k : ℕ}
    (Bs : Finset (RuleSet k)) (w : Gram (windowLength k) → ℤ)
    (hmeet : ∀ B ∈ Bs, ∃ v, Incident B v ∧ Incident {w} v)
    (hdisjoint : ∀ B ∈ Bs, ∀ C ∈ Bs, B ≠ C →
      ∀ v, Incident B v → ¬ Incident C v) :
    Bs.card ≤ Fintype.card (RuleSetVertex {w}) := by
  classical
  let chooseVertex : Bs → RuleSetVertex {w} := fun B =>
    ⟨Classical.choose (hmeet B.val B.property),
      (Classical.choose_spec (hmeet B.val B.property)).2⟩
  have hbelongs (B : Bs) : Incident B.val (chooseVertex B).val :=
    (Classical.choose_spec (hmeet B.val B.property)).1
  have hinj : Function.Injective chooseVertex := by
    intro B C heq
    apply Subtype.ext
    by_contra hne
    have hvertices : (chooseVertex B).val = (chooseVertex C).val :=
      congrArg Subtype.val heq
    have hC : Incident C.val (chooseVertex B).val := by
      rw [hvertices]
      exact hbelongs C
    exact hdisjoint B.val B.property C.val C.property hne
      (chooseVertex B).val (hbelongs B) hC
  simpa using Fintype.card_le_of_injective chooseVertex hinj

/-- If each old block has at most L rules, their attached union plus the new
rule has at most one plus L times the new rule's support-vertex count. -/
theorem attached_union_card_bound {k : ℕ}
    (Bs : Finset (RuleSet k)) (w : Gram (windowLength k) → ℤ) (L : ℕ)
    (hsize : ∀ B ∈ Bs, B.card ≤ L)
    (hmeet : ∀ B ∈ Bs, ∃ v, Incident B v ∧ Incident {w} v)
    (hdisjoint : ∀ B ∈ Bs, ∀ C ∈ Bs, B ≠ C →
      ∀ v, Incident B v → ¬ Incident C v) :
    (insert w (Bs.biUnion id)).card ≤ 1 + L * Fintype.card (RuleSetVertex {w}) := by
  classical
  have hbi : (Bs.biUnion id).card ≤ ∑ B ∈ Bs, B.card := Finset.card_biUnion_le
  have hsum : (∑ B ∈ Bs, B.card) ≤ Bs.card * L := by
    calc
      (∑ B ∈ Bs, B.card) ≤ ∑ _ ∈ Bs, L := Finset.sum_le_sum hsize
      _ = Bs.card * L := by simp
  have hblocks := attached_block_count_le_vertices Bs w hmeet hdisjoint
  calc
    (insert w (Bs.biUnion id)).card ≤ (Bs.biUnion id).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ Bs.card * L + 1 := Nat.add_le_add_right (hbi.trans hsum) 1
    _ ≤ Fintype.card (RuleSetVertex {w}) * L + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right L hblocks) 1
    _ = 1 + L * Fintype.card (RuleSetVertex {w}) := by
      simp only [Nat.mul_comm, Nat.add_comm]

/-- The large-block quadratic size estimate from an actual support-vertex bound. -/
theorem attached_union_card_bound_quadratic {k : ℕ}
    (Bs : Finset (RuleSet k)) (w : Gram (windowLength k) → ℤ) (t L : ℕ)
    (hsize : ∀ B ∈ Bs, B.card ≤ L)
    (hmeet : ∀ B ∈ Bs, ∃ v, Incident B v ∧ Incident {w} v)
    (hdisjoint : ∀ B ∈ Bs, ∀ C ∈ Bs, B ≠ C →
      ∀ v, Incident B v → ¬ Incident C v)
    (hvertices : Fintype.card (RuleSetVertex {w}) ≤ 2 * t * (2 * L + 1)) :
    (insert w (Bs.biUnion id)).card ≤ 1 + 4 * t * L ^ 2 + 2 * t * L := by
  calc
    (insert w (Bs.biUnion id)).card ≤ 1 + L * Fintype.card (RuleSetVertex {w}) :=
      attached_union_card_bound Bs w L hsize hmeet hdisjoint
    _ ≤ 1 + L * (2 * t * (2 * L + 1)) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left L hvertices) 1
    _ = 1 + 4 * t * L ^ 2 + 2 * t * L := by ring

#print axioms attached_block_count_le_vertices
#print axioms attached_union_card_bound
#print axioms attached_union_card_bound_quadratic

end DeletionCode.AttachedBlocks
