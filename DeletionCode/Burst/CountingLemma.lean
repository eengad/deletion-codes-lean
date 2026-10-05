import DeletionCode.Burst.SignedRuleCount
import DeletionCode.Qary.RuleSetGraph
import DeletionCode.Burst.CountExponent
import DeletionCode.Burst.FamilySupport

/-!
Counting underlying signed generating sets, with c(G) intrinsic to the signed
support graph. The class allows every edit-related bubble satisfying the
catalogue graph conditions, so extra catalogue filters only reduce the count.
The fixed index-to-rule grouping carries no additional description cost.
-/
namespace DeletionCode.Burst.CountingLemma

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

open DeletionCode.Qary.Windows DeletionCode.Burst.HeaderRecovery DeletionCode.Burst.GeneratingModel DeletionCode.Qary.SignedSupport DeletionCode.Burst.RuleReconstruction
open DeletionCode.Qary.RuleSetGraph DeletionCode.Burst.SignedRuleCount DeletionCode.Burst.DescriptionCount DeletionCode.Burst.CountExponent

/-- Underlying sets of R rules, presented by the fixed indexed bubble groups.
The component count refers to the signed rule set itself, not its presentation. -/
def GeneratingSet (x : Letters α) (n k d ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : RuleSet α (k + d)) : Prop :=
  Q.card = R ∧ componentCount Q = c ∧
    ∃ E : EditedFamily α (Fin ν) k d,
      (∀ b, E.rank b = (group b).val) ∧
      BubbleGeometry E.family (windowLength k d) ∧
      (∀ i, VertexDisjointOn E.family (windowLength k d) (ruleBubbles E.family i)) ∧
      SignedGenerating E.family x n (windowLength k d) ∧ rulesOfFamily E group = Q

theorem generatingSet_mem (x : Letters α) (n k d ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : RuleSet α (k + d)) (hQ : GeneratingSet x n k d ν R c group Q) :
    GeneratingRuleSet x n k d ν R c group Q := by
  obtain ⟨hcard, hc, E, hrank, H, hdis, hgen, hrules⟩ := hQ
  have hcomponents := FamilySupport.componentCount_rulesOfFamily E.family group hrank H hdis
  change componentCount (rulesOfFamily E group) = _ at hcomponents
  have hcomponentCount : Fintype.card (Qary.SupportComponents.GraphComponents E.family (windowLength k d)) = c := by
    have hnat := hcomponents.trans
      (@Nat.card_eq_fintype_card (Qary.SupportComponents.GraphComponents E.family (windowLength k d))
        (FamilySupport.graphComponentsFintype E.family (windowLength k d))).symm
    rw [hrules] at hnat
    exact (@Nat.card_eq_fintype_card
      (Qary.SupportComponents.GraphComponents E.family (windowLength k d))
      (GeneratingRecovery.graphComponentsFintype E)).symm.trans (hnat.symm.trans hc)
  exact ⟨E, hrank, H, hdis, hgen, hcomponentCount, hrules⟩

def generatingSetInclusion (x : Letters α) (n k d ν R c : ℕ) (group : Fin ν → Fin R) :
    {Q : RuleSet α (k + d) // GeneratingSet x n k d ν R c group Q} →
      {Q : RuleSet α (k + d) // GeneratingRuleSet x n k d ν R c group Q} :=
  fun Q => ⟨Q.val, generatingSet_mem x n k d ν R c group Q.val Q.property⟩

theorem generatingSet_finite (x : Letters α) (n k d ν R c : ℕ) (group : Fin ν → Fin R)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Finite {Q : RuleSet α (k + d) // GeneratingSet x n k d ν R c group Q} := by
  let : Finite {Q : RuleSet α (k + d) // GeneratingRuleSet x n k d ν R c group Q} :=
    generatingRuleSet_finite x n k d ν R c group hν hx
  exact Finite.of_injective (generatingSetInclusion x n k d ν R c group)
    (fun _ _ h => Subtype.ext (congrArg (fun Q : {Q : RuleSet α (k + d) // GeneratingRuleSet x n k d ν R c group Q} => Q.val) h))

theorem generatingSet_record_bound (x : Letters α) (n k d ν R c : ℕ)
    (group : Fin ν → Fin R) (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet α (k + d) // GeneratingSet x n k d ν R c group Q} ≤
      n ^ c * fieldBound (windowLength k d) ν ^ (53 * ν) * Fintype.card α ^ (6 * d * ν) := by
  let : Finite {Q : RuleSet α (k + d) // GeneratingRuleSet x n k d ν R c group Q} :=
    generatingRuleSet_finite x n k d ν R c group hν hx
  have hcard := Nat.card_le_card_of_injective (generatingSetInclusion x n k d ν R c group)
    (fun _ _ h => Subtype.ext (congrArg (fun Q : {Q : RuleSet α (k + d) // GeneratingRuleSet x n k d ν R c group Q} => Q.val) h))
  exact hcard.trans (generatingRuleSet_card_bound x n k d ν R c group hν hx)

/-- The counting lemma's explicit bound for ν=2tR bubble occurrences. -/
theorem counting_generating_sets (t : ℕ) (ht : 1 ≤ t) (x : Letters α)
    (n k d R c : ℕ) (hR : 1 ≤ R) (hx : KUnique x n k)
    (group : Fin (2 * t * R) → Fin R) :
    Nat.card {Q : RuleSet α (k + d) // GeneratingSet x n k d (2 * t * R) R c group Q} ≤
      n ^ c * (windowLength k d * R) ^ (exponent t * R) * Fintype.card α ^ (12 * d * t * R) := by
  have hν : 1 ≤ 2 * t * R := by nlinarith
  have h := (generatingSet_record_bound x n k d (2 * t * R) R c group hν hx).trans
    (Nat.mul_le_mul_right (Fintype.card α ^ (6 * d * (2 * t * R)))
      (Nat.mul_le_mul_left (n ^ c) (field_power_bound (windowLength k d) t R (by unfold windowLength; omega) hR)))
  convert h using 1 <;> congr 2 <;> ring

/-- One integer depending only on t works for every base word, size and component count. -/
theorem exists_counting_exponent (t : ℕ) (ht : 1 ≤ t) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ (x : Letters α) (n k d R c : ℕ),
      1 ≤ R → KUnique x n k → ∀ group : Fin (2 * t * R) → Fin R,
        Nat.card {Q : RuleSet α (k + d) // GeneratingSet x n k d (2 * t * R) R c group Q} ≤
          n ^ c * (windowLength k d * R) ^ (a * R) * Fintype.card α ^ (12 * d * t * R) := by
  exact ⟨exponent t, exponent_pos t ht, fun x n k d R c hR hx group =>
    counting_generating_sets t ht x n k d R c hR hx group⟩

#print axioms generatingSet_finite
#print axioms generatingSet_record_bound
#print axioms counting_generating_sets
#print axioms exists_counting_exponent

end DeletionCode.Burst.CountingLemma
