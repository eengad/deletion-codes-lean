import DeletionCode.SignedRuleCount
import DeletionCode.RuleSetGraph
import DeletionCode.CountExponent

/-!
Counting underlying signed generating sets, with c(G) intrinsic to the signed
support graph. The class allows every edit-related bubble satisfying the
catalogue graph conditions, so extra catalogue filters only reduce the count.
The fixed index-to-rule grouping carries no additional description cost.
-/
namespace DeletionCode.CountingLemma

open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RuleSetGraph SignedRuleCount DescriptionCount CountExponent

/-- Underlying sets of R rules, presented by the fixed indexed bubble groups.
The component count refers to the signed rule set itself, not its presentation. -/
def GeneratingSet (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : RuleSet k) : Prop :=
  Q.card = R ∧ componentCount Q = c ∧
    ∃ E : EditedFamily (Fin ν) k,
      (∀ b, E.rank b = (group b).val) ∧
      BubbleGeometry E.family (windowLength k) ∧
      (∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) ∧
      SignedGenerating E.family x n (windowLength k) ∧ rulesOfFamily E group = Q

theorem generatingSet_mem (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : RuleSet k) (hQ : GeneratingSet x n k ν R c group Q) :
    GeneratingRuleSet x n k ν R c group Q := by
  obtain ⟨hcard, hc, E, hrank, H, hdis, hgen, hrules⟩ := hQ
  have hcomponents := componentCount_rulesOfFamily E group hrank H hdis
  have hcomponentCount : Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) = c := by
    rw [← hcomponents, hrules]
    exact hc
  exact ⟨E, hrank, H, hdis, hgen, hcomponentCount, hrules⟩

def generatingSetInclusion (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R) :
    {Q : RuleSet k // GeneratingSet x n k ν R c group Q} →
      {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} :=
  fun Q => ⟨Q.val, generatingSet_mem x n k ν R c group Q.val Q.property⟩

theorem generatingSet_finite (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Finite {Q : RuleSet k // GeneratingSet x n k ν R c group Q} := by
  let : Finite {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} :=
    generatingRuleSet_finite x n k ν R c group hν hx
  exact Finite.of_injective (generatingSetInclusion x n k ν R c group)
    (fun _ _ h => Subtype.ext (congrArg (fun Q : {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} => Q.val) h))

theorem generatingSet_record_bound (x : Letters) (n k ν R c : ℕ)
    (group : Fin ν → Fin R) (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet k // GeneratingSet x n k ν R c group Q} ≤
      n ^ c * fieldBound (windowLength k) ν ^ (50 * ν) := by
  let : Finite {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} :=
    generatingRuleSet_finite x n k ν R c group hν hx
  have hcard := Nat.card_le_card_of_injective (generatingSetInclusion x n k ν R c group)
    (fun _ _ h => Subtype.ext (congrArg (fun Q : {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} => Q.val) h))
  exact hcard.trans (generatingRuleSet_card_bound x n k ν R c group hν hx)

/-- The counting lemma's explicit bound for ν=2tR bubble occurrences. -/
theorem counting_generating_sets (t : ℕ) (ht : 1 ≤ t) (x : Letters)
    (n k R c : ℕ) (hR : 1 ≤ R) (hx : KUnique x n k)
    (group : Fin (2 * t * R) → Fin R) :
    Nat.card {Q : RuleSet k // GeneratingSet x n k (2 * t * R) R c group Q} ≤
      n ^ c * (windowLength k * R) ^ (exponent t * R) := by
  have hν : 1 ≤ 2 * t * R := by nlinarith
  exact (generatingSet_record_bound x n k (2 * t * R) R c group hν hx).trans
    (Nat.mul_le_mul_left (n ^ c) (field_power_bound k t R hR))

/-- One integer depending only on t works for every base word, size and component count. -/
theorem exists_counting_exponent (t : ℕ) (ht : 1 ≤ t) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ (x : Letters) (n k R c : ℕ),
      1 ≤ R → KUnique x n k → ∀ group : Fin (2 * t * R) → Fin R,
        Nat.card {Q : RuleSet k // GeneratingSet x n k (2 * t * R) R c group Q} ≤
          n ^ c * (windowLength k * R) ^ (a * R) := by
  exact ⟨exponent t, exponent_pos t ht, fun x n k R c hR hx group =>
    counting_generating_sets t ht x n k R c hR hx group⟩

#print axioms generatingSet_finite
#print axioms generatingSet_record_bound
#print axioms counting_generating_sets
#print axioms exists_counting_exponent

end DeletionCode.CountingLemma
