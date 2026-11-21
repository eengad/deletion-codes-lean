import DeletionCode.Burst.RuleReconstruction
import DeletionCode.Burst.GeneratingCount
import DeletionCode.Qary.SignedRuleCount

/-!
Counting signed generating rule sets with a fixed bubble-to-rule indexing.
The class is defined by actual signed spectra and structural bubble geometry.
Signed generation is converted to word generation, and recovered finite data
determines the rule set. No finiteness or injective coding premise is assumed.
Additional catalogue restrictions only reduce this class.
-/
namespace DeletionCode.Burst.SignedRuleCount

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

open DeletionCode.Qary.Windows DeletionCode.Burst.HeaderRecovery DeletionCode.Burst.GeneratingModel DeletionCode.Qary.SignedSupport DeletionCode.Burst.RuleReconstruction
open DeletionCode.Burst.RecordSerialization DeletionCode.Burst.GeneratingCount DeletionCode.Burst.DescriptionCount

abbrev RuleSet := Qary.SignedRuleCount.RuleSet

/-- Rule sets admitting indexed, disjoint bubbles and signed generating provenance. -/
def GeneratingRuleSet (x : Letters α) (n k d ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : RuleSet α (k + d)) : Prop :=
  ∃ E : EditedFamily α (Fin ν) k d,
    (∀ b, E.rank b = (group b).val) ∧
    BubbleGeometry E.family (windowLength k d) ∧
    (∀ i, VertexDisjointOn E.family (windowLength k d) (ruleBubbles E.family i)) ∧
    SignedGenerating E.family x n (windowLength k d) ∧
    Fintype.card (Qary.SupportComponents.GraphComponents E.family (windowLength k d)) = c ∧
    rulesOfFamily E group = Q

/-- Every admitted signed rule set has a generating finite-data preimage. -/
theorem ruleSet_data_exists (x : Letters α) (n k d ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : RuleSet α (k + d)) (hQ : GeneratingRuleSet x n k d ν R c group Q) :
    ∃ data : RecoveredData α ν, GeneratingData x n k d ν c data ∧ rulesOfData k d group data = Q := by
  obtain ⟨E, _, H, hdis, hgen, hc, hQ⟩ := hQ
  have hg := signed_generating_implies_generating E.family x n (windowLength k d) H hdis hgen
  exact ⟨dataOfFamily E, ⟨E, hg, hc, rfl⟩, (rules_roundtrip E group).trans hQ⟩

/-- Choose finite recovered data, whose existence was proved from signed provenance. -/
noncomputable def chooseRuleData (x : Letters α) (n k d ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : {Q : RuleSet α (k + d) // GeneratingRuleSet x n k d ν R c group Q}) :
    {data : RecoveredData α ν // GeneratingData x n k d ν c data} :=
  ⟨Classical.choose (ruleSet_data_exists x n k d ν R c group Q.val Q.property),
    (Classical.choose_spec (ruleSet_data_exists x n k d ν R c group Q.val Q.property)).1⟩

theorem rulesOf_chosenData (x : Letters α) (n k d ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : {Q : RuleSet α (k + d) // GeneratingRuleSet x n k d ν R c group Q}) :
    rulesOfData k d group (chooseRuleData x n k d ν R c group Q).val = Q.val :=
  (Classical.choose_spec (ruleSet_data_exists x n k d ν R c group Q.val Q.property)).2

/-- Deterministic rule reconstruction makes the chosen preimage assignment injective. -/
theorem chooseRuleData_injective (x : Letters α) (n k d ν R c : ℕ) (group : Fin ν → Fin R) :
    Function.Injective (chooseRuleData x n k d ν R c group) := by
  intro Q₁ Q₂ heq
  have h₁ := rulesOf_chosenData x n k d ν R c group Q₁
  have h₂ := rulesOf_chosenData x n k d ν R c group Q₂
  rw [heq] at h₁
  exact Subtype.ext (h₁.symm.trans h₂)

theorem generatingRuleSet_finite (x : Letters α) (n k d ν R c : ℕ) (group : Fin ν → Fin R)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Finite {Q : RuleSet α (k + d) // GeneratingRuleSet x n k d ν R c group Q} := by
  let : Finite {data : RecoveredData α ν // GeneratingData x n k d ν c data} :=
    generatingData_finite x n k d ν c hν hx
  exact Finite.of_injective (chooseRuleData x n k d ν R c group)
    (chooseRuleData_injective x n k d ν R c group)

theorem generatingRuleSet_card_le_data (x : Letters α) (n k d ν R c : ℕ)
    (group : Fin ν → Fin R) (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet α (k + d) // GeneratingRuleSet x n k d ν R c group Q} ≤
      Nat.card {data : RecoveredData α ν // GeneratingData x n k d ν c data} := by
  let : Finite {data : RecoveredData α ν // GeneratingData x n k d ν c data} :=
    generatingData_finite x n k d ν c hν hx
  exact Nat.card_le_card_of_injective (chooseRuleData x n k d ν R c group)
    (chooseRuleData_injective x n k d ν R c group)

/-- The entire class of such signed generating rule sets satisfies the finite-record bound. -/
theorem generatingRuleSet_card_bound (x : Letters α) (n k d ν R c : ℕ)
    (group : Fin ν → Fin R) (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet α (k + d) // GeneratingRuleSet x n k d ν R c group Q} ≤
      n ^ c * (fieldBound (windowLength k d) ν) ^ (53 * ν) * Fintype.card α ^ (6 * d * ν) := by
  exact (generatingRuleSet_card_le_data x n k d ν R c group hν hx).trans
    (generatingData_card_bound x n k d ν c hν hx)

#print axioms ruleSet_data_exists
#print axioms chooseRuleData_injective
#print axioms generatingRuleSet_finite
#print axioms generatingRuleSet_card_le_data
#print axioms generatingRuleSet_card_bound

end DeletionCode.Burst.SignedRuleCount
