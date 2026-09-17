import DeletionCode.RuleReconstruction
import DeletionCode.GeneratingCount

/-!
Counting signed generating rule sets with a fixed bubble-to-rule indexing.
The class is defined by actual signed spectra and structural bubble geometry.
Signed generation is converted to word generation, and recovered finite data
determines the rule set. No finiteness or injective coding premise is assumed.
Additional catalogue restrictions only reduce this class.
-/
namespace DeletionCode.SignedRuleCount

open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RecordSerialization GeneratingCount DescriptionCount

abbrev RuleSet (k : ℕ) := Finset (Gram (windowLength k) → ℤ)

/-- Rule sets admitting indexed, disjoint bubbles and signed generating provenance. -/
def GeneratingRuleSet (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : RuleSet k) : Prop :=
  ∃ E : EditedFamily (Fin ν) k,
    (∀ b, E.rank b = (group b).val) ∧
    BubbleGeometry E.family (windowLength k) ∧
    (∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) ∧
    SignedGenerating E.family x n (windowLength k) ∧
    Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) = c ∧
    rulesOfFamily E group = Q

/-- Every admitted signed rule set has a generating finite-data preimage. -/
theorem ruleSet_data_exists (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : RuleSet k) (hQ : GeneratingRuleSet x n k ν R c group Q) :
    ∃ data : RecoveredData ν, GeneratingData x n k ν c data ∧ rulesOfData k group data = Q := by
  obtain ⟨E, _, H, hdis, hgen, hc, hQ⟩ := hQ
  have hg := signed_generating_implies_generating E.family x n (windowLength k) H hdis hgen
  exact ⟨dataOfFamily E, ⟨E, hg, hc, rfl⟩, (rules_roundtrip E group).trans hQ⟩

/-- Choose finite recovered data, whose existence was proved from signed provenance. -/
noncomputable def chooseRuleData (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q}) :
    {data : RecoveredData ν // GeneratingData x n k ν c data} :=
  ⟨Classical.choose (ruleSet_data_exists x n k ν R c group Q.val Q.property),
    (Classical.choose_spec (ruleSet_data_exists x n k ν R c group Q.val Q.property)).1⟩

theorem rulesOf_chosenData (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q}) :
    rulesOfData k group (chooseRuleData x n k ν R c group Q).val = Q.val :=
  (Classical.choose_spec (ruleSet_data_exists x n k ν R c group Q.val Q.property)).2

/-- Deterministic rule reconstruction makes the chosen preimage assignment injective. -/
theorem chooseRuleData_injective (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R) :
    Function.Injective (chooseRuleData x n k ν R c group) := by
  intro Q₁ Q₂ heq
  apply Subtype.ext
  calc
    Q₁.val = rulesOfData k group (chooseRuleData x n k ν R c group Q₁).val :=
      (rulesOf_chosenData x n k ν R c group Q₁).symm
    _ = rulesOfData k group (chooseRuleData x n k ν R c group Q₂).val :=
      congrArg (fun data : {data : RecoveredData ν // GeneratingData x n k ν c data} =>
        rulesOfData k group data.val) heq
    _ = Q₂.val := rulesOf_chosenData x n k ν R c group Q₂

theorem generatingRuleSet_finite (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Finite {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} := by
  let : Finite {data : RecoveredData ν // GeneratingData x n k ν c data} :=
    generatingData_finite x n k ν c hν hx
  exact Finite.of_injective (chooseRuleData x n k ν R c group)
    (chooseRuleData_injective x n k ν R c group)

theorem generatingRuleSet_card_le_data (x : Letters) (n k ν R c : ℕ)
    (group : Fin ν → Fin R) (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} ≤
      Nat.card {data : RecoveredData ν // GeneratingData x n k ν c data} := by
  let : Finite {data : RecoveredData ν // GeneratingData x n k ν c data} :=
    generatingData_finite x n k ν c hν hx
  exact Nat.card_le_card_of_injective (chooseRuleData x n k ν R c group)
    (chooseRuleData_injective x n k ν R c group)

/-- The entire class of such signed generating rule sets satisfies the finite-record bound. -/
theorem generatingRuleSet_card_bound (x : Letters) (n k ν R c : ℕ)
    (group : Fin ν → Fin R) (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} ≤
      n ^ c * (fieldBound (windowLength k) ν) ^ (50 * ν) := by
  exact (generatingRuleSet_card_le_data x n k ν R c group hν hx).trans
    (generatingData_card_bound x n k ν c hν hx)

#print axioms ruleSet_data_exists
#print axioms chooseRuleData_injective
#print axioms generatingRuleSet_finite
#print axioms generatingRuleSet_card_le_data
#print axioms generatingRuleSet_card_bound

end DeletionCode.SignedRuleCount
