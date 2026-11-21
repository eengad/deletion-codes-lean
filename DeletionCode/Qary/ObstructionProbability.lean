import DeletionCode.Qary.VerifiedConflictGraphWitness
import DeletionCode.Qary.WitnessCounting
import DeletionCode.RandomHash

/-!
A probability bound for an actual retained conflict-graph vertex lying in a
component that is not two-colorable. Verified bounded-witness extraction covers
this event by fixed, independent candidate rule sets. The real-weight hash law
then gives the survival probability of each candidate, and finite union bounds
sum over the candidates and their allowed sizes. No witness or survival event
is supplied as a hypothesis of the final estimate.
-/

namespace DeletionCode.Qary.ObstructionProbability

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

open MeasureTheory DeletionCode.Qary.Windows DeletionCode.Qary.HeaderRecovery DeletionCode.Qary.SignedSupport DeletionCode.Qary.SignedRuleCount DeletionCode.Qary.RuleSetGraph
open DeletionCode.CircleHash DeletionCode.CircleUniform DeletionCode.Qary.ConflictGraphWitness DeletionCode.Qary.WitnessCounting
open scoped BigOperators ENNReal

variable {n : ℕ}

/-- The proved deterministic upper bound on witness size. -/
def cutoff (t k : ℕ) : ℕ := 1 + 4 * t * (windowLength k) ^ 2 + 2 * t * windowLength k

/-- All strict hash tests for one fixed finite set of rules. -/
noncomputable def ruleTestEvent (k Q : ℕ) (U : RuleSet α k) :
    Set (Gram α (windowLength k) → ℝ) :=
  {weights | ∀ u ∈ U, ‖realWeightedHash weights u‖ < 1 / (Q : ℝ)}

/-- The union of tests for actual candidate sets of one fixed size. -/
noncomputable def candidateEvent (t k Q R : ℕ) (x : Bits α n) :
    Set (Gram α (windowLength k) → ℝ) :=
  {weights | ∃ U : RuleSet α k, Candidate t (padBits x) n k R U ∧
    weights ∈ ruleTestEvent k Q U}

/-- The concrete obstruction event in the retained graph, on the real-weight space. -/
noncomputable def obstructionEvent (t k Q : ℕ) (x : Bits α n) :
    Set (Gram α (windowLength k) → ℝ) :=
  {weights | ∃ v : Vertex (n := n) t Q (realWeightedHash weights),
    v.val = x ∧
      ¬ ((graph t Q (realWeightedHash weights)).connectedComponentMk v).toSimpleGraph.Colorable 2}

/-- Each fixed independent finite rule set passes all tests with the exact product probability. -/
theorem ruleTest_probability (k Q : ℕ) (hQ : 2 ≤ Q) (U : RuleSet α k)
    (hU : FiniteGenerating.Independent U) :
    realWeights (Gram α (windowLength k)) (ruleTestEvent k Q U) =
      ENNReal.ofReal (2 / (Q : ℝ)) ^ U.card := by
  have h := RandomHash.real_simultaneous_test_probability (fun u : U => u.val) hU Q hQ
  simpa only [ruleTestEvent, Subtype.forall, Fintype.card_coe] using h

theorem candidateEvent_eq_union (t k Q R : ℕ) (x : Bits α n) :
    candidateEvent t k Q R x =
      ⋃ U : {U : RuleSet α k // Candidate t (padBits x) n k R U}, ruleTestEvent k Q U.val := by
  ext weights
  change (∃ U : RuleSet α k, Candidate t (padBits x) n k R U ∧
    weights ∈ ruleTestEvent k Q U) ↔ _
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨U, hU, htest⟩
    exact ⟨⟨U, hU⟩, htest⟩
  · rintro ⟨U, htest⟩
    exact ⟨U.val, U.property, htest⟩

/-- The fixed-size bound counts underlying finite rule sets, without ordering their rules. -/
theorem candidate_probability_le (t k Q R : ℕ) (ht : 1 ≤ t) (hR : 1 ≤ R)
    (x : Bits α n) (hx : KUnique (padBits x) n k) (hQ : 2 ≤ Q) :
    realWeights (Gram α (windowLength k)) (candidateEvent t k Q R x) ≤
      (Nat.card {U : RuleSet α k // Candidate t (padBits x) n k R U} : ℝ≥0∞) *
        ENNReal.ofReal (2 / (Q : ℝ)) ^ R := by
  classical
  let := candidate_finite t ht (padBits x) n k R hR hx
  let : Fintype {U : RuleSet α k // Candidate t (padBits x) n k R U} := Fintype.ofFinite _
  rw [candidateEvent_eq_union]
  calc
    _ ≤ ∑ U : {U : RuleSet α k // Candidate t (padBits x) n k R U},
        realWeights (Gram α (windowLength k)) (ruleTestEvent k Q U.val) :=
      measure_iUnion_fintype_le _ _
    _ = ∑ _U : {U : RuleSet α k // Candidate t (padBits x) n k R U},
        ENNReal.ofReal (2 / (Q : ℝ)) ^ R := by
      apply Finset.sum_congr rfl
      intro U _hU
      rw [ruleTest_probability k Q hQ U.val U.property.independent, U.property.generating.1]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- Every concrete graph obstruction supplies one of the fixed candidate survival events. -/
theorem obstructionEvent_subset_union (t k Q : ℕ) (ht : 2 ≤ t) (hQ : 2 ≤ Q)
    (x : Bits α n) :
    obstructionEvent t k Q x ⊆
      ⋃ R ∈ Finset.Icc 2 (cutoff t k), candidateEvent t k Q R x := by
  intro weights hbad
  obtain ⟨v, hv, hnot⟩ := hbad
  obtain ⟨U, hU, hgen⟩ :=
    VerifiedConflictGraphWitness.bounded_witness ht hQ (realWeightedHash weights) v hnot
  apply Set.mem_iUnion.mpr
  refine ⟨U.card, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_Icc.mpr ⟨hU.bounds.size_lower, hU.bounds.size_upper⟩
  · refine ⟨U, ⟨?_, hU.bounds, hU.generating.independent⟩, ?_⟩
    · simpa only [hv] using hgen
    · intro u hu
      exact (hU.surviving u hu).2

theorem obstruction_probability_le_of_unique (t k Q : ℕ) (ht : 2 ≤ t) (hQ : 2 ≤ Q)
    (x : Bits α n) (hx : KUnique (padBits x) n k) :
    realWeights (Gram α (windowLength k)) (obstructionEvent t k Q x) ≤
      ∑ R ∈ Finset.Icc 2 (cutoff t k),
        (Nat.card {U : RuleSet α k // Candidate t (padBits x) n k R U} : ℝ≥0∞) *
          ENNReal.ofReal (2 / (Q : ℝ)) ^ R := by
  calc
    _ ≤ realWeights (Gram α (windowLength k))
        (⋃ R ∈ Finset.Icc 2 (cutoff t k), candidateEvent t k Q R x) :=
      measure_mono (obstructionEvent_subset_union t k Q ht hQ x)
    _ ≤ ∑ R ∈ Finset.Icc 2 (cutoff t k),
        realWeights (Gram α (windowLength k)) (candidateEvent t k Q R x) :=
      measure_biUnion_finset_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro R hR
      exact candidate_probability_le t k Q R (by omega)
        (by have h := (Finset.mem_Icc.mp hR).1; omega) x hx hQ

/-- A nonunique word cannot be a vertex of the retained conflict graph. -/
theorem obstructionEvent_empty_of_not_unique (t k Q : ℕ) (x : Bits α n)
    (hx : ¬ KUnique (padBits x) n k) : obstructionEvent t k Q x = ∅ := by
  ext weights
  constructor
  · intro h
    obtain ⟨v, hv, _hnot⟩ := h
    apply hx
    simpa only [hv] using FiniteConflictGraph.vertex_unique v
  · intro h
    exact h.elim

/-- The actual rare-obstruction union bound. All coverage, survival, independence,
and finiteness used in its proof are derived from verified theorems. -/
theorem obstruction_probability_le (t k Q : ℕ) (ht : 2 ≤ t) (hQ : 2 ≤ Q)
    (x : Bits α n) :
    realWeights (Gram α (windowLength k)) (obstructionEvent t k Q x) ≤
      ∑ R ∈ Finset.Icc 2 (cutoff t k),
        (Nat.card {U : RuleSet α k // Candidate t (padBits x) n k R U} : ℝ≥0∞) *
          ENNReal.ofReal (2 / (Q : ℝ)) ^ R := by
  classical
  by_cases hx : KUnique (padBits x) n k
  · exact obstruction_probability_le_of_unique t k Q ht hQ x hx
  · rw [obstructionEvent_empty_of_not_unique t k Q x hx, measure_empty]
    exact bot_le

#print axioms ruleTest_probability
#print axioms candidate_probability_le
#print axioms obstructionEvent_subset_union
#print axioms obstruction_probability_le_of_unique
#print axioms obstructionEvent_empty_of_not_unique
#print axioms obstruction_probability_le

end DeletionCode.Qary.ObstructionProbability
