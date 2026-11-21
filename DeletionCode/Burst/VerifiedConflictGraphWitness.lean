import DeletionCode.Burst.ConflictGraphWitness
import DeletionCode.Burst.CatalogueCoverage
import DeletionCode.Burst.GeneratingEnumeration

/-!
The actual separated chronological coverage theorem discharges the coverage
interface for the burst conflict graph. No local geometry, source-coordinate
placement, or spectrum decomposition is left as an assumption.
-/
namespace DeletionCode.Burst.VerifiedConflictGraphWitness

open DeletionCode.Qary.Windows DeletionCode.Qary.HeaderRecovery
open DeletionCode.Qary.CatalogueWords DeletionCode.Qary.SignedSupport
open DeletionCode.Qary.SignedRuleCount DeletionCode.Qary.RuleSetGraph
open ConflictGraphWitness BoundedWitnessWalk

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

omit [Fintype α] [DecidableEq α] in
theorem listLetters_ofFn {n : ℕ} (x : Bits α n) :
    listLetters (List.ofFn x) = padBits x := by
  funext i
  by_cases hi : i < n
  · simp [listLetters, padBits, hi, List.getD]
  · simp [listLetters, padBits, hi, List.getD]

theorem separated_coverage (b t k n : ℕ) (hk : 1 ≤ k) :
    SeparatedCoverage (α := α) b t k n := by
  intro x y hx es hex hlen hsep
  have hx' : KUnique (listLetters (List.ofFn x)) (List.ofFn x).length k := by
    simpa only [List.length_ofFn, listLetters_ofFn] using hx
  have hsep' : Separated (List.ofFn x).length
      (8 * (windowLength k b + t * b)) es := by simpa only [List.length_ofFn] using hsep
  have hxy : (List.ofFn x).length = (List.ofFn y).length := by simp only [List.length_ofFn]
  have hh := CatalogueCoverage.catalogueRule hk hx' hex hlen hsep' hxy
  simpa only [List.length_ofFn, listLetters_ofFn, spectrum] using hh

theorem edge_catalogue {b t k n Q : ℕ} (hk : 1 ≤ k)
    {H : Spectrum α k b →+ UnitAddCircle}
    {x y : Vertex (n := n) b t Q H} (hxy : (graph b t Q H).Adj x y) :
    Catalogue.Rule t k b (spectrum k b y.val - spectrum k b x.val) :=
  ConflictGraphWitness.edge_catalogue (separated_coverage b t k n hk) hxy

theorem edge_surviving {b t k n Q : ℕ} (hk : 1 ≤ k) (hQ : 2 ≤ Q)
    {H : Spectrum α k b →+ UnitAddCircle}
    {x y : Vertex (n := n) b t Q H} (hxy : (graph b t Q H).Adj x y) :
    spectrum k b y.val - spectrum k b x.val ∈ surviving t Q H :=
  ConflictGraphWitness.edge_surviving hQ (separated_coverage b t k n hk) hxy

theorem bounded_witness_raw {b t k n Q : ℕ} (ht : 2 ≤ t) (hk : 1 ≤ k) (hQ : 2 ≤ Q)
    (H : Spectrum α k b →+ UnitAddCircle) (x : Vertex (n := n) b t Q H)
    (hnot : ¬ ((graph b t Q H).connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ U : RuleSet α (k + b), Witness t k b (spectrum k b x.val) (surviving t Q H) U :=
  ConflictGraphWitness.bounded_witness_of_coverage ht hQ H
    (separated_coverage b t k n hk) x hnot

/-- Every actual graph obstruction has a bounded witness in the finite class
counted by the concrete burst serialization theorem. -/
theorem bounded_witness {b t k n Q : ℕ} (ht : 2 ≤ t) (hk : 1 ≤ k) (hQ : 2 ≤ Q)
    (H : Spectrum α k b →+ UnitAddCircle) (x : Vertex (n := n) b t Q H)
    (hnot : ¬ ((graph b t Q H).connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ U : RuleSet α (k + b),
      Witness t k b (spectrum k b x.val) (surviving t Q H) U ∧
      ManuscriptCounting.GeneratingSet t (padBits x.val) n k b U.card (componentCount U) U := by
  obtain ⟨U, hU⟩ := bounded_witness_raw ht hk hQ H x hnot
  exact ⟨U, hU, GeneratingEnumeration.generatingAt_to_manuscript (padBits x.val) U
    hU.generating hU.catalogue⟩

#print axioms separated_coverage
#print axioms bounded_witness_raw
#print axioms bounded_witness

end DeletionCode.Burst.VerifiedConflictGraphWitness
