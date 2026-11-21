import DeletionCode.Qary.WordHash
import DeletionCode.Qary.WordGraphWitness
import DeletionCode.CircleHash

/-!
The manuscript's deterministic bounded-witness argument on its actual finite
conflict graph. This module exposes separated
alignment coverage as an interface, discharged in VerifiedConflictGraphWitness.
The exceptional set, graph edges, circle labels, survival,
based odd walk, and all bounded-witness conclusions are defined or proved here
and in the imported modules. No probabilistic estimate is used.
-/
namespace DeletionCode.Qary.ConflictGraphWitness

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

open DeletionCode.Qary.Windows DeletionCode.Qary.HeaderRecovery DeletionCode.Qary.SignedSupport DeletionCode.Qary.SignedRuleCount DeletionCode.Qary.RuleSetGraph
open DeletionCode.Qary.ConnectedBlocks DeletionCode.Qary.AlignmentTrace DeletionCode.Qary.WitnessCases

def catalogue (t k : ℕ) : Set (Spectrum α k) := {w | CatalogueRule t k w}

def surviving {k : ℕ} (t Q : ℕ) (H : Spectrum α k →+ UnitAddCircle) : Set (Spectrum α k) :=
  CircleHash.surviving H Q (catalogue t k)

/-- The precise coverage interface, proved in VerifiedConflictGraphWitness: a
k-unique source and an actual separated trace with equally many deletions and
insertions and cost exactly 2t produce a concrete catalogue rule.
The target word is not required to be unique. -/
def SeparatedCoverage (t k n : ℕ) : Prop :=
  ∀ (x y : Bits α n), KUnique (padBits x) n k → ∀ trace : Trace α,
    trace.source = List.ofFn x → trace.target = List.ofFn y →
    trace.deletions = trace.insertions →
    2 * trace.deletions + trace.substitutions = 2 * t →
    FiniteConflictGraph.Separated (4 * windowLength k) trace →
    CatalogueRule t k (spectrum k y - spectrum k x)

/-- Exclusion of the explicit exceptional set supplies every input to
separated coverage. Catalogue membership is not an edge assumption. -/
theorem edge_catalogue {t k n Q : ℕ} {H : Spectrum α k →+ UnitAddCircle}
    (hcoverage : SeparatedCoverage (α := α) t k n)
    {x y : Vertex (n := n) t Q H} (hxy : (graph t Q H).Adj x y) :
    CatalogueRule t k (spectrum k y.val - spectrum k x.val) := by
  obtain ⟨trace, hs, ht, hbal, hsum, hsep⟩ := FiniteConflictGraph.edge_separated_trace hxy
  exact hcoverage x.val y.val (FiniteConflictGraph.vertex_unique x) trace hs ht hbal hsum hsep

/-- Equal circle bins imply actual hash survival for each catalogue edge.
Neither survival nor a norm estimate is assumed of graph edges. -/
theorem edge_surviving {t k n Q : ℕ} {H : Spectrum α k →+ UnitAddCircle}
    (hQ : 2 ≤ Q) (hcoverage : SeparatedCoverage (α := α) t k n)
    {x y : Vertex (n := n) t Q H} (hxy : (graph t Q H).Adj x y) :
    spectrum k y.val - spectrum k x.val ∈ surviving t Q H := by
  exact CircleHash.equal_hash_labels_survive H Q hQ (spectrum k x.val)
    (spectrum k y.val) hxy.2.2 (edge_catalogue hcoverage hxy)

/-- The bounded-witness conclusion for the manuscript's actual finite
conflict graph, conditional only on its earlier separated-coverage lemma. -/
theorem bounded_witness_of_coverage {t k n Q : ℕ} (ht : 2 ≤ t) (hQ : 2 ≤ Q)
    (H : Spectrum α k →+ UnitAddCircle) (hcoverage : SeparatedCoverage (α := α) t k n)
    (x : Vertex (n := n) t Q H)
    (hnot : ¬ ((graph t Q H).connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ U : RuleSet α k,
      Witness t k (spectrum k x.val) (surviving t Q H) U ∧
      ManuscriptCounting.GeneratingSet t (padBits x.val) n k U.card (componentCount U) U := by
  exact WordGraphWitness.component_witness ht (graph t Q H) (fun v => padBits v.val)
    (surviving t Q H) FiniteConflictGraph.vertex_unique
    (fun h => edge_catalogue hcoverage h) (fun h => edge_surviving hQ hcoverage h) x hnot

#print axioms edge_catalogue
#print axioms edge_surviving
#print axioms bounded_witness_of_coverage

end DeletionCode.Qary.ConflictGraphWitness
