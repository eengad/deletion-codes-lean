import DeletionCode.Burst.WordHash
import DeletionCode.Burst.WordGraphWitness

/-!
The actual burst graph's equal-label edges survive the circle norm test.
The sole coverage interface below is discharged by the chronological-source
transport and finite local-bubble construction in VerifiedConflictGraphWitness.
-/
namespace DeletionCode.Burst.ConflictGraphWitness

open DeletionCode.Qary.Windows DeletionCode.Qary.HeaderRecovery
open DeletionCode.Qary.SignedSupport DeletionCode.Qary.SignedRuleCount
open BoundedWitnessWalk

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

def catalogue (b t k : ℕ) : Set (Spectrum α k b) := {w | Catalogue.Rule t k b w}

def surviving {k b : ℕ} (t Q : ℕ) (H : Spectrum α k b →+ UnitAddCircle) :
    Set (Spectrum α k b) := CircleHash.surviving H Q (catalogue b t k)

def SeparatedCoverage (b t k n : ℕ) : Prop :=
  ∀ (x y : Bits α n), KUnique (padBits x) n k → ∀ es : List (Edit α),
    Executes b (List.ofFn x) es (List.ofFn y) → es.length = 2 * t →
    Separated n (8 * (windowLength k b + t * b)) es →
    Catalogue.Rule t k b (spectrum k b y - spectrum k b x)

theorem edge_catalogue {b t k n Q : ℕ} {H : Spectrum α k b →+ UnitAddCircle}
    (hcoverage : SeparatedCoverage (α := α) b t k n)
    {x y : Vertex (n := n) b t Q H} (hxy : (graph b t Q H).Adj x y) :
    Catalogue.Rule t k b (spectrum k b y.val - spectrum k b x.val) := by
  obtain ⟨es, hex, hlen, hsep⟩ := FiniteConflictGraph.edge_separated_script hxy
  exact hcoverage x.val y.val (FiniteConflictGraph.vertex_unique x) es hex hlen hsep

theorem edge_surviving {b t k n Q : ℕ} {H : Spectrum α k b →+ UnitAddCircle}
    (hQ : 2 ≤ Q) (hcoverage : SeparatedCoverage (α := α) b t k n)
    {x y : Vertex (n := n) b t Q H} (hxy : (graph b t Q H).Adj x y) :
    spectrum k b y.val - spectrum k b x.val ∈ surviving t Q H := by
  exact CircleHash.equal_hash_labels_survive H Q hQ (spectrum k b x.val)
    (spectrum k b y.val) hxy.2.2 (edge_catalogue hcoverage hxy)

theorem bounded_witness_of_coverage {b t k n Q : ℕ} (ht : 2 ≤ t) (hQ : 2 ≤ Q)
    (H : Spectrum α k b →+ UnitAddCircle) (hcoverage : SeparatedCoverage (α := α) b t k n)
    (x : Vertex (n := n) b t Q H)
    (hnot : ¬ ((graph b t Q H).connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ U : RuleSet α (k + b), Witness t k b (spectrum k b x.val) (surviving t Q H) U := by
  exact WordGraphWitness.component_witness ht (graph b t Q H) (fun v => padBits v.val)
    (surviving t Q H) FiniteConflictGraph.vertex_unique
    (fun h => edge_catalogue hcoverage h) (fun h => edge_surviving hQ hcoverage h) x hnot

end DeletionCode.Burst.ConflictGraphWitness
