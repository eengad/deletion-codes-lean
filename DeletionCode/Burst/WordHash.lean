import DeletionCode.Burst.FiniteConflictGraph
import DeletionCode.Qary.SignedSupport
import DeletionCode.CircleHash

/-! Actual length-n spectra and circle labels for the burst conflict graph. -/
namespace DeletionCode.Burst.ConflictGraphWitness

open DeletionCode.Qary.HeaderRecovery DeletionCode.Qary.SignedSupport

variable {α : Type*} [Inhabited α]

abbrev Spectrum (α : Type*) (k b : ℕ) := Gram α (windowLength k b) → ℤ

noncomputable def spectrum {n : ℕ} (k b : ℕ) (x : Bits α n) : Spectrum α k b :=
  wordSpectrum (padBits x) n (windowLength k b)

noncomputable def wordLabel {n k b : ℕ} (Q : ℕ)
    (H : Spectrum α k b →+ UnitAddCircle) (x : Bits α n) : ℤ :=
  CircleHash.label Q (H (spectrum k b x))

abbrev Vertex {n k : ℕ} (b t Q : ℕ) (H : Spectrum α k b →+ UnitAddCircle) :=
  FiniteConflictGraph.Vertex (n := n) b t k (wordLabel Q H)

noncomputable def graph {n k : ℕ} (b t Q : ℕ) (H : Spectrum α k b →+ UnitAddCircle) :
    SimpleGraph (Vertex (n := n) b t Q H) :=
  FiniteConflictGraph.graph b t k (wordLabel Q H)

end DeletionCode.Burst.ConflictGraphWitness
