import DeletionCode.Qary.FiniteConflictGraph
import DeletionCode.Qary.SignedSupport
import DeletionCode.CircleHash

/-! Actual finite-word spectra, circle labels and conflict graphs, independent of witnesses. -/
namespace DeletionCode.Qary.ConflictGraphWitness

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

open DeletionCode.Qary.Windows DeletionCode.Qary.HeaderRecovery DeletionCode.Qary.SignedSupport

abbrev Spectrum (α : Type*) (k : ℕ) := Gram α (windowLength k) → ℤ

noncomputable def spectrum {n : ℕ} (k : ℕ) (x : Bits α n) : Spectrum α k :=
  wordSpectrum (padBits x) n (windowLength k)

noncomputable def wordLabel {n k : ℕ} (Q : ℕ) (H : Spectrum α k →+ UnitAddCircle) (x : Bits α n) : ℤ :=
  CircleHash.label Q (H (spectrum k x))

abbrev Vertex {n k : ℕ} (t Q : ℕ) (H : Spectrum α k →+ UnitAddCircle) :=
  FiniteConflictGraph.Vertex (n := n) t k (wordLabel Q H)

noncomputable def graph {n k : ℕ} (t Q : ℕ) (H : Spectrum α k →+ UnitAddCircle) :
    SimpleGraph (Vertex (n := n) t Q H) :=
  FiniteConflictGraph.graph t k (wordLabel Q H)

end DeletionCode.Qary.ConflictGraphWitness
