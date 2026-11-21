import DeletionCode.Burst.ChronologicalSeparation
import DeletionCode.Qary.HeaderRecovery
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
The actual conflict graph for successive bounded substring replacements.
Removing short or nonseparated equal-label partners forces every surviving
edge to admit an exactly 2t-step separated chronological script.
-/
namespace DeletionCode.Burst.FiniteConflictGraph

open DeletionCode.Qary.HeaderRecovery DeletionCode.Qary.Windows

variable {α : Type*} [Inhabited α] {n : ℕ} {H : Type*}

def Unique (k : ℕ) (x : Bits α n) : Prop := KUnique (padBits x) n k

def Confusable (b t : ℕ) (x y : Bits α n) : Prop :=
  Burst.Confusable b t (List.ofFn x) (List.ofFn y)

theorem Confusable.symm {b t : ℕ} {x y : Bits α n} (h : Confusable b t x y) :
    Confusable b t y x := by
  obtain ⟨output, hx, hy⟩ := h
  exact ⟨output, hy, hx⟩

def CandidatePartner (b t k : ℕ) (x y : Bits α n) : Prop :=
  x ≠ y ∧ Burst.Exceptional b t n (8 * (windowLength k b + t * b))
    (List.ofFn x) (List.ofFn y)

def Exceptional (b t k : ℕ) (label : Bits α n → H) (x : Bits α n) : Prop :=
  ∃ y, CandidatePartner b t k x y ∧ label x = label y

def Vertex (b t k : ℕ) (label : Bits α n → H) :=
  {x : Bits α n // Unique k x ∧ ¬Exceptional b t k label x}

instance vertexFinite [Fintype α] (b t k : ℕ) (label : Bits α n → H) :
    Finite (Vertex b t k label) := by unfold Vertex; infer_instance

def graph (b t k : ℕ) (label : Bits α n → H) :
    SimpleGraph (Vertex b t k label) where
  Adj x y := x.val ≠ y.val ∧ Confusable b t x.val y.val ∧ label x.val = label y.val
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
  loopless := by constructor; intro x h; exact h.1 rfl

theorem vertex_unique {b t k : ℕ} {label : Bits α n → H} (x : Vertex b t k label) :
    KUnique (padBits x.val) n k := x.property.1

theorem nonexceptional_script {b t k : ℕ} {label : Bits α n → H}
    (x : Vertex b t k label) (y : Bits α n)
    (hxy : x.val ≠ y) (hlabel : label x.val = label y)
    (es : List (Edit α)) (hex : Executes b (List.ofFn x.val) es (List.ofFn y))
    (hlen : es.length ≤ 2 * t) :
    es.length = 2 * t ∧ Separated n (8 * (windowLength k b + t * b)) es := by
  have hs : ¬es.length < 2 * t := by
    intro hshort
    exact x.property.2 ⟨y, ⟨hxy, es, hex, hlen, Or.inl hshort⟩, hlabel⟩
  refine ⟨by omega, ?_⟩
  by_contra hnot
  exact x.property.2 ⟨y, ⟨hxy, es, hex, hlen, Or.inr hnot⟩, hlabel⟩

theorem edge_separated_script {b t k : ℕ} {label : Bits α n → H}
    {x y : Vertex b t k label} (hxy : (graph b t k label).Adj x y) :
    ∃ es : List (Edit α), Executes b (List.ofFn x.val) es (List.ofFn y.val) ∧
      es.length = 2 * t ∧ Separated n (8 * (windowLength k b + t * b)) es := by
  obtain ⟨r, hr, hs⟩ := Burst.Confusable.script hxy.2.1
  obtain ⟨es, hlen, hex⟩ := hs.exists_executes
  exact ⟨es, hex, nonexceptional_script x y.val hxy.1 hxy.2.2 es hex (by omega)⟩

end DeletionCode.Burst.FiniteConflictGraph
