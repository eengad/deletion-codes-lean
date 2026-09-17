import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-!
The deterministic selection at the end of the manuscript. The vertices in
bipartite connected components admit a coherent two-coloring, constructed
by choosing a coloring for each component. One global color class contains
at least half those vertices and is independent. A separate finite-fiber
argument retains at least a 1/Q fraction in one label class.
-/
namespace DeletionCode.BipartiteSelection

open SimpleGraph
open scoped BigOperators

/-- The finite pigeonhole bound in multiplication form, without rounding.
The selected label exists even when I is empty. -/
theorem exists_large_label_fiber {V : Type*} {Q : ℕ} (I : Finset V)
    (label : V → Fin Q) (hQ : 1 ≤ Q) :
    ∃ a : Fin Q, I.card ≤ Q * (I.filter (fun v => label v = a)).card := by
  classical
  have hne : (Finset.univ : Finset (Fin Q)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin Q))
    (fun b => (I.filter (fun v => label v = b)).card) hne
  refine ⟨a, ?_⟩
  calc
    I.card = ∑ b : Fin Q, (I.filter (fun v => label v = b)).card := by
      symm
      simpa only [Finset.mem_univ, Finset.filter_true] using
        Finset.sum_card_fiberwise_eq_card_filter I (Finset.univ : Finset (Fin Q)) label
    _ ≤ ∑ _b : Fin Q, (I.filter (fun v => label v = a)).card :=
      Finset.sum_le_sum (fun b hb => ha b hb)
    _ = _ := by simp

variable {V : Type*} (G : SimpleGraph V)

/-- A vertex is retained at this stage exactly when its whole component is bipartite. -/
def Good (v : V) : Prop := (G.connectedComponentMk v).toSimpleGraph.Colorable 2

/-- Choose one coloring per bipartite component. The fallback value on other
components is unused by the independent-set construction. -/
noncomputable def componentColor (C : G.ConnectedComponent) : C → Fin 2 := by
  classical
  exact if h : C.toSimpleGraph.Colorable 2 then fun v => h.some v else fun _ => 0

theorem componentColor_valid (C : G.ConnectedComponent) (hC : C.toSimpleGraph.Colorable 2)
    {v w : C} (hvw : C.toSimpleGraph.Adj v w) :
    componentColor G C v ≠ componentColor G C w := by
  classical
  simpa only [componentColor, dite_eq_left hC] using hC.some.valid hvw

/-- The same component choice is used at every vertex in that component. -/
noncomputable def color (v : V) : Fin 2 :=
  componentColor G (G.connectedComponentMk v) ⟨v, rfl⟩

theorem color_eq_component (C : G.ConnectedComponent) (v : V) (hv : v ∈ C) :
    color G v = componentColor G C ⟨v, hv⟩ := by
  change G.connectedComponentMk v = C at hv
  subst C
  rfl

/-- Adjacent retained vertices receive different colors; no coloring of
the nonbipartite components is assumed. -/
theorem good_color_valid {v w : V} (hv : Good G v) (hvw : G.Adj v w) :
    color G v ≠ color G w := by
  let C := G.connectedComponentMk v
  have hvC : v ∈ C := rfl
  have hwC : w ∈ C :=
    (ConnectedComponent.connectedComponentMk_eq_of_adj hvw).symm
  rw [color_eq_component G C v hvC, color_eq_component G C w hwC]
  exact componentColor_valid G C hv (show C.toSimpleGraph.Adj ⟨v, hvC⟩ ⟨w, hwC⟩ from hvw)

/-- The induced graph on all retained components is two-colorable. -/
theorem good_graph_colorable : (G.induce {v | Good G v}).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => color G v.val) ?_⟩
  intro v w hvw
  exact good_color_valid G v.property hvw

variable [Fintype V]

noncomputable def goodVertices : Finset V := by
  classical
  exact Finset.univ.filter (Good G)

@[simp] theorem mem_goodVertices (v : V) : v ∈ goodVertices G ↔ Good G v := by
  classical
  simp only [goodVertices, Finset.mem_filter, Finset.mem_univ, true_and]

/-- At least half of all vertices in bipartite components can be selected
as one independent set. Component colorings and the large fiber are derived. -/
theorem exists_independent_good :
    ∃ I : Finset V, (∀ v ∈ I, Good G v) ∧ G.IsIndepSet (I : Set V) ∧
      (goodVertices G).card ≤ 2 * I.card := by
  classical
  obtain ⟨a, ha⟩ := exists_large_label_fiber (goodVertices G) (color G) (by decide)
  refine ⟨(goodVertices G).filter (fun v => color G v = a), ?_, ?_, ha⟩
  · intro v hv
    exact (mem_goodVertices G v).mp (Finset.mem_filter.mp hv).1
  · intro v hv w hw _ hvw
    have hv' := Finset.mem_filter.mp hv
    have hw' := Finset.mem_filter.mp hw
    exact good_color_valid G ((mem_goodVertices G v).mp hv'.1) hvw
      (hv'.2.trans hw'.2.symm)

#print axioms exists_large_label_fiber
#print axioms good_color_valid
#print axioms good_graph_colorable
#print axioms exists_independent_good

end DeletionCode.BipartiteSelection
