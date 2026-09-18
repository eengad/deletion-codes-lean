import DeletionCode.AlignmentTrace
import DeletionCode.BoundedWitnessWalk
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
The finite conflict graph on actual binary words. Its vertices are k-unique
words after removal of the exceptional set defined by short or nonseparated
equal-label alignments. Consequently every oriented edge admits an actual
trace with exactly t deletions and t insertions, separated in matched-column
coordinates. Converting such traces to catalogue presentations is a separate
interface and is not an assumption of the result below.
-/
namespace DeletionCode.FiniteConflictGraph

open HeaderRecovery AlignmentTrace EditAlignment

variable {n : ℕ} {H : Type*}

/-- A finite word is unique when its actual n-letter padding is k-unique. -/
def Unique (k : ℕ) (x : Bits n) : Prop := Windows.KUnique (padBits x) n k

/-- Both finite words can yield the same output using at most t edits
(insertions, deletions and substitutions in total). -/
def Confusable (t : ℕ) (x y : Bits n) : Prop :=
  ∃ output : List Bool,
    WithinEdits t (List.ofFn x) output ∧ WithinEdits t (List.ofFn y) output

theorem Confusable.symm {t : ℕ} {x y : Bits n} (h : Confusable t x y) :
    Confusable t y x := by
  obtain ⟨output, hx, hy⟩ := h
  exact ⟨output, hy, hx⟩

/-- An edit index selects an actual edit column of a trace. -/
def EditIndex (trace : Trace) (i : Fin trace.length) : Prop :=
  (trace.get i).isEdit = true

/-- Every edit has B matched columns on both sides of the trace boundaries,
and distinct edit columns are separated by B matched columns. Anchors count
matched columns strictly before the selected column. -/
def Separated (B : ℕ) (trace : Trace) : Prop :=
  (∀ i : Fin trace.length, EditIndex trace i →
    B ≤ trace.matchedAnchor i.val ∧
      trace.matchedAnchor i.val + B ≤ trace.matchedCount) ∧
  ∀ i j : Fin trace.length, EditIndex trace i → EditIndex trace j →
    i.val < j.val → trace.matchedAnchor i.val + B ≤ trace.matchedAnchor j.val

/-- The exceptional set uses actual finite equal-label witnesses and actual
trace counters. The witness word need not itself lie outside this set. -/
def Exceptional (t k : ℕ) (label : Bits n → H) (x : Bits n) : Prop :=
  Unique k x ∧ ∃ y : Bits n, x ≠ y ∧ label x = label y ∧
    ∃ trace : Trace,
      trace.source = List.ofFn x ∧ trace.target = List.ofFn y ∧
      trace.deletions = trace.insertions ∧
      (2 * trace.deletions + trace.substitutions < 2 * t ∨
        (2 * trace.deletions + trace.substitutions = 2 * t ∧
          ¬ Separated (4 * windowLength k) trace))

/-- These are finite n-bit words with the two explicit vertex conditions. -/
def Vertex (t k : ℕ) (label : Bits n → H) :=
  {x : Bits n // Unique k x ∧ ¬ Exceptional t k label x}

instance vertexFinite (t k : ℕ) (label : Bits n → H) : Finite (Vertex t k label) := by
  unfold Vertex
  infer_instance

/-- The finite conflict graph has exactly the distinct, confusable,
equal-label pairs of retained words as edges. -/
def graph (t k : ℕ) (label : Bits n → H) : SimpleGraph (Vertex t k label) where
  Adj x y := x.val ≠ y.val ∧ Confusable t x.val y.val ∧ label x.val = label y.val
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
  loopless := by
    constructor
    intro x h
    exact h.1 rfl

theorem vertex_unique {t k : ℕ} {label : Bits n → H} (x : Vertex t k label) :
    Windows.KUnique (padBits x.val) n k := x.property.1

/-- Excluding the exceptional set rules out both traces of cost below 2t and
nonseparated traces of cost exactly 2t. This applies to every such trace, not
merely to one specially chosen alignment. -/
theorem nonexceptional_trace {t k : ℕ} {label : Bits n → H}
    (x : Vertex t k label) (y : Bits n)
    (hxy : x.val ≠ y) (hlabel : label x.val = label y)
    (trace : Trace)
    (hcost : 2 * trace.deletions + trace.substitutions ≤ 2 * t)
    (hsource : trace.source = List.ofFn x.val)
    (htarget : trace.target = List.ofFn y)
    (hbal : trace.deletions = trace.insertions) :
    2 * trace.deletions + trace.substitutions = 2 * t ∧
      Separated (4 * windowLength k) trace := by
  have hsmall : ¬ 2 * trace.deletions + trace.substitutions < 2 * t := by
    intro hlt
    exact x.property.2 ⟨x.property.1, y, hxy, hlabel, trace,
      hsource, htarget, hbal, Or.inl hlt⟩
  have hdt : 2 * trace.deletions + trace.substitutions = 2 * t := by omega
  have hsep : Separated (4 * windowLength k) trace := by
    by_contra hnot
    exact x.property.2 ⟨x.property.1, y, hxy, hlabel, trace,
      hsource, htarget, hbal, Or.inr ⟨hdt, hnot⟩⟩
  exact ⟨hdt, hsep⟩

/-- Every oriented edge supplies a genuine separated trace of cost exactly 2t.
The exact counters and separation follow from exceptional-set exclusion. -/
theorem edge_separated_trace {t k : ℕ} {label : Bits n → H}
    {x y : Vertex t k label} (hxy : (graph t k label).Adj x y) :
    ∃ trace : Trace,
      trace.source = List.ofFn x.val ∧ trace.target = List.ofFn y.val ∧
      trace.deletions = trace.insertions ∧
      2 * trace.deletions + trace.substitutions = 2 * t ∧
      Separated (4 * windowLength k) trace := by
  obtain ⟨output, hxout, hyout⟩ := hxy.2.1
  obtain ⟨d, s, trace, hcost, hs, ht, hdel, hins, hsub⟩ :=
    trace_of_equal_length_confusability (List.ofFn x.val) (List.ofFn y.val)
      output n t (by simp) (by simp) hxout hyout
  have hbal : trace.deletions = trace.insertions := hdel.trans hins.symm
  have hfull := nonexceptional_trace x y.val hxy.1 hxy.2.2 trace
    (by rw [hdel, hsub]; exact hcost) hs ht hbal
  exact ⟨trace, hs, ht, hbal, hfull⟩

#print axioms nonexceptional_trace
#print axioms edge_separated_trace

end DeletionCode.FiniteConflictGraph
