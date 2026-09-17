import DeletionCode.CodeSelection
import DeletionCode.UniqueWordCount
import DeletionCode.ExceptionalProbability
import DeletionCode.ObstructionProbability

/-!
The finite set retained by the two probabilistic discard tests is exactly the
underlying-word image of the good vertices of the actual conflict graph.
Subtype proofs add no multiplicity, so the two cardinalities agree exactly.
-/

namespace DeletionCode.GoodWordBridge

open Windows HeaderRecovery SignedSupport CircleHash ConflictGraphWitness
open ExceptionalProbability ObstructionProbability BipartiteSelection

variable {n : ℕ}

/-- Unique words outside both the exceptional-word and nonbipartite-component events. -/
noncomputable def retainedWords (t k Q : ℕ) (weights : Gram (windowLength k) → ℝ) :
    Finset (Bits n) := by
  classical
  exact (UniqueWordCount.uniqueWords n k).filter (fun x =>
    weights ∉ exceptionalEvent t k Q x ∪ obstructionEvent t k Q x)

/-- The probabilistic tests retain exactly the underlying words of vertices
whose actual connected components are two-colorable. -/
theorem mem_retainedWords_iff (t k Q : ℕ) (weights : Gram (windowLength k) → ℝ)
    (x : Bits n) :
    x ∈ retainedWords t k Q weights ↔
      ∃ v : Vertex (n := n) t Q (realWeightedHash weights), v.val = x ∧
        Good (graph t Q (realWeightedHash weights)) v := by
  classical
  constructor
  · intro hx
    obtain ⟨hxunique, houtside⟩ := Finset.mem_filter.mp hx
    have hunique := (UniqueWordCount.mem_uniqueWords x).mp hxunique
    have hnotExceptional : ¬ FiniteConflictGraph.Exceptional t k
        (wordLabel Q (realWeightedHash weights)) x := by
      intro h
      exact houtside (Or.inl h)
    let v : Vertex (n := n) t Q (realWeightedHash weights) := ⟨x, hunique, hnotExceptional⟩
    refine ⟨v, rfl, ?_⟩
    by_contra hnot
    apply houtside
    exact Or.inr ⟨v, rfl, hnot⟩
  · rintro ⟨v, hv, hgood⟩
    apply Finset.mem_filter.mpr
    refine ⟨(UniqueWordCount.mem_uniqueWords x).mpr ?_, ?_⟩
    · simpa only [hv] using v.property.1
    · intro hbad
      rcases hbad with hexceptional | hobstruction
      · change FiniteConflictGraph.Exceptional t k
          (wordLabel Q (realWeightedHash weights)) x at hexceptional
        apply v.property.2
        simpa only [hv] using hexceptional
      · obtain ⟨w, hw, hnot⟩ := hobstruction
        have hwv : w = v := Subtype.ext (hw.trans hv.symm)
        subst w
        exact hnot hgood

/-- The graph-to-word projection is the entire retained word set. -/
theorem retainedWords_eq_image_goodVertices (t k Q : ℕ)
    (weights : Gram (windowLength k) → ℝ) :
    retainedWords (n := n) t k Q weights =
      (goodVertices (graph (n := n) t Q (realWeightedHash weights))).image Subtype.val := by
  classical
  ext x
  rw [mem_retainedWords_iff]
  constructor
  · rintro ⟨v, hv, hgood⟩
    exact Finset.mem_image.mpr ⟨v, (mem_goodVertices _ v).mpr hgood, hv⟩
  · intro hx
    obtain ⟨v, hv, hval⟩ := Finset.mem_image.mp hx
    exact ⟨v, hval, (mem_goodVertices
      (V := Vertex (n := n) t Q (realWeightedHash weights)) _ v).mp hv⟩

/-- Actual retained words and actual good graph vertices have the same cardinality. -/
theorem card_retainedWords (t k Q : ℕ) (weights : Gram (windowLength k) → ℝ) :
    (retainedWords (n := n) t k Q weights).card =
      (goodVertices (graph (n := n) t Q (realWeightedHash weights))).card := by
  classical
  rw [retainedWords_eq_image_goodVertices]
  apply Finset.card_image_iff.mpr
  intro v _hv w _hw hval
  exact Subtype.ext hval

#print axioms mem_retainedWords_iff
#print axioms retainedWords_eq_image_goodVertices
#print axioms card_retainedWords

end DeletionCode.GoodWordBridge
