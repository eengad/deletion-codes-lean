import DeletionCode.OddGraphWalk
import DeletionCode.BoundedWitnessWalk

/-!
The graph-to-witness connection. Nonbipartiteness of the chosen vertex's
component supplies the odd walk; the existing word-walk theorem then supplies
the bounded witness and the exact generating-set predicate used for counting.
Only the vertex uniqueness and edge catalogue/survival interface is assumed.
-/
namespace DeletionCode.WordGraphWitness

open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open ConnectedBlocks WitnessCases

/-- A nonbipartite component of a graph of k-unique words contains a bounded
surviving generating witness at every chosen word in that component. -/
theorem component_witness {V : Type*} {t k n : ℕ} (ht : 2 ≤ t)
    (G : SimpleGraph V) (words : V → Letters)
    (K : Set (Gram (windowLength k) → ℤ))
    (hunique : ∀ v, KUnique (words v) n k)
    (hcat : ∀ {v w}, G.Adj v w → CatalogueRule t k
      (wordSpectrum (words w) n (windowLength k) -
        wordSpectrum (words v) n (windowLength k)))
    (hK : ∀ {v w}, G.Adj v w →
      (wordSpectrum (words w) n (windowLength k) -
        wordSpectrum (words v) n (windowLength k)) ∈ K)
    (x : V) (hnot : ¬ (G.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ U : RuleSet k,
      Witness t k (wordSpectrum (words x) n (windowLength k)) K U ∧
      ManuscriptCounting.GeneratingSet t (words x) n k U.card (componentCount U) U := by
  obtain ⟨m, hodd, vertices, hstart, hend, hadj⟩ := OddGraphWalk.component_odd_walk x hnot
  let walkWords : Fin (m + 1) → Letters := fun j => words (vertices j)
  have hclosed : Agree (walkWords 0) 0 (walkWords (Fin.last m)) 0 n := by
    intro j _
    simp only [walkWords, hstart, hend]
  obtain ⟨U, hU, hcount⟩ := BoundedWitnessWalk.extract_word_walk ht walkWords K
    (fun j => hunique (vertices j)) hclosed hodd (fun i => hcat (hadj i))
    (fun i => hK (hadj i))
  exact ⟨U, by simpa only [walkWords, hstart] using hU,
    by simpa only [walkWords, hstart] using hcount⟩

/-- An actual finite-word graph is a direct specialization. Padding is fixed;
no unused infinite letter-function data is part of the graph's vertices. -/
theorem finite_word_component_witness {t k n : ℕ} (ht : 2 ≤ t)
    (vertices : Set (Bits n)) (G : SimpleGraph vertices)
    (K : Set (Gram (windowLength k) → ℤ))
    (hunique : ∀ v ∈ vertices, KUnique (padBits v) n k)
    (hcat : ∀ {v w}, G.Adj v w → CatalogueRule t k
      (wordSpectrum (padBits w.val) n (windowLength k) -
        wordSpectrum (padBits v.val) n (windowLength k)))
    (hK : ∀ {v w}, G.Adj v w →
      (wordSpectrum (padBits w.val) n (windowLength k) -
        wordSpectrum (padBits v.val) n (windowLength k)) ∈ K)
    (x : vertices) (hnot : ¬ (G.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ U : RuleSet k,
      Witness t k (wordSpectrum (padBits x.val) n (windowLength k)) K U ∧
      ManuscriptCounting.GeneratingSet t (padBits x.val) n k U.card (componentCount U) U :=
  component_witness ht G (fun v => padBits v.val) K
    (fun v => hunique v.val v.property) hcat hK x hnot

#print axioms component_witness
#print axioms finite_word_component_witness

end DeletionCode.WordGraphWitness
