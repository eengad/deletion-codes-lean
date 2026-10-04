import DeletionCode.ConflictGraphWitness
import DeletionCode.BubbleCatalogue
import DeletionCode.SeparatedTraceCoverage

/-!
The concrete separated-trace theorem discharges the coverage interface for
the manuscript's actual conflict graph. The zero-length degeneracy is handled
explicitly, so coverage itself has no added positivity assumption on k.
-/
namespace DeletionCode.VerifiedConflictGraphWitness

open Windows HeaderRecovery CatalogueWords AlignmentTrace
open ConflictGraphWitness SignedSupport SignedRuleCount RuleSetGraph WitnessCases

theorem listLetters_ofFn {n : ℕ} (x : Bits n) :
    listLetters (List.ofFn x) = padBits x := by
  funext i
  by_cases hi : i < n
  · simp [listLetters, padBits, hi, List.getD]
  · simp [listLetters, padBits, hi, List.getD]

theorem unique_zero_length {n : ℕ} {x : Letters} (hx : KUnique x n 0) : n = 0 := by
  by_contra hn
  have heq : 0 = 1 := hx 0 1 (by omega) (by omega) (by intro i hi; omega)
  omega

theorem empty_catalogue (k : ℕ) : ConnectedBlocks.CatalogueRule 0 k 0 := by
  have h := BubbleCatalogue.catalogueRule (k := k) (t := 0) (fun i => Fin.elim0 i)
    (fun b => Fin.elim0 b) (fun b => Fin.elim0 b) (fun a => Fin.elim0 a)
    (by simp) (by simp)
  simpa using h

/-- Full separated coverage, including the degenerate k = 0 case. There is
no target uniqueness, catalogue presentation, or spectrum-sum premise. -/
theorem separated_coverage (t k n : ℕ) : SeparatedCoverage t k n := by
  intro x y hx trace hs ht hbal hsum hsep
  by_cases hk : 1 ≤ k
  · have hx' : KUnique (listLetters trace.source) trace.source.length k := by
      simpa only [hs, List.length_ofFn, listLetters_ofFn] using hx
    have h := SeparatedTraceCoverage.catalogueRule trace t k hk hx' hsep hbal hsum
    simpa only [hs, ht, List.length_ofFn, listLetters_ofFn, spectrum] using h
  · have hk0 : k = 0 := by omega
    subst k
    have hn := unique_zero_length hx
    have hlen : trace.source.length = n := by rw [hs, List.length_ofFn]
    have hc := trace.source_length
    have ht0 : t = 0 := by omega
    rw [ht0]
    subst n
    have hxy : x = y := Subsingleton.elim _ _
    rw [hxy, sub_self]
    exact empty_catalogue 0

/-- Every edge of the actual retained conflict graph is a catalogue rule;
coverage is proved internally. -/
theorem edge_catalogue {t k n Q : ℕ} {H : Spectrum k →+ UnitAddCircle}
    {x y : Vertex (n := n) t Q H} (hxy : (graph t Q H).Adj x y) :
    ConnectedBlocks.CatalogueRule t k (spectrum k y.val - spectrum k x.val) :=
  ConflictGraphWitness.edge_catalogue (separated_coverage t k n) hxy

theorem edge_surviving {t k n Q : ℕ} {H : Spectrum k →+ UnitAddCircle}
    (hQ : 2 ≤ Q) {x y : Vertex (n := n) t Q H} (hxy : (graph t Q H).Adj x y) :
    spectrum k y.val - spectrum k x.val ∈ surviving t Q H :=
  ConflictGraphWitness.edge_surviving hQ (separated_coverage t k n) hxy

/-- The manuscript's complete deterministic bounded-witness lemma on the
actual finite conflict graph, with its explicit exceptional set and hash.
No earlier coverage lemma is left as an assumption. -/
theorem bounded_witness {t k n Q : ℕ} (ht : 2 ≤ t) (hQ : 2 ≤ Q)
    (H : Spectrum k →+ UnitAddCircle) (x : Vertex (n := n) t Q H)
    (hnot : ¬ ((graph t Q H).connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ U : RuleSet k,
      Witness t k (spectrum k x.val) (surviving t Q H) U ∧
      ManuscriptCounting.GeneratingSet t (padBits x.val) n k U.card (componentCount U) U :=
  ConflictGraphWitness.bounded_witness_of_coverage ht hQ H (separated_coverage t k n) x hnot

#print axioms listLetters_ofFn
#print axioms unique_zero_length
#print axioms empty_catalogue
#print axioms separated_coverage
#print axioms edge_catalogue
#print axioms edge_surviving
#print axioms bounded_witness

end DeletionCode.VerifiedConflictGraphWitness
