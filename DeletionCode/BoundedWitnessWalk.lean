import DeletionCode.WitnessCases
import DeletionCode.FiniteWalkRules
import DeletionCode.GeneratingEnumeration
import DeletionCode.SpectrumPath

/-!
Bounded-witness extraction from an actual odd closed walk of Boolean spectra.
The greedy scan, independence, ordered generation, both stopping cases, and
the concrete presentation counted by ManuscriptCounting are all derived.
Catalogue membership and survival of each step are the remaining interface
to the manuscript's conflict graph and separated-alignment coverage argument.
-/
namespace DeletionCode.BoundedWitnessWalk

open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open CatalogueAlgebra FiniteWalkRules WalkSelection BlockPartition WitnessCases

/-- An odd closed Boolean walk whose steps are surviving catalogue rules
contains an actual finite generating witness with all manuscript bounds. -/
theorem extract {t k m : ℕ} (ht : 2 ≤ t)
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ)
    (K : Set (Gram (windowLength k) → ℤ))
    (hp : ∀ j, WitnessAlgebra.BooleanVector (rationalPath p j))
    (hclosed : p 0 = p (Fin.last m)) (hodd : Odd m)
    (hcat : ∀ i, CatalogueRule t k (step p i))
    (hK : ∀ i, step p i ∈ K) :
    ∃ U : RuleSet k, Witness t k (p 0) K U := by
  classical
  let Good : Finset (Fin m) → Prop := fun S =>
    ∀ B ∈ blocks (selectedRules p S), B.card ≤ windowLength k
  have hgood : Good ∅ := by simp [Good, blocks]
  have hclosedQ : rationalPath p 0 = rationalPath p (Fin.last m) :=
    congrArg rational hclosed
  obtain ⟨i, S, hs, hgen, hnew, hstop⟩ :=
    odd_boolean_closed_walk_stops (rationalPath p) hp Good hgood hclosedQ hodd
  have hcatS (T : Finset (Fin m)) :
      ∀ u ∈ selectedRules p T, CatalogueRule t k u := by
    intro u hu
    obtain ⟨j, _, rfl⟩ := (mem_selectedRules p T u).mp hu
    exact hcat j
  have hKS (T : Finset (Fin m)) : ∀ u ∈ selectedRules p T, u ∈ K := by
    intro u hu
    obtain ⟨j, _, rfl⟩ := (mem_selectedRules p T u).mp hu
    exact hK j
  rcases hstop with hrel | ⟨_, hind, hbad, hgen'⟩
  · have hspan : rational (step p i) ∈
        Submodule.span ℚ (rational '' (↑(selectedRules p S) : Set _)) := by
      simpa only [rational_step, ← selectedSpan_eq] using hrel
    obtain ⟨U, _, hU⟩ := relation_case_of_span ht (p 0) K (selectedRules p S)
      (selected_generatingAt p S hs.independent hgen) (hcatS S) (hKS S)
      hs.good (step p i) (hcat i) (novelty_transfer p S i hnew) hspan
    exact ⟨U, hU⟩
  · have hgenI : FiniteGenerating.GeneratingAt (p 0)
        (insert (step p i) (selectedRules p S)) := by
      simpa only [selectedRules_insert] using
        selected_generatingAt p (insert i S) hind hgen'
    have hKI : ∀ u ∈ insert (step p i) (selectedRules p S), u ∈ K := by
      simpa only [selectedRules_insert] using hKS (insert i S)
    have hbadI : ¬ ∀ B ∈ blocks (insert (step p i) (selectedRules p S)),
        B.card ≤ windowLength k := by
      simpa only [Good, selectedRules_insert] using hbad
    exact ⟨_, large_block_case ht (p 0) K (selectedRules p S) (step p i)
      hgenI (hcat i) (hcatS S) hKI hs.good hbadI⟩

/-- The extracted rule set satisfies the very predicate used by the concrete
counting theorem, while retaining independence and all witness bounds. -/
theorem extract_counted {t k m n : ℕ} (ht : 2 ≤ t) (x : Letters)
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ)
    (K : Set (Gram (windowLength k) → ℤ))
    (hbase : p 0 = wordSpectrum x n (windowLength k))
    (hp : ∀ j, WitnessAlgebra.BooleanVector (rationalPath p j))
    (hclosed : p 0 = p (Fin.last m)) (hodd : Odd m)
    (hcat : ∀ i, CatalogueRule t k (step p i))
    (hK : ∀ i, step p i ∈ K) :
    ∃ U : RuleSet k, Witness t k (wordSpectrum x n (windowLength k)) K U ∧
      ManuscriptCounting.GeneratingSet t x n k U.card (componentCount U) U := by
  obtain ⟨U, hU⟩ := extract ht p K hp hclosed hodd hcat hK
  rw [hbase] at hU
  exact ⟨U, hU, GeneratingEnumeration.generatingAt_to_manuscript x U
    hU.generating hU.catalogue⟩

/-- For a walk of actual k-unique words, Boolean spectra are a consequence of
the checked path lemma. Only the edge catalogue/survival interface remains. -/
theorem extract_word_walk {t k m n : ℕ} (ht : 2 ≤ t)
    (words : Fin (m + 1) → Letters)
    (K : Set (Gram (windowLength k) → ℤ))
    (hunique : ∀ j, Windows.KUnique (words j) n k)
    (hclosed : Agree (words 0) 0 (words (Fin.last m)) 0 n) (hodd : Odd m)
    (hcat : ∀ i : Fin m, CatalogueRule t k
      (wordSpectrum (words i.succ) n (windowLength k) -
       wordSpectrum (words i.castSucc) n (windowLength k)))
    (hK : ∀ i : Fin m, (wordSpectrum (words i.succ) n (windowLength k) -
       wordSpectrum (words i.castSucc) n (windowLength k)) ∈ K) :
    ∃ U : RuleSet k,
      Witness t k (wordSpectrum (words 0) n (windowLength k)) K U ∧
      ManuscriptCounting.GeneratingSet t (words 0) n k U.card (componentCount U) U := by
  classical
  let p := fun j => wordSpectrum (words j) n (windowLength k)
  have hp : ∀ j, WitnessAlgebra.BooleanVector (rationalPath p j) := by
    intro j g
    have hku := SpectrumPath.kunique_mono (words j) n k (windowLength k - 1)
      (hunique j) (by unfold windowLength; omega)
    rcases SpectrumPath.spectrum_boolean (words j) n (windowLength k) hku g with hz | ho
    · left; change (wordSpectrum (words j) n (windowLength k) g : ℚ) = 0
      exact_mod_cast hz
    · right; change (wordSpectrum (words j) n (windowLength k) g : ℚ) = 1
      exact_mod_cast ho
  have hclosedP : p 0 = p (Fin.last m) := by
    funext g
    unfold p wordSpectrum
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val + windowLength k ≤ n
    · have heq : gram (words 0) (windowLength k) i.val =
          gram (words (Fin.last m)) (windowLength k) i.val := by
        funext q
        have hq := hclosed (i.val + q.val) (by have := q.isLt; omega)
        simpa only [Nat.zero_add, gram] using hq
      simp only [hi, true_and, heq]
    · simp only [hi, false_and, ite_false]
  exact extract_counted ht (words 0) p K rfl hp hclosedP hodd hcat hK

#print axioms extract
#print axioms extract_counted
#print axioms extract_word_walk

end DeletionCode.BoundedWitnessWalk
