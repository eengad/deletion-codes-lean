import DeletionCode.TraceBubbleFamily
import DeletionCode.BubbleCatalogue
import DeletionCode.LocalBubbleDisjoint
import DeletionCode.TraceSpectrumAssembly

/-!
Coverage of actual separated alignments by the manuscript's catalogue.
The edit columns provide the finite balanced index set. Each column's local
bubble, its geometry, and pairwise vertex disjointness are derived from the
source and trace. The actual full spectrum difference is assembled using the
proved trace telescope, rather than supplied as a presentation assumption.
-/
namespace DeletionCode.SeparatedTraceCoverage

open Windows HeaderRecovery CatalogueWords AlignmentTrace FiniteConflictGraph
open SignedSupport RunBubbleConstruction TraceEditData TraceBubbleFamily
open scoped BigOperators

/-- Manuscript lemma `lem:coverage`: an actual alignment with equally many
deletions and insertions and 2t edit columns in all, separated by 4L matched
columns and from both boundaries, has its target-minus-source spectrum in
the concrete catalogue. -/
theorem catalogueRule (trace : Trace) (t k : ℕ) (hk : 1 ≤ k)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace)
    (hbal : trace.deletions = trace.insertions)
    (hsum : 2 * trace.deletions + trace.substitutions = 2 * t) :
    ConnectedBlocks.CatalogueRule t k
      (wordSpectrum (listLetters trace.target) trace.target.length (windowLength k) -
        wordSpectrum (listLetters trace.source) trace.source.length (windowLength k)) := by
  classical
  let E : Fin (2 * t) ≃ EditColumn trace := editEquiv trace t hbal hsum
  let P := fun i : Fin (2 * t) => bubbleAt trace k hx hsep (E i)
  let words : Fin (2 * t) → BubbleWord k := fun i => (P i).bubble
  have hboundary : ∀ i, (words i).orientation ≠ .substitution →
      (words i).left.getLast? = some (!(words i).bit) ∧
        (words i).right.head? = some (!(words i).bit) :=
    fun i h => ⟨(P i).left_boundary h, (P i).right_boundary h⟩
  have hgeometry : ∀ i, BubbleContextGeometry.Geometry (words i) :=
    fun i => SingleEditBubbles.LocalBubble.geometry (P i) hk hx
  have hdisjoint : ∀ a b : Fin (2 * t), a ≠ b → ∀ sa sb i j,
      i + (windowLength k - 1) ≤ (BubbleCatalogue.pathWord (words a) sa).length →
      j + (windowLength k - 1) ≤ (BubbleCatalogue.pathWord (words b) sb).length →
      SpectrumPath.vertexAt (listLetters (BubbleCatalogue.pathWord (words a) sa)) (windowLength k) i ≠
        SpectrumPath.vertexAt (listLetters (BubbleCatalogue.pathWord (words b) sb)) (windowLength k) j := by
    intro a b hab sa sb i j hi hj
    have hindices : (E a).val ≠ (E b).val := by
      intro heq
      exact hab (E.injective (Subtype.ext heq))
    exact LocalBubbleDisjoint.localVertex_ne_of_trace hk hx hsep
      (E a).val (E b).val (E a).property (E b).property hindices (P a) (P b)
      sa sb i j hi hj
  have hcount (o : Orientation) :
      (Finset.univ.filter (fun i => (words i).orientation = o)).card =
        Fintype.card {c : EditColumn trace // orientation trace c = o} := by
    calc
      _ = Fintype.card {i : Fin (2 * t) // (words i).orientation = o} :=
        (Fintype.card_subtype (fun i : Fin (2 * t) => (words i).orientation = o)).symm
      _ = _ := Fintype.card_congr (E.subtypeEquiv (by
        intro i
        change (P i).bubble.orientation = o ↔ orientation trace (E i) = o
        rw [(P i).orientation_eq]))
  have hdelWords : (Finset.univ.filter (fun i => (words i).orientation = .deletion)).card =
      trace.deletions :=
    (hcount .deletion).trans (card_deletionColumns trace)
  have hinsWords : (Finset.univ.filter (fun i => (words i).orientation = .insertion)).card =
      trace.insertions :=
    (hcount .insertion).trans (card_insertionColumns trace)
  have hsubWords : (Finset.univ.filter (fun i => (words i).orientation = .substitution)).card =
      trace.substitutions :=
    (hcount .substitution).trans (card_substitutionColumns trace)
  let delta := fun c : EditColumn trace =>
    wordSpectrum (listLetters (oneEditTarget trace c)) (oneEditTarget trace c).length (windowLength k) -
      wordSpectrum (listLetters trace.source) trace.source.length (windowLength k)
  have hspectrum :
      wordSpectrum (listLetters trace.target) trace.target.length (windowLength k) -
        wordSpectrum (listLetters trace.source) trace.source.length (windowLength k) =
      ∑ i : Fin (2 * t),
        (wordSpectrum (listLetters (words i).positiveWord) (words i).positiveWord.length (windowLength k) -
          wordSpectrum (listLetters (words i).negativeWord) (words i).negativeWord.length (windowLength k)) := by
    calc
      _ = ∑ c : EditColumn trace, delta c :=
        TraceSpectrumAssembly.spectrum_sum (by unfold windowLength; omega) hsep
      _ = ∑ i : Fin (2 * t), delta (E i) := (E.sum_comp delta).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact SingleEditBubbles.LocalBubble.spectrum_change (P i)
  rw [hspectrum]
  exact BubbleCatalogue.catalogueRule words hboundary hgeometry hdisjoint
    (by rw [hdelWords, hinsWords]; exact hbal) (by rw [hdelWords, hsubWords]; exact hsum)

#print axioms catalogueRule

end DeletionCode.SeparatedTraceCoverage
