import DeletionCode.Burst.SeparatedBubbles
import DeletionCode.Burst.Catalogue
import DeletionCode.Qary.BubbleCatalogue

/-!
Coverage of actual separated burst histories by the fixed catalogue. Every
catalogue condition follows from source-derived local bubbles, transported
chronological neighborhoods, and exact telescoping of the actual edits.
-/
namespace DeletionCode.Burst.CatalogueCoverage

open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords
open DeletionCode.Qary.SignedSupport DeletionCode.Qary.SupportComponents
open DeletionCode.Burst.Catalogue
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

theorem bubble_spectrum {B : Type*} {k b : ℕ} (words : B → BubbleWord α k b)
    (rank : B → ℕ) (i : B) :
    bubbleSpectrum (family words rank) (windowLength k b) i =
      wordSpectrum (listLetters (words i).positiveWord) (words i).positiveWord.length
        (windowLength k b) -
      wordSpectrum (listLetters (words i).negativeWord) (words i).negativeWord.length
        (windowLength k b) := by
  rw [Qary.BubbleCatalogue.wordSpectrum_eq_pathSpectrum _ _ _ (words i).positiveWord_length_bounds.1,
    Qary.BubbleCatalogue.wordSpectrum_eq_pathSpectrum _ _ _ (words i).negativeWord_length_bounds.1]
  funext g
  simp only [bubbleSpectrum, family, pathWord, Bool.false_eq_true, ite_false, ite_true, Pi.sub_apply]

theorem catalogueRule {k b t : ℕ} {x y : Word α} {es : List (Edit α)}
    (hk : 1 ≤ k) (hx : KUnique (listLetters x) x.length k)
    (h : Executes b x es y) (hlen : es.length = 2 * t)
    (hsep : Separated x.length (8 * (windowLength k b + t * b)) es)
    (hxy : x.length = y.length) :
    Rule t k b (wordSpectrum (listLetters y) y.length (windowLength k b) -
      wordSpectrum (listLetters x) x.length (windowLength k b)) := by
  classical
  obtain ⟨P⟩ := exists_sourcePackets hk hx h (by omega) hsep
  let E : Fin (2 * t) ≃ Fin es.length := finCongr hlen.symm
  let words : Fin (2 * t) → BubbleWord α k b := fun i => (P.packet (E i)).bubble
  let group := fun _ : Fin (2 * t) => (0 : Fin 1)
  let F := indexedFamily words group
  have hL : 1 ≤ windowLength k b := by unfold windowLength; omega
  have hlen' (i : Fin (2 * t)) (s : Bool) := word_length_bounds (words i) s
  have hgeometry : BubbleGeometry F (windowLength k b) := by
    refine ⟨?_, ?_, Catalogue.notBothSingle words (fun i => (group i).val)⟩
    · intro a side i j heq
      have hunique : KUnique (listLetters (pathWord (words a) side))
          (pathWord (words a) side).length (windowLength k b - 1) := by
        cases side
        · exact (P.packet (E a)).negative_unique
        · exact (P.packet (E a)).positive_unique
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      change i.val < (pathWord (words a) side).length - windowLength k b + 2 at hi
      change j.val < (pathWord (words a) side).length - windowLength k b + 2 at hj
      apply hunique i.val j.val (by have := (hlen' a side).1; omega)
        (by have := (hlen' a side).1; omega)
      intro r hr
      exact congrFun heq ⟨r, hr⟩
    · intro a i j hi hj heq
      have hn := (words a).negativeWord_length_bounds.1
      have hp := (words a).positiveWord_length_bounds.1
      change i ≤ (words a).negativeWord.length - windowLength k b + 1 at hi
      change j ≤ (words a).positiveWord.length - windowLength k b + 1 at hj
      have ends := (P.packet (E a)).endpoints i j
        (by change i + (windowLength k b - 1) ≤ (words a).negativeWord.length; omega)
        (by change j + (windowLength k b - 1) ≤ (words a).positiveWord.length; omega)
        (fun r hr => congrFun heq ⟨r, hr⟩)
      change (i = 0 ∧ j = 0) ∨
        (i = (words a).negativeWord.length - windowLength k b + 1 ∧
          j = (words a).positiveWord.length - windowLength k b + 1)
      change (i = 0 ∧ j = 0) ∨
        (i = (words a).negativeWord.length - (windowLength k b - 1) ∧
          j = (words a).positiveWord.length - (windowLength k b - 1)) at ends
      omega
  have hstart : ∀ i, vertex F (windowLength k b) i false 0 =
      vertex F (windowLength k b) i true 0 := by
    intro i
    funext a
    exact (P.packet (E i)).initial_agreement a.val a.isLt
  have hend : ∀ i, vertex F (windowLength k b) i false (F.extra i false + 1) =
      vertex F (windowLength k b) i true (F.extra i true + 1) := by
    intro i
    funext a
    have hn := (words i).negativeWord_length_bounds.1
    have hp := (words i).positiveWord_length_bounds.1
    change listLetters (words i).negativeWord
      ((words i).negativeWord.length - windowLength k b + 1 + a.val) =
      listLetters (words i).positiveWord
      ((words i).positiveWord.length - windowLength k b + 1 + a.val)
    have hnidx : (words i).negativeWord.length - windowLength k b + 1 =
        (words i).negativeWord.length - (windowLength k b - 1) := by omega
    have hpidx : (words i).positiveWord.length - windowLength k b + 1 =
        (words i).positiveWord.length - (windowLength k b - 1) := by omega
    rw [hnidx, hpidx]
    exact (P.packet (E i)).terminal_agreement a.val a.isLt
  have hdis : VertexDisjointOn F (windowLength k b) Finset.univ := by
    intro a _ c _ hne sa sc i j hi hj heq
    have han := (hlen' a sa).1
    have hcn := (hlen' c sc).1
    change i ≤ (pathWord (words a) sa).length - windowLength k b + 1 at hi
    change j ≤ (pathWord (words c) sc).length - windowLength k b + 1 at hj
    exact P.separated_windows hk hx h (by omega) hsep (E a) (E c)
      (fun hh => hne (E.injective hh)) sa sc i j
      (by change i + (windowLength k b - 1) ≤ (pathWord (words a) sa).length; omega)
      (by change j + (windowLength k b - 1) ≤ (pathWord (words c) sc).length; omega)
      (fun r hr => congrFun heq ⟨r, hr⟩)
  have hvalid : ValidCatalogue words group := by
    refine ⟨hgeometry, hstart, hend, ?_⟩
    intro r
    exact fun a _ c _ hne sa sc i j hi hj =>
      hdis a (Finset.mem_univ a) c (Finset.mem_univ c) hne sa sc i j hi hj
  have hbalanced : Balanced words group := by
    intro r
    have hr : r = 0 := Subsingleton.elim _ _
    subst r
    simp only [Qary.RuleReconstruction.groupBubbles, group, Finset.filter_true]
    change (∑ i : Fin (2 * t), (P.packet (E i)).bubble.negativeWord.length) =
      ∑ i : Fin (2 * t), (P.packet (E i)).bubble.positiveWord.length
    rw [E.sum_comp (fun i => (P.packet i).bubble.negativeWord.length),
      E.sum_comp (fun i => (P.packet i).bubble.positiveWord.length)]
    exact P.balanced h (by omega) hsep hxy
  have hsum := P.spectrum_sum h (by omega) hsep
  rw [← E.sum_comp (fun i =>
    wordSpectrum (listLetters (P.packet i).bubble.positiveWord)
      (P.packet i).bubble.positiveWord.length (windowLength k b) -
    wordSpectrum (listLetters (P.packet i).bubble.negativeWord)
      (P.packet i).bubble.negativeWord.length (windowLength k b))] at hsum
  refine ⟨words, hvalid, hbalanced, ?_⟩
  rw [hsum]
  funext g
  simp only [ruleSpectrum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (bubble_spectrum words (fun j => (group j).val) i) g

#print axioms catalogueRule

end DeletionCode.Burst.CatalogueCoverage
