import DeletionCode.Explicit.Borrowed.SeparatedBubbles
import DeletionCode.Explicit.Borrowed.Catalogue
import DeletionCode.Qary.BubbleCatalogue

/-!
Coverage of actual separated burst histories by the fixed catalogue. Every
catalogue condition follows from source-derived local bubbles, transported
chronological neighborhoods, and exact telescoping of the actual edits.
-/
namespace DeletionCode.Explicit.Borrowed.CatalogueCoverage

open DeletionCode.Burst
open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords
open DeletionCode.Qary.SignedSupport DeletionCode.Qary.SupportComponents
open DeletionCode.Explicit.Borrowed.Catalogue
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

theorem bubble_spectrum {B : Type*} {K b L : ℕ} (words : B → BubbleWord α K b L)
    (rank : B → ℕ) (i : B) (hwindow : 3 * (K + b + 1) ≤ L) :
    bubbleSpectrum (family words rank) L i =
      wordSpectrum (listLetters (words i).positiveWord) (words i).positiveWord.length
        L -
      wordSpectrum (listLetters (words i).negativeWord) (words i).negativeWord.length
        L := by
  have hpos := ((words i).positiveWord_length_bounds hwindow).1
  have hneg := ((words i).negativeWord_length_bounds hwindow).1
  rw [Qary.BubbleCatalogue.wordSpectrum_eq_pathSpectrum _ _ _ hpos,
    Qary.BubbleCatalogue.wordSpectrum_eq_pathSpectrum _ _ _ hneg]
  funext g
  simp only [bubbleSpectrum, family, pathWord, Bool.false_eq_true, ite_false, ite_true, Pi.sub_apply]

theorem catalogueRule {K b L t : ℕ} {x y : Word α} {es : List (Edit α)}
    (hk : 1 ≤ K) (hwindow : 3 * (K + b + 1) ≤ L)
    (hx : KUnique (listLetters x) x.length K)
    (h : Executes b x es y) (hlen : es.length = 2 * t)
    (hsep : Separated x.length (8 * (L + t * b)) es)
    (hxy : x.length = y.length) :
    Rule t K b L (wordSpectrum (listLetters y) y.length L -
      wordSpectrum (listLetters x) x.length L) := by
  classical
  obtain ⟨P⟩ := exists_sourcePackets hk hwindow hx h (by omega) hsep
  let E : Fin (2 * t) ≃ Fin es.length := finCongr hlen.symm
  let words : Fin (2 * t) → BubbleWord α K b L := fun i => (P.packet (E i)).bubble
  let group := fun _ : Fin (2 * t) => (0 : Fin 1)
  let F := indexedFamily words group
  have hL : 1 ≤ L := by omega
  have hlen' (i : Fin (2 * t)) (s : Bool) := word_length_bounds (words i) s hwindow
  have hgeometry : BubbleGeometry F L := by
    refine ⟨?_, ?_, Catalogue.notBothSingle words (fun i => (group i).val) hwindow⟩
    · intro a side i j heq
      have hunique : KUnique (listLetters (pathWord (words a) side))
          (pathWord (words a) side).length (L - 1) := by
        cases side
        · exact (P.packet (E a)).negative_unique
        · exact (P.packet (E a)).positive_unique
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      change i.val < (pathWord (words a) side).length - L + 2 at hi
      change j.val < (pathWord (words a) side).length - L + 2 at hj
      apply hunique i.val j.val (by have := (hlen' a side).1; omega)
        (by have := (hlen' a side).1; omega)
      intro r hr
      exact congrFun heq ⟨r, hr⟩
    · intro a i j hi hj heq
      have hn := ((words a).negativeWord_length_bounds hwindow).1
      have hp := ((words a).positiveWord_length_bounds hwindow).1
      change i ≤ (words a).negativeWord.length - L + 1 at hi
      change j ≤ (words a).positiveWord.length - L + 1 at hj
      have ends := (P.packet (E a)).endpoints i j
        (by change i + (L - 1) ≤ (words a).negativeWord.length; omega)
        (by change j + (L - 1) ≤ (words a).positiveWord.length; omega)
        (fun r hr => congrFun heq ⟨r, hr⟩)
      change (i = 0 ∧ j = 0) ∨
        (i = (words a).negativeWord.length - L + 1 ∧
          j = (words a).positiveWord.length - L + 1)
      change (i = 0 ∧ j = 0) ∨
        (i = (words a).negativeWord.length - (L - 1) ∧
          j = (words a).positiveWord.length - (L - 1)) at ends
      omega
  have hstart : ∀ i, vertex F L i false 0 =
      vertex F L i true 0 := by
    intro i
    funext a
    exact (P.packet (E i)).initial_agreement a.val a.isLt
  have hend : ∀ i, vertex F L i false (F.extra i false + 1) =
      vertex F L i true (F.extra i true + 1) := by
    intro i
    funext a
    have hn := ((words i).negativeWord_length_bounds hwindow).1
    have hp := ((words i).positiveWord_length_bounds hwindow).1
    change listLetters (words i).negativeWord
      ((words i).negativeWord.length - L + 1 + a.val) =
      listLetters (words i).positiveWord
      ((words i).positiveWord.length - L + 1 + a.val)
    have hnidx : (words i).negativeWord.length - L + 1 =
        (words i).negativeWord.length - (L - 1) := by omega
    have hpidx : (words i).positiveWord.length - L + 1 =
        (words i).positiveWord.length - (L - 1) := by omega
    rw [hnidx, hpidx]
    exact (P.packet (E i)).terminal_agreement a.val a.isLt
  have hdis : VertexDisjointOn F L Finset.univ := by
    intro a _ c _ hne sa sc i j hi hj heq
    have han := (hlen' a sa).1
    have hcn := (hlen' c sc).1
    change i ≤ (pathWord (words a) sa).length - L + 1 at hi
    change j ≤ (pathWord (words c) sc).length - L + 1 at hj
    exact P.separated_windows hk hwindow hx h (by omega) hsep (E a) (E c)
      (fun hh => hne (E.injective hh)) sa sc i j
      (by change i + (L - 1) ≤ (pathWord (words a) sa).length; omega)
      (by change j + (L - 1) ≤ (pathWord (words c) sc).length; omega)
      (fun r hr => congrFun heq ⟨r, hr⟩)
  have hvalid : ValidCatalogue words group := by
    refine ⟨fun i side => (hlen' i side).1, hgeometry, hstart, hend, ?_⟩
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
    exact P.balanced hwindow h (by omega) hsep hxy
  have hsum := P.spectrum_sum hwindow h (by omega) hsep
  rw [← E.sum_comp (fun i =>
    wordSpectrum (listLetters (P.packet i).bubble.positiveWord)
      (P.packet i).bubble.positiveWord.length L -
    wordSpectrum (listLetters (P.packet i).bubble.negativeWord)
      (P.packet i).bubble.negativeWord.length L)] at hsum
  refine ⟨words, hvalid, hbalanced, ?_⟩
  rw [hsum]
  funext g
  simp only [ruleSpectrum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (bubble_spectrum words (fun j => (group j).val) i hwindow) g

/-- Separated histories of `2 * t` edits give a vector in the manuscript catalogue. -/
theorem coverage {K b L t : ℕ} {x y : Word α} {es : List (Edit α)}
    (hk : 1 ≤ K) (hwindow : 3 * (K + b + 1) ≤ L)
    (hx : KUnique (listLetters x) x.length K)
    (h : Executes b x es y) (hlen : es.length = 2 * t)
    (hsep : Separated x.length (8 * (L + t * b)) es)
    (hxy : x.length = y.length) :
    wordSpectrum (listLetters y) y.length L - wordSpectrum (listLetters x) x.length L ∈
      Catalogue.catalogue α t K b L :=
  (catalogueRule hk hwindow hx h hlen hsep hxy).mem_catalogue

#print axioms catalogueRule
#print axioms coverage

end DeletionCode.Explicit.Borrowed.CatalogueCoverage
