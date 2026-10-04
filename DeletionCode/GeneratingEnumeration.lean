import DeletionCode.FiniteGenerating
import DeletionCode.ManuscriptCounting
import DeletionCode.CatalogueFamily
import Mathlib.Data.Finset.Sort

/-!
A finite generating set has a genuine ordered enumeration, obtained by sorting
its injective ranks. Choosing each rule's concrete catalogue presentation and
flattening the fixed occurrence labels then gives the exact catalogue class
used by the manuscript counting theorem. No enumeration, signed-generation
bridge, or global catalogue presentation is supplied as an assumption.
-/

namespace DeletionCode.GeneratingEnumeration

open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph SupportComponents
open CanonicalIndex ConnectedBlocks FiniteGenerating
open scoped BigOperators

/-- Sort the actual finite set by its injective ranks. -/
theorem rank_sorted_enumeration {k : ℕ} (G : RuleSet k)
    (rank : (Gram (windowLength k) → ℤ) → ℕ)
    (hinj : Set.InjOn rank (↑G : Set _)) :
    ∃ e : Fin G.card ≃ G, StrictMono (fun i => rank (e i).val) := by
  classical
  let S := G.image rank
  let f : G → S := fun u => ⟨rank u.val, Finset.mem_image.mpr ⟨u.val, u.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      apply Subtype.ext
      exact hinj u.property v.property (congrArg Subtype.val huv)
    · intro r
      obtain ⟨u, hu, hur⟩ := Finset.mem_image.mp r.property
      exact ⟨⟨u, hu⟩, Subtype.ext hur⟩
  let er : G ≃ S := Equiv.ofBijective f hf
  have hcard : S.card = G.card := by
    simpa using Fintype.card_congr er.symm
  let sorted : Fin G.card ≃o S := S.orderIsoOfFin hcard
  let e : Fin G.card ≃ G := sorted.toEquiv.trans er.symm
  have hrank (i : Fin G.card) : rank (e i).val = (sorted i).val := by
    exact congrArg Subtype.val (er.apply_symm_apply (sorted i))
  refine ⟨e, ?_⟩
  intro i j hij
  change rank (e i).val < rank (e j).val
  rw [hrank i, hrank j]
  exact sorted.strictMono hij

/-- The earlier-supplier property survives the rank-sorted finite enumeration. -/
theorem exists_ordered_enumeration {k : ℕ} (v : Gram (windowLength k) → ℤ)
    (G : RuleSet k) (hgen : GeneratingAt v G) :
    ∃ e : Fin G.card ≃ G, ∀ i g, (e i).val g = -1 →
      v g ≠ 0 ∨ ∃ j : Fin G.card, j < i ∧ (e j).val g ≠ 0 := by
  classical
  obtain ⟨rank, hinj, horder⟩ := hgen.ordered
  obtain ⟨e, hmono⟩ := rank_sorted_enumeration G rank hinj
  refine ⟨e, ?_⟩
  intro i g hneg
  rcases horder (e i).val (e i).property g hneg with hv | ⟨z, hz, hrank, hzg⟩
  · exact Or.inl hv
  · let j : Fin G.card := e.symm ⟨z, hz⟩
    have hj : (e j).val = z := by simp [j]
    have hji : j < i := by
      by_contra hnot
      have hij : i ≤ j := le_of_not_gt hnot
      have hrle := hmono.monotone hij
      rw [hj] at hrle
      omega
    exact Or.inr ⟨j, hji, by simpa only [hj] using hzg⟩

/-- Retain the actual words and every catalogue filter, including orientation balance. -/
structure CataloguePresentation (t k R : ℕ) (rules : Fin R → Gram (windowLength k) → ℤ) where
  words : Fin R → Fin (2 * t) → BubbleWord k
  valid : ValidCatalogue (flatten t R words) (group t R)
  balanced : OrientationBalanced t (flatten t R words) (group t R)
  rule_eq : ∀ r : Fin R,
    ruleSpectrum (flatFamily t R words).family (windowLength k)
      (groupBubbles (group t R) r) = rules r

private def singleFamily {t k : ℕ} (words : Fin (2 * t) → BubbleWord k) :
    EditedFamily (Fin (2 * t)) k :=
  indexedFamily words (fun _ => (0 : Fin 1))

private theorem flat_extra_eq {t k R : ℕ}
    (words : Fin R → Fin (2 * t) → BubbleWord k) (b : Fin (2 * t * R)) (side : Bool) :
    (flatFamily t R words).family.extra b side =
      (singleFamily (words (group t R b))).family.extra (indexEquiv t R b).2 side := rfl

private theorem flat_vertex_eq {t k R : ℕ}
    (words : Fin R → Fin (2 * t) → BubbleWord k) (b : Fin (2 * t * R))
    (side : Bool) (i : ℕ) :
    vertex (flatFamily t R words).family (windowLength k) b side i =
      vertex (singleFamily (words (group t R b))).family
        (windowLength k) (indexEquiv t R b).2 side i := rfl

private theorem orientation_count {t k R : ℕ}
    (words : Fin R → Fin (2 * t) → BubbleWord k) (r : Fin R) (o : Orientation) :
    (Finset.univ.filter (fun b : Fin (2 * t * R) =>
      group t R b = r ∧ (flatten t R words b).orientation = o)).card =
    (Finset.univ.filter (fun j : Fin (2 * t) => (words r j).orientation = o)).card := by
  classical
  apply Finset.card_bij (fun b _ => (indexEquiv t R b).2)
  · intro b hb
    obtain ⟨hgroup, ho⟩ := (Finset.mem_filter.mp hb).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (words (group t R b) (indexEquiv t R b).2).orientation = o at ho
    simpa only [hgroup] using ho
  · intro a ha b hb hab
    apply (indexEquiv t R).injective
    exact Prod.ext
      (((Finset.mem_filter.mp ha).2.1).trans ((Finset.mem_filter.mp hb).2.1).symm) hab
  · intro j hj
    refine ⟨(indexEquiv t R).symm (r, j), ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, by simp [group], ?_⟩
    simpa only [flatten_at_pair] using (Finset.mem_filter.mp hj).2

/-- Assemble the individual catalogue witnesses with the paper's fixed labels. -/
noncomputable def presentationOfCatalogue {t k R : ℕ}
    (rules : Fin R → Gram (windowLength k) → ℤ)
    (hcat : ∀ r, CatalogueRule t k (rules r)) : CataloguePresentation t k R rules := by
  classical
  let words : Fin R → Fin (2 * t) → BubbleWord k := fun r => Classical.choose (hcat r)
  have hvalid (r : Fin R) : ValidCatalogue (words r) (fun _ => (0 : Fin 1)) :=
    (Classical.choose_spec (hcat r)).1
  have hbalanced (r : Fin R) : OrientationBalanced t (words r) (fun _ => (0 : Fin 1)) :=
    (Classical.choose_spec (hcat r)).2.1
  have hvalue (r : Fin R) :
      ruleSpectrum (singleFamily (words r)).family (windowLength k) Finset.univ = rules r :=
    (Classical.choose_spec (hcat r)).2.2
  refine ⟨words, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro b
      exact (hvalid (group t R b)).boundary (indexEquiv t R b).2
    · intro b side
      exact (hvalid (group t R b)).simple (indexEquiv t R b).2 side
    · intro b i j hi hj heq
      exact (hvalid (group t R b)).endpoints (indexEquiv t R b).2 i j hi hj heq
    · intro r a ha b hb hab sa sb j l hj hl
      have hra := (Finset.mem_filter.mp ha).2
      have hrb := (Finset.mem_filter.mp hb).2
      have hgroup : group t R b = group t R a := hrb.trans hra.symm
      have hlocal_ne : (indexEquiv t R a).2 ≠ (indexEquiv t R b).2 := by
        intro heq
        apply hab
        apply (indexEquiv t R).injective
        exact Prod.ext hgroup.symm heq
      have hj' : j ≤ (singleFamily (words (group t R a))).family.extra
          (indexEquiv t R a).2 sa + 1 := hj
      have hl' : l ≤ (singleFamily (words (group t R a))).family.extra
          (indexEquiv t R b).2 sb + 1 := by
        change l ≤ (flatFamily t R words).family.extra b sb + 1 at hl
        simpa only [flat_extra_eq, hgroup] using hl
      have hd := (hvalid (group t R a)).within_rule_disjoint (0 : Fin 1)
        (indexEquiv t R a).2 (by simp) (indexEquiv t R b).2 (by simp)
        hlocal_ne sa sb j l hj' hl'
      change vertex (flatFamily t R words).family (windowLength k) a sa j ≠
        vertex (flatFamily t R words).family (windowLength k) b sb l
      simpa only [flat_vertex_eq, hgroup, singleFamily] using hd
  · intro r
    constructor
    · rw [orientation_count]
      simpa using (hbalanced r (0 : Fin 1)).1
    · rw [orientation_count]
      simpa using (hbalanced r (0 : Fin 1)).2
  · intro r
    calc
      ruleSpectrum (flatFamily t R words).family (windowLength k)
          (groupBubbles (group t R) r) =
          fun g => ∑ j : Fin (2 * t),
            bubbleSpectrum (pairFamily t R words).family (windowLength k) (r, j) g :=
        flat_rule_spectrum t R words r
      _ = ruleSpectrum (singleFamily (words r)).family (windowLength k) Finset.univ := by
        funext g
        apply Finset.sum_congr rfl
        intro j hj
        rfl
      _ = rules r := hvalue r

/-- The concrete chosen presentation inherits exactly the earlier-rule suppliers. -/
theorem CataloguePresentation.signedGenerating {t k R : ℕ}
    {rules : Fin R → Gram (windowLength k) → ℤ} (P : CataloguePresentation t k R rules)
    (x : Letters) (n : ℕ)
    (hgen : ∀ i g, rules i g = -1 → wordSpectrum x n (windowLength k) g ≠ 0 ∨
      ∃ j : Fin R, j < i ∧ rules j g ≠ 0) :
    SignedGenerating (flatFamily t R P.words).family x n (windowLength k) := by
  let E := flatFamily t R P.words
  have hrank : ∀ b, E.rank b = (group t R b).val := fun _ => rfl
  have heq (r : Fin R) :
      ruleSpectrum E.family (windowLength k) (ruleBubbles E.family r.val) = rules r := by
    rw [rank_bubbles_eq_group E (group t R) hrank r]
    exact P.rule_eq r
  intro i g hneg
  have hnonzero : ruleSpectrum E.family (windowLength k) (ruleBubbles E.family i) g ≠ 0 := by
    change ruleSpectrum E.family (windowLength k) (ruleBubbles E.family i) g = -1 at hneg
    omega
  obtain ⟨b, hb, _⟩ := (rule_support_iff E.family (windowLength k) P.valid.geometry
    (ruleBubbles E.family i) (P.valid.rank_disjoint i) g).mp hnonzero
  have hbi : E.rank b = i := (Finset.mem_filter.mp hb).2
  have hi : i < R := by
    rw [hrank b] at hbi
    exact hbi ▸ (group t R b).isLt
  let r : Fin R := ⟨i, hi⟩
  have hrneg : rules r g = -1 := by
    rw [← heq r]
    exact hneg
  rcases hgen r g hrneg with hv | ⟨j, hj, hjg⟩
  · exact Or.inl hv
  · refine Or.inr ⟨j.val, hj, ?_⟩
    rw [heq j]
    exact hjg

/-- Finite ordered generation on actual catalogue vectors supplies the exact
concrete-presentation predicate counted by the manuscript theorem. -/
theorem generatingAt_to_manuscript {t k n : ℕ} (x : Letters) (G : RuleSet k)
    (hgen : GeneratingAt (wordSpectrum x n (windowLength k)) G)
    (hcat : ∀ w ∈ G, CatalogueRule t k w) :
    ManuscriptCounting.GeneratingSet t x n k G.card (componentCount G) G := by
  classical
  obtain ⟨e, horder⟩ := exists_ordered_enumeration (wordSpectrum x n (windowLength k)) G hgen
  let rules : Fin G.card → Gram (windowLength k) → ℤ := fun r => (e r).val
  let P := presentationOfCatalogue rules (fun r => hcat (e r).val (e r).property)
  have himage : Finset.univ.image rules = G := by
    ext u
    constructor
    · intro hu
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hu
      exact (e r).property
    · intro hu
      obtain ⟨r, hr⟩ := e.surjective ⟨u, hu⟩
      exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, congrArg Subtype.val hr⟩
  have hrules : rulesOfFamily (flatFamily t G.card P.words) (group t G.card) = G := by
    calc
      rulesOfFamily (flatFamily t G.card P.words) (group t G.card) = Finset.univ.image rules := by
        unfold rulesOfFamily
        apply Finset.image_congr
        intro r hr
        exact P.rule_eq r
      _ = G := himage
  exact ⟨rfl, rfl, P.words, P.valid, P.balanced,
    P.signedGenerating x n horder, hrules⟩

#print axioms rank_sorted_enumeration
#print axioms exists_ordered_enumeration
#print axioms presentationOfCatalogue
#print axioms CataloguePresentation.signedGenerating
#print axioms generatingAt_to_manuscript

end DeletionCode.GeneratingEnumeration
