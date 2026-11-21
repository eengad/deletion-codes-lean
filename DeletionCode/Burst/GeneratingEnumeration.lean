import DeletionCode.Burst.CatalogueFamily
import DeletionCode.Burst.CatalogueBridge
import DeletionCode.Burst.ManuscriptCounting
import DeletionCode.Qary.GeneratingEnumeration

/-!
Concrete catalogue presentations inherit the checked ordered enumeration of
finite generating sets. All word geometry and length balance are obtained
from the individual catalogue witnesses.
-/
namespace DeletionCode.Burst.GeneratingEnumeration

open Qary.Windows Qary.RootSelection Qary.SignedSupport Qary.RuleReconstruction
open Qary.RuleSetGraph Qary.SignedRuleCount Qary.FiniteGenerating
open Qary.CanonicalIndex (flatten group indexEquiv group_sum)
open Catalogue CatalogueFamily
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

structure CataloguePresentation (t k b R : ℕ)
    (rules : Fin R → Gram α (windowLength k b) → ℤ) where
  words : Fin R → Fin (2 * t) → BubbleWord α k b
  valid : ValidCatalogue (flatten t R words) (group t R)
  balanced : Balanced (flatten t R words) (group t R)
  rule_eq : ∀ r : Fin R,
    ruleSpectrum (flatFamily t R words) (windowLength k b)
      (groupBubbles (group t R) r) = rules r

noncomputable def presentationOfCatalogue {t k b R : ℕ}
    (rules : Fin R → Gram α (windowLength k b) → ℤ)
    (hcat : ∀ r, Rule t k b (rules r)) : CataloguePresentation t k b R rules := by
  classical
  let words : Fin R → Fin (2 * t) → BubbleWord α k b := fun r => Classical.choose (hcat r)
  have hv (r : Fin R) : ValidCatalogue (words r) (fun _ => (0 : Fin 1)) :=
    (Classical.choose_spec (hcat r)).1
  have hbal (r : Fin R) : Balanced (words r) (fun _ => (0 : Fin 1)) :=
    (Classical.choose_spec (hcat r)).2.1
  let P := CatalogueFamily.ofCatalogue rules hcat
  refine ⟨words, ?_, ?_, P.rule_eq⟩
  · refine ⟨P.geometry, P.start, ?_, ?_⟩
    · intro i
      exact (hv (group t R i)).common_end (indexEquiv t R i).2
    · intro r
      rw [← FamilySupport.rank_bubbles_eq_group P.E (group t R) P.rank r]
      exact P.disjoint r.val
  · intro r
    unfold groupBubbles
    rw [group_sum, group_sum]
    simp only [flatten, Equiv.apply_symm_apply]
    simpa only [Balanced, groupBubbles, Finset.filter_true] using hbal r (0 : Fin 1)

theorem CataloguePresentation.signedGenerating {t k b R : ℕ}
    {rules : Fin R → Gram α (windowLength k b) → ℤ} (P : CataloguePresentation t k b R rules)
    (x : Letters α) (n : ℕ)
    (hgen : ∀ i g, rules i g = -1 → wordSpectrum x n (windowLength k b) g ≠ 0 ∨
      ∃ j : Fin R, j < i ∧ rules j g ≠ 0) :
    SignedGenerating (flatFamily t R P.words) x n (windowLength k b) := by
  let E := flatFamily t R P.words
  have hrank : ∀ j, E.rank j = (group t R j).val := fun _ => rfl
  have heq (r : Fin R) :
      ruleSpectrum E (windowLength k b) (ruleBubbles E r.val) = rules r := by
    rw [FamilySupport.rank_bubbles_eq_group E (group t R) hrank r]
    exact P.rule_eq r
  intro i g hneg
  have hnonzero : ruleSpectrum E (windowLength k b) (ruleBubbles E i) g ≠ 0 := by
    change ruleSpectrum E (windowLength k b) (ruleBubbles E i) g = -1 at hneg
    omega
  obtain ⟨j, hj, _⟩ := (rule_support_iff E (windowLength k b) P.valid.geometry
    (ruleBubbles E i) (P.valid.rank_disjoint i) g).mp hnonzero
  have hji : E.rank j = i := (Finset.mem_filter.mp hj).2
  have hi : i < R := by
    rw [hrank j] at hji
    exact hji ▸ (group t R j).isLt
  let r : Fin R := ⟨i, hi⟩
  have hrneg : rules r g = -1 := by
    rw [← heq r]
    exact hneg
  rcases hgen r g hrneg with hv | ⟨j, hj, hjg⟩
  · exact Or.inl hv
  · refine Or.inr ⟨j.val, hj, ?_⟩
    rw [heq j]
    exact hjg

/-- The same actual finite set counted by recovery is obtained from witness
provenance; no presentation or generation premise is left to the caller. -/
theorem generatingAt_to_manuscript {t k b n : ℕ} (x : Letters α)
    (G : RuleSet α (k + b))
    (hgen : GeneratingAt (wordSpectrum x n (windowLength k b)) G)
    (hcat : ∀ u ∈ G, Rule t k b u) :
    ManuscriptCounting.GeneratingSet t x n k b G.card (componentCount G) G := by
  classical
  obtain ⟨e, horder⟩ := Qary.GeneratingEnumeration.exists_ordered_enumeration
    (wordSpectrum x n (windowLength k b)) G hgen
  let rules : Fin G.card → Gram α (windowLength k b) → ℤ := fun r => (e r).val
  let P := presentationOfCatalogue rules (fun r => hcat (e r).val (e r).property)
  let E := CatalogueBridge.editedFamily (flatten t G.card P.words) (group t G.card) P.valid
  have hfamily : E.family = flatFamily t G.card P.words :=
    CatalogueBridge.family_eq _ _ P.valid
  have hrank : ∀ j, E.rank j = (group t G.card j).val := by
    intro j
    change E.family.rank j = _
    rw [hfamily]
    rfl
  have himage : Finset.univ.image rules = G := by
    ext u
    constructor
    · intro hu
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hu
      exact (e r).property
    · intro hu
      obtain ⟨r, hr⟩ := e.surjective ⟨u, hu⟩
      exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, congrArg Subtype.val hr⟩
  refine ⟨rfl, rfl, E, hrank, ?_, ?_, ?_, ?_⟩
  · rw [hfamily]
    exact P.valid.geometry
  · rw [hfamily]
    exact P.valid.rank_disjoint
  · rw [hfamily]
    exact P.signedGenerating x n horder
  · change FamilySupport.rulesOfFamily E.family (windowLength k b) (group t G.card) = G
    rw [hfamily]
    apply Eq.trans (b := Finset.univ.image rules) _ himage
    unfold FamilySupport.rulesOfFamily
    apply Finset.image_congr
    intro r hr
    exact P.rule_eq r

#print axioms presentationOfCatalogue
#print axioms CataloguePresentation.signedGenerating
#print axioms generatingAt_to_manuscript

end DeletionCode.Burst.GeneratingEnumeration
