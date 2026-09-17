import DeletionCode.CatalogueFamily
import DeletionCode.ComponentFibers
import DeletionCode.RelationSupport
import DeletionCode.SupportInclusion

/-!
Savings from an actual rational relation among catalogue rules. Every support
component containing a single bubble occurrence must survive in the resulting
rule. That rule has at most 2t components, so counting the remaining occurrences
twice yields c(I) ≤ t|I| + t. No independence or generation assumption is needed.
-/

namespace DeletionCode.RelationSavings

open HeaderRecovery SignedSupport RuleReconstruction RuleSetGraph SupportComponents
open SignedRuleCount ConnectedBlocks CatalogueFamily ComponentFibers SupportInclusion
open scoped BigOperators

variable {t k R : ℕ} {G : Fin R → Gram (windowLength k) → ℤ}

private theorem group_disjoint (P : PresentedFamily t k R G) (r : Fin R) :
    VertexDisjointOn P.E.family (windowLength k)
      (groupBubbles (CanonicalIndex.group t R) r) := by
  rw [← rank_bubbles_eq_group P.E (CanonicalIndex.group t R) P.rank r]
  exact P.disjoint r.val

/-- A singleton occurrence component supplies a coordinate unique to its rule. -/
theorem singleton_coordinate (P : PresentedFamily t k R G)
    (C : RuleSetComponents (Finset.univ.image G))
    (hC : SingletonFiber P.bubbleComponent C) :
    ∃ r g, G r g ≠ 0 ∧ (∀ s, s ≠ r → G s g = 0) ∧
      ∃ hg : Incident (Finset.univ.image G) (gramPrefix g),
        Quotient.mk (ruleSetSetoid (Finset.univ.image G)) ⟨gramPrefix g, hg⟩ = C := by
  classical
  obtain ⟨b, hb, huniq⟩ := hC
  let r := CanonicalIndex.group t R b
  let g := gram (P.E.family.path b false) (windowLength k) 0
  have hgram : g ∈ windowSet (P.E.family.path b false) (windowLength k)
      (P.E.family.extra b false) := ⟨⟨0, by omega⟩, rfl⟩
  have hhas : HasGram P.E.family (windowLength k) b g := ⟨false, hgram⟩
  have hmem : b ∈ groupBubbles (CanonicalIndex.group t R) r := by
    simp [groupBubbles, r]
  have hneg : G r g = -1 := by
    rw [← P.rule_eq r]
    exact rule_negative_of_window P.E.family (windowLength k) P.geometry _
      (group_disjoint P r) b hmem g hgram
  refine ⟨r, g, by omega, ?_, ?_⟩
  · intro s hsr
    by_contra hnonzero
    rw [← P.rule_eq s] at hnonzero
    obtain ⟨d, hd, hdg⟩ := (rule_support_iff P.E.family (windowLength k)
      P.geometry _ (group_disjoint P s) g).mp hnonzero
    have hdc : P.bubbleComponent d = C :=
      (P.bubbleComponent_of_common_gram d b g hdg hhas).trans hb
    have hdb := huniq d hdc
    have howner : CanonicalIndex.group t R d = s := (Finset.mem_filter.mp hd).2
    exact hsr (howner.symm.trans (congrArg (CanonicalIndex.group t R) hdb))
  · let hv := P.incident_of_hasVertex b _ (P.gram_prefix_hasVertex b g hhas)
    exact ⟨hv, (P.bubbleComponent_gram_prefix b g hhas hv).symm.trans hb⟩

/-- The relation's nonzero support is contained in the participating rules' support. -/
theorem relation_support_included (w : Gram (windowLength k) → ℤ) (a : Fin R → ℚ)
    (hrel : RelationSupport.Relation G w a) :
    CoordinateSupportIncluded {w} (Finset.univ.image G) := by
  classical
  intro g hg
  obtain ⟨u, hu, hug⟩ := hg
  have huw : u = w := Finset.mem_singleton.mp hu
  subst u
  obtain ⟨r, hr⟩ := RelationSupport.support_inclusion G w a hrel g hug
  exact ⟨G r, Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩, hr⟩

/-- Every singleton occurrence component is hit by an actual vertex of w. -/
theorem singleton_hit (P : PresentedFamily t k R G)
    (w : Gram (windowLength k) → ℤ) (a : Fin R → ℚ)
    (hrel : RelationSupport.Relation G w a) (ha : ∀ r, a r ≠ 0)
    (C : RuleSetComponents (Finset.univ.image G))
    (hC : SingletonFiber P.bubbleComponent C) :
    ∃ v : RuleSetVertex {w},
      supportComponentMap (relation_support_included w a hrel)
        (Quotient.mk (ruleSetSetoid {w}) v) = C := by
  classical
  obtain ⟨r, g, hrg, hother, hv, hcomp⟩ := singleton_coordinate P C hC
  have hwg := RelationSupport.isolated_coordinate_nonzero G w a hrel r g (ha r) hrg hother
  have hwv : Incident {w} (gramPrefix g) :=
    ⟨gramSuffix g, Or.inl ⟨w, Finset.mem_singleton_self w, g, hwg, rfl, rfl⟩⟩
  exact ⟨⟨gramPrefix g, hwv⟩, hcomp⟩

/-- Indexed form of the savings lemma; the bound counts the supplied labels. -/
theorem savings_indexed (G : Fin R → Gram (windowLength k) → ℤ)
    (hcat : ∀ r, CatalogueRule t k (G r))
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : Fin R → ℚ) (ha : ∀ r, a r ≠ 0)
    (hrel : RelationSupport.Relation G w a) :
    componentCount (Finset.univ.image G) ≤ t * R + t := by
  classical
  let P := ofCatalogue G hcat
  have hsingle : Fintype.card {C // SingletonFiber P.bubbleComponent C} ≤ 2 * t := by
    exact (hit_component_count_le (relation_support_included w a hrel)
      (SingletonFiber P.bubbleComponent) (singleton_hit P w a hrel ha)).trans
      (catalogue_singleton_component_count_le w hw)
  have hcount := component_count_bound P.bubbleComponent P.bubbleComponent_surjective t R
    (Fintype.card_fin _) hsingle
  simpa only [componentCount, Nat.card_eq_fintype_card] using hcount

/-- Manuscript savings-from-a-relation lemma on the actual finite rule set.
The statement holds even without the manuscript's independence, generation,
and |I| ≥ 2 restrictions. All participating coefficients must be nonzero. -/
theorem savings_from_relation (I : RuleSet k)
    (hcat : ∀ u ∈ I, CatalogueRule t k u)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ)
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    componentCount I ≤ t * I.card + t := by
  classical
  let e : Fin I.card ≃ I := by
    simpa only [Fintype.card_coe] using (Fintype.equivFin I).symm
  let G : Fin I.card → Gram (windowLength k) → ℤ := fun r => (e r).val
  have himage : Finset.univ.image G = I := by
    ext u
    constructor
    · intro hu
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hu
      exact (e r).property
    · intro hu
      obtain ⟨r, hr⟩ := e.surjective ⟨u, hu⟩
      exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, congrArg Subtype.val hr⟩
  have hre : RelationSupport.Relation G w (fun r => a (G r)) := by
    intro g
    rw [hrel g]
    have he := Equiv.sum_comp e (fun u : I => a u.val * (u.val g : ℚ))
    change (∑ u ∈ I, a u * (u g : ℚ)) =
      ∑ r, a (e r).val * ((e r).val g : ℚ)
    rw [he]
    exact (Finset.sum_coe_sort I (fun u => a u * (u g : ℚ))).symm
  have h := savings_indexed G (fun r => hcat _ (e r).property) w hw
    (fun r => a (G r)) (fun r => ha _ (e r).property) hre
  simpa only [himage] using h

#print axioms singleton_coordinate
#print axioms singleton_hit
#print axioms savings_indexed
#print axioms savings_from_relation

end DeletionCode.RelationSavings
