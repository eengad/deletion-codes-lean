import DeletionCode.Burst.CatalogueFamily
import DeletionCode.Burst.CatalogueVertexBound
import DeletionCode.Burst.CatalogueBounds
import DeletionCode.ComponentFibers
import DeletionCode.Qary.RelationSupport
import DeletionCode.Qary.SupportInclusion

/-!
Savings from an actual rational relation among catalogue rules. Every support
component containing a single bubble occurrence must survive in the resulting
rule. That rule has at most 2t components, so counting the remaining occurrences
twice yields c(I) ≤ t|I| + t. No independence or generation assumption is needed.
-/

namespace DeletionCode.Burst.RelationSavings

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

open Qary.SignedSupport Qary.RuleReconstruction Qary.RuleSetGraph Qary.SupportComponents
open Qary.SignedRuleCount Qary.SupportInclusion DeletionCode.ComponentFibers
open Catalogue CatalogueFamily FamilySupport

open scoped BigOperators

variable {t k b R : ℕ} {G : Fin R → Gram α (windowLength k b) → ℤ}

private theorem group_disjoint (P : PresentedFamily t k b R G) (r : Fin R) :
    VertexDisjointOn P.E (windowLength k b)
      (groupBubbles (Qary.CanonicalIndex.group t R) r) := by
  rw [← FamilySupport.rank_bubbles_eq_group P.E (Qary.CanonicalIndex.group t R) P.rank r]
  exact P.disjoint r.val

/-- A singleton occurrence component supplies a coordinate unique to its rule. -/
theorem singleton_coordinate (P : PresentedFamily t k b R G)
    (C : RuleSetComponents (Finset.univ.image G))
    (hC : SingletonFiber P.bubbleComponent C) :
    ∃ r g, G r g ≠ 0 ∧ (∀ s, s ≠ r → G s g = 0) ∧
      ∃ hg : Incident (Finset.univ.image G) (gramPrefix g),
        Quotient.mk (ruleSetSetoid (Finset.univ.image G)) ⟨gramPrefix g, hg⟩ = C := by
  classical
  obtain ⟨j, hb, huniq⟩ := hC
  let r := Qary.CanonicalIndex.group t R j
  let g := gram (P.E.path j false) (windowLength k b) 0
  have hgram : g ∈ windowSet (P.E.path j false) (windowLength k b)
      (P.E.extra j false) := ⟨⟨0, by omega⟩, rfl⟩
  have hhas : HasGram P.E (windowLength k b) j g := ⟨false, hgram⟩
  have hmem : j ∈ groupBubbles (Qary.CanonicalIndex.group t R) r := by
    simp [groupBubbles, r]
  have hneg : G r g = -1 := by
    rw [← P.rule_eq r]
    exact rule_negative_of_window P.E (windowLength k b) P.geometry _
      (group_disjoint P r) j hmem g hgram
  refine ⟨r, g, by omega, ?_, ?_⟩
  · intro s hsr
    by_contra hnonzero
    rw [← P.rule_eq s] at hnonzero
    obtain ⟨d, hd, hdg⟩ := (rule_support_iff P.E (windowLength k b)
      P.geometry _ (group_disjoint P s) g).mp hnonzero
    have hdc : P.bubbleComponent d = C :=
      (P.bubbleComponent_of_common_gram d j g hdg hhas).trans hb
    have hdb := huniq d hdc
    have howner : Qary.CanonicalIndex.group t R d = s := (Finset.mem_filter.mp hd).2
    exact hsr (howner.symm.trans (congrArg (Qary.CanonicalIndex.group t R) hdb))
  · let hv := P.incident_of_hasVertex j _ (P.gram_prefix_hasVertex j g hhas)
    exact ⟨hv, (P.bubbleComponent_gram_prefix j g hhas hv).symm.trans hb⟩

/-- The relation's nonzero support is contained in the participating rules' support. -/
theorem relation_support_included (w : Gram α (windowLength k b) → ℤ) (a : Fin R → ℚ)
    (hrel : Qary.RelationSupport.Relation G w a) :
    CoordinateSupportIncluded {w} (Finset.univ.image G) := by
  classical
  intro g hg
  obtain ⟨u, hu, hug⟩ := hg
  have huw : u = w := Finset.mem_singleton.mp hu
  subst u
  obtain ⟨r, hr⟩ := Qary.RelationSupport.support_inclusion G w a hrel g hug
  exact ⟨G r, Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩, hr⟩

/-- Every singleton occurrence component is hit by an actual vertex of w. -/
theorem singleton_hit (P : PresentedFamily t k b R G)
    (w : Gram α (windowLength k b) → ℤ) (a : Fin R → ℚ)
    (hrel : Qary.RelationSupport.Relation G w a) (ha : ∀ r, a r ≠ 0)
    (C : RuleSetComponents (Finset.univ.image G))
    (hC : SingletonFiber P.bubbleComponent C) :
    ∃ v : RuleSetVertex {w},
      supportComponentMap (relation_support_included w a hrel)
        (Quotient.mk (ruleSetSetoid {w}) v) = C := by
  classical
  obtain ⟨r, g, hrg, hother, hv, hcomp⟩ := singleton_coordinate P C hC
  have hwg := Qary.RelationSupport.isolated_coordinate_nonzero G w a hrel r g (ha r) hrg hother
  have hwv : Incident {w} (gramPrefix g) :=
    ⟨gramSuffix g, Or.inl ⟨w, Finset.mem_singleton_self w, g, hwg, rfl, rfl⟩⟩
  exact ⟨⟨gramPrefix g, hwv⟩, hcomp⟩

/-- Indexed form of the savings lemma; the bound counts the supplied labels. -/
theorem savings_indexed (G : Fin R → Gram α (windowLength k b) → ℤ)
    (hcat : ∀ r, Rule t k b (G r))
    (w : Gram α (windowLength k b) → ℤ) (hw : Rule t k b w)
    (a : Fin R → ℚ) (ha : ∀ r, a r ≠ 0)
    (hrel : Qary.RelationSupport.Relation G w a) :
    componentCount (Finset.univ.image G) ≤ t * R + t := by
  classical
  let P := ofCatalogue G hcat
  have hsingle : Fintype.card {C // SingletonFiber P.bubbleComponent C} ≤ 2 * t := by
    exact (hit_component_count_le (relation_support_included w a hrel)
      (SingletonFiber P.bubbleComponent) (singleton_hit P w a hrel ha)).trans
      (Catalogue.singleton_component_count_le w hw)
  have hcount := component_count_bound P.bubbleComponent P.bubbleComponent_surjective t R
    (Fintype.card_fin _) hsingle
  simpa only [componentCount, Nat.card_eq_fintype_card] using hcount

/-- Manuscript savings-from-a-relation lemma on the actual finite rule set.
No independence or generation assumption or lower bound on |I| is required.
All participating coefficients must be nonzero. -/
theorem savings_from_relation (I : RuleSet α (k + b))
    (hcat : ∀ u ∈ I, Rule t k b u)
    (w : Gram α (windowLength k b) → ℤ) (hw : Rule t k b w)
    (a : (Gram α (windowLength k b) → ℤ) → ℚ)
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    componentCount I ≤ t * I.card + t := by
  classical
  let e : Fin I.card ≃ I := by
    simpa only [Fintype.card_coe] using (Fintype.equivFin I).symm
  let G : Fin I.card → Gram α (windowLength k b) → ℤ := fun r => (e r).val
  have himage : Finset.univ.image G = I := by
    ext u
    constructor
    · intro hu
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hu
      exact (e r).property
    · intro hu
      obtain ⟨r, hr⟩ := e.surjective ⟨u, hu⟩
      exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, congrArg Subtype.val hr⟩
  have hre : Qary.RelationSupport.Relation G w (fun r => a (G r)) := by
    intro g
    rw [hrel g]
    have he := Equiv.sum_comp e (fun u : I => a u.val * (u.val g : ℚ))
    change (∑ u ∈ I, a u * (u g : ℚ)) =
      ∑ r, a (e r).val * ((e r).val g : ℚ)
    rw [he]
    exact (Finset.sum_coe_sort I (fun u => a u * (u g : ℚ))).symm
  have h := savings_indexed G (fun r => hcat _ (e r).property) w hw
    (fun r => a (G r)) (fun r => ha _ (e r).property) hre
  change componentCount (L := windowLength k b) I ≤ t * I.card + t
  simpa only [himage] using h

/-- All catalogue geometry needed by the shared witness extraction is proved. -/
theorem catalogue_facts (t k b : ℕ) (ht : 1 ≤ t) :
    CatalogueBounds.Facts t (k + b) (2 * t * (2 * windowLength k b + 2 * b + 1))
      {u | Rule (α := α) t k b u} where
  signed := Catalogue.signed_unit
  nonzero := Catalogue.nonzero ht
  components := Catalogue.singleton_component_count_le
  vertices := CatalogueVertexBound.catalogue_vertex_card_le
  capacity := by nlinarith [Nat.zero_le (2 * windowLength k b + 2 * b)]
  savings := savings_from_relation

#print axioms singleton_coordinate
#print axioms singleton_hit
#print axioms savings_indexed
#print axioms savings_from_relation
#print axioms catalogue_facts

end DeletionCode.Burst.RelationSavings
