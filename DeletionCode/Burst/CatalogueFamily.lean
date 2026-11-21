import DeletionCode.Burst.Catalogue
import DeletionCode.Qary.CanonicalIndex

/-!
Choose and combine the actual bubble presentations of finitely many catalogue
rules. The resulting single family has exactly 2tR occurrence labels and its
signed per-rule spectra are the original vectors. No global geometry, support
identity, or component-count identity is assumed in constructing the family.
-/

namespace DeletionCode.Burst.CatalogueFamily

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

open Qary.Windows Qary.RootSelection Qary.SignedSupport Qary.RuleSetGraph Qary.SupportComponents Qary.RuleReconstruction
open Qary.CanonicalIndex (indexEquiv group_sum)
open Catalogue FamilySupport
open scoped BigOperators

structure PresentedFamily (t k w R : ℕ) (G : Fin R → Gram α (windowLength k w) → ℤ) where
  E : Family α (Fin (2 * t * R))
  rank : ∀ b, E.rank b = (Qary.CanonicalIndex.group t R b).val
  geometry : BubbleGeometry E (windowLength k w)
  disjoint : ∀ i, VertexDisjointOn E (windowLength k w) (ruleBubbles E i)
  start : ∀ b, vertex E (windowLength k w) b false 0 = vertex E (windowLength k w) b true 0
  rule_eq : ∀ r : Fin R,
    ruleSpectrum E (windowLength k w) (groupBubbles (Qary.CanonicalIndex.group t R) r) = G r

def flatFamily {k w : ℕ} (t R : ℕ) (words : Fin R → Fin (2 * t) → BubbleWord α k w) :
    Family α (Fin (2 * t * R)) :=
  indexedFamily (Qary.CanonicalIndex.flatten t R words) (Qary.CanonicalIndex.group t R)

private def singleFamily {t k w : ℕ} (words : Fin (2 * t) → BubbleWord α k w) :
    Family α (Fin (2 * t)) :=
  indexedFamily words (fun _ => (0 : Fin 1))

private theorem flat_extra_eq {t k w R : ℕ}
    (words : Fin R → Fin (2 * t) → BubbleWord α k w) (b : Fin (2 * t * R)) (side : Bool) :
    (flatFamily t R words).extra b side =
      (singleFamily (words (Qary.CanonicalIndex.group t R b))).extra
        (indexEquiv t R b).2 side := rfl

private theorem flat_vertex_eq {t k w R : ℕ}
    (words : Fin R → Fin (2 * t) → BubbleWord α k w) (b : Fin (2 * t * R))
    (side : Bool) (i : ℕ) :
    vertex (flatFamily t R words) (windowLength k w) b side i =
      vertex (singleFamily (words (Qary.CanonicalIndex.group t R b)))
        (windowLength k w) (indexEquiv t R b).2 side i := rfl

/-- Combine chosen individual catalogue presentations using the fixed occurrence indexing. -/
noncomputable def ofCatalogue {t k w R : ℕ} (G : Fin R → Gram α (windowLength k w) → ℤ)
    (hcat : ∀ r, Rule t k w (G r)) : PresentedFamily t k w R G := by
  classical
  let words : Fin R → Fin (2 * t) → BubbleWord α k w := fun r => Classical.choose (hcat r)
  have hvalid (r : Fin R) : ValidCatalogue (words r) (fun _ => (0 : Fin 1)) :=
    (Classical.choose_spec (hcat r)).1
  have hvalue (r : Fin R) :
      ruleSpectrum (singleFamily (words r)) (windowLength k w) Finset.univ = G r :=
    (Classical.choose_spec (hcat r)).2.2
  refine ⟨flatFamily t R words, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, Catalogue.notBothSingle (Qary.CanonicalIndex.flatten t R words) (fun b => (Qary.CanonicalIndex.group t R b).val)⟩
    · intro b side
      exact (hvalid (Qary.CanonicalIndex.group t R b)).geometry.simple (indexEquiv t R b).2 side
    · intro b i j hi hj heq
      exact (hvalid (Qary.CanonicalIndex.group t R b)).geometry.endpoints (indexEquiv t R b).2 i j hi hj heq
  · intro i a ha b hb hab sa sb j l hj hl
    have hra := (Finset.mem_filter.mp ha).2
    have hrb := (Finset.mem_filter.mp hb).2
    change (Qary.CanonicalIndex.group t R a).val = i at hra
    change (Qary.CanonicalIndex.group t R b).val = i at hrb
    have hgroup : Qary.CanonicalIndex.group t R b = Qary.CanonicalIndex.group t R a :=
      Fin.ext (hrb.trans hra.symm)
    have hlocal_ne : (indexEquiv t R a).2 ≠ (indexEquiv t R b).2 := by
      intro heq
      apply hab
      apply (indexEquiv t R).injective
      exact Prod.ext hgroup.symm heq
    have hj' : j ≤ (singleFamily (words (Qary.CanonicalIndex.group t R a))).extra
        (indexEquiv t R a).2 sa + 1 := hj
    have hl' : l ≤ (singleFamily (words (Qary.CanonicalIndex.group t R a))).extra
        (indexEquiv t R b).2 sb + 1 := by
      simpa only [flat_extra_eq, hgroup] using hl
    have hdis := (hvalid (Qary.CanonicalIndex.group t R a)).within_rule_disjoint (0 : Fin 1)
      (indexEquiv t R a).2 (by simp [groupBubbles]) (indexEquiv t R b).2 (by simp [groupBubbles])
      hlocal_ne sa sb j l hj' hl'
    simpa only [flat_vertex_eq, hgroup, singleFamily] using hdis
  · intro b
    exact (hvalid (Qary.CanonicalIndex.group t R b)).common_start (indexEquiv t R b).2
  · intro r
    rw [← hvalue r]
    funext g
    unfold ruleSpectrum groupBubbles
    rw [Qary.CanonicalIndex.group_sum]
    apply Finset.sum_congr rfl
    intro j hj
    change bubbleSpectrum (flatFamily t R words) (windowLength k w)
      ((indexEquiv t R).symm (r, j)) g =
      bubbleSpectrum (singleFamily (words r)) (windowLength k w) j g
    simp only [bubbleSpectrum, flatFamily, indexedFamily, Catalogue.family,
      Qary.CanonicalIndex.flatten, Equiv.apply_symm_apply, singleFamily]


namespace PresentedFamily

variable {t k w R : ℕ} {G : Fin R → Gram α (windowLength k w) → ℤ}

theorem rule_set (P : PresentedFamily t k w R G) :
    rulesOfFamily P.E (windowLength k w) (Qary.CanonicalIndex.group t R) = Finset.univ.image G := by
  classical
  unfold FamilySupport.rulesOfFamily
  apply Finset.image_congr
  intro r hr
  exact P.rule_eq r

/-- The intrinsic signed-support count equals the component count of the constructed words. -/
theorem component_count (P : PresentedFamily t k w R G) :
    componentCount (Finset.univ.image G) =
      Fintype.card (GraphComponents P.E (windowLength k w)) := by
  rw [← P.rule_set]
  exact FamilySupport.componentCount_rulesOfFamily P.E (Qary.CanonicalIndex.group t R) P.rank P.geometry P.disjoint

noncomputable def componentEquiv (P : PresentedFamily t k w R G) :
    RuleSetComponents (Finset.univ.image G) ≃ GraphComponents P.E (windowLength k w) := by
  rw [← P.rule_set]
  exact ruleSetComponentEquiv P.E (Qary.CanonicalIndex.group t R) P.rank P.geometry P.disjoint

theorem common_start (P : PresentedFamily t k w R G) (b : Fin (2 * t * R)) :
    vertex P.E (windowLength k w) b false 0 =
      vertex P.E (windowLength k w) b true 0 := P.start b

theorem incident_of_hasVertex (P : PresentedFamily t k w R G)
    (b : Fin (2 * t * R)) (v : Vertex α (windowLength k w))
    (hv : HasVertex P.E (windowLength k w) b v) : Incident (Finset.univ.image G) v := by
  rw [← P.rule_set]
  exact (incident_iff_supported P.E (Qary.CanonicalIndex.group t R) P.rank P.geometry P.disjoint v).mpr
    ⟨b, hv⟩

/-- Send each bubble occurrence to the intrinsic signed-support component containing it. -/
noncomputable def bubbleComponent (P : PresentedFamily t k w R G)
    (b : Fin (2 * t * R)) : RuleSetComponents (Finset.univ.image G) :=
  Quotient.mk (ruleSetSetoid (Finset.univ.image G))
    ⟨representative P.E (windowLength k w) b,
      P.incident_of_hasVertex b _ ⟨false, 0, by omega, rfl⟩⟩

/-- Every vertex on a bubble has the intrinsic component assigned to that bubble. -/
theorem bubbleComponent_vertex (P : PresentedFamily t k w R G)
    (b : Fin (2 * t * R)) (v : Vertex α (windowLength k w))
    (hv : Incident (Finset.univ.image G) v)
    (hhas : HasVertex P.E (windowLength k w) b v) :
    P.bubbleComponent b = Quotient.mk (ruleSetSetoid (Finset.univ.image G)) ⟨v, hv⟩ := by
  apply Quotient.sound
  change RuleSetConnected (Finset.univ.image G) (representative P.E (windowLength k w) b) v
  rw [← P.rule_set]
  apply (rulesOfFamily_connected_iff P.E (Qary.CanonicalIndex.group t R)
    P.rank P.geometry P.disjoint _ _).mpr
  obtain ⟨side, i, hi, hv⟩ := hhas
  rw [hv]
  exact representative_connected P.E (windowLength k w) P.common_start b side i hi

theorem bubbleComponent_surjective (P : PresentedFamily t k w R G) :
    Function.Surjective P.bubbleComponent := by
  intro C
  refine Quotient.inductionOn C ?_
  intro v
  have hv : ∃ b, HasVertex P.E (windowLength k w) b v.val := by
    apply (incident_iff_supported P.E (Qary.CanonicalIndex.group t R)
      P.rank P.geometry P.disjoint v.val).mp
    simpa only [P.rule_set] using v.property
  obtain ⟨b, hb⟩ := hv
  exact ⟨b, P.bubbleComponent_vertex b v.val v.property hb⟩

theorem bubbleComponent_of_shared_vertex (P : PresentedFamily t k w R G)
    (a b : Fin (2 * t * R)) (v : Vertex α (windowLength k w))
    (ha : HasVertex P.E (windowLength k w) a v)
    (hb : HasVertex P.E (windowLength k w) b v) :
    P.bubbleComponent a = P.bubbleComponent b := by
  have hv := P.incident_of_hasVertex a v ha
  exact (P.bubbleComponent_vertex a v hv ha).trans (P.bubbleComponent_vertex b v hv hb).symm

theorem gram_prefix_hasVertex (P : PresentedFamily t k w R G)
    (b : Fin (2 * t * R)) (g : Gram α (windowLength k w))
    (hg : HasGram P.E (windowLength k w) b g) :
    HasVertex P.E (windowLength k w) b (gramPrefix g) := by
  obtain ⟨side, i, hi⟩ := hg
  refine ⟨side, i.val, by have := i.isLt; omega, ?_⟩
  rw [← hi]
  exact prefix_gram P.E (windowLength k w) b side i.val

theorem bubbleComponent_gram_prefix (P : PresentedFamily t k w R G)
    (b : Fin (2 * t * R)) (g : Gram α (windowLength k w))
    (hg : HasGram P.E (windowLength k w) b g)
    (hv : Incident (Finset.univ.image G) (gramPrefix g)) :
    P.bubbleComponent b =
      Quotient.mk (ruleSetSetoid (Finset.univ.image G)) ⟨gramPrefix g, hv⟩ :=
  P.bubbleComponent_vertex b (gramPrefix g) hv (P.gram_prefix_hasVertex b g hg)

theorem bubbleComponent_of_common_gram (P : PresentedFamily t k w R G)
    (a b : Fin (2 * t * R)) (g : Gram α (windowLength k w))
    (ha : HasGram P.E (windowLength k w) a g)
    (hb : HasGram P.E (windowLength k w) b g) :
    P.bubbleComponent a = P.bubbleComponent b := by
  obtain ⟨sa, i, hi⟩ := ha
  obtain ⟨sb, j, hj⟩ := hb
  have hvertex := gram_eq_source_vertices P.E (windowLength k w) a b sa sb i.val j.val
    (hi.trans hj.symm)
  apply P.bubbleComponent_of_shared_vertex a b (vertex P.E (windowLength k w) a sa i.val)
  · exact ⟨sa, i.val, by have := i.isLt; omega, rfl⟩
  · exact ⟨sb, j.val, by have := j.isLt; omega, hvertex⟩

end PresentedFamily

#print axioms ofCatalogue
#print axioms PresentedFamily.rule_set
#print axioms PresentedFamily.component_count
#print axioms PresentedFamily.componentEquiv
#print axioms PresentedFamily.bubbleComponent_vertex
#print axioms PresentedFamily.bubbleComponent_surjective
#print axioms PresentedFamily.bubbleComponent_of_common_gram

end DeletionCode.Burst.CatalogueFamily
