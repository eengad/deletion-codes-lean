import DeletionCode.ConnectedBlocks
import DeletionCode.CanonicalIndex

/-!
Choose and combine the actual bubble presentations of finitely many catalogue
rules. The resulting single family has exactly 2tR occurrence labels and its
signed per-rule spectra are the original vectors. No global geometry, support
identity, or component-count identity is assumed in constructing the family.
-/

namespace DeletionCode.CatalogueFamily

open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph SupportComponents
open CanonicalIndex ConnectedBlocks
open scoped BigOperators

structure PresentedFamily (t k R : ℕ) (G : Fin R → Gram (windowLength k) → ℤ) where
  E : EditedFamily (Fin (2 * t * R)) k
  rank : ∀ b, E.rank b = (CanonicalIndex.group t R b).val
  geometry : BubbleGeometry E.family (windowLength k)
  disjoint : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)
  rule_eq : ∀ r : Fin R,
    ruleSpectrum E.family (windowLength k) (groupBubbles (CanonicalIndex.group t R) r) = G r

private def singleFamily {t k : ℕ} (words : Fin (2 * t) → BubbleWord k) :
    EditedFamily (Fin (2 * t)) k :=
  indexedFamily words (fun _ => (0 : Fin 1))

private theorem flat_extra_eq {t k R : ℕ}
    (words : Fin R → Fin (2 * t) → BubbleWord k) (b : Fin (2 * t * R)) (side : Bool) :
    (flatFamily t R words).family.extra b side =
      (singleFamily (words (CanonicalIndex.group t R b))).family.extra
        (indexEquiv t R b).2 side := rfl

private theorem flat_vertex_eq {t k R : ℕ}
    (words : Fin R → Fin (2 * t) → BubbleWord k) (b : Fin (2 * t * R))
    (side : Bool) (i : ℕ) :
    vertex (flatFamily t R words).family (windowLength k) b side i =
      vertex (singleFamily (words (CanonicalIndex.group t R b))).family
        (windowLength k) (indexEquiv t R b).2 side i := rfl

/-- Combine chosen individual catalogue presentations using the fixed occurrence indexing. -/
noncomputable def ofCatalogue {t k R : ℕ} (G : Fin R → Gram (windowLength k) → ℤ)
    (hcat : ∀ r, CatalogueRule t k (G r)) : PresentedFamily t k R G := by
  classical
  let words : Fin R → Fin (2 * t) → BubbleWord k := fun r => Classical.choose (hcat r)
  have hvalid (r : Fin R) : ValidCatalogue (words r) (fun _ => (0 : Fin 1)) :=
    (Classical.choose_spec (hcat r)).1
  have hvalue (r : Fin R) :
      ruleSpectrum (singleFamily (words r)).family (windowLength k) Finset.univ = G r :=
    (Classical.choose_spec (hcat r)).2.2
  refine ⟨flatFamily t R words, fun _ => rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, CatalogueBridge.differentLengths (flatFamily t R words)⟩
    · intro b side
      exact (hvalid (CanonicalIndex.group t R b)).simple (indexEquiv t R b).2 side
    · intro b i j hi hj heq
      exact (hvalid (CanonicalIndex.group t R b)).endpoints (indexEquiv t R b).2 i j hi hj heq
  · intro i a ha b hb hab sa sb j l hj hl
    have hra := (Finset.mem_filter.mp ha).2
    have hrb := (Finset.mem_filter.mp hb).2
    change (CanonicalIndex.group t R a).val = i at hra
    change (CanonicalIndex.group t R b).val = i at hrb
    have hgroup : CanonicalIndex.group t R b = CanonicalIndex.group t R a :=
      Fin.ext (hrb.trans hra.symm)
    have hlocal_ne : (indexEquiv t R a).2 ≠ (indexEquiv t R b).2 := by
      intro heq
      apply hab
      apply (indexEquiv t R).injective
      exact Prod.ext hgroup.symm heq
    have hj' : j ≤ (singleFamily (words (CanonicalIndex.group t R a))).family.extra
        (indexEquiv t R a).2 sa + 1 := hj
    have hl' : l ≤ (singleFamily (words (CanonicalIndex.group t R a))).family.extra
        (indexEquiv t R b).2 sb + 1 := by
      simpa only [flat_extra_eq, hgroup] using hl
    have hdis := (hvalid (CanonicalIndex.group t R a)).within_rule_disjoint (0 : Fin 1)
      (indexEquiv t R a).2 (by simp) (indexEquiv t R b).2 (by simp)
      hlocal_ne sa sb j l hj' hl'
    simpa only [flat_vertex_eq, hgroup, singleFamily] using hdis
  · intro r
    calc
      ruleSpectrum (flatFamily t R words).family (windowLength k)
          (groupBubbles (CanonicalIndex.group t R) r) =
          fun g => ∑ j : Fin (2 * t),
            bubbleSpectrum (pairFamily t R words).family (windowLength k) (r, j) g :=
        flat_rule_spectrum t R words r
      _ = ruleSpectrum (singleFamily (words r)).family (windowLength k) Finset.univ := by
        funext g
        apply Finset.sum_congr rfl
        intro j hj
        rfl
      _ = G r := hvalue r

namespace PresentedFamily

variable {t k R : ℕ} {G : Fin R → Gram (windowLength k) → ℤ}

theorem rule_set (P : PresentedFamily t k R G) :
    rulesOfFamily P.E (CanonicalIndex.group t R) = Finset.univ.image G := by
  classical
  unfold rulesOfFamily
  apply Finset.image_congr
  intro r hr
  exact P.rule_eq r

/-- The intrinsic signed-support count equals the component count of the constructed words. -/
theorem component_count (P : PresentedFamily t k R G) :
    componentCount (Finset.univ.image G) =
      Fintype.card (GraphComponents P.E.family (windowLength k)) := by
  rw [← P.rule_set]
  exact componentCount_rulesOfFamily P.E (CanonicalIndex.group t R) P.rank P.geometry P.disjoint

noncomputable def componentEquiv (P : PresentedFamily t k R G) :
    RuleSetComponents (Finset.univ.image G) ≃ GraphComponents P.E.family (windowLength k) := by
  rw [← P.rule_set]
  exact ruleSetComponentEquiv P.E (CanonicalIndex.group t R) P.rank P.geometry P.disjoint

theorem common_start (P : PresentedFamily t k R G) (b : Fin (2 * t * R)) :
    vertex P.E.family (windowLength k) b false 0 =
      vertex P.E.family (windowLength k) b true 0 := by
  apply (vertex_eq_iff_agree P.E.family (windowLength k) b b false true 0 0).mpr
  exact PathMemory.pathInitialAgreement k (P.E.header b) (P.E.long b)

theorem incident_of_hasVertex (P : PresentedFamily t k R G)
    (b : Fin (2 * t * R)) (v : Vertex (windowLength k))
    (hv : HasVertex P.E.family (windowLength k) b v) : Incident (Finset.univ.image G) v := by
  rw [← P.rule_set]
  exact (incident_iff_supported P.E (CanonicalIndex.group t R) P.rank P.geometry P.disjoint v).mpr
    ⟨b, hv⟩

/-- Send each bubble occurrence to the intrinsic signed-support component containing it. -/
noncomputable def bubbleComponent (P : PresentedFamily t k R G)
    (b : Fin (2 * t * R)) : RuleSetComponents (Finset.univ.image G) :=
  Quotient.mk (ruleSetSetoid (Finset.univ.image G))
    ⟨representative P.E.family (windowLength k) b,
      P.incident_of_hasVertex b _ ⟨false, 0, by omega, rfl⟩⟩

/-- Every vertex on a bubble has the intrinsic component assigned to that bubble. -/
theorem bubbleComponent_vertex (P : PresentedFamily t k R G)
    (b : Fin (2 * t * R)) (v : Vertex (windowLength k))
    (hv : Incident (Finset.univ.image G) v)
    (hhas : HasVertex P.E.family (windowLength k) b v) :
    P.bubbleComponent b = Quotient.mk (ruleSetSetoid (Finset.univ.image G)) ⟨v, hv⟩ := by
  apply Quotient.sound
  change RuleSetConnected (Finset.univ.image G) (representative P.E.family (windowLength k) b) v
  rw [← P.rule_set]
  apply (rulesOfFamily_connected_iff P.E (CanonicalIndex.group t R)
    P.rank P.geometry P.disjoint _ _).mpr
  obtain ⟨side, i, hi, hv⟩ := hhas
  rw [hv]
  exact representative_connected P.E.family (windowLength k) P.common_start b side i hi

theorem bubbleComponent_surjective (P : PresentedFamily t k R G) :
    Function.Surjective P.bubbleComponent := by
  intro C
  refine Quotient.inductionOn C ?_
  intro v
  have hv : ∃ b, HasVertex P.E.family (windowLength k) b v.val := by
    apply (incident_iff_supported P.E (CanonicalIndex.group t R)
      P.rank P.geometry P.disjoint v.val).mp
    simpa only [P.rule_set] using v.property
  obtain ⟨b, hb⟩ := hv
  exact ⟨b, P.bubbleComponent_vertex b v.val v.property hb⟩

theorem bubbleComponent_of_shared_vertex (P : PresentedFamily t k R G)
    (a b : Fin (2 * t * R)) (v : Vertex (windowLength k))
    (ha : HasVertex P.E.family (windowLength k) a v)
    (hb : HasVertex P.E.family (windowLength k) b v) :
    P.bubbleComponent a = P.bubbleComponent b := by
  have hv := P.incident_of_hasVertex a v ha
  exact (P.bubbleComponent_vertex a v hv ha).trans (P.bubbleComponent_vertex b v hv hb).symm

theorem gram_prefix_hasVertex (P : PresentedFamily t k R G)
    (b : Fin (2 * t * R)) (g : Gram (windowLength k))
    (hg : HasGram P.E.family (windowLength k) b g) :
    HasVertex P.E.family (windowLength k) b (gramPrefix g) := by
  obtain ⟨side, i, hi⟩ := hg
  refine ⟨side, i.val, by have := i.isLt; omega, ?_⟩
  rw [← hi]
  exact prefix_gram P.E.family (windowLength k) b side i.val

theorem bubbleComponent_gram_prefix (P : PresentedFamily t k R G)
    (b : Fin (2 * t * R)) (g : Gram (windowLength k))
    (hg : HasGram P.E.family (windowLength k) b g)
    (hv : Incident (Finset.univ.image G) (gramPrefix g)) :
    P.bubbleComponent b =
      Quotient.mk (ruleSetSetoid (Finset.univ.image G)) ⟨gramPrefix g, hv⟩ :=
  P.bubbleComponent_vertex b (gramPrefix g) hv (P.gram_prefix_hasVertex b g hg)

theorem bubbleComponent_of_common_gram (P : PresentedFamily t k R G)
    (a b : Fin (2 * t * R)) (g : Gram (windowLength k))
    (ha : HasGram P.E.family (windowLength k) a g)
    (hb : HasGram P.E.family (windowLength k) b g) :
    P.bubbleComponent a = P.bubbleComponent b := by
  obtain ⟨sa, i, hi⟩ := ha
  obtain ⟨sb, j, hj⟩ := hb
  have hvertex := gram_eq_source_vertices P.E.family (windowLength k) a b sa sb i.val j.val
    (hi.trans hj.symm)
  apply P.bubbleComponent_of_shared_vertex a b (vertex P.E.family (windowLength k) a sa i.val)
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

end DeletionCode.CatalogueFamily
