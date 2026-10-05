import DeletionCode.Qary.RuleSetGraph

/-!
The correspondence between indexed word-path families and intrinsic signed
support components, for arbitrary window lengths and local replacement models.
The graph objects and all edge-connectivity lemmas are the checked q-ary ones.
-/
namespace DeletionCode.Burst.FamilySupport

open Qary.RootSelection Qary.SignedSupport Qary.SupportComponents Qary.RuleSetGraph
open Qary.RuleReconstruction (groupBubbles)

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

noncomputable instance graphComponentsFintype {B : Type*} (F : Family α B) (L : ℕ) :
    Fintype (GraphComponents F L) := by
  classical
  let _ : Fintype (SupportedVertex F L) := by
    unfold SupportedVertex Vertex
    infer_instance
  unfold GraphComponents
  exact Fintype.ofFinite _

noncomputable def rulesOfFamily {ν R : ℕ} (E : Family α (Fin ν)) (L : ℕ)
    (group : Fin ν → Fin R) : Finset (Gram α L → ℤ) := by
  classical
  exact Finset.univ.image (fun r => ruleSpectrum E L (groupBubbles group r))

theorem rank_bubbles_eq_group {ν R : ℕ} (E : Family α (Fin ν))
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val) (r : Fin R) :
    ruleBubbles E r.val = groupBubbles group r := by
  ext b
  simp only [ruleBubbles, groupBubbles, Finset.mem_filter, Finset.mem_univ, true_and]
  change E.rank b = r.val ↔ group b = r
  rw [hrank b]
  constructor
  · exact Fin.ext
  · exact congrArg (fun z : Fin R => z.val)

/-- Passing from a list of indexed rules to its underlying set preserves the
unsigned support union, even if an image contains repeated rules. -/
theorem rulesOfFamily_edge_iff {ν R L : ℕ} (E : Family α (Fin ν))
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E L)
    (hdis : ∀ i, VertexDisjointOn E L (ruleBubbles E i))
    (u v : Vertex α L) :
    RuleSetEdge (rulesOfFamily E L group) u v ↔
      signedSupportEdge E L u v := by
  classical
  constructor
  · rintro ⟨rule, hrule, g, hg, hu, hv⟩
    change rule ∈ Finset.univ.image
      (fun r => ruleSpectrum E L (groupBubbles group r)) at hrule
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hrule
    refine ⟨r.val, g, ?_, hu, hv⟩
    simpa only [rank_bubbles_eq_group E group hrank r] using hg
  · rintro ⟨i, g, hg, hu, hv⟩
    obtain ⟨b, hb, _⟩ :=
      (rule_support_iff E L H
        (ruleBubbles E i) (hdis i) g).mp hg
    have hbi : E.rank b = i := (Finset.mem_filter.mp hb).2
    have hri : (group b).val = i := (hrank b).symm.trans hbi
    have hsets : ruleBubbles E i = groupBubbles group (group b) := by
      rw [← hri]
      exact rank_bubbles_eq_group E group hrank (group b)
    refine ⟨ruleSpectrum E L (groupBubbles group (group b)),
      ?_, g, ?_, hu, hv⟩
    · exact Finset.mem_image.mpr ⟨group b, Finset.mem_univ _, rfl⟩
    · simpa only [hsets] using hg

theorem rulesOfFamily_edge_eq {ν R L : ℕ} (E : Family α (Fin ν))
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E L)
    (hdis : ∀ i, VertexDisjointOn E L (ruleBubbles E i)) :
    RuleSetEdge (rulesOfFamily E L group) = signedSupportEdge E L := by
  funext u v
  exact propext (rulesOfFamily_edge_iff (L := L) E group hrank H hdis u v)

theorem incident_iff_supported {ν R L : ℕ} (E : Family α (Fin ν))
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E L)
    (hdis : ∀ i, VertexDisjointOn E L (ruleBubbles E i))
    (v : Vertex α L) :
    Incident (rulesOfFamily E L group) v ↔
      ∃ b, HasVertex E L b v := by
  unfold Incident
  rw [rulesOfFamily_edge_eq (L := L) E group hrank H hdis]
  exact (supported_iff_signed_incident E L H hdis v).symm

/-- The identity on vertex labels gives the bijection of actual vertex types. -/
def incidentVertexEquiv {ν R L : ℕ} (E : Family α (Fin ν))
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E L)
    (hdis : ∀ i, VertexDisjointOn E L (ruleBubbles E i)) :
    RuleSetVertex (rulesOfFamily E L group) ≃ SupportedVertex E L where
  toFun v := ⟨v.val, (incident_iff_supported (L := L) E group hrank H hdis v.val).mp v.property⟩
  invFun v := ⟨v.val, (incident_iff_supported (L := L) E group hrank H hdis v.val).mpr v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rulesOfFamily_connected_iff {ν R L : ℕ} (E : Family α (Fin ν))
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E L)
    (hdis : ∀ i, VertexDisjointOn E L (ruleBubbles E i))
    (u v : Vertex α L) :
    RuleSetConnected (rulesOfFamily E L group) u v ↔
      GraphConnected E L u v := by
  unfold RuleSetConnected
  rw [rulesOfFamily_edge_eq (L := L) E group hrank H hdis]
  exact signed_graph_connected_iff E L H hdis u v

noncomputable def ruleSetComponentMap {ν R L : ℕ} (E : Family α (Fin ν))
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E L)
    (hdis : ∀ i, VertexDisjointOn E L (ruleBubbles E i)) :
    RuleSetComponents (rulesOfFamily E L group) → GraphComponents E L :=
  Quotient.map (incidentVertexEquiv (L := L) E group hrank H hdis) (fun a b hab =>
    (rulesOfFamily_connected_iff (L := L) E group hrank H hdis a.val b.val).mp hab)

theorem ruleSetComponentMap_injective {ν R L : ℕ} (E : Family α (Fin ν))
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E L)
    (hdis : ∀ i, VertexDisjointOn E L (ruleBubbles E i)) :
    Function.Injective (ruleSetComponentMap (L := L) E group hrank H hdis) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro a b hab
  apply Quotient.sound
  apply (rulesOfFamily_connected_iff (L := L) E group hrank H hdis a.val b.val).mpr
  exact Quotient.exact hab

theorem ruleSetComponentMap_surjective {ν R L : ℕ} (E : Family α (Fin ν))
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E L)
    (hdis : ∀ i, VertexDisjointOn E L (ruleBubbles E i)) :
    Function.Surjective (ruleSetComponentMap (L := L) E group hrank H hdis) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro v
  refine ⟨Quotient.mk (ruleSetSetoid (rulesOfFamily E L group))
    ((incidentVertexEquiv (L := L) E group hrank H hdis).symm v), ?_⟩
  apply Quotient.sound
  exact Relation.EqvGen.refl v.val

/-- Component equivalence is proved from edges and incident vertices, not assumed. -/
noncomputable def ruleSetComponentEquiv {ν R L : ℕ} (E : Family α (Fin ν))
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E L)
    (hdis : ∀ i, VertexDisjointOn E L (ruleBubbles E i)) :
    RuleSetComponents (rulesOfFamily E L group) ≃ GraphComponents E L :=
  Equiv.ofBijective (ruleSetComponentMap (L := L) E group hrank H hdis)
    ⟨ruleSetComponentMap_injective (L := L) E group hrank H hdis,
      ruleSetComponentMap_surjective (L := L) E group hrank H hdis⟩

/-- The c used by recovery is the intrinsic number of signed-support components. -/
theorem componentCount_rulesOfFamily {ν R L : ℕ} (E : Family α (Fin ν))
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E L)
    (hdis : ∀ i, VertexDisjointOn E L (ruleBubbles E i)) :
    componentCount (rulesOfFamily E L group) =
      Fintype.card (GraphComponents E L) := by
  classical
  unfold componentCount
  rw [Nat.card_congr (ruleSetComponentEquiv (L := L) E group hrank H hdis)]
  exact Nat.card_eq_fintype_card


#print axioms rulesOfFamily_edge_iff
#print axioms ruleSetComponentEquiv
#print axioms componentCount_rulesOfFamily

end DeletionCode.Burst.FamilySupport
