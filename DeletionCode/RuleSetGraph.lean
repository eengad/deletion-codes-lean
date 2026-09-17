import DeletionCode.RuleReconstruction
import Mathlib.SetTheory.Cardinal.Finite

/-!
The support-component count intrinsic to a finite set of signed rules.

Edges are the nonzero coordinates of the rules, with their true prefix/suffix
vertices. The graph's vertex type contains exactly incident vertices. No bubble
decomposition is part of the definition of RuleSetComponents or componentCount.
For a geometrically valid indexed family, we prove that this quotient is
equivalent to the word-path graph quotient used by the recovery construction.
-/

namespace DeletionCode.RuleSetGraph

open Windows HeaderRecovery GeneratingModel RootSelection
open SignedSupport RuleReconstruction SupportComponents

/-- The union of the nonzero signed supports; coefficients of different rules
are not summed against one another. -/
def RuleSetEdge {L : ℕ} (Q : Finset (Gram L → ℤ)) (u v : Vertex L) : Prop :=
  ∃ rule ∈ Q, ∃ g, rule g ≠ 0 ∧ u = gramPrefix g ∧ v = gramSuffix g

def Incident {L : ℕ} (Q : Finset (Gram L → ℤ)) (v : Vertex L) : Prop :=
  ∃ w, RuleSetEdge Q v w ∨ RuleSetEdge Q w v

def RuleSetVertex {L : ℕ} (Q : Finset (Gram L → ℤ)) :=
  {v : Vertex L // Incident Q v}

def RuleSetConnected {L : ℕ} (Q : Finset (Gram L → ℤ)) : Vertex L → Vertex L → Prop :=
  Relation.EqvGen (RuleSetEdge Q)

def ruleSetSetoid {L : ℕ} (Q : Finset (Gram L → ℤ)) : Setoid (RuleSetVertex Q) where
  r := fun u v => RuleSetConnected Q u.val v.val
  iseqv := ⟨fun v => Relation.EqvGen.refl v.val,
    fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩

abbrev RuleSetComponents {L : ℕ} (Q : Finset (Gram L → ℤ)) :=
  Quotient (ruleSetSetoid Q)

/-- This number depends only on the signed rule set Q. -/
noncomputable def componentCount {L : ℕ} (Q : Finset (Gram L → ℤ)) : ℕ :=
  Nat.card (RuleSetComponents Q)

theorem rank_bubbles_eq_group {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val) (r : Fin R) :
    ruleBubbles E.family r.val = groupBubbles group r := by
  ext b
  simp only [ruleBubbles, groupBubbles, Finset.mem_filter, Finset.mem_univ, true_and]
  change E.rank b = r.val ↔ group b = r
  rw [hrank b]
  constructor
  · exact Fin.ext
  · exact congrArg (fun z : Fin R => z.val)

/-- Passing from a list of indexed rules to its underlying set preserves the
unsigned support union, even if an image contains repeated rules. -/
theorem rulesOfFamily_edge_iff {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i))
    (u v : Vertex (windowLength k)) :
    RuleSetEdge (rulesOfFamily E group) u v ↔
      signedSupportEdge E.family (windowLength k) u v := by
  classical
  constructor
  · rintro ⟨rule, hrule, g, hg, hu, hv⟩
    change rule ∈ Finset.univ.image
      (fun r => ruleSpectrum E.family (windowLength k) (groupBubbles group r)) at hrule
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hrule
    refine ⟨r.val, g, ?_, hu, hv⟩
    simpa only [rank_bubbles_eq_group E group hrank r] using hg
  · rintro ⟨i, g, hg, hu, hv⟩
    obtain ⟨b, hb, _⟩ :=
      (rule_support_iff E.family (windowLength k) H
        (ruleBubbles E.family i) (hdis i) g).mp hg
    have hbi : E.rank b = i := (Finset.mem_filter.mp hb).2
    have hri : (group b).val = i := (hrank b).symm.trans hbi
    have hsets : ruleBubbles E.family i = groupBubbles group (group b) := by
      rw [← hri]
      exact rank_bubbles_eq_group E group hrank (group b)
    refine ⟨ruleSpectrum E.family (windowLength k) (groupBubbles group (group b)),
      ?_, g, ?_, hu, hv⟩
    · exact Finset.mem_image.mpr ⟨group b, Finset.mem_univ _, rfl⟩
    · simpa only [hsets] using hg

theorem rulesOfFamily_edge_eq {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) :
    RuleSetEdge (rulesOfFamily E group) = signedSupportEdge E.family (windowLength k) := by
  funext u v
  exact propext (rulesOfFamily_edge_iff E group hrank H hdis u v)

theorem incident_iff_supported {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i))
    (v : Vertex (windowLength k)) :
    Incident (rulesOfFamily E group) v ↔
      ∃ b, HasVertex E.family (windowLength k) b v := by
  unfold Incident
  rw [rulesOfFamily_edge_eq E group hrank H hdis]
  exact (supported_iff_signed_incident E.family (windowLength k) H hdis v).symm

/-- The identity on vertex labels gives the bijection of actual vertex types. -/
def incidentVertexEquiv {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) :
    RuleSetVertex (rulesOfFamily E group) ≃ SupportedVertex E.family (windowLength k) where
  toFun v := ⟨v.val, (incident_iff_supported E group hrank H hdis v.val).mp v.property⟩
  invFun v := ⟨v.val, (incident_iff_supported E group hrank H hdis v.val).mpr v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rulesOfFamily_connected_iff {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i))
    (u v : Vertex (windowLength k)) :
    RuleSetConnected (rulesOfFamily E group) u v ↔
      GraphConnected E.family (windowLength k) u v := by
  unfold RuleSetConnected
  rw [rulesOfFamily_edge_eq E group hrank H hdis]
  exact signed_graph_connected_iff E.family (windowLength k) H hdis u v

noncomputable def ruleSetComponentMap {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) :
    RuleSetComponents (rulesOfFamily E group) → GraphComponents E.family (windowLength k) :=
  Quotient.map (incidentVertexEquiv E group hrank H hdis) (fun a b hab =>
    (rulesOfFamily_connected_iff E group hrank H hdis a.val b.val).mp hab)

theorem ruleSetComponentMap_injective {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) :
    Function.Injective (ruleSetComponentMap E group hrank H hdis) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro a b hab
  apply Quotient.sound
  apply (rulesOfFamily_connected_iff E group hrank H hdis a.val b.val).mpr
  exact Quotient.exact hab

theorem ruleSetComponentMap_surjective {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) :
    Function.Surjective (ruleSetComponentMap E group hrank H hdis) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro v
  refine ⟨Quotient.mk (ruleSetSetoid (rulesOfFamily E group))
    ((incidentVertexEquiv E group hrank H hdis).symm v), ?_⟩
  apply Quotient.sound
  exact Relation.EqvGen.refl v.val

/-- Component equivalence is proved from edges and incident vertices, not assumed. -/
noncomputable def ruleSetComponentEquiv {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) :
    RuleSetComponents (rulesOfFamily E group) ≃ GraphComponents E.family (windowLength k) :=
  Equiv.ofBijective (ruleSetComponentMap E group hrank H hdis)
    ⟨ruleSetComponentMap_injective E group hrank H hdis,
      ruleSetComponentMap_surjective E group hrank H hdis⟩

/-- The c used by recovery is the intrinsic number of signed-support components. -/
theorem componentCount_rulesOfFamily {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) :
    componentCount (rulesOfFamily E group) =
      Fintype.card (GraphComponents E.family (windowLength k)) := by
  classical
  unfold componentCount
  rw [Nat.card_congr (ruleSetComponentEquiv E group hrank H hdis)]
  exact Nat.card_eq_fintype_card

#print axioms rulesOfFamily_edge_iff
#print axioms incident_iff_supported
#print axioms ruleSetComponentEquiv
#print axioms componentCount_rulesOfFamily

end DeletionCode.RuleSetGraph
