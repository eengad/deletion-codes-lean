import DeletionCode.RuleSetGraph
import Mathlib.Data.Fintype.Sum

/-!
Component inequalities for the actual signed-support graph. The proof maps the
components of two edge unions onto the components of their union. A common
incident vertex gives two distinct preimages of the same union component.
-/
namespace DeletionCode.ComponentBounds

open SignedSupport SupportComponents RuleSetGraph

noncomputable instance incidentVerticesFintype {L : ℕ} (Q : Finset (Gram L → ℤ)) :
    Fintype (RuleSetVertex Q) := by
  classical
  unfold RuleSetVertex
  infer_instance

noncomputable instance componentsFintype {L : ℕ} (Q : Finset (Gram L → ℤ)) :
    Fintype (RuleSetComponents Q) := by
  classical
  exact Fintype.ofFinite (Quotient (ruleSetSetoid Q))

theorem edge_mono {L : ℕ} {Q S : Finset (Gram L → ℤ)} (h : Q ⊆ S)
    {u v : Vertex L} (he : RuleSetEdge Q u v) : RuleSetEdge S u v := by
  obtain ⟨w, hw, g, hg, hu, hv⟩ := he
  exact ⟨w, h hw, g, hg, hu, hv⟩

theorem incident_mono {L : ℕ} {Q S : Finset (Gram L → ℤ)} (h : Q ⊆ S)
    {v : Vertex L} (hv : Incident Q v) : Incident S v := by
  obtain ⟨u, hu | hu⟩ := hv
  · exact ⟨u, Or.inl (edge_mono h hu)⟩
  · exact ⟨u, Or.inr (edge_mono h hu)⟩

theorem connected_mono {L : ℕ} {Q S : Finset (Gram L → ℤ)} (h : Q ⊆ S)
    {u v : Vertex L} (hc : RuleSetConnected Q u v) : RuleSetConnected S u v := by
  induction hc with
  | rel a b hab => exact Relation.EqvGen.rel _ _ (edge_mono h hab)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab hbc ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc

def componentMap {L : ℕ} {Q S : Finset (Gram L → ℤ)} (h : Q ⊆ S) :
    RuleSetComponents Q → RuleSetComponents S :=
  Quotient.map (fun v => ⟨v.val, incident_mono h v.property⟩)
    (fun _ _ hc => connected_mono h hc)

theorem incident_union_iff {L : ℕ} (Q S : Finset (Gram L → ℤ)) (v : Vertex L) :
    Incident (Q ∪ S) v ↔ Incident Q v ∨ Incident S v := by
  classical
  constructor
  · rintro ⟨u, ⟨w, hw, g, hg, hv, hu⟩ | ⟨w, hw, g, hg, hu, hv⟩⟩
    · rcases Finset.mem_union.mp hw with hw | hw
      · exact Or.inl ⟨u, Or.inl ⟨w, hw, g, hg, hv, hu⟩⟩
      · exact Or.inr ⟨u, Or.inl ⟨w, hw, g, hg, hv, hu⟩⟩
    · rcases Finset.mem_union.mp hw with hw | hw
      · exact Or.inl ⟨u, Or.inr ⟨w, hw, g, hg, hu, hv⟩⟩
      · exact Or.inr ⟨u, Or.inr ⟨w, hw, g, hg, hu, hv⟩⟩
  · rintro (h | h)
    · exact incident_mono Finset.subset_union_left h
    · exact incident_mono Finset.subset_union_right h

def unionComponentMap {L : ℕ} (Q S : Finset (Gram L → ℤ)) :
    RuleSetComponents Q ⊕ RuleSetComponents S → RuleSetComponents (Q ∪ S) :=
  Sum.elim (componentMap Finset.subset_union_left) (componentMap Finset.subset_union_right)

theorem unionComponentMap_surjective {L : ℕ} (Q S : Finset (Gram L → ℤ)) :
    Function.Surjective (unionComponentMap Q S) := by
  intro C
  refine Quotient.inductionOn C ?_
  intro v
  rcases (incident_union_iff Q S v.val).mp v.property with hQ | hS
  · refine ⟨Sum.inl (Quotient.mk _ ⟨v.val, hQ⟩), ?_⟩
    apply Quotient.sound
    exact Relation.EqvGen.refl _
  · refine ⟨Sum.inr (Quotient.mk _ ⟨v.val, hS⟩), ?_⟩
    apply Quotient.sound
    exact Relation.EqvGen.refl _

private theorem card_add_one_le_of_collision {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Surjective f) (a b : A) (hne : a ≠ b)
    (heq : f a = f b) : Fintype.card B + 1 ≤ Fintype.card A := by
  classical
  let g : B → A := fun y => Classical.choose (hf y)
  have hfg : ∀ y, f (g y) = y := fun y => Classical.choose_spec (hf y)
  have hginj : Function.Injective g := by
    intro y z h
    calc y = f (g y) := (hfg y).symm
         _ = f (g z) := congrArg f h
         _ = z := hfg z
  have hgnsurj : ¬ Function.Surjective g := by
    intro hg
    obtain ⟨y, hy⟩ := hg a
    obtain ⟨z, hz⟩ := hg b
    have hyz : y = z := by
      calc y = f (g y) := (hfg y).symm
           _ = f a := congrArg f hy
           _ = f b := heq
           _ = f (g z) := (congrArg f hz).symm
           _ = z := hfg z
    exact hne (hy.symm.trans ((congrArg g hyz).trans hz))
  exact Fintype.card_lt_of_injective_not_surjective g hginj hgnsurj

/-- An intersecting pair of support unions saves at least one component. -/
theorem componentCount_union_add_one_le {L : ℕ} (Q S : Finset (Gram L → ℤ))
    (hmeet : ∃ v, Incident Q v ∧ Incident S v) :
    componentCount (Q ∪ S) + 1 ≤ componentCount Q + componentCount S := by
  classical
  obtain ⟨v, hvQ, hvS⟩ := hmeet
  let a : RuleSetComponents Q ⊕ RuleSetComponents S :=
    Sum.inl (Quotient.mk _ ⟨v, hvQ⟩)
  let b : RuleSetComponents Q ⊕ RuleSetComponents S :=
    Sum.inr (Quotient.mk _ ⟨v, hvS⟩)
  have hab : a ≠ b := by simp [a, b]
  have himage : unionComponentMap Q S a = unionComponentMap Q S b := by
    apply Quotient.sound
    exact Relation.EqvGen.refl _
  have h := card_add_one_le_of_collision (unionComponentMap Q S)
    (unionComponentMap_surjective Q S) a b hab himage
  simpa only [componentCount, Nat.card_eq_fintype_card, Fintype.card_sum] using h

#print axioms componentCount_union_add_one_le

end DeletionCode.ComponentBounds
