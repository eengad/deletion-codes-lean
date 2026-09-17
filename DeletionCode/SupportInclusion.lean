import DeletionCode.ComponentBounds

/-!
Maps between actual signed-support component quotients from inclusion of
nonzero coordinates. The rule sets themselves need not be nested. In
particular, one rule obtained as a linear combination can have its support
inside the support union of a different set of rules.
-/
namespace DeletionCode.SupportInclusion

open SignedSupport SupportComponents RuleSetGraph

/-- Inclusion concerns nonzero coordinates, not membership of rules in a set. -/
def CoordinateSupportIncluded {L : ℕ} (Q S : Finset (Gram L → ℤ)) : Prop :=
  ∀ g, (∃ w ∈ Q, w g ≠ 0) → ∃ w ∈ S, w g ≠ 0

theorem edge_mono {L : ℕ} {Q S : Finset (Gram L → ℤ)}
    (hsub : CoordinateSupportIncluded Q S) {u v : Vertex L}
    (he : RuleSetEdge Q u v) : RuleSetEdge S u v := by
  obtain ⟨w, hw, g, hg, hu, hv⟩ := he
  obtain ⟨z, hz, hzg⟩ := hsub g ⟨w, hw, hg⟩
  exact ⟨z, hz, g, hzg, hu, hv⟩

theorem incident_mono {L : ℕ} {Q S : Finset (Gram L → ℤ)}
    (hsub : CoordinateSupportIncluded Q S) {v : Vertex L}
    (hv : Incident Q v) : Incident S v := by
  obtain ⟨u, hu | hu⟩ := hv
  · exact ⟨u, Or.inl (edge_mono hsub hu)⟩
  · exact ⟨u, Or.inr (edge_mono hsub hu)⟩

theorem connected_mono {L : ℕ} {Q S : Finset (Gram L → ℤ)}
    (hsub : CoordinateSupportIncluded Q S) {u v : Vertex L}
    (hc : RuleSetConnected Q u v) : RuleSetConnected S u v := by
  induction hc with
  | rel a b hab => exact Relation.EqvGen.rel _ _ (edge_mono hsub hab)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab hbc ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc

/-- The identity on vertex labels descends to a map of support components. -/
def supportComponentMap {L : ℕ} {Q S : Finset (Gram L → ℤ)}
    (hsub : CoordinateSupportIncluded Q S) :
    RuleSetComponents Q → RuleSetComponents S :=
  Quotient.map (fun v => ⟨v.val, incident_mono hsub v.property⟩)
    (fun _ _ hc => connected_mono hsub hc)

@[simp] theorem supportComponentMap_mk {L : ℕ} {Q S : Finset (Gram L → ℤ)}
    (hsub : CoordinateSupportIncluded Q S) (v : RuleSetVertex Q) :
    supportComponentMap hsub (Quotient.mk (ruleSetSetoid Q) v) =
      Quotient.mk (ruleSetSetoid S) ⟨v.val, incident_mono hsub v.property⟩ := rfl

noncomputable instance hitComponentsFintype {L : ℕ} (S : Finset (Gram L → ℤ))
    (P : RuleSetComponents S → Prop) : Fintype {C : RuleSetComponents S // P C} :=
  Fintype.ofFinite _

/-- Components hit by a smaller support union cannot outnumber that union's
components. The preimage condition is witnessed at the quotient level. -/
theorem hit_component_count_le_of_preimages {L : ℕ}
    {Q S : Finset (Gram L → ℤ)} (hsub : CoordinateSupportIncluded Q S)
    (P : RuleSetComponents S → Prop)
    (hhit : ∀ C, P C → ∃ D, supportComponentMap hsub D = C) :
    Fintype.card {C : RuleSetComponents S // P C} ≤ componentCount Q := by
  classical
  let select : {C : RuleSetComponents S // P C} → RuleSetComponents Q :=
    fun C => Classical.choose (hhit C.val C.property)
  have hselect : ∀ C, supportComponentMap hsub (select C) = C.val :=
    fun C => Classical.choose_spec (hhit C.val C.property)
  have hinj : Function.Injective select := by
    intro C D h
    apply Subtype.ext
    calc
      C.val = supportComponentMap hsub (select C) := (hselect C).symm
      _ = supportComponentMap hsub (select D) := congrArg (supportComponentMap hsub) h
      _ = D.val := hselect D
  have hcard := Fintype.card_le_of_injective select hinj
  simpa only [componentCount, Nat.card_eq_fintype_card] using hcard

/-- Vertex witnesses suffice to bound any selected collection of components
of the larger signed-support graph. No injective assignment is assumed. -/
theorem hit_component_count_le {L : ℕ} {Q S : Finset (Gram L → ℤ)}
    (hsub : CoordinateSupportIncluded Q S) (P : RuleSetComponents S → Prop)
    (hhit : ∀ C, P C → ∃ v : RuleSetVertex Q,
      supportComponentMap hsub (Quotient.mk (ruleSetSetoid Q) v) = C) :
    Fintype.card {C : RuleSetComponents S // P C} ≤ componentCount Q := by
  apply hit_component_count_le_of_preimages hsub P
  intro C hC
  obtain ⟨v, hv⟩ := hhit C hC
  exact ⟨Quotient.mk (ruleSetSetoid Q) v, hv⟩

#print axioms connected_mono
#print axioms supportComponentMap
#print axioms hit_component_count_le_of_preimages
#print axioms hit_component_count_le

end DeletionCode.SupportInclusion
