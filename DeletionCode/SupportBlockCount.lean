import DeletionCode.BlockPartition
import DeletionCode.SupportInclusion

/-!
When a rule's coordinate support lies in an old support union, one connected
component of that rule cannot meet two old rule blocks. This is proved using
actual support edges and induced rule blocks. Choosing actual hit vertices then
bounds the number of blocks met by the rule's support-component count.
-/

namespace DeletionCode.SupportBlockCount

open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition SupportComponents

/-- An actual support edge lies entirely in the old block of its owning rule. -/
theorem edge_block_witness {k : ℕ} (G : RuleSet k)
    {u v : Vertex (windowLength k)} (he : RuleSetEdge G u v) :
    ∃ B ∈ blocks G, RuleSetEdge B u v ∧ Incident B u ∧ Incident B v := by
  obtain ⟨w, hw, g, hg, hu, hv⟩ := he
  have hwin : w ∈ blockOf G w :=
    (mem_blockOf G w w).mpr ⟨hw, Relation.EqvGen.refl _⟩
  have hblock : blockOf G w ∈ blocks G :=
    (mem_blocks G (blockOf G w)).mpr ⟨w, hw, rfl⟩
  have hedge : RuleSetEdge (blockOf G w) u v := ⟨w, hwin, g, hg, hu, hv⟩
  exact ⟨blockOf G w, hblock, hedge, ⟨v, Or.inl hedge⟩, ⟨u, Or.inr hedge⟩⟩

/-- An edge touching an old block is an edge of that block's actual support. -/
theorem edge_in_block {k : ℕ} (G B : RuleSet k) (hB : B ∈ blocks G)
    {u v : Vertex (windowLength k)} (he : RuleSetEdge G u v)
    (hu : Incident B u) : RuleSetEdge B u v := by
  classical
  obtain ⟨C, hC, heC, huC, _⟩ := edge_block_witness G he
  have hBC : B = C := by
    by_contra hne
    exact blocks_support_disjoint G B hB C hC hne u hu huC
  simpa only [hBC] using heC

theorem edge_incident_iff {k : ℕ} (G B : RuleSet k) (hB : B ∈ blocks G)
    {u v : Vertex (windowLength k)} (he : RuleSetEdge G u v) :
    Incident B u ↔ Incident B v := by
  classical
  obtain ⟨C, hC, _, huC, hvC⟩ := edge_block_witness G he
  constructor
  · intro hu
    have hBC : B = C := by
      by_contra hne
      exact blocks_support_disjoint G B hB C hC hne u hu huC
    simpa only [hBC] using hvC
  · intro hv
    have hBC : B = C := by
      by_contra hne
      exact blocks_support_disjoint G B hB C hC hne v hv hvC
    simpa only [hBC] using huC

/-- A support path in G cannot leave the incident vertices of its starting block. -/
theorem support_path_incident_iff {k : ℕ} (G B : RuleSet k) (hB : B ∈ blocks G)
    {u v : Vertex (windowLength k)} (hpath : RuleSetConnected G u v) :
    Incident B u ↔ Incident B v := by
  induction hpath with
  | rel u v he => exact edge_incident_iff G B hB he
  | refl u => exact Iff.rfl
  | symm u v h ih => exact ih.symm
  | trans u v z huv hvz ihu ihv => exact ihu.trans ihv

/-- The same actual support path can be restricted to the old block's edges. -/
theorem support_path_in_block {k : ℕ} (G B : RuleSet k) (hB : B ∈ blocks G)
    {u v : Vertex (windowLength k)} (hpath : RuleSetConnected G u v) :
    Incident B u → RuleSetConnected B u v := by
  induction hpath with
  | rel u v he =>
    intro hu
    exact Relation.EqvGen.rel _ _ (edge_in_block G B hB he hu)
  | refl u =>
    intro hu
    exact Relation.EqvGen.refl _
  | symm u v h ih =>
    intro hv
    have hu := (support_path_incident_iff G B hB h).mpr hv
    exact Relation.EqvGen.symm _ _ (ih hu)
  | trans u v z huv hvz ihu ihv =>
    intro hu
    have hv := (support_path_incident_iff G B hB huv).mp hu
    exact Relation.EqvGen.trans _ _ _ (ihu hu) (ihv hv)

/-- Distinct old blocks met by w use distinct actual support components of w.
Both the map and its injectivity are derived from the given hit vertices. -/
theorem block_count_le_components {k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (Bs : Finset (RuleSet k))
    (hBs : Bs ⊆ blocks G)
    (hsub : SupportInclusion.CoordinateSupportIncluded {w} G)
    (hhit : ∀ B ∈ Bs, ∃ v, Incident B v ∧ Incident {w} v) :
    Bs.card ≤ componentCount {w} := by
  classical
  let select : Bs → RuleSetVertex {w} := fun B =>
    ⟨Classical.choose (hhit B.val B.property),
      (Classical.choose_spec (hhit B.val B.property)).2⟩
  have hselect (B : Bs) : Incident B.val (select B).val :=
    (Classical.choose_spec (hhit B.val B.property)).1
  let encode : Bs → RuleSetComponents {w} := fun B =>
    Quotient.mk (ruleSetSetoid {w}) (select B)
  have hinj : Function.Injective encode := by
    intro B C heq
    apply Subtype.ext
    by_contra hne
    have hpathW : RuleSetConnected {w} (select B).val (select C).val :=
      Quotient.exact heq
    have hpathG : RuleSetConnected G (select B).val (select C).val :=
      SupportInclusion.connected_mono hsub hpathW
    have hCvertexB : Incident B.val (select C).val :=
      (support_path_incident_iff G B.val (hBs B.property) hpathG).mp (hselect B)
    exact blocks_support_disjoint G B.val (hBs B.property) C.val (hBs C.property)
      hne (select C).val hCvertexB (hselect C)
  have hcard := Fintype.card_le_of_injective encode hinj
  simpa [componentCount, Nat.card_eq_fintype_card] using hcard

/-- A catalogue rule with support inside G can meet at most 2t old blocks. -/
theorem catalogue_block_count_le {t k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (Bs : Finset (RuleSet k))
    (hw : CatalogueRule t k w) (hBs : Bs ⊆ blocks G)
    (hsub : SupportInclusion.CoordinateSupportIncluded {w} G)
    (hhit : ∀ B ∈ Bs, ∃ v, Incident B v ∧ Incident {w} v) :
    Bs.card ≤ 2 * t :=
  (block_count_le_components G w Bs hBs hsub hhit).trans
    (catalogue_singleton_component_count_le w hw)

/-- In particular, the actual collection of all blocks touching w has this bound. -/
theorem attached_blocks_count_le {t k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (hsub : SupportInclusion.CoordinateSupportIncluded {w} G) :
    (attachedBlocks G w).card ≤ 2 * t := by
  apply catalogue_block_count_le G w (attachedBlocks G w) hw
  · intro B hB
    exact ((mem_attachedBlocks G B w).mp hB).1
  · exact hsub
  · intro B hB
    exact ((mem_attachedBlocks G B w).mp hB).2

#print axioms edge_in_block
#print axioms support_path_incident_iff
#print axioms support_path_in_block
#print axioms block_count_le_components
#print axioms catalogue_block_count_le
#print axioms attached_blocks_count_le

end DeletionCode.SupportBlockCount
