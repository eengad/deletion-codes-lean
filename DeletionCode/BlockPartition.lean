import DeletionCode.ConnectedBlocks
import DeletionCode.AttachedBlocks

/-!
Actual rule blocks are equivalence classes of rule adjacency induced on a
finite set of rules. Distinct blocks have disjoint incident support vertices.
Consequently the attached-block size accounting applies to the blocks selected
by sharing an actual support vertex with a newly adjoined rule.
-/

namespace DeletionCode.BlockPartition

open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks

def ConnectedIn {k : ℕ} (U : RuleSet k)
    (a b : Gram (windowLength k) → ℤ) : Prop :=
  Relation.EqvGen (FiniteConnectedGrowth.Induced U RuleAdjacent) a b

/-- The entire old block of one rule, with every adjacency restricted to U. -/
noncomputable def blockOf {k : ℕ} (U : RuleSet k)
    (a : Gram (windowLength k) → ℤ) : RuleSet k := by
  classical
  exact U.filter (fun b => ConnectedIn U a b)

/-- The actual finite collection of old rule blocks. -/
noncomputable def blocks {k : ℕ} (U : RuleSet k) : Finset (RuleSet k) := by
  classical
  exact U.image (blockOf U)

@[simp] theorem mem_blockOf {k : ℕ} (U : RuleSet k)
    (a b : Gram (windowLength k) → ℤ) :
    b ∈ blockOf U a ↔ b ∈ U ∧ ConnectedIn U a b := by
  classical
  simp [blockOf]

@[simp] theorem mem_blocks {k : ℕ} (U B : RuleSet k) :
    B ∈ blocks U ↔ ∃ a ∈ U, blockOf U a = B := by
  classical
  simp [blocks]

theorem blockOf_nonempty {k : ℕ} (U : RuleSet k)
    (a : Gram (windowLength k) → ℤ) (ha : a ∈ U) : (blockOf U a).Nonempty := by
  refine ⟨a, (mem_blockOf U a a).mpr ⟨ha, ?_⟩⟩
  exact Relation.EqvGen.refl _

theorem blockOf_eq_of_connected {k : ℕ} (U : RuleSet k)
    (a b : Gram (windowLength k) → ℤ) (hab : ConnectedIn U a b) :
    blockOf U a = blockOf U b := by
  classical
  ext c
  simp only [mem_blockOf]
  constructor
  · rintro ⟨hc, hac⟩
    exact ⟨hc, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hab) hac⟩
  · rintro ⟨hc, hbc⟩
    exact ⟨hc, Relation.EqvGen.trans _ _ _ hab hbc⟩

/-- Every incident vertex of a support union belongs to an actual rule in it. -/
theorem incident_iff_rule {k : ℕ} (U : RuleSet k)
    (v : SupportComponents.Vertex (windowLength k)) :
    Incident U v ↔ ∃ w ∈ U, Incident {w} v := by
  classical
  constructor
  · rintro ⟨u, ⟨w, hw, g, hg, hv, hu⟩ | ⟨w, hw, g, hg, hu, hv⟩⟩
    · exact ⟨w, hw, u, Or.inl ⟨w, Finset.mem_singleton_self w, g, hg, hv, hu⟩⟩
    · exact ⟨w, hw, u, Or.inr ⟨w, Finset.mem_singleton_self w, g, hg, hu, hv⟩⟩
  · rintro ⟨w, hw, hv⟩
    exact ComponentBounds.incident_mono (Finset.singleton_subset_iff.mpr hw) hv

/-- Sharing even one actual support vertex would merge two old rule blocks. -/
theorem blocks_support_disjoint {k : ℕ} (U : RuleSet k) :
    ∀ B ∈ blocks U, ∀ C ∈ blocks U, B ≠ C →
      ∀ v, Incident B v → ¬ Incident C v := by
  intro B hB C hC hne v hvB hvC
  obtain ⟨a, ha, rfl⟩ := (mem_blocks U B).mp hB
  obtain ⟨d, hd, rfl⟩ := (mem_blocks U C).mp hC
  obtain ⟨b, hb, hvb⟩ := (incident_iff_rule (blockOf U a) v).mp hvB
  obtain ⟨c, hc, hvc⟩ := (incident_iff_rule (blockOf U d) v).mp hvC
  obtain ⟨hbU, hab⟩ := (mem_blockOf U a b).mp hb
  obtain ⟨hcU, hdc⟩ := (mem_blockOf U d c).mp hc
  have hbc : ConnectedIn U b c :=
    Relation.EqvGen.rel _ _ ⟨hbU, hcU, v, hvb, hvc⟩
  have had : ConnectedIn U a d := Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.trans _ _ _ hab hbc) (Relation.EqvGen.symm _ _ hdc)
  exact hne (blockOf_eq_of_connected U a d had)

/-- Old blocks actually touching the newly adjoined rule. -/
noncomputable def attachedBlocks {k : ℕ} (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) : Finset (RuleSet k) := by
  classical
  exact (blocks U).filter (fun B => ∃ v, Incident B v ∧ Incident {w} v)

@[simp] theorem mem_attachedBlocks {k : ℕ} (U B : RuleSet k)
    (w : Gram (windowLength k) → ℤ) :
    B ∈ attachedBlocks U w ↔
      B ∈ blocks U ∧ ∃ v, Incident B v ∧ Incident {w} v := by
  classical
  simp [attachedBlocks]

theorem attached_blocks_count_bound {k : ℕ} (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) :
    (attachedBlocks U w).card ≤ Fintype.card (RuleSetVertex {w}) := by
  apply AttachedBlocks.attached_block_count_le_vertices
  · intro B hB
    exact ((mem_attachedBlocks U B w).mp hB).2
  · intro B hB C hC hne
    exact blocks_support_disjoint U B ((mem_attachedBlocks U B w).mp hB).1
      C ((mem_attachedBlocks U C w).mp hC).1 hne

/-- The large-block upper estimate applied to the actual old block partition.
The disjoint-support condition is proved above, rather than assumed here. -/
theorem attached_blocks_union_bound {k : ℕ} (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (t L : ℕ)
    (hsize : ∀ B ∈ blocks U, B.card ≤ L)
    (hvertices : Fintype.card (RuleSetVertex {w}) ≤ 4 * t * L) :
    (insert w ((attachedBlocks U w).biUnion id)).card ≤ 1 + 4 * t * L ^ 2 := by
  apply AttachedBlocks.attached_union_card_bound_quadratic
  · intro B hB
    exact hsize B ((mem_attachedBlocks U B w).mp hB).1
  · intro B hB
    exact ((mem_attachedBlocks U B w).mp hB).2
  · intro B hB C hC hne
    exact blocks_support_disjoint U B ((mem_attachedBlocks U B w).mp hB).1
      C ((mem_attachedBlocks U C w).mp hC).1 hne
  · exact hvertices

#print axioms blockOf_eq_of_connected
#print axioms incident_iff_rule
#print axioms blocks_support_disjoint
#print axioms attached_blocks_count_bound
#print axioms attached_blocks_union_bound

end DeletionCode.BlockPartition
