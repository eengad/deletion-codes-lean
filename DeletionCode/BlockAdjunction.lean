import DeletionCode.BlockPartition
import DeletionCode.CatalogueVertexBound

/-!
Adjoining a rule merges precisely the old blocks that touch it. The identity
below is proved from actual induced adjacency paths. It supplies the large-block
size and component bounds for the new block without assuming its decomposition.
-/

namespace DeletionCode.BlockAdjunction

open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition

theorem connectedIn_mono {k : ℕ} {U V : RuleSet k} (hUV : U ⊆ V)
    {a b : Gram (windowLength k) → ℤ} (h : ConnectedIn U a b) : ConnectedIn V a b := by
  induction h with
  | rel a b hab =>
    exact Relation.EqvGen.rel _ _ ⟨hUV hab.1, hUV hab.2.1, hab.2.2⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab hbc ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc

/-- Paths within an equivalence class can be restricted to that class itself. -/
theorem path_within_block {k : ℕ} (U : RuleSet k)
    {b c : Gram (windowLength k) → ℤ} (hbc : ConnectedIn U b c) :
    ∀ a, ConnectedIn U a b → ConnectedIn (blockOf U a) b c := by
  induction hbc with
  | rel b c hbc =>
    intro a hab
    have hb : b ∈ blockOf U a := (mem_blockOf U a b).mpr ⟨hbc.1, hab⟩
    have hc : c ∈ blockOf U a := (mem_blockOf U a c).mpr
      ⟨hbc.2.1, Relation.EqvGen.trans _ _ _ hab (Relation.EqvGen.rel _ _ hbc)⟩
    exact Relation.EqvGen.rel _ _ ⟨hb, hc, hbc.2.2⟩
  | refl b =>
    intro a hab
    exact Relation.EqvGen.refl _
  | symm b c hbc ih =>
    intro a hac
    have hab : ConnectedIn U a b :=
      Relation.EqvGen.trans _ _ _ hac (Relation.EqvGen.symm _ _ hbc)
    exact Relation.EqvGen.symm _ _ (ih a hab)
  | trans b c d hbc hcd ihbc ihcd =>
    intro a hab
    exact Relation.EqvGen.trans _ _ _ (ihbc a hab)
      (ihcd a (Relation.EqvGen.trans _ _ _ hab hbc))

/-- Every actual rule block is connected using only its own rules. -/
theorem blockOf_connected {k : ℕ} (U : RuleSet k)
    (a : Gram (windowLength k) → ℤ) : Connected (blockOf U a) := by
  intro b hb c hc
  have hab := ((mem_blockOf U a b).mp hb).2
  have hac := ((mem_blockOf U a c).mp hc).2
  exact path_within_block U
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hab) hac) a hab

private theorem adjacent_mem_attached_union {k : ℕ} (U : RuleSet k)
    (w b : Gram (windowLength k) → ℤ) (hb : b ∈ U) (hwb : RuleAdjacent w b) :
    b ∈ (attachedBlocks U w).biUnion id := by
  classical
  have hbblock : b ∈ blockOf U b :=
    (mem_blockOf U b b).mpr ⟨hb, Relation.EqvGen.refl _⟩
  obtain ⟨v, hvw, hvb⟩ := hwb
  have hvblock : Incident (blockOf U b) v :=
    ComponentBounds.incident_mono (Finset.singleton_subset_iff.mpr hbblock) hvb
  have hblock : blockOf U b ∈ attachedBlocks U w :=
    (mem_attachedBlocks U (blockOf U b) w).mpr
      ⟨(mem_blocks U (blockOf U b)).mpr ⟨b, hb, rfl⟩, v, hvblock, hvw⟩
  exact Finset.mem_biUnion.mpr ⟨blockOf U b, hblock, hbblock⟩

private theorem attached_union_closed {k : ℕ} (U : RuleSet k)
    (w a b : Gram (windowLength k) → ℤ)
    (ha : a ∈ (attachedBlocks U w).biUnion id) (hb : b ∈ U)
    (hab : RuleAdjacent a b) : b ∈ (attachedBlocks U w).biUnion id := by
  classical
  obtain ⟨B, hB, haB⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨d, hd, hBvalue⟩ := (mem_blocks U B).mp ((mem_attachedBlocks U B w).mp hB).1
  have had : a ∈ blockOf U d := by simpa only [id_eq, hBvalue] using haB
  obtain ⟨haU, hda⟩ := (mem_blockOf U d a).mp had
  have hdb : ConnectedIn U d b := Relation.EqvGen.trans _ _ _ hda
    (Relation.EqvGen.rel _ _ ⟨haU, hb, hab⟩)
  have hbB : b ∈ B := by
    rw [← hBvalue]
    exact (mem_blockOf U d b).mpr ⟨hb, hdb⟩
  exact Finset.mem_biUnion.mpr ⟨B, hB, hbB⟩

/-- The new block is exactly the new rule and the old blocks touching it.
Freshness of w is unnecessary for this identity. -/
theorem blockOf_insert_eq {k : ℕ} (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) :
    blockOf (insert w U) w = insert w ((attachedBlocks U w).biUnion id) := by
  classical
  let M := insert w ((attachedBlocks U w).biUnion id)
  have hstep (a b : Gram (windowLength k) → ℤ)
      (ha : a ∈ insert w U) (hb : b ∈ insert w U) (hab : RuleAdjacent a b) :
      a ∈ M → b ∈ M := by
    intro haM
    by_cases hbw : b = w
    · subst b
      exact Finset.mem_insert_self _ _
    · have hbU : b ∈ U := (Finset.mem_insert.mp hb).resolve_left hbw
      rcases Finset.mem_insert.mp haM with haw | haUnion
      · subst a
        exact Finset.mem_insert_of_mem (adjacent_mem_attached_union U w b hbU hab)
      · exact Finset.mem_insert_of_mem (attached_union_closed U w a b haUnion hbU hab)
  have hpreserve (a b : Gram (windowLength k) → ℤ)
      (h : ConnectedIn (insert w U) a b) : a ∈ M ↔ b ∈ M := by
    induction h with
    | rel a b hab =>
      exact ⟨hstep a b hab.1 hab.2.1 hab.2.2,
        hstep b a hab.2.1 hab.1 hab.2.2.symm⟩
    | refl a => exact Iff.rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  ext b
  constructor
  · intro hb
    have hpath := ((mem_blockOf (insert w U) w b).mp hb).2
    exact (hpreserve w b hpath).mp (Finset.mem_insert_self _ _)
  · intro hb
    rcases Finset.mem_insert.mp hb with hbw | hbUnion
    · subst b
      exact (mem_blockOf (insert w U) w w).mpr
        ⟨Finset.mem_insert_self _ _, Relation.EqvGen.refl _⟩
    · obtain ⟨B, hB, hbB⟩ := Finset.mem_biUnion.mp hbUnion
      obtain ⟨hBold, v, hvB, hvw⟩ := (mem_attachedBlocks U B w).mp hB
      obtain ⟨a, haB, hva⟩ := (incident_iff_rule B v).mp hvB
      obtain ⟨d, hd, hBvalue⟩ := (mem_blocks U B).mp hBold
      have haBlock : a ∈ blockOf U d := by simpa only [id_eq, hBvalue] using haB
      have hbBlock : b ∈ blockOf U d := by simpa only [id_eq, hBvalue] using hbB
      obtain ⟨haU, hda⟩ := (mem_blockOf U d a).mp haBlock
      obtain ⟨hbU, hdb⟩ := (mem_blockOf U d b).mp hbBlock
      have habOld : ConnectedIn U a b :=
        Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hda) hdb
      have habNew : ConnectedIn (insert w U) a b :=
        connectedIn_mono (Finset.subset_insert _ _) habOld
      have hwa : ConnectedIn (insert w U) w a := Relation.EqvGen.rel _ _
        ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem haU, v, hvw, hva⟩
      exact (mem_blockOf (insert w U) w b).mpr
        ⟨Finset.mem_insert_of_mem hbU, Relation.EqvGen.trans _ _ _ hwa habNew⟩

/-- The size estimate for the actual newly formed block of a catalogue rule. -/
theorem new_block_card_bound {t k : ℕ} (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (hsize : ∀ B ∈ blocks U, B.card ≤ windowLength k) :
    (blockOf (insert w U) w).card ≤
      1 + 4 * t * (windowLength k) ^ 2 + 2 * t * windowLength k := by
  rw [blockOf_insert_eq]
  exact attached_blocks_union_bound U w t (windowLength k) hsize
    (CatalogueVertexBound.catalogue_vertex_card_le w hw)

/-- The actual new block also satisfies the connected-block component bound. -/
theorem new_block_component_bound {t k : ℕ} (ht : 1 ≤ t) (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (hcatalogue : ∀ u ∈ U, CatalogueRule t k u) :
    componentCount (blockOf (insert w U) w) ≤
      (2 * t - 1) * (blockOf (insert w U) w).card + 1 := by
  apply connected_block_bound ht _
    (blockOf_nonempty (insert w U) w (Finset.mem_insert_self _ _))
  · intro u hu
    have huNew := ((mem_blockOf (insert w U) w u).mp hu).1
    rcases Finset.mem_insert.mp huNew with huw | huOld
    · simpa only [huw] using hw
    · exact hcatalogue u huOld
  · exact blockOf_connected (insert w U) w

#print axioms path_within_block
#print axioms blockOf_connected
#print axioms blockOf_insert_eq
#print axioms new_block_card_bound
#print axioms new_block_component_bound

end DeletionCode.BlockAdjunction
