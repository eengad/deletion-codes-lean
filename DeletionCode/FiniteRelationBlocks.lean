import DeletionCode.RelationBlockSupport
import DeletionCode.BlockPartition
import DeletionCode.RelationBlockSavings

/-!
Finite-set form of the nonzero restriction step. The selected blocks are the
actual adjacency blocks of G meeting the relation's coefficient support I.
Independence derives a nonzero restriction in each such block; its gram cannot
occur outside the block, so it survives in w. Their union is the existing
finite block hull, without choosing block representatives as input data.
-/

namespace DeletionCode.FiniteRelationBlocks

open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph BlockPartition
open scoped BigOperators

/-- Actual old rule blocks containing at least one participating rule. -/
noncomputable def selectedBlocks {k : ℕ} (G I : RuleSet k) : Finset (RuleSet k) := by
  classical
  exact (blocks G).filter (fun B => (B ∩ I).Nonempty)

@[simp] theorem mem_selectedBlocks {k : ℕ} (G I B : RuleSet k) :
    B ∈ selectedBlocks G I ↔ B ∈ blocks G ∧ (B ∩ I).Nonempty := by
  classical
  simp [selectedBlocks]

private theorem subtype_connected {k : ℕ} (G : RuleSet k) {u v : G}
    (h : GeneratingBlocks.Connected (fun z : G => z.val) u v) :
    ConnectedIn G u.val v.val := by
  induction h with
  | rel u v huv => exact Relation.EqvGen.rel _ _ ⟨u.property, v.property, huv⟩
  | refl u => exact Relation.EqvGen.refl _
  | symm u v huv ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v z huv hvz ihuv ihvz => exact Relation.EqvGen.trans _ _ _ ihuv ihvz

/-- Extending the finite relation's coefficients by zero gives the same actual
relation indexed by all rules of G. -/
private theorem indexed_relation {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ)
    (a : (Gram (windowLength k) → ℤ) → ℚ)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    RelationSupport.Relation (fun u : G => u.val) w
      (fun u : G => if u.val ∈ I then a u.val else 0) := by
  classical
  intro g
  rw [hrel g]
  symm
  calc
    (∑ u : G, (if u.val ∈ I then a u.val else 0) * (u.val g : ℚ)) =
        ∑ u ∈ G, (if u ∈ I then a u else 0) * (u g : ℚ) := by
      apply Finset.sum_bij (fun (u : G) _ => u.val)
      · intro u _
        exact u.property
      · intro u _ v _ huv
        exact Subtype.ext huv
      · intro u hu
        exact ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩
      · intro u _
        rfl
    _ = ∑ u ∈ I, (if u ∈ I then a u else 0) * (u g : ℚ) := by
      symm
      apply Finset.sum_subset hIG
      intro u _ hu
      simp [hu]
    _ = ∑ u ∈ I, a u * (u g : ℚ) := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [if_pos hu]

/-- Every selected actual adjacency block has a gram of one of its rules that
survives in the relation vector. No nonzero-restriction premise is required. -/
theorem selected_block_nonzero {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ)
    (a : (Gram (windowLength k) → ℤ) → ℚ)
    (hind : LinearIndependent ℚ (fun (u : G) g => (u.val g : ℚ)))
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ))
    (B : RuleSet k) (hB : B ∈ selectedBlocks G I) :
    ∃ g u, u ∈ B ∧ u g ≠ 0 ∧ w g ≠ 0 := by
  classical
  obtain ⟨hBblock, hBI⟩ := (mem_selectedBlocks G I B).mp hB
  let T : Finset G := Finset.univ.filter (fun u => u.val ∈ B)
  let coeff : G → ℚ := fun u => if u.val ∈ I then a u.val else 0
  have hmem (u : G) : u ∈ T ↔ u.val ∈ B := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
  have hactive : ∃ u ∈ T, coeff u ≠ 0 := by
    obtain ⟨u, hu⟩ := hBI
    obtain ⟨huB, huI⟩ := Finset.mem_inter.mp hu
    let uG : G := ⟨u, hIG huI⟩
    refine ⟨uG, (hmem uG).mpr huB, ?_⟩
    simpa only [coeff, uG, if_pos huI] using ha u huI
  have hclosed : GeneratingBlocks.BlockClosed (fun u : G => u.val) (↑T : Set G) := by
    intro u hu v huv
    obtain ⟨r, _, hr⟩ := (mem_blocks G B).mp hBblock
    have huB : u.val ∈ blockOf G r := by rw [hr]; exact (hmem u).mp hu
    have hru := ((mem_blockOf G r u.val).mp huB).2
    apply (hmem v).mpr
    rw [← hr]
    exact (mem_blockOf G r v.val).mpr ⟨v.property,
      Relation.EqvGen.trans _ _ _ hru (subtype_connected G huv)⟩
  obtain ⟨g, hw, u, hu, hug⟩ := RelationBlockSupport.block_restriction_nonzero
    (fun u : G => u.val) w coeff hind (indexed_relation G I hIG w a hrel)
    T hactive hclosed
  exact ⟨g, u.val, (hmem u).mp hu, hug, hw⟩

/-- Each selected block shares an actual incident de Bruijn vertex with w. -/
theorem selected_block_meets {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ)
    (a : (Gram (windowLength k) → ℤ) → ℚ)
    (hind : LinearIndependent ℚ (fun (u : G) g => (u.val g : ℚ)))
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ))
    (B : RuleSet k) (hB : B ∈ selectedBlocks G I) :
    ∃ v, Incident B v ∧ Incident {w} v := by
  obtain ⟨g, u, hu, hug, hwg⟩ := selected_block_nonzero G I hIG w a hind ha hrel B hB
  exact ⟨gramPrefix g,
    (incident_iff_rule B (gramPrefix g)).mpr
      ⟨u, hu, GeneratingBlocks.nonzero_incident u g hug⟩,
    GeneratingBlocks.nonzero_incident w g hwg⟩

/-- Selection by a nonzero relation coefficient implies actual attachment. -/
theorem selectedBlocks_subset_attachedBlocks {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ)
    (a : (Gram (windowLength k) → ℤ) → ℚ)
    (hind : LinearIndependent ℚ (fun (u : G) g => (u.val g : ℚ)))
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    selectedBlocks G I ⊆ attachedBlocks G w := by
  intro B hB
  exact (mem_attachedBlocks G B w).mpr
    ⟨((mem_selectedBlocks G I B).mp hB).1,
      selected_block_meets G I hIG w a hind ha hrel B hB⟩

/-- A linear combination cannot introduce a gram outside the actual support
union of the ambient rules. Independence and nonzero coefficients are unneeded. -/
theorem relation_support_included {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ)
    (a : (Gram (windowLength k) → ℤ) → ℚ)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    SupportInclusion.CoordinateSupportIncluded {w} G := by
  classical
  intro g hg
  obtain ⟨z, hz, hzg⟩ := hg
  have hzw : z = w := Finset.mem_singleton.mp hz
  subst z
  by_contra hnone
  push Not at hnone
  have hzero : (w g : ℚ) = 0 := by
    rw [hrel g]
    apply Finset.sum_eq_zero
    intro u hu
    simp [hnone u (hIG hu)]
  exact hzg (by exact_mod_cast hzero)

/-- The finite union of precisely the selected blocks is the existing actual
block hull of I in G. This is a partition identity, independent of the relation. -/
theorem selectedBlocks_biUnion {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G) :
    (selectedBlocks G I).biUnion id = RelationBlockSavings.blockHull G I := by
  classical
  ext u
  constructor
  · intro hu
    obtain ⟨B, hB, huB⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨hBblock, i, hi⟩ := (mem_selectedBlocks G I B).mp hB
    obtain ⟨hiB, hiI⟩ := Finset.mem_inter.mp hi
    obtain ⟨r, _, hr⟩ := (mem_blocks G B).mp hBblock
    have hui := (mem_blockOf G r u).mp (by simpa only [hr, id_eq] using huB)
    have hii := (mem_blockOf G r i).mp (by simpa only [hr] using hiB)
    apply Finset.mem_filter.mpr
    exact ⟨hui.1, i, hiI, Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ hii.2) hui.2⟩
  · intro hu
    obtain ⟨_, i, hiI, hiu⟩ := Finset.mem_filter.mp hu
    have hiG := hIG hiI
    have hiB : i ∈ blockOf G i :=
      (mem_blockOf G i i).mpr ⟨hiG, Relation.EqvGen.refl i⟩
    have hB : blockOf G i ∈ selectedBlocks G I :=
      (mem_selectedBlocks G I (blockOf G i)).mpr
        ⟨(mem_blocks G (blockOf G i)).mpr ⟨i, hiG, rfl⟩,
          i, Finset.mem_inter.mpr ⟨hiB, hiI⟩⟩
    exact Finset.mem_biUnion.mpr ⟨blockOf G i, hB,
      (mem_blockOf G i u).mpr ⟨(RelationBlockSavings.blockHull_subset G I hu), hiu⟩⟩

#print axioms selected_block_nonzero
#print axioms selected_block_meets
#print axioms selectedBlocks_subset_attachedBlocks
#print axioms relation_support_included
#print axioms selectedBlocks_biUnion

end DeletionCode.FiniteRelationBlocks
