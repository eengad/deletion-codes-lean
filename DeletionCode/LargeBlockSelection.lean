import DeletionCode.BlockAdjunction

/-!
Selecting the newly formed large block. Adjoining one rule cannot change a
block that does not contain that rule: paths inside such a block already stay
inside the old rule set. Therefore, if all old blocks are small, every oversized
block after adjunction is precisely the block of the adjoined rule.
-/

namespace DeletionCode.LargeBlockSelection

open HeaderRecovery SignedSupport SignedRuleCount BlockPartition BlockAdjunction

/-- A new block excluding the adjoined rule consists entirely of old rules. -/
theorem blockOf_insert_subset_of_not_mem {k : ℕ} (G : RuleSet k)
    (w a : Gram (windowLength k) → ℤ)
    (hw : w ∉ blockOf (insert w G) a) : blockOf (insert w G) a ⊆ G := by
  classical
  intro b hb
  have hbNew := ((mem_blockOf (insert w G) a b).mp hb).1
  rcases Finset.mem_insert.mp hbNew with hbw | hbG
  · exact False.elim (hw (by simpa only [hbw] using hb))
  · exact hbG

/-- A block that does not contain the new rule is unchanged. No freshness
assumption on w, or membership assumption on its representative a, is needed. -/
theorem blockOf_insert_eq_of_not_mem {k : ℕ} (G : RuleSet k)
    (w a : Gram (windowLength k) → ℤ)
    (hw : w ∉ blockOf (insert w G) a) :
    blockOf (insert w G) a = blockOf G a := by
  classical
  have hsub := blockOf_insert_subset_of_not_mem G w a hw
  ext b
  constructor
  · intro hb
    have hab := ((mem_blockOf (insert w G) a b).mp hb).2
    have hpath : ConnectedIn (blockOf (insert w G) a) a b :=
      path_within_block (insert w G) hab a (Relation.EqvGen.refl a)
    exact (mem_blockOf G a b).mpr
      ⟨hsub hb, connectedIn_mono hsub hpath⟩
  · intro hb
    obtain ⟨hbG, hab⟩ := (mem_blockOf G a b).mp hb
    exact (mem_blockOf (insert w G) a b).mpr
      ⟨Finset.mem_insert_of_mem hbG,
        connectedIn_mono (Finset.subset_insert w G) hab⟩

/-- Any actual new block excluding w is an actual old block. -/
theorem block_not_containing_new_is_old {k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (B : RuleSet k)
    (hB : B ∈ blocks (insert w G)) (hw : w ∉ B) : B ∈ blocks G := by
  classical
  obtain ⟨a, ha, hvalue⟩ := (mem_blocks (insert w G) B).mp hB
  have hw' : w ∉ blockOf (insert w G) a := by simpa only [hvalue] using hw
  have haBlock : a ∈ blockOf (insert w G) a :=
    (mem_blockOf (insert w G) a a).mpr ⟨ha, Relation.EqvGen.refl a⟩
  have haG := blockOf_insert_subset_of_not_mem G w a hw' haBlock
  exact (mem_blocks G B).mpr
    ⟨a, haG, (blockOf_insert_eq_of_not_mem G w a hw').symm.trans hvalue⟩

/-- An actual block containing w is the actual block represented by w. -/
theorem block_containing_new_eq {k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (B : RuleSet k)
    (hB : B ∈ blocks (insert w G)) (hw : w ∈ B) :
    B = blockOf (insert w G) w := by
  classical
  obtain ⟨a, _, hvalue⟩ := (mem_blocks (insert w G) B).mp hB
  have hw' : w ∈ blockOf (insert w G) a := by simpa only [hvalue] using hw
  have haw := ((mem_blockOf (insert w G) a w).mp hw').2
  exact hvalue.symm.trans (blockOf_eq_of_connected (insert w G) a w haw)

/-- If every old block has size at most L, an oversized new block must be the
block of the adjoined rule. -/
theorem oversized_block_eq_new_block {k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (L : ℕ)
    (hsize : ∀ B ∈ blocks G, B.card ≤ L)
    (B : RuleSet k) (hB : B ∈ blocks (insert w G)) (hlarge : L < B.card) :
    B = blockOf (insert w G) w := by
  classical
  by_cases hw : w ∈ B
  · exact block_containing_new_eq G w B hB hw
  · have hold := hsize B (block_not_containing_new_is_old G w B hB hw)
    omega

/-- The stopping condition that some new block is too large gives the lower
bound on the specific new block used in the witness construction. -/
theorem new_block_large_of_exists {k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (L : ℕ)
    (hsize : ∀ B ∈ blocks G, B.card ≤ L)
    (hlarge : ∃ B ∈ blocks (insert w G), L < B.card) :
    L < (blockOf (insert w G) w).card := by
  obtain ⟨B, hB, hcard⟩ := hlarge
  simpa only [oversized_block_eq_new_block G w L hsize B hB hcard] using hcard

#print axioms blockOf_insert_eq_of_not_mem
#print axioms block_not_containing_new_is_old
#print axioms oversized_block_eq_new_block
#print axioms new_block_large_of_exists

end DeletionCode.LargeBlockSelection
