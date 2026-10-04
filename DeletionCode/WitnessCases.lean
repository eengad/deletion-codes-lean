import DeletionCode.FiniteGenerating
import DeletionCode.FiniteRelationBlocks
import DeletionCode.SupportBlockCount
import DeletionCode.CatalogueAlgebra
import DeletionCode.LargeBlockSelection

/-!
The two stopping cases produce actual finite surviving generating witnesses.
The relation case derives the number of retained blocks from independence and
support containment, and hence its size bound. The large-block case derives
the oversized new block from the cutoff failure. All counts concern the
underlying finite rule sets, with inherited generating order and independence.
-/
namespace DeletionCode.WitnessCases

open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition FiniteGenerating FiniteRelationBlocks CatalogueAlgebra
open scoped BigOperators

structure WitnessBounds (t k : ℕ) (U : RuleSet k) : Prop where
  size_lower : 2 ≤ U.card
  size_upper : U.card ≤ 1 + 4 * t * (windowLength k) ^ 2
  components : componentCount U ≤ (2 * t - 1) * U.card + 1
  small_components : U.card ≤ windowLength k → componentCount U ≤ (2 * t - 1) * U.card

/-- The exact size/component conditions together with actual catalogue,
survival, rational independence, and ordered negative-gram provenance. -/
structure Witness (t k : ℕ) (v : Gram (windowLength k) → ℤ)
    (K : Set (Gram (windowLength k) → ℤ)) (U : RuleSet k) : Prop where
  generating : GeneratingAt v U
  catalogue : ∀ u ∈ U, CatalogueRule t k u
  surviving : ∀ u ∈ U, u ∈ K
  bounds : WitnessBounds t k U

/-- Independence forces every selected block to meet w; support containment
then assigns distinct selected blocks to distinct actual components of w. -/
theorem relation_block_count {t k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ) (hind : Independent G)
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    (selectedBlocks G I).card ≤ 2 * t := by
  apply SupportBlockCount.catalogue_block_count_le G w (selectedBlocks G I) hw
  · intro B hB
    exact ((mem_selectedBlocks G I B).mp hB).1
  · exact relation_support_included G I hIG w a hrel
  · exact selected_block_meets G I hIG w a hind ha hrel

theorem relation_hull_card {t k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ) (hind : Independent G)
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ))
    (hsize : ∀ B ∈ blocks G, B.card ≤ windowLength k) :
    (RelationBlockSavings.blockHull G I).card ≤ 2 * t * windowLength k := by
  classical
  rw [← selectedBlocks_biUnion G I hIG]
  calc
    ((selectedBlocks G I).biUnion id).card ≤ ∑ B ∈ selectedBlocks G I, B.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _B ∈ selectedBlocks G I, windowLength k := by
      apply Finset.sum_le_sum
      intro B hB
      exact hsize B ((mem_selectedBlocks G I B).mp hB).1
    _ = (selectedBlocks G I).card * windowLength k := by simp
    _ ≤ 2 * t * windowLength k := Nat.mul_le_mul_right _
      (relation_block_count G I hIG w hw a hind ha hrel)

/-- Retaining whole blocks in the relation case gives the full bounded
witness, including the stronger component bound for every resulting size. -/
theorem relation_case {t k : ℕ} (ht : 2 ≤ t)
    (v : Gram (windowLength k) → ℤ) (K : Set (Gram (windowLength k) → ℤ))
    (G I : RuleSet k) (hIG : I ⊆ G) (hI : 2 ≤ I.card)
    (hgen : GeneratingAt v G) (hcat : ∀ u ∈ G, CatalogueRule t k u)
    (hK : ∀ u ∈ G, u ∈ K) (hsize : ∀ B ∈ blocks G, B.card ≤ windowLength k)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ) (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    Witness t k v K (RelationBlockSavings.blockHull G I) := by
  let U := RelationBlockSavings.blockHull G I
  have hUG : U ⊆ G := RelationBlockSavings.blockHull_subset G I
  have hlow : 2 ≤ U.card := hI.trans
    (Finset.card_le_card (RelationBlockSavings.subset_blockHull G I hIG))
  have hupper : U.card ≤ 2 * t * windowLength k :=
    relation_hull_card G I hIG w hw a hgen.independent ha hrel hsize
  have hc : componentCount U ≤ (2 * t - 1) * U.card :=
    RelationBlockSavings.relation_block_hull_bound ht G I hIG hI hcat w hw a ha hrel
  have hL : 1 ≤ windowLength k := by unfold windowLength; omega
  have hquad : 2 * t * windowLength k ≤ 1 + 4 * t * (windowLength k) ^ 2 := by
    nlinarith [Nat.mul_le_mul_left (2 * t * windowLength k) hL]
  exact ⟨generating_blockHull hgen I, (fun u hu => hcat u (hUG hu)),
    (fun u hu => hK u (hUG hu)), hlow, hupper.trans hquad, hc.trans (Nat.le_succ _), fun _ => hc⟩

/-- Novelty up to sign derives a relation with at least two active coefficients,
so no relation-support set is assumed in the in-span stopping case. -/
theorem relation_case_of_span {t k : ℕ} (ht : 2 ≤ t)
    (v : Gram (windowLength k) → ℤ) (K : Set (Gram (windowLength k) → ℤ))
    (G : RuleSet k) (hgen : GeneratingAt v G)
    (hcat : ∀ u ∈ G, CatalogueRule t k u) (hK : ∀ u ∈ G, u ∈ K)
    (hsize : ∀ B ∈ blocks G, B.card ≤ windowLength k)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (hnew : ∀ u ∈ G, w ≠ u ∧ w ≠ -u)
    (hspan : rational w ∈ Submodule.span ℚ (rational '' (↑G : Set _))) :
    ∃ U : RuleSet k, U ⊆ G ∧ Witness t k v K U := by
  obtain ⟨I, hIG, hI, a, ha, hrel⟩ := new_relation_support (by omega : 1 ≤ t)
    G hcat w hw hnew hspan
  exact ⟨_, RelationBlockSavings.blockHull_subset G I,
    relation_case ht v K G I hIG hI hgen hcat hK hsize w hw a ha hrel⟩

/-- A cutoff failure after an independent append selects its actual new block,
with both the strict lower cutoff and the full manuscript upper bounds. -/
theorem large_block_case {t k : ℕ} (ht : 2 ≤ t)
    (v : Gram (windowLength k) → ℤ) (K : Set (Gram (windowLength k) → ℤ))
    (G : RuleSet k) (w : Gram (windowLength k) → ℤ)
    (hgen : GeneratingAt v (insert w G)) (hw : CatalogueRule t k w)
    (hcat : ∀ u ∈ G, CatalogueRule t k u)
    (hK : ∀ u ∈ insert w G, u ∈ K)
    (hsize : ∀ B ∈ blocks G, B.card ≤ windowLength k)
    (hbad : ¬ ∀ B ∈ blocks (insert w G), B.card ≤ windowLength k) :
    Witness t k v K (blockOf (insert w G) w) := by
  classical
  have hex : ∃ B ∈ blocks (insert w G), windowLength k < B.card := by
    push Not at hbad
    exact hbad
  have hlarge := LargeBlockSelection.new_block_large_of_exists G w (windowLength k) hsize hex
  have hL : 2 ≤ windowLength k := by unfold windowLength; omega
  have hlow : 2 ≤ (blockOf (insert w G) w).card := hL.trans (Nat.le_of_lt hlarge)
  have hupper := BlockAdjunction.new_block_card_bound G w hw hsize
  have hc := BlockAdjunction.new_block_component_bound (by omega : 1 ≤ t) G w hw hcat
  refine ⟨generating_blockOf hgen w, ?_, ?_, hlow, hupper, hc, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.mp ((mem_blockOf (insert w G) w u).mp hu).1 with huw | huG
    · simpa only [huw] using hw
    · exact hcat u huG
  · intro u hu
    exact hK u ((mem_blockOf (insert w G) w u).mp hu).1
  · intro hsmall
    omega

#print axioms relation_block_count
#print axioms relation_hull_card
#print axioms relation_case
#print axioms relation_case_of_span
#print axioms large_block_case

end DeletionCode.WitnessCases
