import DeletionCode.Burst.CatalogueBounds

/-!
The existing greedy scan and support-block arguments produce a bounded
independent witness for any catalogue satisfying the proved geometric
contracts. Its cutoff uses the actual per-rule support-vertex bound V.
-/
namespace DeletionCode.Burst.WitnessExtraction

open Qary.SignedSupport Qary.SignedRuleCount Qary.RuleSetGraph Qary.ConnectedBlocks
open Qary.BlockPartition Qary.FiniteGenerating Qary.FiniteRelationBlocks
open Qary.CatalogueAlgebra Qary.FiniteWalkRules Qary.WalkSelection
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

def cutoff (k V : ℕ) : ℕ := 1 + V * Qary.HeaderRecovery.windowLength k

structure WitnessBounds (t k V : ℕ) (U : RuleSet α k) : Prop where
  size_lower : 2 ≤ U.card
  size_upper : U.card ≤ cutoff k V
  components : componentCount U ≤ (2 * t - 1) * U.card + 1
  small_components : U.card ≤ Qary.HeaderRecovery.windowLength k →
    componentCount U ≤ (2 * t - 1) * U.card

structure Witness (t k V : ℕ)
    (C : Set (Gram α (Qary.HeaderRecovery.windowLength k) → ℤ))
    (v : Gram α (Qary.HeaderRecovery.windowLength k) → ℤ)
    (K : Set (Gram α (Qary.HeaderRecovery.windowLength k) → ℤ))
    (U : RuleSet α k) : Prop where
  generating : GeneratingAt v U
  catalogue : ∀ u ∈ U, u ∈ C
  surviving : ∀ u ∈ U, u ∈ K
  bounds : WitnessBounds t k V U

variable {t k V : ℕ}
variable {C : Set (Gram α (Qary.HeaderRecovery.windowLength k) → ℤ)}
variable (F : CatalogueBounds.Facts t k V C)
include F

theorem new_block_card_bound (U : RuleSet α k)
    (w : Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) (hw : w ∈ C)
    (hsize : ∀ B ∈ blocks U, B.card ≤ Qary.HeaderRecovery.windowLength k) :
    (blockOf (insert w U) w).card ≤ cutoff k V := by
  classical
  rw [Qary.BlockAdjunction.blockOf_insert_eq]
  have h := Qary.AttachedBlocks.attached_union_card_bound (attachedBlocks U w) w
    (Qary.HeaderRecovery.windowLength k)
    (fun B hB => hsize B ((mem_attachedBlocks U B w).mp hB).1)
    (fun B hB => ((mem_attachedBlocks U B w).mp hB).2)
    (fun B hB D hD hne => blocks_support_disjoint U B
      ((mem_attachedBlocks U B w).mp hB).1 D ((mem_attachedBlocks U D w).mp hD).1 hne)
  unfold cutoff
  calc
    _ ≤ 1 + Qary.HeaderRecovery.windowLength k * Fintype.card (RuleSetVertex {w}) := h
    _ ≤ 1 + Qary.HeaderRecovery.windowLength k * V :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (F.vertices w hw)) 1
    _ = _ := by ring

theorem new_block_component_bound (ht : 1 ≤ t) (U : RuleSet α k)
    (w : Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) (hw : w ∈ C)
    (hcatalogue : ∀ u ∈ U, u ∈ C) :
    componentCount (blockOf (insert w U) w) ≤
      (2 * t - 1) * (blockOf (insert w U) w).card + 1 := by
  apply CatalogueBounds.connected_block_bound F ht _
    (blockOf_nonempty (insert w U) w (Finset.mem_insert_self _ _))
  · intro u hu
    rcases Finset.mem_insert.mp ((mem_blockOf (insert w U) w u).mp hu).1 with huw | hu
    · simpa only [huw] using hw
    · exact hcatalogue u hu
  · exact Qary.BlockAdjunction.blockOf_connected (insert w U) w

theorem relation_block_count  (G I : RuleSet α k) (hIG : I ⊆ G)
    (w : Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) (hw : w ∈ C)
    (a : (Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) → ℚ) (hind : Independent G)
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    (selectedBlocks G I).card ≤ 2 * t := by
  exact (Qary.SupportBlockCount.block_count_le_components G w (selectedBlocks G I)
    (fun B hB => ((mem_selectedBlocks G I B).mp hB).1)
    (relation_support_included G I hIG w a hrel)
    (selected_block_meets G I hIG w a hind ha hrel)).trans (F.components w hw)


theorem relation_hull_card  (G I : RuleSet α k) (hIG : I ⊆ G)
    (w : Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) (hw : w ∈ C)
    (a : (Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) → ℚ) (hind : Independent G)
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ))
    (hsize : ∀ B ∈ blocks G, B.card ≤ Qary.HeaderRecovery.windowLength k) :
    (Qary.RelationBlockSavings.blockHull G I).card ≤ 2 * t * Qary.HeaderRecovery.windowLength k := by
  classical
  rw [← selectedBlocks_biUnion G I hIG]
  calc
    ((selectedBlocks G I).biUnion id).card ≤ ∑ B ∈ selectedBlocks G I, B.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _B ∈ selectedBlocks G I, Qary.HeaderRecovery.windowLength k := by
      apply Finset.sum_le_sum
      intro B hB
      exact hsize B ((mem_selectedBlocks G I B).mp hB).1
    _ = (selectedBlocks G I).card * Qary.HeaderRecovery.windowLength k := by simp
    _ ≤ 2 * t * Qary.HeaderRecovery.windowLength k := Nat.mul_le_mul_right _
      (relation_block_count F G I hIG w hw a hind ha hrel)

/-- Retaining whole blocks in the relation case gives the full bounded
witness, including the stronger component bound for every resulting size. -/
theorem relation_case  (ht : 2 ≤ t)
    (v : Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) (K : Set (Gram α (Qary.HeaderRecovery.windowLength k) → ℤ))
    (G I : RuleSet α k) (hIG : I ⊆ G) (hI : 2 ≤ I.card)
    (hgen : GeneratingAt v G) (hcat : ∀ u ∈ G, u ∈ C)
    (hK : ∀ u ∈ G, u ∈ K) (hsize : ∀ B ∈ blocks G, B.card ≤ Qary.HeaderRecovery.windowLength k)
    (w : Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) (hw : w ∈ C)
    (a : (Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) → ℚ) (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    Witness t k V C v K (Qary.RelationBlockSavings.blockHull G I) := by
  let U := Qary.RelationBlockSavings.blockHull G I
  have hUG : U ⊆ G := Qary.RelationBlockSavings.blockHull_subset G I
  have hlow : 2 ≤ U.card := hI.trans
    (Finset.card_le_card (Qary.RelationBlockSavings.subset_blockHull G I hIG))
  have hupper : U.card ≤ 2 * t * Qary.HeaderRecovery.windowLength k :=
    relation_hull_card F G I hIG w hw a hgen.independent ha hrel hsize
  have hc : componentCount U ≤ (2 * t - 1) * U.card :=
    CatalogueBounds.relation_block_hull_bound F ht G I hIG hI hcat w hw a ha hrel
  have hL : 1 ≤ Qary.HeaderRecovery.windowLength k := by unfold Qary.HeaderRecovery.windowLength; omega
  have hquad : 2 * t * Qary.HeaderRecovery.windowLength k ≤ cutoff k V := by
    have h := Nat.mul_le_mul_right (Qary.HeaderRecovery.windowLength k) F.capacity
    unfold cutoff
    omega
  exact ⟨generating_blockHull hgen I, (fun u hu => hcat u (hUG hu)),
    (fun u hu => hK u (hUG hu)), hlow, hupper.trans hquad, hc.trans (Nat.le_succ _), fun _ => hc⟩

/-- Novelty up to sign derives a relation with at least two active coefficients,
so no relation-support set is assumed in the in-span stopping case. -/
theorem relation_case_of_span  (ht : 2 ≤ t)
    (v : Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) (K : Set (Gram α (Qary.HeaderRecovery.windowLength k) → ℤ))
    (G : RuleSet α k) (hgen : GeneratingAt v G)
    (hcat : ∀ u ∈ G, u ∈ C) (hK : ∀ u ∈ G, u ∈ K)
    (hsize : ∀ B ∈ blocks G, B.card ≤ Qary.HeaderRecovery.windowLength k)
    (w : Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) (hw : w ∈ C)
    (hnew : ∀ u ∈ G, w ≠ u ∧ w ≠ -u)
    (hspan : rational w ∈ Submodule.span ℚ (rational '' (↑G : Set _))) :
    ∃ U : RuleSet α k, U ⊆ G ∧ Witness t k V C v K U := by
  obtain ⟨I, hIG, hI, a, ha, hrel⟩ := CatalogueBounds.new_relation_support F (by omega : 1 ≤ t)
    G hcat w hw hnew hspan
  exact ⟨_, Qary.RelationBlockSavings.blockHull_subset G I,
    relation_case F ht v K G I hIG hI hgen hcat hK hsize w hw a ha hrel⟩

/-- A cutoff failure after an independent append selects its actual new block,
with both the strict lower cutoff and the full manuscript upper bounds. -/
theorem large_block_case  (ht : 2 ≤ t)
    (v : Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) (K : Set (Gram α (Qary.HeaderRecovery.windowLength k) → ℤ))
    (G : RuleSet α k) (w : Gram α (Qary.HeaderRecovery.windowLength k) → ℤ)
    (hgen : GeneratingAt v (insert w G)) (hw : w ∈ C)
    (hcat : ∀ u ∈ G, u ∈ C)
    (hK : ∀ u ∈ insert w G, u ∈ K)
    (hsize : ∀ B ∈ blocks G, B.card ≤ Qary.HeaderRecovery.windowLength k)
    (hbad : ¬ ∀ B ∈ blocks (insert w G), B.card ≤ Qary.HeaderRecovery.windowLength k) :
    Witness t k V C v K (blockOf (insert w G) w) := by
  classical
  have hex : ∃ B ∈ blocks (insert w G), Qary.HeaderRecovery.windowLength k < B.card := by
    push Not at hbad
    exact hbad
  have hlarge := Qary.LargeBlockSelection.new_block_large_of_exists G w (Qary.HeaderRecovery.windowLength k) hsize hex
  have hL : 2 ≤ Qary.HeaderRecovery.windowLength k := by unfold Qary.HeaderRecovery.windowLength; omega
  have hlow : 2 ≤ (blockOf (insert w G) w).card := hL.trans (Nat.le_of_lt hlarge)
  have hupper := new_block_card_bound F G w hw hsize
  have hc := new_block_component_bound F (by omega : 1 ≤ t) G w hw hcat
  refine ⟨generating_blockOf hgen w, ?_, ?_, hlow, hupper, hc, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.mp ((mem_blockOf (insert w G) w u).mp hu).1 with huw | huG
    · simpa only [huw] using hw
    · exact hcat u huG
  · intro u hu
    exact hK u ((mem_blockOf (insert w G) w u).mp hu).1
  · intro hsmall
    omega

theorem extract {m : ℕ} (ht : 2 ≤ t)
    (p : Fin (m + 1) → Gram α (Qary.HeaderRecovery.windowLength k) → ℤ)
    (K : Set (Gram α (Qary.HeaderRecovery.windowLength k) → ℤ))
    (hp : ∀ j, Qary.WitnessAlgebra.BooleanVector (rationalPath p j))
    (hclosed : p 0 = p (Fin.last m)) (hodd : Odd m)
    (hcat : ∀ i, (step p i) ∈ C)
    (hK : ∀ i, step p i ∈ K) :
    ∃ U : RuleSet α k, Witness t k V C (p 0) K U := by
  classical
  let Good : Finset (Fin m) → Prop := fun S =>
    ∀ B ∈ blocks (selectedRules p S), B.card ≤ Qary.HeaderRecovery.windowLength k
  have hgood : Good ∅ := by simp [Good, blocks]
  have hclosedQ : rationalPath p 0 = rationalPath p (Fin.last m) :=
    congrArg rational hclosed
  obtain ⟨i, S, hs, hgen, hnew, hstop⟩ :=
    odd_boolean_closed_walk_stops (rationalPath p) hp Good hgood hclosedQ hodd
  have hcatS (T : Finset (Fin m)) :
      ∀ u ∈ selectedRules p T, u ∈ C := by
    intro u hu
    obtain ⟨j, _, rfl⟩ := (mem_selectedRules p T u).mp hu
    exact hcat j
  have hKS (T : Finset (Fin m)) : ∀ u ∈ selectedRules p T, u ∈ K := by
    intro u hu
    obtain ⟨j, _, rfl⟩ := (mem_selectedRules p T u).mp hu
    exact hK j
  rcases hstop with hrel | ⟨_, hind, hbad, hgen'⟩
  · have hspan : rational (step p i) ∈
        Submodule.span ℚ (rational '' (↑(selectedRules p S) : Set _)) := by
      simpa only [rational_step, ← selectedSpan_eq] using hrel
    obtain ⟨U, _, hU⟩ := relation_case_of_span F ht (p 0) K (selectedRules p S)
      (selected_generatingAt p S hs.independent hgen) (hcatS S) (hKS S)
      hs.good (step p i) (hcat i) (novelty_transfer p S i hnew) hspan
    exact ⟨U, hU⟩
  · have hgenI : Qary.FiniteGenerating.GeneratingAt (p 0)
        (insert (step p i) (selectedRules p S)) := by
      simpa only [selectedRules_insert] using
        selected_generatingAt p (insert i S) hind hgen'
    have hKI : ∀ u ∈ insert (step p i) (selectedRules p S), u ∈ K := by
      simpa only [selectedRules_insert] using hKS (insert i S)
    have hbadI : ¬ ∀ B ∈ blocks (insert (step p i) (selectedRules p S)),
        B.card ≤ Qary.HeaderRecovery.windowLength k := by
      simpa only [Good, selectedRules_insert] using hbad
    exact ⟨_, large_block_case F ht (p 0) K (selectedRules p S) (step p i)
      hgenI (hcat i) (hcatS S) hKI hs.good hbadI⟩


#print axioms new_block_card_bound
#print axioms relation_case
#print axioms large_block_case
#print axioms extract

end DeletionCode.Burst.WitnessExtraction
