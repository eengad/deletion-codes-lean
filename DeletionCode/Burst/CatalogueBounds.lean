import DeletionCode.Qary.FiniteRelationBlocks
import DeletionCode.Qary.SupportBlockCount
import DeletionCode.Qary.LargeBlockSelection
import DeletionCode.Qary.FiniteWalkRules

/-!
Catalogue-independent bounds for the existing support graphs. The hypotheses
below are concrete geometric conclusions about a fixed set of signed vectors;
the burst catalogue supplies them from its actual local word presentations.
This module does not assert a burst-channel theorem from unproved premises.
-/
namespace DeletionCode.Burst.CatalogueBounds

open Qary.SignedSupport Qary.SignedRuleCount Qary.RuleSetGraph
open Qary.ConnectedBlocks Qary.BlockPartition Qary.FiniteGenerating
open Qary.CatalogueAlgebra Qary.FiniteRelationBlocks
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

structure Facts (t k V : ℕ)
    (C : Set (Gram α (Qary.HeaderRecovery.windowLength k) → ℤ)) : Prop where
  signed : ∀ u ∈ C, Qary.WitnessAlgebra.SignedUnitVector (rational u)
  nonzero : ∀ u ∈ C, u ≠ 0
  components : ∀ u ∈ C, componentCount {u} ≤ 2 * t
  vertices : ∀ u ∈ C, Fintype.card (RuleSetVertex {u}) ≤ V
  capacity : 2 * t ≤ V
  savings : ∀ (I : RuleSet α k), (∀ u ∈ I, u ∈ C) →
    ∀ w ∈ C, ∀ a : (Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) → ℚ,
      (∀ u ∈ I, a u ≠ 0) →
      (∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) →
      componentCount I ≤ t * I.card + t

variable {t k V : ℕ}
variable {C : Set (Gram α (Qary.HeaderRecovery.windowLength k) → ℤ)}
variable (F : Facts t k V C)
include F

theorem adjoining_rule_component_sum
    (U : RuleSet α k) (w : Gram α (Qary.HeaderRecovery.windowLength k) → ℤ)
    (hw : w ∈ C) (hadj : ∃ u ∈ U, RuleAdjacent w u) :
    componentCount (insert w U) + 1 ≤ componentCount U + 2 * t := by
  classical
  obtain ⟨u, hu, v, hvw, hvu⟩ := hadj
  have hsub : ({u} : RuleSet α k) ⊆ U := by
    intro a ha
    have hau : a = u := Finset.mem_singleton.mp ha
    simpa only [hau] using hu
  have hmeet : ∃ v, Incident U v ∧ Incident {w} v :=
    ⟨v, Qary.ComponentBounds.incident_mono hsub hvu, hvw⟩
  have h := Qary.ComponentBounds.componentCount_union_add_one_le U {w} hmeet
  have heq : U ∪ {w} = insert w U := by
    ext a
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
    exact or_comm
  rw [heq] at h
  exact h.trans (Nat.add_le_add_left (F.components w hw) _)

/-- The first assertion of the manuscript's connected-block lemma. -/
theorem adjoining_rule_bound  (ht : 1 ≤ t)
    (U : RuleSet α k) (w : Gram α (Qary.HeaderRecovery.windowLength k) → ℤ)
    (hw : w ∈ C) (hadj : ∃ u ∈ U, RuleAdjacent w u) :
    componentCount (insert w U) ≤ componentCount U + (2 * t - 1) := by
  have h := adjoining_rule_component_sum F U w hw hadj
  omega

theorem connected_block_bound  (ht : 1 ≤ t) (B : RuleSet α k)
    (hB : B.Nonempty) (hcatalogue : ∀ w ∈ B, w ∈ C)
    (hconnected : Connected B) :
    componentCount B ≤ (2 * t - 1) * B.card + 1 := by
  classical
  apply FiniteConnectedGrowth.connected_count_bound B RuleAdjacent hB hconnected
    componentCount (2 * t) (by omega)
  · intro w hw
    exact F.components w (hcatalogue w hw)
  · intro U hUB w hwB _ hadj
    apply adjoining_rule_component_sum F U w (hcatalogue w hwB)
    obtain ⟨u, hu, hwu | huw⟩ := hadj
    · exact ⟨u, hu, hwu⟩
    · exact ⟨u, hu, huw.symm⟩

omit F in
private theorem seeded_frontier {k : ℕ} (U I S : RuleSet α k)
    (hcover : ∀ u ∈ U, ∃ i ∈ I,
      Relation.EqvGen (FiniteConnectedGrowth.Induced U RuleAdjacent) i u)
    (hIS : I ⊆ S) (hSU : S ⊆ U) (hne : S ≠ U) :
    ∃ w ∈ U, w ∉ S ∧ ∃ u ∈ S, RuleAdjacent w u ∨ RuleAdjacent u w := by
  classical
  by_contra hnone
  have preserve : ∀ a b,
      Relation.EqvGen (FiniteConnectedGrowth.Induced U RuleAdjacent) a b →
      (a ∈ S ↔ b ∈ S) := by
    intro a b hpath
    induction hpath with
    | rel a b hedge =>
      obtain ⟨haU, hbU, hr⟩ := hedge
      constructor
      · intro haS
        by_contra hbS
        exact hnone ⟨b, hbU, hbS, a, haS, Or.inr hr⟩
      · intro hbS
        by_contra haS
        exact hnone ⟨a, haU, haS, b, hbS, Or.inl hr⟩
    | refl a => exact Iff.rfl
    | symm a b h ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  have hUS : U ⊆ S := by
    intro u hu
    obtain ⟨i, hi, hpath⟩ := hcover u hu
    exact (preserve i u hpath).mp (hIS hi)
  exact hne (Finset.Subset.antisymm hSU hUS)

/-- The actual support-component increase when every retained rule is linked
to at least one seed rule by a path staying inside U. -/
theorem seeded_component_growth (ht : 1 ≤ t) (U I : RuleSet α k)
    (hIU : I ⊆ U) (hcat : ∀ w ∈ U, w ∈ C)
    (hcover : ∀ u ∈ U, ∃ i ∈ I,
      Relation.EqvGen (FiniteConnectedGrowth.Induced U RuleAdjacent) i u) :
    componentCount U ≤ componentCount I + (2 * t - 1) * (U.card - I.card) := by
  classical
  let d := 2 * t - 1
  let P : RuleSet α k → Prop := fun S =>
    componentCount S + d * I.card ≤ componentCount I + d * S.card
  have aux : ∀ n : ℕ, ∀ S : RuleSet α k, I ⊆ S → S ⊆ U → P S →
      U.card - S.card = n → P U := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hIS hSU hP hdiff
      by_cases heq : S = U
      · simpa only [heq] using hP
      · obtain ⟨w, hwU, hwS, hadj⟩ := seeded_frontier U I S hcover hIS hSU heq
        have hSU' : insert w S ⊆ U := Finset.insert_subset_iff.mpr ⟨hwU, hSU⟩
        have hIS' : I ⊆ insert w S := hIS.trans (Finset.subset_insert w S)
        have hstep : componentCount (insert w S) ≤ componentCount S + d := by
          apply adjoining_rule_bound F ht S w (hcat w hwU)
          obtain ⟨u, hu, hwu | huw⟩ := hadj
          · exact ⟨u, hu, hwu⟩
          · exact ⟨u, hu, huw.symm⟩
        have hcard : (insert w S).card = S.card + 1 := Finset.card_insert_of_notMem hwS
        have hP' : P (insert w S) := by
          change componentCount (insert w S) + d * I.card ≤
            componentCount I + d * (insert w S).card
          change componentCount S + d * I.card ≤ componentCount I + d * S.card at hP
          rw [hcard, Nat.mul_add, Nat.mul_one]
          omega
        have hbound : (insert w S).card ≤ U.card := Finset.card_le_card hSU'
        have hsmaller : U.card - (insert w S).card < n := by omega
        exact ih (U.card - (insert w S).card) hsmaller (insert w S)
          hIS' hSU' hP' rfl
  have hfinal := aux (U.card - I.card) I (by intro u hu; exact hu) hIU
    (by dsimp [P]; exact le_rfl) rfl
  change componentCount U + d * I.card ≤ componentCount I + d * U.card at hfinal
  have hcard := Finset.card_le_card hIU
  have hadd : I.card + (U.card - I.card) = U.card := by omega
  have hmul : d * U.card = d * I.card + d * (U.card - I.card) := by
    rw [← Nat.mul_add, hadd]
  rw [hmul] at hfinal
  change componentCount U ≤ componentCount I + d * (U.card - I.card)
  omega

/-- Savings from the relation survive adjoining all rules linked to its seeds. -/
theorem relation_seeded_bound (ht : 2 ≤ t) (U I : RuleSet α k)
    (hIU : I ⊆ U) (hI : 2 ≤ I.card) (hcat : ∀ u ∈ U, u ∈ C)
    (hcover : ∀ u ∈ U, ∃ i ∈ I,
      Relation.EqvGen (FiniteConnectedGrowth.Induced U RuleAdjacent) i u)
    (w : Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) (hw : w ∈ C)
    (a : (Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) → ℚ) (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    componentCount U ≤ (2 * t - 1) * U.card := by
  have hsave := F.savings I
    (fun u hu => hcat u (hIU hu)) w hw a ha hrel
  have hprod := Nat.mul_le_mul_left (t - 1) hI
  have hcoef : 2 * t - 1 = t + (t - 1) := by omega
  have hsmall : t * I.card + t ≤ (2 * t - 1) * I.card := by
    rw [hcoef, Nat.add_mul]
    omega
  have hseed : componentCount I ≤ (2 * t - 1) * I.card := hsave.trans hsmall
  have hgrowth := seeded_component_growth F (by omega : 1 ≤ t) U I hIU hcat hcover
  have hcard := Finset.card_le_card hIU
  have hadd : I.card + (U.card - I.card) = U.card := by omega
  calc
    componentCount U ≤ componentCount I + (2 * t - 1) * (U.card - I.card) := hgrowth
    _ ≤ (2 * t - 1) * I.card + (2 * t - 1) * (U.card - I.card) :=
      Nat.add_le_add_right hseed _
    _ = (2 * t - 1) * U.card := by rw [← Nat.mul_add, hadd]

open Qary.RelationBlockSavings

theorem relation_block_hull_bound  (ht : 2 ≤ t) (G I : RuleSet α k)
    (hIG : I ⊆ G) (hI : 2 ≤ I.card) (hcat : ∀ u ∈ G, u ∈ C)
    (w : Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) (hw : w ∈ C)
    (a : (Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) → ℚ) (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    componentCount (blockHull G I) ≤ (2 * t - 1) * (blockHull G I).card := by
  exact relation_seeded_bound F ht (blockHull G I) I (subset_blockHull G I hIG) hI
    (fun u hu => hcat u (blockHull_subset G I hu)) (blockHull_covered G I hIG)
    w hw a ha hrel

theorem new_relation_support  (ht : 1 ≤ t) (G : RuleSet α k)
    (hcat : ∀ u ∈ G, u ∈ C)
    (w : Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) (hw : w ∈ C)
    (hnew : ∀ u ∈ G, w ≠ u ∧ w ≠ -u)
    (hspan : rational w ∈ Submodule.span ℚ (rational '' (↑G : Set _))) :
    ∃ I : RuleSet α k, I ⊆ G ∧ 2 ≤ I.card ∧
      ∃ a : (Gram α (Qary.HeaderRecovery.windowLength k) → ℤ) → ℚ,
        (∀ u ∈ I, a u ≠ 0) ∧
        ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ) := by
  classical
  obtain ⟨a, hsum⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' ℚ).mp hspan
  let I := G.filter (fun u => a u ≠ 0)
  have hIG : I ⊆ G := Finset.filter_subset _ _
  have ha : ∀ u ∈ I, a u ≠ 0 := fun u hu => (Finset.mem_filter.mp hu).2
  have hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ) := by
    intro g
    have h := congrFun hsum g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rational] at h
    rw [← h]
    symm
    apply Finset.sum_subset hIG
    intro u huG huI
    have hz : a u = 0 := by
      by_contra hne
      exact huI (Finset.mem_filter.mpr ⟨huG, hne⟩)
    simp [hz]
  have hcard : 2 ≤ I.card := by
    by_contra hnot
    have hsmall : I.card ≤ 1 := by omega
    by_cases hzero : I.card = 0
    · have hIempty := Finset.card_eq_zero.mp hzero
      have hwzero : w = 0 := by
        funext g
        have h := hrel g
        simp only [hIempty, Finset.sum_empty] at h
        exact_mod_cast h
      exact F.nonzero w hw hwzero
    · have hone : I.card = 1 := by omega
      obtain ⟨u, hI⟩ := Finset.card_eq_one.mp hone
      have huI : u ∈ I := by rw [hI]; exact Finset.mem_singleton_self u
      have huG := hIG huI
      have hlinear : rational w = a u • rational u := by
        funext g
        simpa only [hI, Finset.sum_singleton, rational, Pi.smul_apply, smul_eq_mul]
          using hrel g
      have hu0 : rational u ≠ 0 := by
        intro hu0
        apply F.nonzero u (hcat u huG)
        exact rational_injective (hu0.trans rational_zero.symm)
      rcases Qary.WitnessAlgebra.scalar_multiple_eq_or_neg (rational u) (rational w) (a u)
        (F.signed u (hcat u huG)) (F.signed w hw)
        hu0 (ha u huI) hlinear with heq | heq
      · exact (hnew u huG).1 (rational_injective heq)
      · exact (hnew u huG).2 (rational_injective (heq.trans (rational_neg u).symm))
  exact ⟨I, hIG, hcard, a, ha, hrel⟩


#print axioms adjoining_rule_bound
#print axioms connected_block_bound
#print axioms relation_block_hull_bound
#print axioms new_relation_support

end DeletionCode.Burst.CatalogueBounds
