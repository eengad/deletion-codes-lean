import DeletionCode.RelationSavings
import DeletionCode.FiniteConnectedGrowth

/-!
The component estimate in the relation case of the bounded-witness argument.
Starting from the rules participating in the relation, every remaining member
of their whole ambient blocks can be added along actual rule adjacencies.
The finite growth argument is proved here; no ordering or component estimate
is supplied as an assumption.
-/
namespace DeletionCode.RelationBlockSavings

open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators

private theorem seeded_frontier {k : ℕ} (U I S : RuleSet k)
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
theorem seeded_component_growth {t k : ℕ} (ht : 1 ≤ t) (U I : RuleSet k)
    (hIU : I ⊆ U) (hcat : ∀ w ∈ U, CatalogueRule t k w)
    (hcover : ∀ u ∈ U, ∃ i ∈ I,
      Relation.EqvGen (FiniteConnectedGrowth.Induced U RuleAdjacent) i u) :
    componentCount U ≤ componentCount I + (2 * t - 1) * (U.card - I.card) := by
  classical
  let d := 2 * t - 1
  let P : RuleSet k → Prop := fun S =>
    componentCount S + d * I.card ≤ componentCount I + d * S.card
  have aux : ∀ n : ℕ, ∀ S : RuleSet k, I ⊆ S → S ⊆ U → P S →
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
          apply adjoining_rule_bound ht S w (hcat w hwU)
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
theorem relation_seeded_bound {t k : ℕ} (ht : 2 ≤ t) (U I : RuleSet k)
    (hIU : I ⊆ U) (hI : 2 ≤ I.card) (hcat : ∀ u ∈ U, CatalogueRule t k u)
    (hcover : ∀ u ∈ U, ∃ i ∈ I,
      Relation.EqvGen (FiniteConnectedGrowth.Induced U RuleAdjacent) i u)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ) (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    componentCount U ≤ (2 * t - 1) * U.card := by
  have hsave := RelationSavings.savings_from_relation I
    (fun u hu => hcat u (hIU hu)) w hw a ha hrel
  have hprod := Nat.mul_le_mul_left (t - 1) hI
  have hcoef : 2 * t - 1 = t + (t - 1) := by omega
  have hsmall : t * I.card + t ≤ (2 * t - 1) * I.card := by
    rw [hcoef, Nat.add_mul]
    omega
  have hseed : componentCount I ≤ (2 * t - 1) * I.card := hsave.trans hsmall
  have hgrowth := seeded_component_growth (by omega : 1 ≤ t) U I hIU hcat hcover
  have hcard := Finset.card_le_card hIU
  have hadd : I.card + (U.card - I.card) = U.card := by omega
  calc
    componentCount U ≤ componentCount I + (2 * t - 1) * (U.card - I.card) := hgrowth
    _ ≤ (2 * t - 1) * I.card + (2 * t - 1) * (U.card - I.card) :=
      Nat.add_le_add_right hseed _
    _ = (2 * t - 1) * U.card := by rw [← Nat.mul_add, hadd]

/-- The actual finite union of ambient rule blocks meeting I. -/
noncomputable def blockHull {k : ℕ} (G I : RuleSet k) : RuleSet k := by
  classical
  exact G.filter (fun u => ∃ i ∈ I,
    Relation.EqvGen (FiniteConnectedGrowth.Induced G RuleAdjacent) i u)

theorem blockHull_subset {k : ℕ} (G I : RuleSet k) : blockHull G I ⊆ G := by
  classical
  exact Finset.filter_subset _ _

theorem subset_blockHull {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G) : I ⊆ blockHull G I := by
  classical
  intro i hi
  exact Finset.mem_filter.mpr ⟨hIG hi, i, hi, Relation.EqvGen.refl i⟩

private theorem induced_mem_iff {k : ℕ} (G : RuleSet k)
    {a b : Gram (windowLength k) → ℤ}
    (h : Relation.EqvGen (FiniteConnectedGrowth.Induced G RuleAdjacent) a b) :
    a ∈ G ↔ b ∈ G := by
  induction h with
  | rel a b hab => exact ⟨fun _ => hab.2.1, fun _ => hab.1⟩
  | refl a => exact Iff.rfl
  | symm a b h ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

theorem blockHull_closed {k : ℕ} (G I : RuleSet k)
    {a b : Gram (windowLength k) → ℤ} (ha : a ∈ blockHull G I)
    (hpath : Relation.EqvGen (FiniteConnectedGrowth.Induced G RuleAdjacent) a b) :
    b ∈ blockHull G I := by
  classical
  obtain ⟨haG, i, hi, hia⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨(induced_mem_iff G hpath).mp haG,
    i, hi, Relation.EqvGen.trans i a b hia hpath⟩

private theorem blockHull_path {k : ℕ} (G I : RuleSet k)
    {a b : Gram (windowLength k) → ℤ}
    (hpath : Relation.EqvGen (FiniteConnectedGrowth.Induced G RuleAdjacent) a b) :
    a ∈ blockHull G I →
      Relation.EqvGen (FiniteConnectedGrowth.Induced (blockHull G I) RuleAdjacent) a b := by
  induction hpath with
  | rel a b hab =>
    intro ha
    exact Relation.EqvGen.rel a b
      ⟨ha, blockHull_closed G I ha (Relation.EqvGen.rel a b hab), hab.2.2⟩
  | refl a => intro _; exact Relation.EqvGen.refl a
  | symm a b h ih =>
    intro hb
    have ha := blockHull_closed G I hb (Relation.EqvGen.symm a b h)
    exact Relation.EqvGen.symm a b (ih ha)
  | trans a b c hab hbc ihab ihbc =>
    intro ha
    exact Relation.EqvGen.trans a b c (ihab ha) (ihbc (blockHull_closed G I ha hab))

theorem blockHull_covered {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G) :
    ∀ u ∈ blockHull G I, ∃ i ∈ I,
      Relation.EqvGen (FiniteConnectedGrowth.Induced (blockHull G I) RuleAdjacent) i u := by
  classical
  intro u hu
  obtain ⟨_, i, hi, hpath⟩ := Finset.mem_filter.mp hu
  exact ⟨i, hi, blockHull_path G I hpath (subset_blockHull G I hIG hi)⟩

/-- The component estimate for the relation case of the bounded-witness proof,
applied to the union of whole ambient blocks that meet the relation support. -/
theorem relation_block_hull_bound {t k : ℕ} (ht : 2 ≤ t) (G I : RuleSet k)
    (hIG : I ⊆ G) (hI : 2 ≤ I.card) (hcat : ∀ u ∈ G, CatalogueRule t k u)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ) (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    componentCount (blockHull G I) ≤ (2 * t - 1) * (blockHull G I).card := by
  exact relation_seeded_bound ht (blockHull G I) I (subset_blockHull G I hIG) hI
    (fun u hu => hcat u (blockHull_subset G I hu)) (blockHull_covered G I hIG)
    w hw a ha hrel

#print axioms seeded_component_growth
#print axioms relation_seeded_bound
#print axioms blockHull_covered
#print axioms relation_block_hull_bound

end DeletionCode.RelationBlockSavings
