import DeletionCode.ComponentBounds
import DeletionCode.CatalogueBridge
import DeletionCode.FiniteConnectedGrowth

/-!
The manuscript's connected-block lemma for actual signed catalogue rules.
Rule adjacency means that the two signed supports share an incident de Bruijn
vertex. The component count is RuleSetGraph.componentCount, computed from the
nonzero support union, and the number of rules is the cardinality of the rule
set itself. No generating order, independence, or assumed component bound is used.
-/
namespace DeletionCode.ConnectedBlocks

open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph

/-- Actual support adjacency, including endpoints of bubble paths. -/
def RuleAdjacent {L : ℕ} (w u : Gram L → ℤ) : Prop :=
  ∃ v, Incident {w} v ∧ Incident {u} v

theorem RuleAdjacent.symm {L : ℕ} {w u : Gram L → ℤ}
    (h : RuleAdjacent w u) : RuleAdjacent u w := by
  obtain ⟨v, hw, hu⟩ := h
  exact ⟨v, hu, hw⟩

/-- A concrete presentation of a catalogue vector by exactly 2t bubbles.
The local words and all catalogue geometry are explicit, including t bubbles
in each orientation. -/
def CatalogueRule (t k : ℕ) (w : Gram (windowLength k) → ℤ) : Prop :=
  ∃ words : Fin (2 * t) → BubbleWord k,
    ValidCatalogue words (fun _ => (0 : Fin 1)) ∧
    OrientationBalanced t words (fun _ => (0 : Fin 1)) ∧
    ruleSpectrum (indexedFamily words (fun _ => (0 : Fin 1))).family
      (windowLength k) Finset.univ = w

private theorem singleton_rules {t k : ℕ} (words : Fin (2 * t) → BubbleWord k)
    (w : Gram (windowLength k) → ℤ)
    (hvalue : ruleSpectrum (indexedFamily words (fun _ => (0 : Fin 1))).family
      (windowLength k) Finset.univ = w) :
    rulesOfFamily (indexedFamily words (fun _ => (0 : Fin 1)))
      (fun _ => (0 : Fin 1)) = {w} := by
  classical
  have hgroup (r : Fin 1) :
      groupBubbles (fun _ : Fin (2 * t) => (0 : Fin 1)) r = Finset.univ := by
    have hr : r = 0 := Subsingleton.elim _ _
    subst r
    simp [groupBubbles]
  ext f
  simp only [rulesOfFamily, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨r, hf⟩
    rw [hgroup r, hvalue] at hf
    exact hf.symm
  · intro hf
    refine ⟨0, ?_⟩
    rw [hgroup 0, hvalue, hf]

/-- A catalogue rule has at most 2t components of its actual signed support.
This follows from the proved support-graph equivalence and its 2t path bubbles. -/
theorem catalogue_singleton_component_count_le {t k : ℕ}
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w) :
    componentCount {w} ≤ 2 * t := by
  obtain ⟨words, hvalid, _, hvalue⟩ := hw
  rw [← singleton_rules words w hvalue]
  rw [componentCount_rulesOfFamily
    (indexedFamily words (fun _ => (0 : Fin 1))) (fun _ => (0 : Fin 1))
    (fun _ => rfl) hvalid.geometry hvalid.rank_disjoint]
  exact GeneratingCount.editedFamily_component_count_le
    (indexedFamily words (fun _ => (0 : Fin 1)))

/-- A rule meeting the old support union saves one of its possible 2t components. -/
theorem adjoining_rule_component_sum {t k : ℕ}
    (U : RuleSet k) (w : Gram (windowLength k) → ℤ)
    (hw : CatalogueRule t k w) (hadj : ∃ u ∈ U, RuleAdjacent w u) :
    componentCount (insert w U) + 1 ≤ componentCount U + 2 * t := by
  classical
  obtain ⟨u, hu, v, hvw, hvu⟩ := hadj
  have hsub : ({u} : RuleSet k) ⊆ U := by
    intro a ha
    have hau : a = u := Finset.mem_singleton.mp ha
    simpa only [hau] using hu
  have hmeet : ∃ v, Incident U v ∧ Incident {w} v :=
    ⟨v, ComponentBounds.incident_mono hsub hvu, hvw⟩
  have h := ComponentBounds.componentCount_union_add_one_le U {w} hmeet
  have heq : U ∪ {w} = insert w U := by
    ext a
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
    exact or_comm
  rw [heq] at h
  exact h.trans (Nat.add_le_add_left (catalogue_singleton_component_count_le w hw) _)

/-- The first assertion of the manuscript's connected-block lemma. -/
theorem adjoining_rule_bound {t k : ℕ} (ht : 1 ≤ t)
    (U : RuleSet k) (w : Gram (windowLength k) → ℤ)
    (hw : CatalogueRule t k w) (hadj : ∃ u ∈ U, RuleAdjacent w u) :
    componentCount (insert w U) ≤ componentCount U + (2 * t - 1) := by
  have h := adjoining_rule_component_sum U w hw hadj
  omega

/-- Connectedness is restricted to rules of B: intermediate rules outside B
cannot serve as a connecting path. -/
def Connected {k : ℕ} (B : RuleSet k) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B,
    Relation.EqvGen (FiniteConnectedGrowth.Induced B RuleAdjacent) a b

/-- Every nonempty connected block of catalogue rules satisfies
c(B) ≤ (2t−1)|B|+1, with c(B) intrinsic to its signed support union. -/
theorem connected_block_bound {t k : ℕ} (ht : 1 ≤ t) (B : RuleSet k)
    (hB : B.Nonempty) (hcatalogue : ∀ w ∈ B, CatalogueRule t k w)
    (hconnected : Connected B) :
    componentCount B ≤ (2 * t - 1) * B.card + 1 := by
  classical
  apply FiniteConnectedGrowth.connected_count_bound B RuleAdjacent hB hconnected
    componentCount (2 * t) (by omega)
  · intro w hw
    exact catalogue_singleton_component_count_le w (hcatalogue w hw)
  · intro U hUB w hwB _ hadj
    apply adjoining_rule_component_sum U w (hcatalogue w hwB)
    obtain ⟨u, hu, hwu | huw⟩ := hadj
    · exact ⟨u, hu, hwu⟩
    · exact ⟨u, hu, huw.symm⟩

#print axioms catalogue_singleton_component_count_le
#print axioms adjoining_rule_component_sum
#print axioms adjoining_rule_bound
#print axioms connected_block_bound

end DeletionCode.ConnectedBlocks
