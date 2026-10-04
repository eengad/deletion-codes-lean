import DeletionCode.ConnectedBlocks
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
A vertex bound for the actual signed support of one catalogue rule. A bubble's
two paths share their initial vertex. Naming every negative-path vertex and
every positive-path vertex except its initial one therefore covers its full
vertex set using at most 2L names. For 2t bubbles this gives at most 4tL actual
incident vertices. The bound deliberately allows repeated names and vertices.
-/
namespace DeletionCode.CatalogueVertexBound

open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport RuleReconstruction RuleSetGraph SupportComponents ConnectedBlocks
open scoped BigOperators

/-- One shared initial vertex need only be named on the negative path. -/
abbrev VertexNames {t k : ℕ} (E : EditedFamily (Fin (2 * t)) k) :=
  Σ b : Fin (2 * t),
    Fin (E.family.extra b false + 2) ⊕ Fin (E.family.extra b true + 1)

def namedVertex {t k : ℕ} (E : EditedFamily (Fin (2 * t)) k) :
    VertexNames E → SupportedVertex E.family (windowLength k)
  | ⟨b, Sum.inl i⟩ => ⟨vertex E.family (windowLength k) b false i.val,
      b, false, i.val, by have := i.isLt; omega, rfl⟩
  | ⟨b, Sum.inr i⟩ => ⟨vertex E.family (windowLength k) b true (i.val + 1),
      b, true, i.val + 1, by have := i.isLt; omega, rfl⟩

theorem namedVertex_surjective {t k : ℕ} (E : EditedFamily (Fin (2 * t)) k) :
    Function.Surjective (namedVertex E) := by
  intro v
  obtain ⟨b, side, i, hi, hv⟩ := v.property
  cases side with
  | false =>
    refine ⟨⟨b, Sum.inl ⟨i, by omega⟩⟩, ?_⟩
    apply Subtype.ext
    exact hv.symm
  | true =>
    by_cases hzero : i = 0
    · subst i
      refine ⟨⟨b, Sum.inl ⟨0, by omega⟩⟩, ?_⟩
      apply Subtype.ext
      change vertex E.family (windowLength k) b false 0 = v.val
      rw [GeneratingRecovery.initial_vertices_agree E b]
      exact hv.symm
    · refine ⟨⟨b, Sum.inr ⟨i - 1, by omega⟩⟩, ?_⟩
      apply Subtype.ext
      change vertex E.family (windowLength k) b true (i - 1 + 1) = v.val
      have hindex : i - 1 + 1 = i := by omega
      rw [hindex]
      exact hv.symm

/-- The two path lengths and rho ≥ 1 give at most 2L vertex names per bubble. -/
theorem bubble_vertex_names_le {t k : ℕ} (E : EditedFamily (Fin (2 * t)) k)
    (b : Fin (2 * t)) :
    E.family.extra b false + 2 + (E.family.extra b true + 1) ≤ 2 * windowLength k := by
  have hlo := E.rho_lower b
  have hhi := E.rho_upper b
  cases ho : (E.header b).orientation <;>
    simp only [EditedFamily.family, PathMemory.pathLength, Bool.false_eq_true,
      ite_false, ite_true, negativeLength, positiveLength, shortLength, longLength,
      windowLength, ho] <;> omega

theorem supported_vertex_count_le {t k : ℕ} (E : EditedFamily (Fin (2 * t)) k) :
    Nat.card (SupportedVertex E.family (windowLength k)) ≤ 4 * t * windowLength k := by
  classical
  letI : Fintype (SupportedVertex E.family (windowLength k)) := by
    unfold SupportedVertex
    infer_instance
  have hnames : Fintype.card (VertexNames E) ≤ (2 * t) * (2 * windowLength k) := by
    rw [Fintype.card_sigma]
    calc
      (∑ b : Fin (2 * t),
          Fintype.card (Fin (E.family.extra b false + 2) ⊕
            Fin (E.family.extra b true + 1))) ≤
          ∑ _b : Fin (2 * t), 2 * windowLength k := by
        apply Finset.sum_le_sum
        intro b hb
        simpa only [Fintype.card_sum, Fintype.card_fin] using bubble_vertex_names_le E b
      _ = (2 * t) * (2 * windowLength k) := by simp
  have hcard := Fintype.card_le_of_surjective (namedVertex E) (namedVertex_surjective E)
  calc
    Nat.card (SupportedVertex E.family (windowLength k)) =
        Fintype.card (SupportedVertex E.family (windowLength k)) := Nat.card_eq_fintype_card
    _ ≤ (2 * t) * (2 * windowLength k) := hcard.trans hnames
    _ = 4 * t * windowLength k := by ring

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

/-- The finite vertex type is the actual incident-vertex set of the rule's
nonzero signed support, not a count attached to a chosen presentation. -/
theorem catalogue_vertex_card_le {t k : ℕ}
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w) :
    Fintype.card (RuleSetVertex {w}) ≤ 4 * t * windowLength k := by
  obtain ⟨words, hvalid, _, hvalue⟩ := hw
  let E := indexedFamily words (fun _ => (0 : Fin 1))
  have hQ : rulesOfFamily E (fun _ => (0 : Fin 1)) = {w} :=
    singleton_rules words w hvalue
  let e : RuleSetVertex {w} ≃ SupportedVertex E.family (windowLength k) := by
    rw [← hQ]
    exact incidentVertexEquiv E (fun _ => (0 : Fin 1)) (fun _ => rfl)
      hvalid.geometry hvalid.rank_disjoint
  calc
    Fintype.card (RuleSetVertex {w}) = Nat.card (RuleSetVertex {w}) :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card (SupportedVertex E.family (windowLength k)) := Nat.card_congr e
    _ ≤ 4 * t * windowLength k := supported_vertex_count_le E

#print axioms namedVertex_surjective
#print axioms bubble_vertex_names_le
#print axioms supported_vertex_count_le
#print axioms catalogue_vertex_card_le

end DeletionCode.CatalogueVertexBound
