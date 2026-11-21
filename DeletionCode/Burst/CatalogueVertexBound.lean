import DeletionCode.Burst.Catalogue
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
A vertex bound for the actual signed support of one catalogue rule. A bubble's
two paths share their initial vertex. Naming every negative-path vertex and
every positive-path vertex except its initial one therefore covers its full
vertex set using at most 2L+2b+1 names. For 2t bubbles this gives at most
2t(2L+2b+1) actual incident vertices. This deliberately loose bound counts the
shared terminal vertex twice and also allows other repeated names and vertices.
-/
namespace DeletionCode.Burst.CatalogueVertexBound

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

open Qary.Windows Qary.RootSelection Qary.SignedSupport Qary.RuleSetGraph Qary.SupportComponents
open Catalogue FamilySupport
open scoped BigOperators

/-- One shared initial vertex need only be named on the negative path. -/
abbrev VertexNames {t k b : ℕ} (words : Fin (2 * t) → BubbleWord α k b) :=
  Σ j : Fin (2 * t),
    Fin ((indexedFamily words (fun _ => (0 : Fin 1))).extra j false + 2) ⊕ Fin ((indexedFamily words (fun _ => (0 : Fin 1))).extra j true + 1)

def namedVertex {t k b : ℕ} (words : Fin (2 * t) → BubbleWord α k b) :
    VertexNames words → SupportedVertex (indexedFamily words (fun _ => (0 : Fin 1))) (windowLength k b)
  | ⟨j, Sum.inl i⟩ => ⟨vertex (indexedFamily words (fun _ => (0 : Fin 1))) (windowLength k b) j false i.val,
      j, false, i.val, by have := i.isLt; omega, rfl⟩
  | ⟨j, Sum.inr i⟩ => ⟨vertex (indexedFamily words (fun _ => (0 : Fin 1))) (windowLength k b) j true (i.val + 1),
      j, true, i.val + 1, by have := i.isLt; omega, rfl⟩

theorem namedVertex_surjective {t k b : ℕ} (words : Fin (2 * t) → BubbleWord α k b)
    (hv : ValidCatalogue words (fun _ => (0 : Fin 1))) :
    Function.Surjective (namedVertex words) := by
  intro v
  obtain ⟨j, side, i, hi, hjv⟩ := v.property
  cases side with
  | false =>
    refine ⟨⟨j, Sum.inl ⟨i, by omega⟩⟩, ?_⟩
    apply Subtype.ext
    exact hjv.symm
  | true =>
    by_cases hzero : i = 0
    · subst i
      refine ⟨⟨j, Sum.inl ⟨0, by omega⟩⟩, ?_⟩
      apply Subtype.ext
      change vertex (indexedFamily words (fun _ => (0 : Fin 1))) (windowLength k b) j false 0 = v.val
      rw [hv.common_start j]
      exact hjv.symm
    · refine ⟨⟨j, Sum.inr ⟨i - 1, by omega⟩⟩, ?_⟩
      apply Subtype.ext
      change vertex (indexedFamily words (fun _ => (0 : Fin 1))) (windowLength k b) j true (i - 1 + 1) = v.val
      have hindex : i - 1 + 1 = i := by omega
      rw [hindex]
      exact hjv.symm

/-- The two path lengths give at most 2L+2b+1 vertex names per bubble. -/
theorem bubble_vertex_names_le {t k b : ℕ} (words : Fin (2 * t) → BubbleWord α k b)
    (j : Fin (2 * t)) :
    (indexedFamily words (fun _ => (0 : Fin 1))).extra j false + 2 +
      ((indexedFamily words (fun _ => (0 : Fin 1))).extra j true + 1) ≤
        2 * windowLength k b + 2 * b + 1 := by
  have hn := word_length_bounds (words j) false
  have hp := word_length_bounds (words j) true
  have hL : 1 ≤ windowLength k b := by unfold windowLength; omega
  simp only [indexedFamily, family]
  omega

theorem supported_vertex_count_le {t k b : ℕ} (words : Fin (2 * t) → BubbleWord α k b)
    (hv : ValidCatalogue words (fun _ => (0 : Fin 1))) :
    Nat.card (SupportedVertex (indexedFamily words (fun _ => (0 : Fin 1))) (windowLength k b)) ≤
      2 * t * (2 * windowLength k b + 2 * b + 1) := by
  classical
  letI : Fintype (SupportedVertex (indexedFamily words (fun _ => (0 : Fin 1))) (windowLength k b)) := by
    unfold SupportedVertex
    infer_instance
  have hnames : Fintype.card (VertexNames words) ≤ (2 * t) * (2 * windowLength k b + 2 * b + 1) := by
    rw [Fintype.card_sigma]
    calc
      (∑ j : Fin (2 * t),
          Fintype.card (Fin ((indexedFamily words (fun _ => (0 : Fin 1))).extra j false + 2) ⊕
            Fin ((indexedFamily words (fun _ => (0 : Fin 1))).extra j true + 1))) ≤
          ∑ _b : Fin (2 * t), (2 * windowLength k b + 2 * b + 1) := by
        apply Finset.sum_le_sum
        intro j hj
        simpa only [Fintype.card_sum, Fintype.card_fin] using bubble_vertex_names_le words j
      _ = (2 * t) * (2 * windowLength k b + 2 * b + 1) := by simp
  have hcard := Fintype.card_le_of_surjective (namedVertex words) (namedVertex_surjective words hv)
  calc
    Nat.card (SupportedVertex (indexedFamily words (fun _ => (0 : Fin 1))) (windowLength k b)) =
        Fintype.card (SupportedVertex (indexedFamily words (fun _ => (0 : Fin 1))) (windowLength k b)) := Nat.card_eq_fintype_card
    _ ≤ (2 * t) * (2 * windowLength k b + 2 * b + 1) := hcard.trans hnames

/-- The finite vertex type is the actual incident-vertex set of the rule's
nonzero signed support, not a count attached to a chosen presentation. -/
theorem catalogue_vertex_card_le {t k b : ℕ}
    (w : Gram α (windowLength k b) → ℤ) (hw : Rule t k b w) :
    Fintype.card (RuleSetVertex {w}) ≤ 2 * t * (2 * windowLength k b + 2 * b + 1) := by
  obtain ⟨words, hv, _, heq⟩ := hw
  let F := indexedFamily words (fun _ => (0 : Fin 1))
  let e : RuleSetVertex {w} ≃ SupportedVertex F (windowLength k b) := by
    rw [← Catalogue.singleton_rules words w heq]
    exact incidentVertexEquiv F (fun _ => (0 : Fin 1)) (fun _ => rfl)
      hv.geometry hv.rank_disjoint
  calc
    Fintype.card (RuleSetVertex {w}) = Nat.card (RuleSetVertex {w}) :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card (SupportedVertex F (windowLength k b)) := Nat.card_congr e
    _ ≤ 2 * t * (2 * windowLength k b + 2 * b + 1) := supported_vertex_count_le words hv

#print axioms namedVertex_surjective
#print axioms bubble_vertex_names_le
#print axioms supported_vertex_count_le
#print axioms catalogue_vertex_card_le

end DeletionCode.Burst.CatalogueVertexBound
