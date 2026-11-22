import DeletionCode.Explicit.Borrowed.Catalogue
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Basic

/-! A finite check for the existing bubble and catalogue predicates. -/

namespace DeletionCode.Explicit.Borrowed.Catalogue

open Qary.SignedSupport Qary.SupportComponents
open Qary.RootSelection (Family)
open Qary.RuleReconstruction (groupBubbles)

variable {α : Type*} [Inhabited α] [DecidableEq α]
variable {K b L ν R : ℕ}

/-- Vertex offsets run from zero to one past the last gram offset. -/
private abbrev VertexIndex (F : Family α (Fin ν)) (j : Fin ν) (side : Bool) :=
  Fin (F.extra j side + 2)

private def localValid (F : Family α (Fin ν)) (L : ℕ) (j : Fin ν) : Bool :=
  decide (∀ side : Bool, ∀ i k : VertexIndex F j side,
    vertex F L j side i.val = vertex F L j side k.val → i = k) &&
  decide (∀ (i : VertexIndex F j false) (k : VertexIndex F j true),
    vertex F L j false i.val = vertex F L j true k.val →
      (i.val = 0 ∧ k.val = 0) ∨ (i.val = F.extra j false+1 ∧ k.val = F.extra j true+1)) &&
  decide (F.extra j false ≠ 0 ∨ F.extra j true ≠ 0) &&
  decide (vertex F L j false 0 = vertex F L j true 0) &&
  decide (vertex F L j false (F.extra j false+1) = vertex F L j true (F.extra j true+1))

private def disjointValid (F : Family α (Fin ν)) (L : ℕ)
    (group : Fin ν → Fin R) : Bool :=
  decide (∀ (i j : Fin ν), group i = group j → i ≠ j →
    ∀ sa sb : Bool, ∀ (a : VertexIndex F i sa) (b : VertexIndex F j sb),
      vertex F L i sa a.val ≠ vertex F L j sb b.val)

def validCheck (words : Fin ν → BubbleWord α K b L) (group : Fin ν → Fin R) : Bool :=
  let F := indexedFamily words group
  (List.finRange ν).all (fun j =>
    decide (∀ side : Bool, L ≤ (pathWord (words j) side).length) && localValid F L j) &&
    disjointValid F L group

theorem validCheck_iff (words : Fin ν → BubbleWord α K b L) (group : Fin ν → Fin R) :
    validCheck words group = true ↔ ValidCatalogue words group := by
  let F := indexedFamily words group
  constructor
  · intro h
    obtain ⟨localChecks,disj⟩ := Bool.and_eq_true_iff.mp h
    have atIndex (j : Fin ν) := Bool.and_eq_true_iff.mp (List.all_eq_true.mp localChecks j (List.mem_finRange j))
    have geom (j : Fin ν) := (atIndex j).2
    refine ⟨fun j => of_decide_eq_true (atIndex j).1,⟨?_,?_,?_⟩,?_,?_,?_⟩
    · intro j side i k he
      have hh := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (geom j)).1).1).1).1
      exact of_decide_eq_true hh side i k he
    · intro j i k hi hk he
      have hh := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (geom j)).1).1).1).2
      exact of_decide_eq_true hh ⟨i,by omega⟩ ⟨k,by omega⟩ he
    · intro j
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (geom j)).1).1).2
    · intro j
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (geom j)).1).2
    · intro j
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp (geom j)).2
    · intro r i hi j hj hne sa sb a b ha hb
      have hgroup : group i = group j :=
        ((Finset.mem_filter.mp hi).2).trans ((Finset.mem_filter.mp hj).2).symm
      exact of_decide_eq_true disj i j hgroup hne sa sb ⟨a,by omega⟩ ⟨b,by omega⟩
  · intro h
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply List.all_eq_true.mpr
      intro j _
      change (decide (∀ side : Bool, L ≤ (pathWord (words j) side).length) && localValid F L j) = true
      refine Bool.and_eq_true_iff.mpr ⟨decide_eq_true (h.length_lower j),?_⟩
      unfold localValid
      simp only [Bool.and_eq_true_iff,decide_eq_true_eq]
      exact ⟨⟨⟨⟨fun side i k he => h.geometry.simple j side (a₁ := i) (a₂ := k) he,
          fun i k => h.geometry.endpoints j i.val k.val (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ k.isLt)⟩,
        h.geometry.notBothSingle j⟩,h.common_start j⟩,h.common_end j⟩
    · apply decide_eq_true
      intro i j hgroup hne sa sb a b
      exact h.within_rule_disjoint (group i) i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩)
        j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hgroup.symm⟩) hne sa sb a.val b.val
        (by omega) (by omega)

#print axioms validCheck_iff

end DeletionCode.Explicit.Borrowed.Catalogue
