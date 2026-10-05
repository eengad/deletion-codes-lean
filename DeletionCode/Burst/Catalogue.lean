import DeletionCode.Burst.BubbleWords
import DeletionCode.Burst.FamilySupport
import DeletionCode.Qary.WitnessAlgebra
import DeletionCode.Qary.CanonicalIndex
import DeletionCode.Qary.CatalogueAlgebra
import Mathlib.Data.Fintype.Sigma

/-!
The fixed catalogue of whole substring-replacement bubbles. The underlying
words, path geometry, within-rule disjointness and total length balance are
part of its definition. No hash or chosen generating history enters it.
-/
namespace DeletionCode.Burst.Catalogue

open Qary.Windows
open Qary.CatalogueWords (listLetters)
open Qary.RootSelection Qary.SignedSupport Qary.SupportComponents Qary.RuleSetGraph
open Qary.RuleReconstruction (groupBubbles)
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

def pathWord {k b : ℕ} (p : BubbleWord α k b) (side : Bool) : List α :=
  if side then p.positiveWord else p.negativeWord

def family {B : Type*} {k b : ℕ} (words : B → BubbleWord α k b)
    (rank : B → ℕ) : Family α B where
  rank := rank
  path i side := listLetters (pathWord (words i) side)
  extra i side := (pathWord (words i) side).length - windowLength k b

def indexedFamily {k b ν R : ℕ} (words : Fin ν → BubbleWord α k b)
    (group : Fin ν → Fin R) : Family α (Fin ν) := family words (fun i => (group i).val)

theorem word_length_bounds {k b : ℕ} (p : BubbleWord α k b) (side : Bool) :
    windowLength k b ≤ (pathWord p side).length ∧
      (pathWord p side).length ≤ 2 * (windowLength k b - 1) + b := by
  cases side
  · exact p.negativeWord_length_bounds
  · exact p.positiveWord_length_bounds

theorem path_length_eq {B : Type*} {k b : ℕ} (words : B → BubbleWord α k b)
    (rank : B → ℕ) (i : B) (side : Bool) :
    (pathWord (words i) side).length = windowLength k b + (family words rank).extra i side := by
  have h := (word_length_bounds (words i) side).1
  simp only [family]
  omega

theorem notBothSingle {B : Type*} {k b : ℕ} (words : B → BubbleWord α k b)
    (rank : B → ℕ) (i : B) :
    (family words rank).extra i false ≠ 0 ∨ (family words rank).extra i true ≠ 0 := by
  left
  have hl := (words i).left_lower
  have hr := (words i).right_lower
  simp only [family, pathWord, Bool.false_eq_true, ite_false, BubbleWord.negativeWord,
    List.length_append]
  unfold windowLength at *
  omega

structure ValidCatalogue {k b ν R : ℕ}
    (words : Fin ν → BubbleWord α k b) (group : Fin ν → Fin R) : Prop where
  geometry : BubbleGeometry (indexedFamily words group) (windowLength k b)
  common_start : ∀ i, vertex (indexedFamily words group) (windowLength k b) i false 0 =
    vertex (indexedFamily words group) (windowLength k b) i true 0
  common_end : ∀ i,
    vertex (indexedFamily words group) (windowLength k b) i false
      ((indexedFamily words group).extra i false + 1) =
    vertex (indexedFamily words group) (windowLength k b) i true
      ((indexedFamily words group).extra i true + 1)
  within_rule_disjoint : ∀ r : Fin R,
    VertexDisjointOn (indexedFamily words group) (windowLength k b) (groupBubbles group r)

def Balanced {k b ν R : ℕ} (words : Fin ν → BubbleWord α k b)
    (group : Fin ν → Fin R) : Prop :=
  ∀ r : Fin R,
    (∑ i ∈ groupBubbles group r, (words i).negativeWord.length) =
      ∑ i ∈ groupBubbles group r, (words i).positiveWord.length

theorem ValidCatalogue.rank_disjoint {k b ν R : ℕ}
    {words : Fin ν → BubbleWord α k b} {group : Fin ν → Fin R}
    (h : ValidCatalogue words group) :
    ∀ j, VertexDisjointOn (indexedFamily words group) (windowLength k b)
      (ruleBubbles (indexedFamily words group) j) := by
  intro j a ha c hc hac sa sc i l hi hl
  have hra := (Finset.mem_filter.mp ha).2
  have hrc := (Finset.mem_filter.mp hc).2
  change (group a).val = j at hra
  change (group c).val = j at hrc
  have hg : group c = group a := Fin.ext (hrc.trans hra.symm)
  exact h.within_rule_disjoint (group a) a (by simp [groupBubbles])
    c (by simp [groupBubbles, hg]) hac sa sc i l hi hl

def Rule (t k b : ℕ) (w : Gram α (windowLength k b) → ℤ) : Prop :=
  ∃ words : Fin (2 * t) → BubbleWord α k b,
    ValidCatalogue words (fun _ => (0 : Fin 1)) ∧
    Balanced words (fun _ => (0 : Fin 1)) ∧
    ruleSpectrum (indexedFamily words (fun _ => (0 : Fin 1)))
      (windowLength k b) Finset.univ = w

theorem singleton_rules {t k b : ℕ} (words : Fin (2 * t) → BubbleWord α k b)
    (w : Gram α (windowLength k b) → ℤ)
    (hw : ruleSpectrum (indexedFamily words (fun _ => (0 : Fin 1)))
      (windowLength k b) Finset.univ = w) :
    FamilySupport.rulesOfFamily (indexedFamily words (fun _ => (0 : Fin 1)))
      (windowLength k b) (fun _ => (0 : Fin 1)) = {w} := by
  classical
  have hg (r : Fin 1) : groupBubbles (fun _ : Fin (2 * t) => (0 : Fin 1)) r = Finset.univ := by
    have hr : r = 0 := Subsingleton.elim _ _
    subst r
    simp [groupBubbles]
  ext u
  simp only [FamilySupport.rulesOfFamily, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨r, hr⟩
    rw [hg r, hw] at hr
    exact hr.symm
  · intro hu
    exact ⟨0, by rw [hg, hw, hu]⟩

theorem family_component_count_le {ν L : ℕ} (F : Family α (Fin ν)) (hL : 1 ≤ L)
    (hstart : ∀ i, vertex F L i false 0 = vertex F L i true 0) :
    Fintype.card (GraphComponents F L) ≤ ν := by
  classical
  let _ : Fintype (Components F L) := by
    unfold Components
    exact Fintype.ofFinite _
  rw [← Fintype.card_congr (Qary.SupportComponents.componentEquiv F L hL hstart)]
  let f : Fin ν → Components F L := Quotient.mk (Qary.SupportComponents.componentSetoid F L)
  have hf : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn with
    | _ i => exact ⟨i, rfl⟩
  simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective f hf

theorem singleton_component_count_le {t k b : ℕ}
    (w : Gram α (windowLength k b) → ℤ) (hw : Rule t k b w) :
    componentCount {w} ≤ 2 * t := by
  obtain ⟨words, hv, _, heq⟩ := hw
  rw [← singleton_rules words w heq,
    FamilySupport.componentCount_rulesOfFamily _ _ (fun _ => rfl) hv.geometry hv.rank_disjoint]
  exact family_component_count_le _ (by unfold windowLength; omega) hv.common_start

theorem signed_unit {t k b : ℕ}
    (w : Gram α (windowLength k b) → ℤ) (hw : Rule t k b w) :
    Qary.WitnessAlgebra.SignedUnitVector (Qary.CatalogueAlgebra.rational w) := by
  obtain ⟨words, hv, _, heq⟩ := hw
  have hd : VertexDisjointOn (indexedFamily words (fun _ => (0 : Fin 1)))
      (windowLength k b) Finset.univ := by
    simpa only [groupBubbles, Finset.filter_true] using hv.within_rule_disjoint (0 : Fin 1)
  have h := Qary.WitnessAlgebra.ruleSpectrum_signed_unit _ _ hv.geometry Finset.univ hd
  change Qary.WitnessAlgebra.SignedUnitVector (fun g => (w g : ℚ))
  simpa only [heq] using h

theorem nonzero {t k b : ℕ} (ht : 1 ≤ t)
    (w : Gram α (windowLength k b) → ℤ) (hw : Rule t k b w) : w ≠ 0 := by
  classical
  obtain ⟨words, hv, _, heq⟩ := hw
  let F := indexedFamily words (fun _ => (0 : Fin 1))
  let i : Fin (2 * t) := ⟨0, by omega⟩
  have hd : VertexDisjointOn F (windowLength k b) Finset.univ := by
    simpa only [groupBubbles, Finset.filter_true] using hv.within_rule_disjoint (0 : Fin 1)
  let g := gram (F.path i false) (windowLength k b) 0
  have hg : g ∈ windowSet (F.path i false) (windowLength k b) (F.extra i false) :=
    ⟨⟨0, by omega⟩, rfl⟩
  have hneg := rule_negative_of_window F (windowLength k b) hv.geometry Finset.univ hd
    i (Finset.mem_univ i) g hg
  rw [heq] at hneg
  intro hz
  rw [hz] at hneg
  norm_num at hneg

#print axioms singleton_component_count_le
#print axioms signed_unit
#print axioms nonzero

end DeletionCode.Burst.Catalogue
