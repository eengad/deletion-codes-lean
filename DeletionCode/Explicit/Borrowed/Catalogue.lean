import DeletionCode.Burst.Catalogue
import DeletionCode.Explicit.Borrowed.BubbleWords

/-!
The catalogue of vertex-disjoint substring-replacement bubbles at length `L`.
The balanced predicate also records the equal total length needed for the
comparison with the existence development.
-/
namespace DeletionCode.Explicit.Borrowed.Catalogue

open Qary.Windows
open Qary.CatalogueWords (listLetters)
open Qary.RootSelection Qary.SignedSupport Qary.SupportComponents
open Qary.RuleReconstruction (groupBubbles)
open scoped BigOperators

variable {α : Type*} [Inhabited α]

def pathWord {K b L : ℕ} (p : BubbleWord α K b L) (side : Bool) : List α :=
  if side then p.positiveWord else p.negativeWord

def family {B : Type*} {K b L : ℕ} (words : B → BubbleWord α K b L)
    (rank : B → ℕ) : Family α B where
  rank := rank
  path i side := listLetters (pathWord (words i) side)
  extra i side := (pathWord (words i) side).length - L

def indexedFamily {K b L ν R : ℕ} (words : Fin ν → BubbleWord α K b L)
    (group : Fin ν → Fin R) : Family α (Fin ν) := family words (fun i => (group i).val)

omit [Inhabited α] in
theorem word_length_bounds {K b L : ℕ} (p : BubbleWord α K b L) (side : Bool)
    (hwindow : 3 * (K + b + 1) ≤ L) :
    L ≤ (pathWord p side).length ∧
      (pathWord p side).length ≤ 2 * (L - 1) + b := by
  cases side
  · exact p.negativeWord_length_bounds hwindow
  · exact p.positiveWord_length_bounds hwindow

theorem notBothSingle {B : Type*} {K b L : ℕ} (words : B → BubbleWord α K b L)
    (rank : B → ℕ) (hwindow : 3 * (K + b + 1) ≤ L) (i : B) :
    (family words rank).extra i false ≠ 0 ∨ (family words rank).extra i true ≠ 0 := by
  left
  have hl := (words i).left_lower
  have hr := (words i).right_lower
  simp only [family, pathWord, Bool.false_eq_true, ite_false, BubbleWord.negativeWord,
    List.length_append]
  omega

structure ValidCatalogue {K b L ν R : ℕ}
    (words : Fin ν → BubbleWord α K b L) (group : Fin ν → Fin R) : Prop where
  length_lower : ∀ i side, L ≤ (pathWord (words i) side).length
  geometry : BubbleGeometry (indexedFamily words group) L
  common_start : ∀ i, vertex (indexedFamily words group) L i false 0 =
    vertex (indexedFamily words group) L i true 0
  common_end : ∀ i,
    vertex (indexedFamily words group) L i false
      ((indexedFamily words group).extra i false + 1) =
    vertex (indexedFamily words group) L i true
      ((indexedFamily words group).extra i true + 1)
  within_rule_disjoint : ∀ r : Fin R,
    VertexDisjointOn (indexedFamily words group) L (groupBubbles group r)

def Balanced {K b L ν R : ℕ} (words : Fin ν → BubbleWord α K b L)
    (group : Fin ν → Fin R) : Prop :=
  ∀ r : Fin R,
    (∑ i ∈ groupBubbles group r, (words i).negativeWord.length) =
      ∑ i ∈ groupBubbles group r, (words i).positiveWord.length

/-- A sum of exactly `2 * t` oriented bubbles with pairwise disjoint vertex sets. -/
def IsRule (t K b L : ℕ) (w : Gram α L → ℤ) : Prop :=
  ∃ words : Fin (2 * t) → BubbleWord α K b L,
    ValidCatalogue words (fun _ => (0 : Fin 1)) ∧
    ruleSpectrum (indexedFamily words (fun _ => (0 : Fin 1))) L Finset.univ = w

/-- The manuscript catalogue `𝒦₀` (`def:catalogue`). -/
def catalogue (α : Type*) [Inhabited α] (t K b L : ℕ) :
    Set (Gram α L → ℤ) := {w | IsRule t K b L w}

/-- A rule whose total positive and negative word lengths agree. -/
def Rule (t K b L : ℕ) (w : Gram α L → ℤ) : Prop :=
  ∃ words : Fin (2 * t) → BubbleWord α K b L,
    ValidCatalogue words (fun _ => (0 : Fin 1)) ∧
    Balanced words (fun _ => (0 : Fin 1)) ∧
    ruleSpectrum (indexedFamily words (fun _ => (0 : Fin 1))) L Finset.univ = w

theorem Rule.mem_catalogue {t K b L : ℕ} {w : Gram α L → ℤ}
    (h : Rule t K b L w) : w ∈ catalogue α t K b L := by
  obtain ⟨words, hvalid, _, heq⟩ := h
  exact ⟨words, hvalid, heq⟩

#print axioms catalogue
#print axioms Rule

end DeletionCode.Explicit.Borrowed.Catalogue
