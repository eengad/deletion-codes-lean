import DeletionCode.Explicit.CatalogueEnumeration
import DeletionCode.Explicit.LiftDictionary

/-! The executable catalogue vectors use the borrowed signed spectrum. -/

namespace DeletionCode.Explicit.CatalogueEnumeration

open Borrowed FieldHash LiftDictionary
open Qary.SignedSupport Qary.Windows
open Qary.BubbleCatalogue (wordSpectrum_eq_pathSpectrum)
open Qary.RuleReconstruction (groupBubbles)
open scoped BigOperators

variable {q K b L s : ℕ}

set_option linter.style.haveILetI false in
theorem row_eq_spectrum (pad : Fin q) (words : Fin s → BubbleWord (Fin q) K b L) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    Catalogue.ValidCatalogue words (fun _ => (0 : Fin 1)) →
    ∀ g : Gram (Fin q) L, row pad words (finFunctionFinEquiv g) =
      (ruleSpectrum (Catalogue.indexedFamily words (fun _ => (0 : Fin 1))) L Finset.univ g : F₃) := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  intro h g
  let F := Catalogue.indexedFamily words (fun _ => (0 : Fin 1))
  have hs (i : Fin s) (side : Bool) : listFieldSpectrum pad (Catalogue.pathWord (words i) side) L g =
      (pathSpectrum (F.path i side) L (F.extra i side) g : F₃) := by
    have hlo : L ≤ (Catalogue.pathWord (words i) side).length := h.length_lower i side
    unfold listFieldSpectrum
    rw [fieldSpectrum_eq_cast,wordSpectrum_eq_pathSpectrum _ _ _ hlo]
    rfl
  unfold row ruleSpectrum
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hpos : listFieldSpectrum pad (words i).positiveWord L g = _ := hs i true
  have hneg : listFieldSpectrum pad (words i).negativeWord L g = _ := hs i false
  simp [BubbleFamilies.vector,bubbleSpectrum,hpos,hneg,F]

set_option linter.style.haveILetI false in
theorem negative_gram (pad : Fin q) (words : Fin s → BubbleWord (Fin q) K b L) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    Catalogue.ValidCatalogue words (fun _ => (0 : Fin 1)) →
    ∀ (i : Fin s) (a : ℕ), a+L ≤ (words i).negativeWord.length →
      row pad words (finFunctionFinEquiv (gram (paddedLetters pad (words i).negativeWord.get) L a)) = -1 := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  intro h i a ha
  let F := Catalogue.indexedFamily words (fun _ => (0 : Fin 1))
  have hdis : VertexDisjointOn F L Finset.univ := by
    have hgroup : groupBubbles (fun _ : Fin s => (0 : Fin 1)) 0 = Finset.univ := by
      ext j
      exact iff_of_true (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩) (Finset.mem_univ _)
    have h := h.within_rule_disjoint (0 : Fin 1)
    rw [hgroup] at h
    exact h
  have hm : a < F.extra i false + 1 := by
    change a < (words i).negativeWord.length-L+1
    omega
  have hg : gram (F.path i false) L a ∈ windowSet (F.path i false) L (F.extra i false) :=
    ⟨⟨a,hm⟩,rfl⟩
  have hword : gram (paddedLetters pad (words i).negativeWord.get) L a =
      gram (F.path i false) L a := by
    funext j
    have hj : a+j.val < (words i).negativeWord.length := by omega
    simp [gram,paddedLetters,F,Catalogue.indexedFamily,Catalogue.family,Catalogue.pathWord,
      Qary.CatalogueWords.listLetters,List.getD_eq_getElem?_getD,hj]
  rw [hword,row_eq_spectrum pad words h,rule_value_at_gram F L h.geometry Finset.univ hdis i
    (Finset.mem_univ _) _ ⟨false,hg⟩,bubble_negative_value F L h.geometry i _ hg]
  rfl

set_option linter.style.haveILetI false in
theorem row_ne_zero (pad : Fin q) (words : Fin s → BubbleWord (Fin q) K b L) (hs : 0 < s) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    Catalogue.ValidCatalogue words (fun _ => (0 : Fin 1)) →
    row pad words ≠ 0 := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  intro h hz
  let i : Fin s := ⟨0,hs⟩
  have ha : L ≤ (words i).negativeWord.length := h.length_lower i false
  have hcoord := negative_gram pad words h i 0 (by simpa using ha)
  rw [hz] at hcoord
  exact (by decide : (0 : F₃) ≠ -1) hcoord

#print axioms row_eq_spectrum
#print axioms negative_gram
#print axioms row_ne_zero

end DeletionCode.Explicit.CatalogueEnumeration
