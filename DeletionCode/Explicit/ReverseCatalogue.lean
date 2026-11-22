import DeletionCode.Explicit.RecognizerClosure

/-! Swapping the two paths preserves catalogue validity and negates the rule. -/

namespace DeletionCode.Explicit.CatalogueEnumeration

open Borrowed FieldHash BubbleFamilies
open Qary.SignedSupport Qary.SupportComponents
open scoped BigOperators

variable {q K b L s θ : ℕ}

def reverseWord (w : BubbleWord (Fin q) K b L) : BubbleWord (Fin q) K b L :=
  ⟨w.left,w.right,w.replacement,w.removed,w.replacement_bound,w.removed_bound,
    Ne.symm w.different,w.left_lower,w.left_upper,w.right_lower,w.right_upper⟩

theorem reverse_valid [Inhabited (Fin q)] (words : Fin s → BubbleWord (Fin q) K b L)
    (hw : Catalogue.ValidCatalogue words (fun _ => (0 : Fin 1))) :
    Catalogue.ValidCatalogue (fun i => reverseWord (words i)) (fun _ => (0 : Fin 1)) := by
  refine ⟨?_,⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro i side
    cases side
    · exact hw.length_lower i true
    · exact hw.length_lower i false
  · intro i side
    cases side
    · exact hw.geometry.simple i true
    · exact hw.geometry.simple i false
  · intro i j k hj hk h
    rcases hw.geometry.endpoints i k j hk hj h.symm with h' | h'
    · exact Or.inl ⟨h'.2,h'.1⟩
    · exact Or.inr ⟨h'.2,h'.1⟩
  · intro i
    exact (hw.geometry.notBothSingle i).symm
  · intro i
    exact (hw.common_start i).symm
  · intro i
    exact (hw.common_end i).symm
  · intro r i hi j hj hij si sj k l hk hl
    cases si <;> cases sj
    · exact hw.within_rule_disjoint r i hi j hj hij true true k l hk hl
    · exact hw.within_rule_disjoint r i hi j hj hij true false k l hk hl
    · exact hw.within_rule_disjoint r i hi j hj hij false true k l hk hl
    · exact hw.within_rule_disjoint r i hi j hj hij false false k l hk hl

theorem reversed_row (pad : Fin q) (words : Fin s → BubbleWord (Fin q) K b L) :
    row pad (fun i => reverseWord (words i)) = -row pad words := by
  funext g
  change (∑ i : Fin s, vector pad (reverseWord (words i)) g) = -(∑ i : Fin s, vector pad (words i) g)
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change listFieldSpectrum pad (words i).negativeWord L (finFunctionFinEquiv.symm g) -
    listFieldSpectrum pad (words i).positiveWord L (finFunctionFinEquiv.symm g) =
    -(listFieldSpectrum pad (words i).positiveWord L (finFunctionFinEquiv.symm g) -
      listFieldSpectrum pad (words i).negativeWord L (finFunctionFinEquiv.symm g))
  rw [neg_sub]

theorem kernelRules_neg (H : TernaryMatrix θ (q^L)) (pad : Fin q) (hL : 0 < L)
    {ρ : Gram (Fin q) L → F₃}
    (h : ρ ∈ Recognizer.kernelRules (K := K) (b := b) (s := s) H pad) :
    -ρ ∈ Recognizer.kernelRules (K := K) (b := b) (s := s) H pad := by
  let : Inhabited (Fin q) := ⟨pad⟩
  obtain ⟨words,hw,hker,rfl⟩ := h
  have hvalid := (mem_rules_iff pad hL words).mp hw
  have hr := reverse_valid words hvalid
  refine ⟨fun i => reverseWord (words i),(mem_rules_iff pad hL _).mpr hr,?_,?_⟩
  · rw [reversed_row,Matrix.mulVec_neg,hker,neg_zero]
  · rw [reversed_row,map_neg]

#print axioms reverse_valid
#print axioms kernelRules_neg

end DeletionCode.Explicit.CatalogueEnumeration
