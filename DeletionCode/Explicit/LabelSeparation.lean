import DeletionCode.Explicit.RecognizerRecords
import DeletionCode.Explicit.Borrowed.CatalogueCoverage
import DeletionCode.Explicit.ExceptionalWeight

/-! Equal labels on completed strong, nonexceptional sources exclude confusability. -/

namespace DeletionCode.Explicit.Recognizer

open FieldHash CanonicalColour LetterSequence BooleanClosure LiftDictionary Borrowed
open Qary.SignedSupport Qary.Windows Qary.CatalogueWords

variable {ℓ q K b L Λ R t θ : ℕ}

private theorem padded_list (pad : Fin q) (x : Fin ℓ → Fin q) :
    paddedLetters pad x = fun i => (List.ofFn x).getD i pad := by
  funext i
  by_cases h : i < ℓ
  · simp [paddedLetters,h,List.getD_eq_getElem?_getD]
  · simp [paddedLetters,h,List.getD_eq_getElem?_getD]

theorem accepted_labels_separate (P : RuleAddition.Bounds K b L Λ (2*t) R)
    (H : TernaryMatrix θ (q^L)) (pad : Fin q) (root : Fin ℓ) {x y : Fin ℓ → Fin q}
    {hs ht : History ℓ q L (2*t)}
    (htwo : 2 ≤ t) (hK : 1 ≤ K) (hL : K+2*Λ+1 ≤ L)
    (hstrong : Strong x K Λ) (hstrong' : Strong y K Λ)
    (hgood : ¬ExceptionalWeight.Exceptional pad finFunctionFinEquiv.symm H b t K x)
    (hx : ResultValid H pad x K b Λ R (.complete hs))
    (hy : ResultValid H pad y K b Λ R (.complete ht))
    (hr : RecordedBatches P pad x root hs)
    (he : labelOf (K := K) (b := b) H pad x hs = labelOf (K := K) (b := b) H pad y ht)
    (hconf : Burst.Confusable b t (List.ofFn x) (List.ofFn y)) : x = y := by
  classical
  let : Inhabited (Fin q) := ⟨pad⟩
  have hLp : 0 < L := by omega
  have hKu : KUnique (paddedLetters pad x) ℓ K := MatchingWeight.strong_kunique hstrong pad
  have hlistLetters (z : Fin ℓ → Fin q) : listLetters (List.ofFn z) = paddedLetters pad z := by
    change (fun i => (List.ofFn z).getD i pad) = _
    exact (padded_list pad z).symm
  have hux : KUnique (listLetters (List.ofFn x)) (List.ofFn x).length K := by
    simpa only [List.length_ofFn,hlistLetters] using hKu
  have hspectrum (z : Fin ℓ → Fin q) :
      ExceptionalWeight.spectrum pad finFunctionFinEquiv.symm (List.ofFn z) = spectrum pad z L := by
    funext i
    simp only [ExceptionalWeight.spectrum,listFieldSpectrum,spectrum,List.length_ofFn,padded_list]
  have hhash : H.mulVec (spectrum pad x L) = H.mulVec (spectrum pad y L) := by
    have hpair := labelOf_eq_labelPair he
    obtain ⟨a,ha⟩ := alpha_exists (catalogueRows q K b L (2*t) pad) (oldRows hs)
    obtain ⟨a',ha'⟩ := alpha_exists (catalogueRows q K b L (2*t) pad) (oldRows ht)
    rw [labelPair,labelPair,ha,ha'] at hpair
    exact congrArg Prod.fst (Option.some.inj hpair)
  by_contra hne
  have hlist : List.ofFn y ≠ List.ofFn x := fun h => hne (List.ofFn_injective h).symm
  rcases Burst.confusable_dichotomy (n := ℓ) (D := 8*(L+t*b)) hconf with hex | ⟨edits,hed,hlen,hsep⟩
  · apply hgood
    refine ⟨?_,List.ofFn y,by simp,hlist,hex,?_⟩
    · rw [← padded_list pad x]
      exact hKu
    · rw [hspectrum,hspectrum]
      exact hhash.symm
  · have hsep' : Burst.Separated (List.ofFn x).length (8*(L+t*b)) edits := by simpa using hsep
    have hcov := Borrowed.CatalogueCoverage.catalogueRule hK P.window hux hed hlen hsep' (by simp)
    obtain ⟨words,hcat,_,hrow⟩ := hcov
    let ρ := CatalogueEnumeration.row pad words
    have hdiff : ρ = spectrum pad y L-spectrum pad x L := by
      funext col
      let g := finFunctionFinEquiv.symm col
      have hc := CatalogueEnumeration.row_eq_spectrum pad words hcat g
      have heq : finFunctionFinEquiv g = col := Equiv.apply_symm_apply _ _
      rw [heq,hrow] at hc
      rw [Pi.sub_apply]
      simp only [spectrum,fieldSpectrum_eq_cast]
      simpa only [ρ,hlistLetters,g,List.length_ofFn,Pi.sub_apply,Int.cast_sub] using hc
    have hmove : spectrum pad y L = spectrum pad x L+ρ := by rw [hdiff]; abel
    have hker : gramEquiv (q := q) (L := L) ρ ∈ kernelRules (K := K) (b := b) (s := 2*t) H pad := by
      refine ⟨words,(CatalogueEnumeration.mem_rules_iff pad hLp words).mpr hcat,?_,rfl⟩
      change H.mulVec ρ = 0
      rw [hdiff,Matrix.mulVec_sub,← hhash,sub_self]
    have hv := spectrum_isBoolean (L := L) pad x hstrong (by omega)
    have hv' := spectrum_isBoolean (L := L) pad y hstrong' (by omega)
    have happ : Applies (fieldSpectrum (paddedLetters pad x) ℓ L)
        (gramEquiv (q := q) (L := L) ρ) := by
      constructor
      · intro g
        simpa [spectrum] using hv (finFunctionFinEquiv g)
      · intro g
        rw [hmove] at hv'
        simpa [spectrum,gramEquiv,LinearEquiv.funCongrLeft_apply,Pi.add_apply] using hv' (finFunctionFinEquiv g)
    have hx' := hx
    obtain ⟨_,_,hxGraph,hbefore,_⟩ := hx'
    have hsigned := hr.signed_intersection hxGraph hstrong hbefore (by omega) hL
    exact labels_separate_kernel_move H pad hLp hx hy hr.independent hr.catalogue_rows
      hsigned ρ hmove hker happ he

#print axioms accepted_labels_separate

end DeletionCode.Explicit.Recognizer
