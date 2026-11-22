import DeletionCode.Explicit.RecognizerRun
import DeletionCode.Explicit.ReverseCatalogue
import DeletionCode.Explicit.ParityLabel

/-! Colour the closure produced by a successful recognition. -/

namespace DeletionCode.Explicit.Recognizer

open FieldHash CanonicalColour BooleanClosure LiftDictionary
open Qary.SignedSupport

variable {ℓ q K b L Λ s R θ : ℕ}

def catalogueRows (q K b L s : ℕ) (pad : Fin q) : List (Row (q^L)) :=
  (CatalogueEnumeration.rules q K b L s pad).map (CatalogueEnumeration.row pad)

def labelOf (H : TernaryMatrix θ (q^L)) (pad : Fin q) (x : Fin ℓ → Fin q)
    (hs : History ℓ q L s) : Option ℕ :=
  (labelPair H (catalogueRows q K b L s pad) (oldRows hs) (spectrum pad x L)).map
    (fun p => (packLabel p).val)

theorem labelOf_exists (H : TernaryMatrix θ (q^L)) (pad : Fin q) (x : Fin ℓ → Fin q)
    (hs : History ℓ q L s) :
    ∃ u, labelOf (K := K) (b := b) H pad x hs = some u ∧ u < 3*3^θ := by
  obtain ⟨a,ha⟩ := alpha_exists (catalogueRows q K b L s pad) (oldRows hs)
  refine ⟨(packLabel (H.mulVec (spectrum pad x L),dotProduct (spectrum pad x L) a)).val,
    ?_,packLabel_bound _⟩
  simp [labelOf,labelPair,ha]

theorem labelOf_eq_labelPair {H : TernaryMatrix θ (q^L)} {pad : Fin q}
    {x y : Fin ℓ → Fin q} {hs ht : History ℓ q L s}
    (h : labelOf (K := K) (b := b) H pad x hs = labelOf (K := K) (b := b) H pad y ht) :
    labelPair H (catalogueRows q K b L s pad) (oldRows hs) (spectrum pad x L) =
      labelPair H (catalogueRows q K b L s pad) (oldRows ht) (spectrum pad y L) := by
  exact Option.map_injective (fun a b he => packLabel_injective (Fin.ext he)) h

/-- Closed histories that lie one applicable kernel rule apart receive
different integer labels whenever the first history's catalogue
intersection consists of its signed independent rows. -/
theorem labels_separate_kernel_move (H : TernaryMatrix θ (q^L)) (pad : Fin q) {x y : Fin ℓ → Fin q}
    {hs ht : History ℓ q L s} (hL : 0 < L)
    (hx : ResultValid H pad x K b Λ R (.complete hs))
    (hy : ResultValid H pad y K b Λ R (.complete ht))
    (hind : LinearIndependent F₃ (fun i : Fin hs.length => (hs.get i).row))
    (hcat : ∀ v ∈ oldRows hs, v ∈ catalogueRows q K b L s pad)
    (hinter : ∀ v ∈ catalogueRows q K b L s pad, v ∈ span (oldRows hs) →
      ∃ i : Fin hs.length, v = (hs.get i).row ∨ v = -(hs.get i).row)
    (ρ : Row (q^L)) (hmove : spectrum pad y L = spectrum pad x L+ρ)
    (hker : gramEquiv (q := q) (L := L) ρ ∈ kernelRules (K := K) (b := b) (s := s) H pad)
    (happly : Applies (fieldSpectrum (paddedLetters pad x) ℓ L)
      (gramEquiv (q := q) (L := L) ρ)) :
    labelOf (K := K) (b := b) H pad x hs ≠ labelOf (K := K) (b := b) H pad y ht := by
  let C := kernelRules (K := K) (b := b) (s := s) H pad
  let v := fieldSpectrum (paddedLetters pad x) ℓ L
  let r := gramEquiv (q := q) (L := L) ρ
  obtain ⟨_,_,_,_,hxspan⟩ := hx
  obtain ⟨_,_,_,_,hyspan⟩ := hy
  have hclosure : historySpace hs = historySpace ht := by
    have he (z : Fin ℓ → Fin q) :
        gramEquiv (q := q) (L := L) (spectrum pad z L) = fieldSpectrum (paddedLetters pad z) ℓ L := by
      funext g
      change fieldSpectrum (paddedLetters pad z) ℓ L (finFunctionFinEquiv.symm (finFunctionFinEquiv g)) = _
      rw [Equiv.symm_apply_apply]
    have hspec := congrArg (gramEquiv (q := q) (L := L)) hmove
    rw [he,map_add,he] at hspec
    rw [hxspan,hyspan,hspec]
    exact (closure_invariance hker (CatalogueEnumeration.kernelRules_neg H pad hL hker) happly).symm
  have hspans : span (oldRows hs) = span (oldRows ht) :=
    (Submodule.map_injective_of_injective (gramEquiv (q := q) (L := L)).injective) hclosure
  have hcl : r ∈ historySpace hs := by
    rw [hxspan]
    have h := closure_closed (rules := C) (v := v) r hker
    apply h
    refine ⟨0,Submodule.zero_mem _,?_,?_⟩
    · simpa using happly.1
    · change IsZeroOne (v+0+r)
      rw [add_zero]
      exact happly.2
  have hr : ρ ∈ span (oldRows hs) := by
    obtain ⟨a,ha,h⟩ := Submodule.mem_map.mp hcl
    have he : a = ρ := gramEquiv.injective h
    rwa [he] at ha
  have hmem : ρ ∈ catalogueRows q K b L s pad := by
    obtain ⟨words,hm,_,hr⟩ := hker
    have he : CatalogueEnumeration.row pad words = ρ := gramEquiv.injective hr
    exact List.mem_map.mpr ⟨words,hm,he⟩
  have he : span (oldRows hs) = Submodule.span F₃
      (Set.range (fun i : Fin hs.length => (hs.get i).row)) := by
    have eq : {v | v ∈ oldRows hs} = Set.range (fun i : Fin hs.length => (hs.get i).row) := by
      ext u
      change u ∈ oldRows hs ↔ ∃ i : Fin hs.length, (hs.get i).row = u
      rw [oldRows,List.mem_map]
      constructor
      · rintro ⟨b,hb,rfl⟩
        obtain ⟨i,hi⟩ := List.mem_iff_get.mp hb
        exact ⟨i,congrArg Batch.row hi⟩
      · rintro ⟨i,rfl⟩
        exact ⟨hs.get i,List.get_mem ..,rfl⟩
    exact congrArg (Submodule.span F₃) eq
  intro h
  have hp := labelOf_eq_labelPair h
  rw [hmove] at hp
  exact labelPair_separates H _ _ _ _ he hind hcat hinter hspans hmem hr hp

#print axioms labelOf_exists
#print axioms labels_separate_kernel_move

end DeletionCode.Explicit.Recognizer
