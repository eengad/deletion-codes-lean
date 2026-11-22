import DeletionCode.Explicit.RecognizerTransition
import DeletionCode.Explicit.BooleanClosure

/-! The successful scan computes the paper's closure in the gram coordinates. -/

namespace DeletionCode.Explicit.Recognizer

open FieldHash CanonicalColour LetterSequence LetterGraphCuts LiftDictionary BooleanClosure
open Qary.SignedSupport

variable {ℓ q K b L Λ s θ : ℕ}

def kernelRules (H : TernaryMatrix θ (q^L)) (pad : Fin q) : Set (Gram (Fin q) L → F₃) :=
  {ρ | ∃ words ∈ CatalogueEnumeration.rules q K b L s pad,
    H.mulVec (CatalogueEnumeration.row pad words) = 0 ∧
      gramEquiv (q := q) (L := L) (CatalogueEnumeration.row pad words) = ρ}

def historySpace (hs : History ℓ q L s) : Space (Fin q) L :=
  (span (oldRows hs)).map (gramEquiv (q := q) (L := L)).toLinearMap

@[simp] theorem historySpace_nil : historySpace (L := L) ([] : History ℓ q L s) = ⊥ := by
  simp [historySpace,oldRows]

private theorem historySpace_append (hs : History ℓ q L s) (p : Batch ℓ q L s) :
    historySpace (hs ++ [p]) =
      adjoining (historySpace hs) (gramEquiv (q := q) (L := L) p.row) := by
  have h : {v | v ∈ oldRows (hs ++ [p])} = {v | v ∈ oldRows hs} ∪ {p.row} := by
    ext v
    simp [oldRows,or_comm]
  unfold historySpace adjoining
  change (Submodule.span F₃ {v | v ∈ oldRows (hs ++ [p])}).map _ = _
  rw [h,Submodule.span_union,Submodule.map_sup,Submodule.map_span _ ({p.row} : Set (Row (q^L))),
    Set.image_singleton]
  rfl

private theorem mapped_mem (hs : History ℓ q L s) (a : Row (q^L)) :
    gramEquiv (q := q) (L := L) a ∈ historySpace hs ↔ a ∈ span (oldRows hs) := by
  unfold historySpace
  constructor
  · intro h
    obtain ⟨w,hw,he⟩ := Submodule.mem_map.mp h
    exact (gramEquiv.injective he) ▸ hw
  · exact Submodule.mem_map_of_mem

private theorem abstract_boolean (u : Row (q^L)) :
    IsZeroOne (gramEquiv (q := q) (L := L) u) ↔ FibreEnumeration.IsBoolean u := by
  constructor
  · intro h j
    have h' := h (finFunctionFinEquiv.symm j)
    change u (finFunctionFinEquiv (finFunctionFinEquiv.symm j)) = 0 ∨
      u (finFunctionFinEquiv (finFunctionFinEquiv.symm j)) = 1 at h'
    simpa only [Equiv.apply_symm_apply] using h'
  · intro h g
    exact h (finFunctionFinEquiv g)

set_option maxHeartbeats 800000 in
theorem candidate_exposure_iff (H : TernaryMatrix θ (q^L)) (pad : Fin q) {x : Fin ℓ → Fin q}
    {hs : History ℓ q L s} {edges : Letter ℓ (Fin q) → Letter ℓ (Fin q) → Prop}
    {marks : Finset (Fin ℓ)} (hv : GraphValid pad x b Λ hs edges marks)
    (hx : Strong x K Λ) (hL : K+2*Λ+1 ≤ L)
    (words : Fin s → Borrowed.BubbleWord (Fin q) K b L) :
    let row := CatalogueEnumeration.row pad words
    let ρ := gramEquiv (q := q) (L := L) row
    candidateOK H pad x hs words = true ↔
      H.mulVec row = 0 ∧ ρ ∉ historySpace hs ∧
        Exposed (fieldSpectrum (paddedLetters pad x) ℓ L) (historySpace hs) ρ := by
  dsimp only
  have hb := spectrum_isBoolean (L := L) pad x hx (show K ≤ L-1 by omega)
  have hpp {i j : Fin hs.length} (hij : i ≠ j) (g : Fin (q^L))
      (hg : ComponentExposure.occupies (parts hs i) g = true) :
      ComponentExposure.occupies (parts hs j) g ≠ true :=
    parts_support_disjoint pad x hs hx hv.fit (by omega) hv.vectors hij g hg
  have hcheck := candidateOK_iff H pad x hs words hb hpp
  dsimp only at hcheck
  rw [hcheck,mapped_mem]
  have he : gramEquiv (q := q) (L := L) (spectrum pad x L) = fieldSpectrum (paddedLetters pad x) ℓ L := by
    funext g
    change fieldSpectrum (paddedLetters pad x) ℓ L (finFunctionFinEquiv.symm (finFunctionFinEquiv g)) = _
    rw [Equiv.symm_apply_apply]
  constructor
  · rintro ⟨hker,hn,w,hw,hv,hr⟩
    refine ⟨hker,hn,gramEquiv (q := q) (L := L) w,(mapped_mem hs w).mpr hw,?_,?_⟩
    · rw [← he,← map_add]
      exact (abstract_boolean _).mpr hv
    · rw [← he,← map_add,← map_add]
      exact (abstract_boolean _).mpr hr
  · rintro ⟨hker,hn,w,hw,hv,hr⟩
    obtain ⟨a,ha,rfl⟩ := Submodule.mem_map.mp hw
    refine ⟨hker,hn,a,ha,?_,?_⟩
    · apply (abstract_boolean _).mp
      rwa [map_add,he]
    · apply (abstract_boolean _).mp
      rwa [map_add,map_add,he]

theorem nextRule_greedy_step (H : TernaryMatrix θ (q^L)) (pad : Fin q) {x : Fin ℓ → Fin q}
    {hs hs' : History ℓ q L s} {edges : Letter ℓ (Fin q) → Letter ℓ (Fin q) → Prop}
    {marks : Finset (Fin ℓ)} (hv : GraphValid pad x b Λ hs edges marks)
    (hx : Strong x K Λ) (hL : K+2*Λ+1 ≤ L) (root : Fin ℓ)
    (hbefore : Greedy (kernelRules (K := K) (b := b) (s := s) H pad)
      (fieldSpectrum (paddedLetters pad x) ℓ L) hs.length (historySpace hs))
    {words : Fin s → Borrowed.BubbleWord (Fin q) K b L}
    (hfound : nextRule H pad x hs (CatalogueEnumeration.rules q K b L s pad) = some words)
    (hadd : appendRule pad x root hs words = some hs') :
    Greedy (kernelRules (K := K) (b := b) (s := s) H pad)
      (fieldSpectrum (paddedLetters pad x) ℓ L) hs'.length (historySpace hs') := by
  have hmem := List.mem_of_find?_eq_some hfound
  have hcheck := List.find?_some hfound
  obtain ⟨hker,hn,hex⟩ := (candidate_exposure_iff H pad hv hx hL words).mp hcheck
  obtain ⟨p,rfl,hrow⟩ := appendRule_shape pad x root hadd
  rw [List.length_append,List.length_singleton,historySpace_append,hrow]
  exact .add hbefore ⟨words,hmem,hker,rfl⟩ hex hn

theorem nextRule_none_closed (H : TernaryMatrix θ (q^L)) (pad : Fin q) {x : Fin ℓ → Fin q}
    {hs : History ℓ q L s} {edges : Letter ℓ (Fin q) → Letter ℓ (Fin q) → Prop}
    {marks : Finset (Fin ℓ)} (hv : GraphValid pad x b Λ hs edges marks)
    (hx : Strong x K Λ) (hL : K+2*Λ+1 ≤ L)
    (hnone : nextRule H pad x hs (CatalogueEnumeration.rules q K b L s pad) = none) :
    ClosedAt (kernelRules (K := K) (b := b) (s := s) H pad)
      (fieldSpectrum (paddedLetters pad x) ℓ L) (historySpace hs) := by
  rintro ρ ⟨words,hw,hker,rfl⟩ hex
  by_contra hn
  have hc := (candidate_exposure_iff H pad hv hx hL words).mpr ⟨hker,hn,hex⟩
  exact (List.find?_eq_none.mp hnone words hw) hc

#print axioms nextRule_greedy_step
#print axioms nextRule_none_closed

end DeletionCode.Explicit.Recognizer
