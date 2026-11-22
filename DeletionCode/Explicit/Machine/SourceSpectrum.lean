import DeletionCode.Explicit.Machine.GramOrder
import DeletionCode.Explicit.Machine.SourceHashChoice
import DeletionCode.Explicit.Recognizer

/-! Compute the recognizer's spectrum and a row-major hash of it. -/
namespace DeletionCode.Explicit.Machine.SourceSpectrum

set_option maxHeartbeats 350000

open FieldHash Ternary GramOrder CataloguePrefix LiftDictionary
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open scoped BigOperators

variable {q n ℓ θ : ℕ}

/-- Read every gram in the recognizer's little-endian order. -/
def spectrumWith (gs : List (QWord q)) (w : QWord q) : Row :=
  gs.map (fun g => (ExceptionalWeight.gramCount w g : F₃))

def spectrum (pad : Fin q) (L : ℕ) (w : QWord q) : Row := spectrumWith (mainWords pad L) w

@[simp] theorem spectrum_length (pad : Fin q) (L : ℕ) (w : QWord q) :
    (spectrum pad L w).length = q^L := by simp [spectrum,spectrumWith,mainWords]

private theorem listPadded_eq (pad : Fin q) (x : Fin ℓ → Fin q) :
    (fun i => (List.ofFn x).getD i pad) = paddedLetters pad x := by
  funext i
  by_cases hi : i < ℓ
  · exact (BooleanFibres.ofFn_getD x ⟨i,hi⟩ pad).trans
      (by simp [paddedLetters,hi])
  · simp [paddedLetters,hi,List.getD_eq_getElem?_getD]

theorem spectrum_eq (pad : Fin q) (hq : 2 ≤ q) (L : ℕ) (w : QWord q) :
    spectrum pad L w = List.ofFn (ExceptionalWeight.spectrum pad (finFunctionFinEquiv.symm : Fin (q^L) ≃ (Fin L → Fin q)) w) := by
  rw [spectrum,spectrumWith,mainWords_eq pad hq,List.map_ofFn]
  congr 1
  funext j
  exact ExceptionalWeight.gramCount_field pad w L _

theorem spectrum_recognizer (pad : Fin q) (hq : 2 ≤ q) (L : ℕ) (x : Fin ℓ → Fin q) :
    spectrum pad L (List.ofFn x) = List.ofFn (Recognizer.spectrum pad x L) := by
  rw [spectrum_eq pad hq]
  congr 1
  funext j
  simp only [Recognizer.spectrum, ExceptionalWeight.spectrum, listFieldSpectrum,
    List.length_ofFn, listPadded_eq]

/-- Multiply a row-major matrix by a word of trits at the declared width. -/
def applyRows (n : ℕ) (A : Rows) (r : Row) : Row := A.map (fun a => dot n a r)

private theorem dot_rowOf (n : ℕ) (a r : Row) :
    dot n a r = rowOf n a ⬝ᵥ rowOf n r := by
  unfold dot dotProduct
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem (by simp)
  intro j hj hi
  simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  rfl

theorem applyRows_eq (n : ℕ) (A : Rows) (r : Row) :
    applyRows n A r = List.ofFn ((matrixOf (n,A)).mulVec (rowOf n r)) := by
  apply List.ext_getElem (by simp [applyRows])
  intro i hi hj
  have h : i < A.length := by simpa [applyRows] using hi
  simp only [applyRows,List.getElem_map,List.getElem_ofFn,dot_rowOf,Matrix.mulVec]
  congr 1
  funext j
  change A[i].getD j.val 0 = (A.getD i []).getD j.val 0
  rw [List.getD_eq_getElem _ _ h]

theorem applyRows_matrix_eq (A : TernaryMatrix θ n) (r : Fin n → F₃) :
    applyRows n (matrixRows A) (List.ofFn r) = List.ofFn (A.mulVec r) := by
  simp only [applyRows,matrixRows,List.map_ofFn,Function.comp_def,dot_eq]
  rfl

def word (pad : Fin q) (b t : ℕ) (x : ℕ × QWord q) : Row :=
  spectrum pad (UniformParameters.gram q b t x.1) x.2

def hash (pad : Fin q) (b t : ℕ) (x : ℕ × (Rows × QWord q)) : Row :=
  applyRows (q^UniformParameters.gram q b t x.1) x.2.1 (word pad b t (x.1,x.2.2))

theorem hash_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (x : Fin ℓ → Fin q)
    (H : TernaryMatrix θ (q^UniformParameters.gram q b t ℓ)) :
    hash pad b t (ℓ,matrixRows H,List.ofFn x) =
      List.ofFn (H.mulVec (Recognizer.spectrum pad x (UniformParameters.gram q b t ℓ))) := by
  simp only [hash,word,spectrum_recognizer pad hq,applyRows_matrix_eq]

theorem mainWords_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun l => mainWords pad (UniformParameters.gram q b t l))
      encUnary (encList (wordEncoding q)) := by
  let e := encPair encUnary encUnary
  have hi := unary_to_binary.comp (snd encUnary encUnary)
  have hL := (Machine.UniformParameters.gram_machine q b t).comp (fst encUnary encUnary)
  have hd := (Machine.RareAddress.fixedDigits_polyTime pad).comp (hL.prod hi)
  have hr := (listReverse (MatchingPrefixes.symbolEncoding q)).comp (encIn := e) (encMid := wordEncoding q) hd
  unfold mainWords
  exact mapWithInput (encIn := encUnary) (encA := encUnary)
    (unary_range' (SourceHashChoice.width_polyTime q b t hq)) hr

abbrev SpectrumInput (q : ℕ) := List (QWord q) × QWord q
abbrev spectrumEncoding (q : ℕ) := encPair (encList (wordEncoding q)) (wordEncoding q)

theorem spectrumWith_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : SpectrumInput q => spectrumWith x.1 x.2) (spectrumEncoding q) rowEncoding := by
  let e := spectrumEncoding q
  let a := encPair e (wordEncoding q)
  let w := wordEncoding q
  have hx := fst e w
  have hg := snd e w
  have hpack : ComputableInPolyTime (fun x : SpectrumInput q × QWord q => (x.1.2,x.2)) a (encPair w w) :=
    ((snd (encList w) w).comp hx).prod hg
  have hc := (ExceptionalRecords.gramCount_machine q).comp (encIn := a) (encMid := encPair w w) hpack
  exact mapWithInput (encIn := e) (encA := w) (fst (encList w) w)
    (ExceptionalRecords.tritOfUnary.comp hc)

theorem word_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (word pad b t) (encPair encUnary (wordEncoding q)) rowEncoding := by
  have h := (mainWords_polyTime pad b t hq).comp (fst encUnary (wordEncoding q))
  exact (spectrumWith_polyTime q).comp (h.prod (snd encUnary (wordEncoding q)))

abbrev ApplyInput := (ℕ × Rows) × Row
abbrev applyEncoding := encPair matrixEncoding rowEncoding

theorem applyRows_polyTime :
    ComputableInPolyTime (fun x : ApplyInput => applyRows x.1.1 x.1.2 x.2) applyEncoding rowEncoding := by
  let e := encPair applyEncoding rowEncoding
  have hm := fst matrixEncoding rowEncoding
  have hw := snd matrixEncoding rowEncoding
  have hx := fst applyEncoding rowEncoding
  have ha := snd applyEncoding rowEncoding
  have hn := hm.fst'.comp (encIn := e) hx
  have hv := hw.comp (encIn := e) hx
  have hp : ComputableInPolyTime (fun x : ApplyInput × Row => (x.1.1.1,(x.2,x.1.2))) e dotEncoding :=
    hn.prod (ha.prod hv)
  have hf : ComputableInPolyTime (fun x : ApplyInput × Row => dot x.1.1.1 x.2 x.1.2)
      e tritEncoding := by
    have hdot := dot_polyTime.comp (encIn := e) (encMid := dotEncoding) hp
    exact hdot.of_enc_eq (fun _ => rfl)
  unfold applyRows
  exact mapWithInput (encIn := applyEncoding) (encA := rowEncoding) (encB := tritEncoding)
    (list := fun x : ApplyInput => x.1.2) (f := fun x a => dot x.1.1 a x.2) hm.snd' hf

theorem hash_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (hash pad b t) (exceptionalPrefixEncoding q) rowEncoding := by
  let src := exceptionalPrefixEncoding q
  let p := encPair rowsEncoding (wordEncoding q)
  have hl := fst encUnary p
  have hx := snd encUnary p
  have hn := (SourceHashChoice.width_polyTime q b t hq).comp (encIn := src) hl
  have hw := (word_polyTime pad b t hq).comp (encIn := src)
    (encMid := encPair encUnary (wordEncoding q)) (hl.prod hx.snd')
  have harg : ComputableInPolyTime (fun x : ℕ × (Rows × QWord q) =>
      ((SourceHashChoice.width q b t x.1,x.2.1),word pad b t (x.1,x.2.2))) src applyEncoding :=
    (hn.prod hx.fst').prod hw
  exact (applyRows_polyTime.comp (encIn := src) (encMid := applyEncoding) harg).of_enc_eq
    (fun _ => rfl)

theorem columns_polyBounded (q b t : ℕ) (hq : 2 ≤ q) :
    PolyBounded (fun l : ℕ => l) (fun l => q^UniformParameters.gram q b t l) := by
  simpa only [SourceHashChoice.width,encUnary_apply,List.length_replicate] using
    (SourceHashChoice.width_polyTime q b t hq).polyBounded_length

theorem hashWidth_polyBounded (q b t : ℕ) :
    PolyBounded (fun l : ℕ => l) (UniformParameters.hashWidth q b t) := by
  simpa only [encUnary_apply,List.length_replicate] using
    (Machine.UniformParameters.width_machine q b t).polyBounded_length

#print axioms spectrum_recognizer
#print axioms hash_eq
#print axioms word_polyTime
#print axioms hash_polyTime
#print axioms columns_polyBounded
#print axioms hashWidth_polyBounded

end DeletionCode.Explicit.Machine.SourceSpectrum
