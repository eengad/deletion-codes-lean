import DeletionCode.Explicit.ComponentRows
import DeletionCode.Explicit.ComponentExposure
import DeletionCode.Explicit.CatalogueCoordinates
import DeletionCode.Explicit.PrepareRule
import DeletionCode.Explicit.FirstEventGeometry

/-! The executable catalogue scan and the letter-graph recognizer. -/

namespace DeletionCode.Explicit.Recognizer

open FieldHash CanonicalColour RulePatch Borrowed
open ReplayEntry LetterGraphCuts LiftDictionary

variable {ℓ q K b L s θ : ℕ}

/-- Keep the ordered gate batch and the rule selected by the scan. -/
structure Batch (ℓ q L s : ℕ) where
  row : Row (q^L)
  bubbles : Fin s → PreparedBubble ℓ L (Fin q)

abbrev History (ℓ q L s : ℕ) := List (Batch ℓ q L s)

def completed (hs : History ℓ q L s) : Array (Completed ℓ (Fin q)) :=
  Array.ofFn fun i : Fin (hs.length*s) =>
    let (r,j) := finProdFinEquiv.symm i
    ((hs.get r).bubbles j).completed

def gates (hs : History ℓ q L s) (e : Fin hs.length × Fin s) : GateData ℓ (Fin q) :=
  ((hs.get e.1).bubbles e.2).data

def parts (hs : History ℓ q L s) : Fin hs.length → List (Row (q^L)) :=
  partRows (PatchTable.incidence (gates hs)) (fun i => (hs.get i).row)

def oldRows (hs : History ℓ q L s) : List (Row (q^L)) := hs.map Batch.row

def spectrum (pad : Fin q) (x : Fin ℓ → Fin q) (L : ℕ) : Row (q^L) :=
  fun j => fieldSpectrum (paddedLetters pad x) ℓ L (finFunctionFinEquiv.symm j)

def candidateOK (H : TernaryMatrix θ (q^L)) (pad : Fin q) (x : Fin ℓ → Fin q)
    (hs : History ℓ q L s) (words : Fin s → BubbleWord (Fin q) K b L) : Bool :=
  let ρ := CatalogueEnumeration.row pad words
  H.mulVec ρ == 0 && !inSpan (oldRows hs) ρ && ComponentExposure.check (parts hs) (spectrum pad x L) ρ

def nextRule (H : TernaryMatrix θ (q^L)) (pad : Fin q) (x : Fin ℓ → Fin q)
    (hs : History ℓ q L s) (catalogue : List (Fin s → BubbleWord (Fin q) K b L)) :
    Option (Fin s → BubbleWord (Fin q) K b L) :=
  catalogue.find? (candidateOK H pad x hs)

theorem nextRule_selected (H : TernaryMatrix θ (q^L)) (pad : Fin q) (x : Fin ℓ → Fin q)
    (hs : History ℓ q L s) (catalogue : List (Fin s → BubbleWord (Fin q) K b L))
    {words : Fin s → BubbleWord (Fin q) K b L}
    (h : nextRule H pad x hs catalogue = some words) :
    words ∈ catalogue ∧ H.mulVec (CatalogueEnumeration.row pad words) = 0 ∧
      CatalogueEnumeration.row pad words ∉ span (oldRows hs) := by
  refine ⟨List.mem_of_find?_eq_some h,?_⟩
  have hcheck := List.find?_some h
  have ha := Bool.and_eq_true_iff.mp hcheck
  have hb := Bool.and_eq_true_iff.mp ha.1
  exact ⟨beq_iff_eq.mp hb.1, fun hm => by
    have he := (inSpan_iff _ _).mpr hm
    simp [he] at hb⟩

def appendRule (pad : Fin q) (x : Fin ℓ → Fin q) (root : Fin ℓ)
    (hs : History ℓ q L s) (words : Fin s → BubbleWord (Fin q) K b L) :
    Option (History ℓ q L s) :=
  if h : ∀ j, 0 < (words j).left.length ∧ 0 < (words j).right.length then do
    let ws ← prepareRule pad x (completed hs) words root hs.length (fun j => (h j).1) (fun j => (h j).2)
    if hw : ws.length = s then
      some (hs ++ [⟨CatalogueEnumeration.row pad words,fun j => ws.get (Fin.cast hw.symm j)⟩])
    else none
  else none

theorem appendRule_shape (pad : Fin q) (x : Fin ℓ → Fin q) (root : Fin ℓ)
    {hs hs' : History ℓ q L s} {words : Fin s → BubbleWord (Fin q) K b L}
    (h : appendRule pad x root hs words = some hs') :
    ∃ p : Batch ℓ q L s, hs' = hs ++ [p] ∧ p.row = CatalogueEnumeration.row pad words := by
  unfold appendRule at h
  split at h
  next hpos =>
    cases hws : prepareRule pad x (completed hs) words root hs.length (fun j => (hpos j).1) (fun j => (hpos j).2) with
    | none => simp [hws] at h
    | some ws =>
      by_cases hlen : ws.length = s
      · let p : Batch ℓ q L s :=
          ⟨CatalogueEnumeration.row pad words,fun j => ws.get (Fin.cast hlen.symm j)⟩
        refine ⟨p,?_,rfl⟩
        simpa [hws,hlen,p] using h.symm
      · simp [hws,hlen] at h
  next => contradiction

inductive Result (ℓ q L s : ℕ) where
  | complete (history : History ℓ q L s)
  | firstEvent (history : History ℓ q L s) (last : Fin history.length)

def run (H : TernaryMatrix θ (q^L)) (pad : Fin q) (x : Fin ℓ → Fin q)
    (root : Fin ℓ) (R : ℕ) (catalogue : List (Fin s → BubbleWord (Fin q) K b L)) :
    ℕ → History ℓ q L s → Option (Result ℓ q L s)
  | 0, _ => none
  | fuel+1, hs =>
    match nextRule H pad x hs catalogue with
    | none => some (.complete hs)
    | some words => do
      let hs' ← appendRule pad x root hs words
      if h : hs.length < hs'.length then
        let last : Fin hs'.length := ⟨hs.length,h⟩
        if FirstEvent.componentEvent (PatchTable.incidence (gates hs')) R last then
          some (.firstEvent hs' last)
        else run H pad x root R catalogue fuel hs'
      else none

/-- At most one independent row per gram coordinate can be added. One
additional scan detects closure. The initial reference origin is zero. -/
def recognize (H : TernaryMatrix θ (q^L)) (pad : Fin q) (x : Fin ℓ → Fin q) (R : ℕ) :
    Option (Result ℓ q L s) :=
  if h : 0 < ℓ then
    run H pad x ⟨0,h⟩ R (CatalogueEnumeration.rules q K b L s pad) (q^L+1) []
  else some (.complete [])

#print axioms nextRule_selected
#print axioms appendRule_shape

end DeletionCode.Explicit.Recognizer
