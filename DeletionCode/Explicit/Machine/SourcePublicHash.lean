import DeletionCode.Explicit.SourceHashTable
import DeletionCode.Explicit.Machine.SourceHashChoice
import DeletionCode.Explicit.Machine.UniformParameters
import DeletionCode.Explicit.Machine.SourceLists
import Batteries.Tactic.OpenPrivate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder

/-! Read the exact source hash used by the concrete callbacks on arbitrary bits. -/
namespace DeletionCode.Explicit.Machine.SourcePublicHash

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open FieldHash Ternary CataloguePrefix SourceLists
open _root_.DeletionCode.Explicit.SourceHashTable
open private readTrit from DeletionCode.Explicit.SourceHashTable

private theorem nthFrame_eq (bits : List Bool) (j : ℕ) : nthFrame bits j = (frames bits)[j]? := by
  induction j generalizing bits with
  | zero => cases bits <;> simp [nthFrame, frames_of_ne_nil]
  | succ j ih => cases bits <;> simp [nthFrame, frames_of_ne_nil, ih]

private theorem nthFrame_polyTime :
    ComputableInPolyTime (fun p : List Bool × ℕ => nthFrame p.1 p.2)
      (encPair encBits encUnary) (encOption encBits) := by
  have h := (getElem?_polyTime ([] : List Bool) encBits).comp
    ((computableInPolyTime_frames.comp (fst encBits encUnary)).prod (snd encBits encUnary))
  exact h.of_enc_eq (fun p => congrArg (encOption encBits) (nthFrame_eq p.1 p.2))

private theorem readTrit_polyTime : ComputableInPolyTime readTrit encBits tritEncoding := by
  have hb := id' (encIn := encBits)
  have h1 := hb.decide_eq' (const (tritEncoding 1))
  have h2 := hb.decide_eq' (const (tritEncoding 2))
  have h := h1.ite' (const (encOut := tritEncoding) 1) (h2.ite' (const 2) (const 0))
  exact h.of_enc_eq (fun x => by simp [readTrit])

private def readCell (bits : List Bool) (i j : ℕ) : F₃ :=
  ((nthFrame bits i).bind (fun row => nthFrame row j)).elim 0 readTrit

private theorem readCell_polyTime :
    ComputableInPolyTime (fun p : (List Bool × ℕ) × ℕ => readCell p.1.1 p.1.2 p.2)
      (encPair (encPair encBits encUnary) encUnary) tritEncoding := by
  let e := encPair (encPair encBits encUnary) encUnary
  have hi := nthFrame_polyTime.comp (fst (encPair encBits encUnary) encUnary)
  have hj := nthFrame_polyTime.comp ((snd e encBits).prod ((snd (encPair encBits encUnary) encUnary).comp (fst e encBits)))
  have h := optionBindWithInput (f := fun (p : (List Bool × ℕ) × ℕ) row => nthFrame row p.2) hi hj
  exact optionElimWithInput (body := fun _ bits => readTrit bits) h (const 0)
    (readTrit_polyTime.comp (snd e encBits))

def readRows (q b t l : ℕ) (bits : List Bool) : Rows :=
  tabRows (_root_.DeletionCode.Explicit.UniformParameters.hashWidth q b t l) (SourceHashChoice.width q b t l)
    (readCell bits)

theorem readRows_eq (q b t l : ℕ) (bits : List Bool) :
    readRows q b t l bits = matrixRows (readHash q b t l bits) := by
  rw [readRows, tabRows, range_map_eq]
  unfold matrixRows
  congr 1
  funext i
  rw [range_map_eq]
  rfl

set_option maxHeartbeats 500000 in
theorem readRows_polyTime (q b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : ℕ × List Bool => readRows q b t p.1 p.2)
      (encPair encUnary encBits) rowsEncoding := by
  let e := encPair encUnary encBits
  let a := encPair e encUnary
  let d := encPair a encUnary
  have hl := fst encUnary encBits
  have hθ := (UniformParameters.width_machine q b t).comp hl
  have hw := (SourceHashChoice.width_polyTime q b t hq).comp hl
  have hb := (snd encUnary encBits).comp ((fst e encUnary).comp (fst a encUnary))
  have hi := (snd e encUnary).comp (fst a encUnary)
  have hj := snd a encUnary
  unfold readRows
  exact tabRows_polyTime (enc := e) (f := fun p i j => readCell p.2 i j) hθ hw
    (readCell_polyTime.comp (encIn := d) ((hb.prod hi).prod hj))

def lookupRows (q b t : ℕ) (bits : List Bool) (l : ℕ) : Option Rows :=
  if l < _root_.DeletionCode.Explicit.UniformParameters.minLength q b t then none
  else (nthFrame bits (l - _root_.DeletionCode.Explicit.UniformParameters.minLength q b t)).map (readRows q b t l)

theorem lookupRows_eq (q b t : ℕ) (bits : List Bool) (l : ℕ) :
    lookupRows q b t bits l = (lookup q b t bits l).map matrixRows := by
  let cutoff := _root_.DeletionCode.Explicit.UniformParameters.minLength q b t
  by_cases h : l < cutoff
  · simp [lookupRows, lookup, show l < _root_.DeletionCode.Explicit.UniformParameters.minLength q b t from h]
  · cases hn : nthFrame bits (l - cutoff) <;>
      simp [lookupRows, lookup, ← show cutoff = _root_.DeletionCode.Explicit.UniformParameters.minLength q b t from rfl,
        h, hn, readRows_eq]

set_option maxHeartbeats 500000 in
theorem lookupRows_polyTime (q b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : List Bool × ℕ => lookupRows q b t p.1 p.2)
      (encPair encBits encUnary) (encOption rowsEncoding) := by
  let e := encPair encBits encUnary
  let cutoff := _root_.DeletionCode.Explicit.UniformParameters.minLength q b t
  have hb := fst encBits encUnary
  have hl := snd encBits encUnary
  have hf := nthFrame_polyTime.comp (hb.prod (unary_sub' hl (const cutoff)))
  have hr := (readRows_polyTime q b t hq).comp (encIn := encPair e encBits)
    ((hl.comp (fst e encBits)).prod (snd e encBits))
  have h := optionMapWithInput (f := fun (p : List Bool × ℕ) bits => readRows q b t p.2 bits) hf hr
  exact ((unary_lt' hl (const cutoff)).ite' (const none) h).of_enc_eq (fun p => by
    simp [lookupRows, cutoff])

#print axioms lookupRows_eq
#print axioms lookupRows_polyTime

end DeletionCode.Explicit.Machine.SourcePublicHash
