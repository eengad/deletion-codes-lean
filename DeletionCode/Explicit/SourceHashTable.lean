import DeletionCode.Explicit.ConcreteSource
import DeletionCode.Explicit.Machine.TernaryRank

/-! A length-indexed table of public ternary hashes using the existing
framing and ternary row encodings. -/

namespace DeletionCode.Explicit.SourceHashTable

open ConcreteSource UniformParameters FieldHash Machine.Ternary
open Turing.MultiTapeTM

variable {q b t ℓ : ℕ}

def nthFrame (bits : List Bool) : ℕ → Option (List Bool)
  | 0 => if bits.isEmpty then none else some (unframe bits)
  | j+1 => if bits.isEmpty then none else nthFrame (dropFrame bits) j

theorem nthFrame_encList {α : Type*} (enc : α ↪ List Bool) (xs : List α) (j : ℕ) :
    nthFrame (encList enc xs) j = xs[j]?.map enc := by
  induction j generalizing xs with
  | zero =>
    cases xs with
    | nil => rfl
    | cons a tail =>
      rw [encList_cons]
      have h : (frame (enc a) ++ encList enc tail).isEmpty = false := by simp [frame]
      simp only [nthFrame,h,Bool.false_eq_true,ite_false,unframe_frame_append,List.getElem?_cons_zero,Option.map_some]
  | succ j ih =>
    cases xs with
    | nil => rfl
    | cons a tail =>
      rw [encList_cons]
      have h : (frame (enc a) ++ encList enc tail).isEmpty = false := by simp [frame]
      simp only [nthFrame,h,Bool.false_eq_true,ite_false,dropFrame_frame_append,List.getElem?_cons_succ]
      exact ih tail

def writeHash (H : Hash q b t ℓ) : List Bool :=
  rowsEncoding (List.ofFn fun i : Fin (hashWidth q b t ℓ) =>
    List.ofFn fun j : Fin (q^gram q b t ℓ) => H i j)

private def readTrit (bits : List Bool) : F₃ :=
  if bits = tritEncoding 1 then 1 else if bits = tritEncoding 2 then 2 else 0

private theorem readTrit_code (a : F₃) : readTrit (tritEncoding a) = a := by
  fin_cases a
  · change readTrit (tritEncoding (0 : F₃)) = 0
    decide
  · change readTrit (tritEncoding (1 : F₃)) = 1
    decide
  · change readTrit (tritEncoding (2 : F₃)) = 2
    decide

def readHash (q b t ℓ : ℕ) (bits : List Bool) : Hash q b t ℓ :=
  fun i j => ((nthFrame bits i.val).bind fun row => nthFrame row j.val).elim 0 readTrit

theorem read_write_hash (H : Hash q b t ℓ) : readHash q b t ℓ (writeHash H) = H := by
  funext i j
  simp [readHash,writeHash,nthFrame_encList,i.isLt,j.isLt,readTrit_code]

def write (q b t n : ℕ) (H : (l : ℕ) → Hash q b t l) : List Bool :=
  encList encBits ((List.range (n+1-minLength q b t)).map
    (fun j => writeHash (H (minLength q b t+j))))

def lookup (q b t : ℕ) (bits : List Bool) (l : ℕ) : Option (Hash q b t l) :=
  if l < minLength q b t then none
  else (nthFrame bits (l-minLength q b t)).map (readHash q b t l)

theorem lookup_write (H : (l : ℕ) → Hash q b t l) {n l : ℕ}
    (hlo : minLength q b t ≤ l) (hhi : l ≤ n) :
    lookup q b t (write q b t n H) l = some (H l) := by
  have h : l-minLength q b t < n+1-minLength q b t := by omega
  have hsum : minLength q b t + (l-minLength q b t) = l := by omega
  have hidx : l-minLength q b t < (List.range (n+1-minLength q b t)).length := by
    simpa only [List.length_range] using h
  rw [lookup,ite_eq_right (not_lt_of_ge hlo),write,nthFrame_encList,List.getElem?_map,
    List.getElem?_eq_getElem hidx,List.getElem_range]
  simp only [Option.map_some,encBits_apply]
  have he := congrArg (fun j => writeHash (H j)) hsum
  rw [he,read_write_hash]

theorem lookup_write_none (H : (l : ℕ) → Hash q b t l) {n l : ℕ}
    (hout : l < minLength q b t ∨ n < l) :
    lookup q b t (write q b t n H) l = none := by
  unfold lookup
  split
  next => rfl
  next h =>
    have hu : n < l := hout.resolve_left h
    have hidx : (List.range (n+1-minLength q b t)).length ≤ l-minLength q b t := by
      rw [List.length_range]
      omega
    simp [write,nthFrame_encList,List.getElem?_eq_none_iff.mpr hidx]

#print axioms lookup_write

end DeletionCode.Explicit.SourceHashTable
