import DeletionCode.Explicit.Machine.SourceCoreReplay
import DeletionCode.Explicit.Machine.SourceSlice

/-! Compact identifiers and supplier-reference translation for retained gates. -/
namespace DeletionCode.Explicit.Machine.SourceCompact

open SourceReference SourceLists
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open private idxOf_val from DeletionCode.Explicit.Machine.SourceCoreReplay

def index (keys : List ℕ) (id : ℕ) : ℕ := (keys.idxOf? id).getD 0

private theorem index_apply (keys : List ℕ) (id : ℕ) :
    index keys id = if id ∈ keys then keys.idxOf id else 0 := by
  unfold index List.idxOf?
  rw [List.findIdx?_eq_guard_findIdx_lt]
  by_cases h : id ∈ keys
  · have hi := List.idxOf_lt_length_of_mem h
    change keys.findIdx (· == id) < keys.length at hi
    simp [h,hi,List.idxOf]
  · have hi := mt List.idxOf_lt_length_iff.mp h
    change ¬ keys.findIdx (· == id) < keys.length at hi
    simp [h,hi,Option.guard]

theorem index_eq {N : ℕ} (s : Finset (Fin N)) (id : ℕ) :
    index (s.sort.map Fin.val) id = ReplayEntry.compactIndex s id := by
  rw [index_apply,ReplayEntry.compactIndex]
  by_cases h : id < N
  · let i : Fin N := ⟨id,h⟩
    have hm : id ∈ s.sort.map Fin.val ↔ i ∈ s := by
      simp only [List.mem_map,Finset.mem_sort]
      exact ⟨fun ⟨j,hj,h⟩ => (show j = i from Fin.ext h) ▸ hj,fun h => ⟨i,h,rfl⟩⟩
    rw [dite_eq_left h]
    by_cases hi : i ∈ s
    · rw [if_pos (hm.mpr hi),dite_eq_left hi,BackwardSlice.number,Finset.orderIsoOfFin_symm_apply]
      exact idxOf_val s.sort i
    · rw [if_neg (fun h => hi (hm.mp h)),dite_eq_right hi]
  · rw [dite_eq_right h,if_neg]
    intro hh
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hh
    exact h i.isLt

abbrev indexEncoding := encPair PatchGraph.rowEncoding encUnary

theorem index_polyTime :
    ComputableInPolyTime (fun x : List ℕ × ℕ => index x.1 x.2) indexEncoding encUnary := by
  let e := indexEncoding
  have h := optionElimWithInput (encA := e) (encB := encUnary) (encC := encUnary)
    (body := fun _ x => x) (idxOf?_polyTime 0 encUnary) (const 0) (snd e encUnary)
  exact h.of_enc_eq (fun x => by
    unfold index
    cases x.1.idxOf? x.2 <;> rfl)

def rename (keys : List ℕ) (ref : Ref) : Ref :=
  (ref.1,ref.2.map (fun r => (index keys r.1,r.2)))

theorem rename_eq {N : ℕ} (s : Finset (Fin N)) (ref : ReplayEntry.Reference) :
    rename (s.sort.map Fin.val) (referenceData ref) =
      referenceData (ReplayEntry.renameRef (ReplayEntry.compactIndex s) ref) := by
  cases ref <;> simp [rename,referenceData,ReplayEntry.renameRef,index_eq]

theorem rename_polyTime :
    ComputableInPolyTime (fun x : List ℕ × Ref => rename x.1 x.2)
      (encPair PatchGraph.rowEncoding refEncoding) refEncoding := by
  let e := encPair PatchGraph.rowEncoding refEncoding
  let a := encPair e supplierEncoding
  have h := snd PatchGraph.rowEncoding refEncoding
  have hr := snd e supplierEncoding
  have hi := index_polyTime.comp (((fst PatchGraph.rowEncoding refEncoding).comp (fst e supplierEncoding)).prod hr.fst')
  have hmap := optionMapWithInput (encA := e) (encB := supplierEncoding) (encC := supplierEncoding)
    (f := fun x r => (index x.1 r.1,r.2)) h.snd' (hi.prod hr.snd')
  exact h.fst'.prod hmap

#print axioms index_eq
#print axioms index_polyTime
#print axioms rename_eq
#print axioms rename_polyTime

end DeletionCode.Explicit.Machine.SourceCompact
