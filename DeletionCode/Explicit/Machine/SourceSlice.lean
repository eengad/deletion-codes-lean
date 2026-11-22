import DeletionCode.Explicit.Machine.SourceLists
import DeletionCode.Explicit.BackwardSlice
import Batteries.Tactic.OpenPrivate

/-! Directed supplier closure and the chronological list of retained entries. -/
namespace DeletionCode.Explicit.Machine.SourceSlice

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open private expand from DeletionCode.Explicit.BackwardSlice

variable {N : ℕ}

abbrev Suppliers := List (List ℕ)
abbrev suppliersEncoding := encList PatchGraph.rowEncoding
abbrev sliceEncoding := encPair suppliersEncoding PatchGraph.flagsEncoding

def supplierData (f : Fin N → Finset (Fin N)) : Suppliers :=
  List.ofFn fun i => ((List.finRange N).filter (· ∈ f i)).map Fin.val

def flags (S : Finset (Fin N)) : List Bool :=
  List.ofFn fun i => decide (i ∈ S)

def step (f : Suppliers) (seen : List Bool) : List Bool :=
  (List.range f.length).map fun i => seen.getD i false ||
    (List.range f.length).any (fun j => seen.getD j false && (f.getD j []).contains i)

def slice (f : Suppliers) (seed : List Bool) : List Bool := (step f)^[f.length] seed

def retained (f : Suppliers) (seed : List Bool) : List ℕ :=
  (List.range f.length).filter fun i => (slice f seed).getD i false

theorem retained_length_le (f : Suppliers) (seed : List Bool) :
    (retained f seed).length ≤ f.length := by
  unfold retained
  simpa using List.length_filter_le (fun i => (slice f seed).getD i false) (List.range f.length)

private theorem step_eq (f : Fin N → Finset (Fin N)) (S : Finset (Fin N)) :
    step (supplierData f) (flags S) = flags (expand f S) := by
  unfold step
  simp only [supplierData,List.length_ofFn]
  rw [SourceLists.range_map_eq]
  congr 1
  funext i
  change ((flags S).getD i.val false ||
    (List.range N).any (fun j => (flags S).getD j false &&
      ((supplierData f).getD j []).contains i.val)) = decide (i ∈ expand f S)
  rw [show List.range N = (List.finRange N).map Fin.val by simp,List.any_map]
  have hf (j : Fin N) : ((supplierData f).getD j.val []).contains i.val = decide (i ∈ f j) := by
    unfold supplierData
    rw [BooleanFibres.ofFn_getD _ j []]
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem,List.mem_map,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
    exact ⟨fun ⟨a,ha,he⟩ => Fin.ext he ▸ ha,fun h => ⟨i,h,rfl⟩⟩
  simp only [Function.comp_def,hf,flags,BooleanFibres.ofFn_getD]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true_iff,decide_eq_true_eq,List.any_eq_true,List.mem_finRange,true_and,
    Bool.and_eq_true_iff,expand,Finset.mem_union,Finset.mem_biUnion]

private theorem bounded_expand (f : Fin N → Finset (Fin N)) (fuel : ℕ)
    (S : Finset (Fin N)) (hf : N-S.card ≤ fuel) :
    (expand f)^[fuel] S = BackwardSlice.slice f S := by
  induction fuel generalizing S with
  | zero =>
    have he : expand f S = S := by
      refine Finset.eq_of_subset_of_card_le Finset.subset_union_left ?_ |>.symm
      have hc : (expand f S).card ≤ N := by simpa using (expand f S).card_le_univ
      change (expand f S).card ≤ S.card
      omega
    rw [Function.iterate_zero_apply,BackwardSlice.slice]
    simp [he]
  | succ fuel ih =>
    by_cases he : expand f S = S
    · rw [Function.iterate_fixed he,BackwardSlice.slice]
      simp [he]
    · rw [Function.iterate_succ_apply,BackwardSlice.slice]
      rw [dite_eq_right he]
      have hc : S.card < (expand f S).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left,Ne.symm he⟩)
      exact ih _ (by omega)

theorem slice_eq (f : Fin N → Finset (Fin N)) (S : Finset (Fin N)) :
    slice (supplierData f) (flags S) = flags (BackwardSlice.slice f S) := by
  have h (k : ℕ) : (step (supplierData f))^[k] (flags S) = flags ((expand f)^[k] S) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih,step_eq]
  unfold slice
  rw [h,bounded_expand]
  simp [supplierData]

theorem retained_eq (f : Fin N → Finset (Fin N)) (S : Finset (Fin N)) :
    retained (supplierData f) (flags S) =
      ((List.finRange N).filter (· ∈ BackwardSlice.slice f S)).map Fin.val := by
  unfold retained
  rw [slice_eq,show (supplierData f).length = N by simp [supplierData],
    show List.range N = (List.finRange N).map Fin.val by simp,List.filter_map]
  congr 1
  apply List.filter_congr
  intro j _
  exact BooleanFibres.ofFn_getD _ j false

private theorem step_polyTime :
    ComputableInPolyTime (fun x : Suppliers × List Bool => step x.1 x.2)
      sliceEncoding PatchGraph.flagsEncoding := by
  let e := sliceEncoding
  let a := encPair e encUnary
  let f := PatchGraph.flagsEncoding
  let b := PatchGraph.rowEncoding
  let hx := fst suppliersEncoding f
  let hv := snd suppliersEncoding f
  let p := encPair a encUnary
  have hr := unary_range' ((length_list b).comp hx)
  have hi := snd e encUnary
  have hj := snd a encUnary
  have ha := fst e encUnary
  have hp := fst a encUnary
  have hrow := listGetDWithInput ((hx.comp ha).comp hp) hj ([] : List ℕ)
  have hin := contains hrow (hi.comp hp)
  have hsj := listGetDWithInput ((hv.comp ha).comp hp) hj false
  have hsi := listGetDWithInput (hv.comp ha) hi false
  have htest := anyWithInput (encIn := a) (encA := encUnary)
    (test := fun x j => x.1.2.getD j false && (x.1.1.getD j []).contains x.2)
    (hr.comp ha) ((bool_and' hsj hin).of_enc_eq (fun _ => rfl))
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := encBool)
    (f := fun x i => x.2.getD i false ||
      (List.range x.1.length).any (fun j => x.2.getD j false && (x.1.getD j []).contains i))
    hr ((bool_or' hsi htest).of_enc_eq (fun _ => rfl))

theorem slice_polyTime :
    ComputableInPolyTime (fun x : Suppliers × List Bool => slice x.1 x.2)
      sliceEncoding PatchGraph.flagsEncoding := by
  let f := PatchGraph.flagsEncoding
  let e := sliceEncoding
  have hx := fst suppliersEncoding f
  have hseed := snd suppliersEncoding f
  have hn := (length_list PatchGraph.rowEncoding).comp hx
  have hcount : PolyBounded (fun x : Suppliers × List Bool => (e x).length) (fun x => x.1.length) := by
    simpa only [encUnary_apply,List.length_replicate,Function.comp_def] using hn.polyBounded_length
  let inv (x : Suppliers × List Bool) (_ : ℕ) (s : List Bool) :=
    s = x.2 ∨ s.length = x.1.length
  have hs := (PolyBounded.const 3).mul hcount |>.add hseed.polyBounded_length
  exact (iterateWith_spec (step := step) hx hn hseed step_polyTime inv
    (fun _ => Or.inl rfl) (fun x _ s _ _ => Or.inr (by simp [step])) hs (by
      intro x _ s _ hs
      rcases hs with rfl | h
      · exact Nat.le_add_left _ _
      · have hb := length_encList_le encBool s (b := 1) (fun a _ => by simp [encBool_apply])
        rw [h] at hb
        exact hb.trans (by dsimp; omega))).1

theorem retained_polyTime :
    ComputableInPolyTime (fun x : Suppliers × List Bool => retained x.1 x.2)
      sliceEncoding PatchGraph.rowEncoding := by
  let e := sliceEncoding
  have hn := (length_list PatchGraph.rowEncoding).comp (fst suppliersEncoding PatchGraph.flagsEncoding)
  have ht := listGetDWithInput (slice_polyTime.comp (fst e encUnary)) (snd e encUnary) false
  exact filterWithInput (encIn := e) (encA := encUnary)
    (test := fun x i => (slice x.1 x.2).getD i false) (unary_range' hn) ht

#print axioms slice_eq
#print axioms retained_eq
#print axioms retained_length_le
#print axioms slice_polyTime
#print axioms retained_polyTime

end DeletionCode.Explicit.Machine.SourceSlice
