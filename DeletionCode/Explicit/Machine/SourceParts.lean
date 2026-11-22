import DeletionCode.Explicit.ComponentRows
import DeletionCode.Explicit.Machine.PatchGraph
import DeletionCode.Explicit.Machine.SourceLists

/-! Keep chronological recognizer rows under the least rule of each patch component. -/
namespace DeletionCode.Explicit.Machine.SourceParts

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open RulePatch Ternary SourceLists
open PatchGraph (Graph graphData graphEncoding graphIndexEncoding ruleIds ruleIds_eq)

variable {d s c n : ℕ}

def representative (g : Graph) (j : ℕ) : ℕ := (ruleIds g j).getD 0 j

theorem representative_eq (a : Incidence d s c) (j : Fin d) :
    representative (graphData a) j.val = (RulePatch.representative a j).val := by
  unfold representative RulePatch.representative
  have hj : j.val = PatchGraph.vertexNumber (Sum.inl (β := Fin c) j) := rfl
  rw [hj,ruleIds_eq]
  simp only [List.getD_eq_getElem?_getD,← List.head?_eq_getElem?,List.head?_map,List.head?_filter]
  cases (List.finRange d).find? (fun i => decide (i ∈ componentRules a (.inl j))) <;> rfl

def ids (g : Graph) (p : ℕ) : List ℕ :=
  (List.range g.2.length).filter (fun j => decide (representative g j = p))

theorem ids_eq (a : Incidence d s c) (p : Fin d) :
    ids (graphData a) p.val = (RulePatch.ids a p).map Fin.val := by
  unfold ids RulePatch.ids
  have h : (graphData a).2.length = d := by simp [graphData]
  rw [h,show List.range d = (List.finRange d).map Fin.val from by simp,List.filter_map]
  congr 1
  apply List.filter_congr
  intro j _
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_def,representative_eq,decide_eq_true_eq,beq_iff_eq]
  exact Fin.ext_iff.symm

def partRows (g : Graph) (rs : Rows) (p : ℕ) : Rows := (ids g p).map (fun i => rs.getD i [])

def parts (g : Graph) (rs : Rows) : List Rows :=
  (List.range g.2.length).map (partRows g rs)

theorem parts_eq (a : Incidence d s c) (rs : Fin d → Fin n → FieldHash.F₃) :
    parts (graphData a) (List.ofFn (fun i => List.ofFn (rs i))) =
      List.ofFn (fun i => (RulePatch.partRows a rs i).map List.ofFn) := by
  unfold parts
  have h : (graphData a).2.length = d := by simp [graphData]
  rw [h,range_map_eq]
  congr 1
  funext i
  unfold partRows RulePatch.partRows
  rw [ids_eq,List.map_map,List.map_map]
  apply List.map_congr_left
  intro j _
  exact BooleanFibres.ofFn_getD (fun i => List.ofFn (rs i)) j []

theorem representative_polyTime :
    ComputableInPolyTime (fun x : Graph × ℕ => representative x.1 x.2) graphIndexEncoding encUnary := by
  have hh := Turing.MultiTapeTM.ComputableInPolyTime.getElem? (encA := encUnary)
    PatchGraph.ruleIds_polyTime (const 0)
  exact (optionGetDWithInput hh (snd graphEncoding encUnary)).of_enc_eq (fun _ => rfl)

theorem ids_polyTime :
    ComputableInPolyTime (fun x : Graph × ℕ => ids x.1 x.2) graphIndexEncoding PatchGraph.rowEncoding := by
  let e := graphIndexEncoding
  let p := encPair e encUnary
  have hg := (fst graphEncoding encUnary).comp (fst e encUnary)
  have hi := (snd graphEncoding encUnary).comp (fst e encUnary)
  have hj := snd e encUnary
  have h := representative_polyTime.comp (encIn := p) (hg.prod hj)
  exact filterWithInput (encIn := e) (encA := encUnary)
    (test := fun x j => decide (representative x.1 j = x.2))
    (unary_range' ((length_list PatchGraph.rowEncoding).comp (fst graphEncoding encUnary).snd'))
    ((h.decide_eq' hi).of_enc_eq (fun _ => rfl))

abbrev partRowsEncoding := encPair (encPair graphEncoding Ternary.rowsEncoding) encUnary
abbrev partsEncoding := encPair graphEncoding Ternary.rowsEncoding

theorem partRows_polyTime :
    ComputableInPolyTime (fun x : (Graph × Rows) × ℕ => partRows x.1.1 x.1.2 x.2)
      partRowsEncoding rowsEncoding := by
  let e := partRowsEncoding
  let p := encPair e encUnary
  have hd := fst partsEncoding encUnary
  have hj := snd partsEncoding encUnary
  have hi := ids_polyTime.comp (encIn := e) (hd.fst'.prod hj)
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := Ternary.rowEncoding)
    (f := fun x j => x.1.2.getD j []) (hi.of_enc_eq (fun _ => rfl))
    (listGetDWithInput (hd.snd'.comp (fst e encUnary)) (snd e encUnary) ([] : Row))

theorem parts_polyTime :
    ComputableInPolyTime (fun x : Graph × Rows => parts x.1 x.2)
      partsEncoding SourceExposure.componentsEncoding := by
  let e := partsEncoding
  let p := encPair e encUnary
  have hg := fst graphEncoding rowsEncoding
  have hd := (length_list PatchGraph.rowEncoding).comp hg.snd'
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := rowsEncoding)
    (f := fun x i => partRows x.1 x.2 i) (unary_range' hd) partRows_polyTime

#print axioms parts_eq
#print axioms parts_polyTime

end DeletionCode.Explicit.Machine.SourceParts
