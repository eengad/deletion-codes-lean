import DeletionCode.Explicit.PatchTable
import DeletionCode.Explicit.Machine.PatchMerge
import DeletionCode.Explicit.Machine.PatchGraph

/-! Construct the patch table and its inventories from serialized gate records. -/
namespace DeletionCode.Explicit.Machine.SourcePatchTable

open LetterGraphCuts LetterSequence RulePatch
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open PatchMerge

variable {ℓ d s : ℕ} {α δ : Type}

abbrev GateRecord (δ : Type) := (ℕ × Interval) × (List ℕ × List δ)
abbrev Table (δ : Type) := List (List (GateRecord δ))

def gateRecord (g : GateData ℓ α) (marks : List ℕ) (inserted : List δ) : GateRecord δ :=
  ((g.id,data g.interval),(marks,inserted))

def tabulate (gs : Fin d × Fin s → GateData ℓ α)
    (ms : Fin d × Fin s → List ℕ) (ins : Fin d × Fin s → List δ) : Table δ :=
  (List.finRange d).map fun i => (List.finRange s).map fun j =>
    gateRecord (gs (i,j)) (ms (i,j)) (ins (i,j))

def allGates (gs : Table δ) : List (GateRecord δ) := gs.flatMap id

def intervals (gs : Table δ) : List Interval := (allGates gs).map (·.1.2)

def patches (gs : Table δ) : List Interval := coalesce (intervals gs)

def patchOf (ps : List Interval) (g : GateRecord δ) : ℕ :=
  (locate ps g.1.2).getD 0

def graph (gs : Table δ) : PatchGraph.Graph :=
  let ps := patches gs
  (ps.length,gs.map (List.map (patchOf ps)))

def gatesAt (gs : Table δ) (p : ℕ) : List (GateRecord δ) :=
  let ps := patches gs
  (allGates gs).filter (fun g => decide (patchOf ps g = p))

def marks (gs : Table δ) (p : ℕ) : List ℕ := (gatesAt gs p).flatMap (·.2.1)

def stock (gs : Table δ) (p : ℕ) : List δ := (gatesAt gs p).flatMap (·.2.2)

def owner (gs : Table δ) (id : ℕ) : Option ℕ :=
  ((allGates gs).find? (fun g => decide (g.1.1 = id))).map (patchOf (patches gs))

theorem allGates_eq (gs : Fin d × Fin s → GateData ℓ α)
    (ms : Fin d × Fin s → List ℕ) (ins : Fin d × Fin s → List δ) :
    allGates (tabulate gs ms ins) = (edgeList d s).map (fun e => gateRecord (gs e) (ms e) (ins e)) := by
  simp [allGates,tabulate,edgeList,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]

theorem intervals_eq (gs : Fin d × Fin s → GateData ℓ α)
    (ms : Fin d × Fin s → List ℕ) (ins : Fin d × Fin s → List δ) :
    intervals (tabulate gs ms ins) = (PatchTable.intervals gs).map data := by
  rw [intervals,allGates_eq]
  simp [PatchTable.intervals,List.map_map,Function.comp_def,gateRecord]

theorem patches_eq (gs : Fin d × Fin s → GateData ℓ α)
    (ms : Fin d × Fin s → List ℕ) (ins : Fin d × Fin s → List δ) :
    patches (tabulate gs ms ins) = (CreationInterval.coalesce (PatchTable.intervals gs)).map data := by
  rw [patches,intervals_eq,coalesce_eq]

theorem patchOf_eq (gs : Fin d × Fin s → GateData ℓ α)
    (ms : Fin d × Fin s → List ℕ) (ins : Fin d × Fin s → List δ) (e : Fin d × Fin s) :
    patchOf (patches (tabulate gs ms ins)) (gateRecord (gs e) (ms e) (ins e)) = (PatchTable.incidence gs e).val := by
  unfold patchOf
  have h := PatchMerge.label_eq (PatchTable.intervals gs) (gs e).interval (PatchTable.interval_mem gs e)
  rw [patches,intervals_eq]
  change (locate (coalesce ((PatchTable.intervals gs).map data)) (data (gs e).interval)).getD 0 = _
  rw [h]
  rfl

theorem graph_eq (gs : Fin d × Fin s → GateData ℓ α)
    (ms : Fin d × Fin s → List ℕ) (ins : Fin d × Fin s → List δ) :
    graph (tabulate gs ms ins) = PatchGraph.graphData (PatchTable.incidence gs) := by
  unfold graph PatchGraph.graphData
  dsimp only
  rw [patches_eq,List.length_map]
  congr 1
  simp only [tabulate,List.map_map,Function.comp_def]
  have hd : List.finRange d = List.ofFn (fun i : Fin d => i) := rfl
  have hs : List.finRange s = List.ofFn (fun j : Fin s => j) := rfl
  simp [hd,hs,List.map_ofFn,Function.comp_def]
  funext i
  congr 1
  funext j
  simpa only [patches_eq] using patchOf_eq gs ms ins (i,j)

theorem marks_eq (gs : Fin d × Fin s → GateData ℓ α)
    (ms : Fin d × Fin s → List ℕ) (ins : Fin d × Fin s → List δ)
    (p : Fin (PatchTable.patchCount gs)) (hm : ∀ e, (ms e).toFinset = (gs e).marks) :
    (marks (tabulate gs ms ins) p.val).toFinset = (PatchTable.patches gs).marks p := by
  ext k
  change _ ↔ k ∈ (atPatch (PatchTable.incidence gs) Finset.univ p).biUnion (fun e => (gs e).marks)
  simp only [marks,gatesAt,allGates_eq,List.mem_toFinset,List.mem_flatMap,List.mem_filter,List.mem_map,
    Finset.mem_biUnion,atPatch,Finset.mem_filter,edges,Finset.univ_product_univ,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨g,⟨⟨e,_,rfl⟩,he⟩,hk⟩
    exact ⟨e,Fin.ext (by simpa [patchOf_eq] using he),hm e ▸ List.mem_toFinset.mpr hk⟩
  · rintro ⟨e,he,hk⟩
    refine ⟨gateRecord (gs e) (ms e) (ins e),⟨⟨e,mem_edgeList e,rfl⟩,?_⟩,?_⟩
    · simp [patchOf_eq,he]
    · exact List.mem_toFinset.mp (hm e ▸ hk)

theorem stock_eq [DecidableEq α] [DecidableEq δ] (encode : Letter ℓ α → δ)
    (gs : Fin d × Fin s → GateData ℓ α)
    (ms : Fin d × Fin s → List ℕ) (ins : Fin d × Fin s → List δ)
    (p : Fin (PatchTable.patchCount gs))
    (hi : ∀ e, (ins e).toFinset = (gs e).inserted.image encode) :
    (stock (tabulate gs ms ins) p.val).toFinset = (PatchTable.stock gs p).image encode := by
  ext k
  simp only [stock,gatesAt,allGates_eq,List.mem_toFinset,List.mem_flatMap,List.mem_filter,List.mem_map,
    PatchTable.stock,Finset.mem_image,Finset.mem_biUnion,atPatch,Finset.mem_filter,edges,
    Finset.univ_product_univ,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨g,⟨⟨e,_,rfl⟩,he⟩,hk⟩
    have hs := hi e ▸ List.mem_toFinset.mpr hk
    obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp hs
    exact ⟨a,⟨e,Fin.ext (by simpa [patchOf_eq] using he),ha⟩,heq⟩
  · rintro ⟨a,⟨e,he,ha⟩,rfl⟩
    refine ⟨gateRecord (gs e) (ms e) (ins e),⟨⟨e,mem_edgeList e,rfl⟩,?_⟩,?_⟩
    · simp [patchOf_eq,he]
    · exact List.mem_toFinset.mp (hi e ▸ Finset.mem_image.mpr ⟨a,ha,rfl⟩)

theorem owner_eq (gs : Fin d × Fin s → GateData ℓ α)
    (ms : Fin d × Fin s → List ℕ) (ins : Fin d × Fin s → List δ) (id : ℕ) :
    owner (tabulate gs ms ins) id = (PatchTable.owner gs id).map Fin.val := by
  unfold owner PatchTable.owner
  rw [allGates_eq,List.find?_map]
  simp only [Function.comp_def,gateRecord,Option.map_map]
  congr 1
  funext e
  exact patchOf_eq gs ms ins e

abbrev gateEncoding (e : δ ↪ List Bool) :=
  encPair (encPair encUnary intervalEncoding) (encPair (encList encUnary) (encList e))

abbrev tableEncoding (e : δ ↪ List Bool) := encList (encList (gateEncoding e))

theorem allGates_polyTime (e : δ ↪ List Bool) :
    ComputableInPolyTime allGates (tableEncoding e) (encList (gateEncoding e)) := by
  let unit := encList (gateEncoding e)
  exact flatMapWithInput (encIn := tableEncoding e) (encA := unit) (encB := gateEncoding e)
    (f := fun _ row => row) id' (snd (tableEncoding e) unit)

theorem intervals_polyTime (e : δ ↪ List Bool) :
    ComputableInPolyTime intervals (tableEncoding e) intervalsEncoding := by
  have h := (fst (encPair encUnary intervalEncoding) (encPair (encList encUnary) (encList e))).snd'
  exact (ComputableInPolyTime.map h).comp (allGates_polyTime e)

theorem patches_polyTime (e : δ ↪ List Bool) :
    ComputableInPolyTime patches (tableEncoding e) intervalsEncoding :=
  coalesce_polyTime.comp (intervals_polyTime e)

theorem patchOf_polyTime (e : δ ↪ List Bool) :
    ComputableInPolyTime (fun x : List Interval × GateRecord δ => patchOf x.1 x.2)
      (encPair intervalsEncoding (gateEncoding e)) encUnary := by
  let src := encPair intervalsEncoding (gateEncoding e)
  have hg := snd intervalsEncoding (gateEncoding e)
  have hf := locate_polyTime.comp (encIn := src) (encMid := locateEncoding)
    ((fst intervalsEncoding (gateEncoding e)).prod hg.fst'.snd')
  exact (optionGetDWithInput hf (const 0)).of_enc_eq (fun _ => rfl)

theorem graph_polyTime (e : δ ↪ List Bool) :
    ComputableInPolyTime graph (tableEncoding e) PatchGraph.graphEncoding := by
  let src := tableEncoding e
  let g := gateEncoding e
  let r := encList g
  let p := encPair src r
  let u := encPair p g
  have hp := patches_polyTime e
  have hn := (length_list intervalEncoding).comp hp
  have hf := (patchOf_polyTime e).comp (encIn := u) (encMid := encPair intervalsEncoding g)
    ((hp.comp ((fst src r).comp (fst p g))).prod (snd p g))
  have hinner := mapWithInput (encIn := p) (encA := g) (encB := encUnary)
    (f := fun x g => patchOf (patches x.1) g) (snd src r) (hf.of_enc_eq (fun _ => rfl))
  have h := mapWithInput (encIn := src) (encA := r) (encB := encList encUnary)
    (f := fun x gs => gs.map (patchOf (patches x))) id' hinner
  exact (hn.prod h).of_enc_eq (fun _ => rfl)

abbrev inventoryEncoding (e : δ ↪ List Bool) := encPair (tableEncoding e) encUnary

theorem gatesAt_polyTime (e : δ ↪ List Bool) :
    ComputableInPolyTime (fun x : Table δ × ℕ => gatesAt x.1 x.2)
      (inventoryEncoding e) (encList (gateEncoding e)) := by
  let src := inventoryEncoding e
  let g := gateEncoding e
  let p := encPair src g
  have hx := fst (tableEncoding e) encUnary
  have hp := (patches_polyTime e).comp (encIn := p) (hx.comp (fst src g))
  have ho := (patchOf_polyTime e).comp (encIn := p) (encMid := encPair intervalsEncoding g)
    (hp.prod (snd src g))
  have hi := (snd (tableEncoding e) encUnary).comp (fst src g)
  exact filterWithInput (encIn := src) (encA := g)
    (test := fun x a => decide (patchOf (patches x.1) a = x.2))
    ((allGates_polyTime e).comp (encIn := src) hx) ((ho.decide_eq' hi).of_enc_eq (fun _ => rfl))

theorem marks_polyTime (e : δ ↪ List Bool) :
    ComputableInPolyTime (fun x : Table δ × ℕ => marks x.1 x.2)
      (inventoryEncoding e) (encList encUnary) := by
  let src := inventoryEncoding e
  let g := gateEncoding e
  exact flatMapWithInput (encIn := src) (encA := g) (encB := encUnary)
    (f := fun _ g => g.2.1) (gatesAt_polyTime e) (snd src g).snd'.fst'

theorem stock_polyTime (e : δ ↪ List Bool) :
    ComputableInPolyTime (fun x : Table δ × ℕ => stock x.1 x.2)
      (inventoryEncoding e) (encList e) := by
  let src := inventoryEncoding e
  let g := gateEncoding e
  exact flatMapWithInput (encIn := src) (encA := g) (encB := e)
    (f := fun _ g => g.2.2) (gatesAt_polyTime e) (snd src g).snd'.snd'

theorem owner_polyTime (e : δ ↪ List Bool) :
    ComputableInPolyTime (fun x : Table δ × ℕ => owner x.1 x.2)
      (inventoryEncoding e) (encOption encUnary) := by
  let src := inventoryEncoding e
  let g := gateEncoding e
  let p := encPair src g
  have hg := snd src g
  have hx := fst (tableEncoding e) encUnary
  have hy := snd (tableEncoding e) encUnary
  have h := findWithInput (encIn := src) (encA := g)
    (test := fun x g => decide (g.1.1 = x.2))
    ((allGates_polyTime e).comp (encIn := src) hx) (hg.fst'.fst'.decide_eq' (hy.comp (fst src g)))
  have hp := (patches_polyTime e).comp (encIn := p) (hx.comp (fst src g))
  have hf := (patchOf_polyTime e).comp (encIn := p) (encMid := encPair intervalsEncoding g)
    (hp.prod hg)
  exact optionMapWithInput (encA := src) (encB := g) (encC := encUnary)
    (f := fun x g => patchOf (patches x.1) g) h (hf.of_enc_eq (fun _ => rfl))

theorem patchCount_le (gs : Fin d × Fin s → GateData ℓ α)
    (ms : Fin d × Fin s → List ℕ) (ins : Fin d × Fin s → List δ) :
    (patches (tabulate gs ms ins)).length ≤ d*s := by
  rw [patches_eq,List.length_map]
  simpa using Fintype.card_le_of_surjective _ (PatchTable.incidence_surjective gs)

#print axioms graph_eq
#print axioms marks_eq
#print axioms stock_eq
#print axioms owner_eq
#print axioms graph_polyTime
#print axioms marks_polyTime
#print axioms stock_polyTime
#print axioms owner_polyTime
#print axioms patchCount_le

end DeletionCode.Explicit.Machine.SourcePatchTable
