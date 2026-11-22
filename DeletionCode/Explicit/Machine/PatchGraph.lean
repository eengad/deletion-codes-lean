import DeletionCode.Explicit.FirstEventGeometry
import DeletionCode.Explicit.Machine.SourceExposure
import Batteries.Tactic.OpenPrivate

/-! The first-event graph test on lists of incidences. -/
namespace DeletionCode.Explicit.Machine.PatchGraph

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open RulePatch
open private incident neighbors expand expandFrom from DeletionCode.Explicit.RulePatchComponents

variable {d s c : ℕ}

abbrev Graph := ℕ × List (List ℕ)
abbrev rowEncoding := encList encUnary
abbrev graphEncoding := encPair encUnary (encList rowEncoding)

def graphData (a : Incidence d s c) : Graph :=
  (c,List.ofFn fun i => List.ofFn fun j => (a (i,j)).val)

def vertexNumber (x : Fin d ⊕ Fin c) : ℕ := (finSumFinEquiv x).val

private lemma number_left (i : Fin d) :
    vertexNumber (Sum.inl (β := Fin c) i) = i.val := by
  simp [vertexNumber,finSumFinEquiv_apply_left]

private lemma number_right (j : Fin c) :
    vertexNumber (Sum.inr (α := Fin d) j) = d+j.val := by
  simp [vertexNumber,finSumFinEquiv_apply_right]

def adjacent (g : Graph) (i j : ℕ) : Bool :=
  let d := g.2.length
  if i < d then
    if d ≤ j then (g.2.getD i []).contains (j-d) else false
  else
    if j < d then (g.2.getD j []).contains (i-d) else false

private theorem incident_eq (a : Incidence d s c) (i : Fin d) (p : Fin c) :
    ((graphData a).2.getD i.val []).contains p.val = incident a i p := by
  apply Bool.eq_iff_iff.mpr
  have hi := BooleanFibres.ofFn_getD (fun i => List.ofFn fun j => (a (i,j)).val) i []
  change ((List.ofFn fun i => List.ofFn fun j => (a (i,j)).val).getD i.val []).contains p.val = true ↔ _
  rw [hi]
  simp [incident,List.mem_ofFn,Fin.ext_iff]

theorem adjacent_eq (a : Incidence d s c) (x y : Fin d ⊕ Fin c) :
    adjacent (graphData a) (vertexNumber x) (vertexNumber y) = RulePatch.adjacent a x y := by
  have hlen : (graphData a).2.length = d := by simp [graphData]
  cases x <;> cases y
  · rename_i i j
    simp [adjacent,RulePatch.adjacent,number_left,hlen,i.isLt,Nat.not_le_of_lt j.isLt]
  · rename_i i j
    have hd : d ≤ d+j.val := by omega
    simpa only [adjacent,RulePatch.adjacent,number_left,number_right,hlen,i.isLt,hd,↓reduceIte,Nat.add_sub_cancel_left]
      using incident_eq a i j
  · rename_i p i
    have hd : ¬d+p.val < d := by omega
    simpa only [adjacent,RulePatch.adjacent,number_left,number_right,hlen,i.isLt,hd,↓reduceIte,Nat.add_sub_cancel_left]
      using incident_eq a i p
  · simp [adjacent,RulePatch.adjacent,number_right,hlen]

def vertexCount (g : Graph) : ℕ := g.2.length+g.1

def seed (g : Graph) (x : ℕ) : List Bool :=
  (List.range (vertexCount g)).map (fun i => decide (i = x))

def step (g : Graph) (seen : List Bool) : List Bool :=
  (List.range (vertexCount g)).map fun i => seen.getD i false ||
    (List.range (vertexCount g)).any (fun j => seen.getD j false && adjacent g j i)

def component (g : Graph) (x : ℕ) : List Bool := (step g)^[vertexCount g] (seed g x)

private theorem range_map_eq {α : Type} {k : ℕ} (f : ℕ → α) :
    (List.range k).map f = List.ofFn (fun i : Fin k => f i.val) := by
  have hr : List.range k = (List.finRange k).map Fin.val := by simp
  rw [hr,List.map_map]
  change (List.ofFn (fun i : Fin k => i)).map (f ∘ Fin.val) = _
  rw [List.map_ofFn]
  rfl

private def flags (v : Finset (Fin d ⊕ Fin c)) : List Bool :=
  List.ofFn fun i : Fin (d+c) => decide (finSumFinEquiv.symm i ∈ v)

private theorem vertexCount_eq (a : Incidence d s c) : vertexCount (graphData a) = d+c := by
  simp [vertexCount,graphData]

private theorem seed_eq (a : Incidence d s c) (x : Fin d ⊕ Fin c) :
    seed (graphData a) (vertexNumber x) = flags {x} := by
  rw [seed,vertexCount_eq,range_map_eq]
  congr 1
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [flags,decide_eq_true_eq,Finset.mem_singleton,vertexNumber]
  constructor
  · intro h
    exact finSumFinEquiv.symm_apply_eq.mpr (Fin.ext (of_decide_eq_true h))
  · intro h
    exact decide_eq_true (congrArg Fin.val (finSumFinEquiv.symm_apply_eq.mp h))

private theorem flags_get (V : Finset (Fin d ⊕ Fin c)) (i : Fin (d+c)) :
    (flags V).getD i.val false = decide (finSumFinEquiv.symm i ∈ V) :=
  BooleanFibres.ofFn_getD _ i false

private theorem step_eq (a : Incidence d s c) (V : Finset (Fin d ⊕ Fin c)) :
    step (graphData a) (flags V) = flags (expand a V) := by
  rw [step,vertexCount_eq,range_map_eq]
  congr 1
  funext i
  change ((flags V).getD i.val false ||
      (List.range (d+c)).any fun j => (flags V).getD j false && adjacent (graphData a) j i.val) =
    decide (finSumFinEquiv.symm i ∈ expand a V)
  have hr : List.range (d+c) = (List.finRange (d+c)).map Fin.val := by simp
  rw [hr,List.any_map,flags_get]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true_iff,decide_eq_true_eq,List.any_eq_true,List.mem_finRange,true_and,
    Function.comp_def,flags_get,Bool.and_eq_true_iff,expand,Finset.mem_union,Finset.mem_biUnion,
    neighbors,Finset.mem_filter,Finset.mem_univ]
  apply or_congr_right
  constructor
  · rintro ⟨j,hj,h⟩
    refine ⟨finSumFinEquiv.symm j,hj,?_⟩
    have h1 : vertexNumber (finSumFinEquiv.symm j) = j.val := by simp [vertexNumber]
    have h2 : vertexNumber (finSumFinEquiv.symm i) = i.val := by simp [vertexNumber]
    simpa only [← adjacent_eq a,h1,h2] using h
  · rintro ⟨j,hj,h⟩
    refine ⟨finSumFinEquiv j,by simpa using hj,?_⟩
    have he := (adjacent_eq a j (finSumFinEquiv.symm i)).trans h
    simpa [vertexNumber] using he

theorem component_eq (a : Incidence d s c) (x : Fin d ⊕ Fin c) :
    component (graphData a) (vertexNumber x) = flags (RulePatch.component a x) := by
  unfold component RulePatch.component
  rw [vertexCount_eq,seed_eq]
  generalize d+c = k
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,expandFrom,step_eq]

def ruleIds (g : Graph) (x : ℕ) : List ℕ :=
  let f := component g x
  (List.range g.2.length).filter (fun i => f.getD i false)

def patchIds (g : Graph) (x : ℕ) : List ℕ :=
  let f := component g x
  (List.range g.1).filter (fun j => f.getD (g.2.length+j) false)

theorem ruleIds_eq (a : Incidence d s c) (x : Fin d ⊕ Fin c) :
    ruleIds (graphData a) (vertexNumber x) =
      ((List.finRange d).filter (fun i => decide (i ∈ componentRules a x))).map Fin.val := by
  unfold ruleIds
  rw [component_eq]
  simp only [graphData,List.length_ofFn]
  rw [show List.range d = (List.finRange d).map Fin.val from by simp,List.filter_map]
  congr 1
  apply List.filter_congr
  intro i _
  simp only [Function.comp_def,componentRules,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [← Fin.val_castAdd c i,flags_get,finSumFinEquiv_symm_apply_castAdd]

theorem patchIds_eq (a : Incidence d s c) (x : Fin d ⊕ Fin c) :
    patchIds (graphData a) (vertexNumber x) =
      ((List.finRange c).filter (fun j => decide (j ∈ componentPatches a x))).map Fin.val := by
  unfold patchIds
  rw [component_eq]
  simp only [graphData,List.length_ofFn]
  rw [show List.range c = (List.finRange c).map Fin.val from by simp,List.filter_map]
  congr 1
  apply List.filter_congr
  intro j _
  simp only [Function.comp_def,componentPatches,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [← Fin.val_natAdd d j,flags_get,finSumFinEquiv_symm_apply_natAdd]

private theorem finsetLength {k : ℕ} (S : Finset (Fin k)) :
    ((List.finRange k).filter (fun j => decide (j ∈ S))).length = S.card := by
  have hn := (List.nodup_finRange k).filter (fun j => decide (j ∈ S))
  have he : ((List.finRange k).filter (fun j => decide (j ∈ S))).toFinset = S := by
    ext j
    simp
  exact (List.toFinset_card_of_nodup hn).symm.trans (congrArg Finset.card he)

def event (s R : ℕ) (g : Graph) (i : ℕ) : Bool :=
  let r := (ruleIds g i).length
  let p := (patchIds g i).length
  decide (R < r ∨ r+p ≤ r*s)

theorem event_eq (a : Incidence d s c) (R : ℕ) (i : Fin d) :
    event s R (graphData a) i.val = FirstEvent.componentEvent a R i := by
  have he : i.val = vertexNumber (Sum.inl (β := Fin c) i) := (number_left i).symm
  unfold event FirstEvent.componentEvent
  rw [he,ruleIds_eq,patchIds_eq,List.length_map,List.length_map,finsetLength,finsetLength]

abbrev graphIndexEncoding := encPair graphEncoding encUnary
abbrev graphPairEncoding := encPair graphIndexEncoding encUnary
abbrev flagsEncoding := encList encBool

theorem vertexCount_polyTime : ComputableInPolyTime vertexCount graphEncoding encUnary := by
  have hd := (length_list rowEncoding).comp (snd encUnary (encList rowEncoding))
  exact (unary_add' hd (fst encUnary (encList rowEncoding))).of_enc_eq (fun _ => rfl)

theorem adjacent_polyTime :
    ComputableInPolyTime (fun x : (Graph × ℕ) × ℕ => adjacent x.1.1 x.1.2 x.2)
      graphPairEncoding encBool := by
  let e := graphPairEncoding
  have hg := (fst graphEncoding encUnary).comp (fst graphIndexEncoding encUnary)
  have hi := (snd graphEncoding encUnary).comp (fst graphIndexEncoding encUnary)
  have hj := snd graphIndexEncoding encUnary
  have hs := hg.snd'
  have hd := (length_list rowEncoding).comp hs
  have hr := listGetDWithInput hs hi ([] : List ℕ)
  have hp := listGetDWithInput hs hj ([] : List ℕ)
  have hfirst := (unary_le' hd hj).ite' (contains hr (unary_sub' hj hd)) (const false)
  have hsecond := (unary_lt' hj hd).ite' (contains hp (unary_sub' hi hd)) (const false)
  have h := (unary_lt' hi hd).ite' hfirst hsecond
  exact h.of_enc_eq (fun x => by simp [adjacent,Function.comp_def])

theorem seed_polyTime :
    ComputableInPolyTime (fun x : Graph × ℕ => seed x.1 x.2) graphIndexEncoding flagsEncoding := by
  let e := graphIndexEncoding
  have hg := fst graphEncoding encUnary
  have hx := (snd graphEncoding encUnary).comp (fst e encUnary)
  have hi := snd e encUnary
  unfold seed
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := encBool)
    (f := fun x i => decide (i = x.2)) (unary_range' (vertexCount_polyTime.comp hg))
    (hi.decide_eq' hx)

theorem step_polyTime :
    ComputableInPolyTime (fun x : Graph × List Bool => step x.1 x.2)
      (encPair graphEncoding flagsEncoding) flagsEncoding := by
  let e := encPair graphEncoding flagsEncoding
  let p := encPair e encUnary
  let r := encPair p encUnary
  have hg := fst graphEncoding flagsEncoding
  have hf := snd graphEncoding flagsEncoding
  have hlist := unary_range' (vertexCount_polyTime.comp hg)
  have hx := fst e encUnary
  have hi := snd e encUnary
  have hz := fst p encUnary
  have hj := snd p encUnary
  have ha := adjacent_polyTime.comp (encIn := r) (encMid := graphPairEncoding)
    ((((hg.comp hx).comp hz).prod hj).prod (hi.comp hz))
  have hjSeen := listGetDWithInput ((hf.comp hx).comp hz) hj false
  have hiSeen := listGetDWithInput (hf.comp hx) hi false
  have hs := anyWithInput (encIn := p) (encA := encUnary)
    (test := fun x j => x.1.2.getD j false && adjacent x.1.1 j x.2)
    (hlist.comp hx) ((bool_and' hjSeen ha).of_enc_eq (fun _ => rfl))
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := encBool)
    (f := fun x i => x.2.getD i false ||
      (List.range (vertexCount x.1)).any (fun j => x.2.getD j false && adjacent x.1 j i))
    hlist ((bool_or' hiSeen hs).of_enc_eq (fun _ => rfl))

theorem component_polyTime :
    ComputableInPolyTime (fun x : Graph × ℕ => component x.1 x.2) graphIndexEncoding flagsEncoding := by
  let e := graphIndexEncoding
  have hg := fst graphEncoding encUnary
  have hn := vertexCount_polyTime.comp hg
  have hsize := (PolyBounded.const 3).mul (show PolyBounded (fun x : Graph × ℕ => (e x).length)
    (fun x => vertexCount x.1) by
    simpa only [Function.comp_def,encUnary_apply,List.length_replicate] using hn.polyBounded_length)
  exact (iterateWith_spec (step := step) hg hn seed_polyTime step_polyTime
    (fun x _ fs => fs.length = vertexCount x.1)
    (fun x => by simp [seed])
    (fun x i fs _ _ => by simp [step]) hsize (by
      intro x i fs hi h
      have h1 := length_encList_le encBool fs (b := 1) (by intro a _; cases a <;> decide)
      rw [h] at h1
      simpa [Nat.mul_comm] using h1)).1

private theorem ids_polyTime (patch : Bool) :
    ComputableInPolyTime (if patch then fun x : Graph × ℕ => patchIds x.1 x.2
      else fun x => ruleIds x.1 x.2) graphIndexEncoding rowEncoding := by
  let e := graphIndexEncoding
  let p := encPair e encUnary
  have hg := fst graphEncoding encUnary
  have hd := (length_list rowEncoding).comp hg.snd'
  have hj := snd e encUnary
  have hf := component_polyTime.comp (encIn := p) (fst e encUnary)
  cases patch
  · exact filterWithInput (encIn := e) (encA := encUnary)
      (test := fun x i => (component x.1 x.2).getD i false)
      (unary_range' hd) (listGetDWithInput hf hj false)
  · exact filterWithInput (encIn := e) (encA := encUnary)
      (test := fun x j => (component x.1 x.2).getD (x.1.2.length+j) false)
      (unary_range' hg.fst') (listGetDWithInput hf (unary_add' (hd.comp (fst e encUnary)) hj) false)

theorem ruleIds_polyTime :
    ComputableInPolyTime (fun x : Graph × ℕ => ruleIds x.1 x.2) graphIndexEncoding rowEncoding :=
  ids_polyTime false

theorem patchIds_polyTime :
    ComputableInPolyTime (fun x : Graph × ℕ => patchIds x.1 x.2) graphIndexEncoding rowEncoding :=
  ids_polyTime true

abbrev eventEncoding := encPair (encPair encUnary encUnary) graphIndexEncoding

theorem event_polyTime :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × (Graph × ℕ) => event x.1.1 x.1.2 x.2.1 x.2.2)
      eventEncoding encBool := by
  let e := eventEncoding
  have hb := fst (encPair encUnary encUnary) graphIndexEncoding
  have hg := snd (encPair encUnary encUnary) graphIndexEncoding
  have hr := (length_list encUnary).comp (ruleIds_polyTime.comp (encIn := e) hg)
  have hp := (length_list encUnary).comp (patchIds_polyTime.comp (encIn := e) hg)
  have h := decide_or (unary_lt' hb.snd' hr)
    (unary_le' (unary_add' hr hp) (unary_mul' hr hb.fst'))
  exact h.of_enc_eq (fun _ => rfl)

#print axioms adjacent_eq
#print axioms component_eq
#print axioms component_polyTime
#print axioms event_eq
#print axioms event_polyTime

end DeletionCode.Explicit.Machine.PatchGraph
