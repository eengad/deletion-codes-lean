import DeletionCode.Explicit.RecognizerTransition

/-! The recognizer's computed incidence is the certified first-event update. -/

namespace DeletionCode.Explicit.Recognizer

open LetterGraphCuts RulePatch FirstEvent
open scoped BigOperators

variable {ℓ q L s d c c' : ℕ}

private theorem event_congr {d' : ℕ} (hd : d = d') (hc : c = c')
    (a : Incidence d s c) (a' : Incidence d' s c')
    (ha : ∀ i j, (a (i,j)).val = (a' (Fin.cast hd i,j)).val) (R : ℕ) (i : Fin d) :
    componentEvent a R i = componentEvent a' R (Fin.cast hd i) := by
  subst d'
  subst c'
  have he : a = a' := by
    funext e
    exact Fin.ext (ha e.1 e.2)
  subst a'
  rfl

private theorem finRange_last (d : ℕ) :
    List.finRange (d+1) = (List.finRange d).map Fin.castSucc ++ [Fin.last d] := by
  have h (n : ℕ) : List.finRange n = List.ofFn (fun i : Fin n => i) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [List.getElem_finRange]
  rw [h (d+1),List.ofFn_succ',List.concat_eq_append,h d,List.map_ofFn]
  rfl

private def appendData (data : Fin d × Fin s → GateData ℓ (Fin q))
    (added : Fin s → GateData ℓ (Fin q)) : Fin (d+1) × Fin s → GateData ℓ (Fin q) :=
  fun (i,j) => Fin.lastCases (added j) (fun k => data (k,j)) i

private theorem intervals_append (data : Fin d × Fin s → GateData ℓ (Fin q))
    (added : Fin s → GateData ℓ (Fin q)) :
    PatchTable.intervals (appendData data added) =
      PatchTable.intervals data ++ (List.finRange s).map (fun j => (added j).interval) := by
  simp [PatchTable.intervals,edgeList,finRange_last d,List.flatMap_append,List.flatMap_map,
    List.map_flatMap,List.map_map,Function.comp_def,appendData]

private theorem label_eq_of_coalesce {xs ys : List (CreationInterval ℓ)} (h : CreationInterval.coalesce xs = CreationInterval.coalesce ys)
    {i : CreationInterval ℓ} (hx : i ∈ xs) (hy : i ∈ ys) :
    (CreationInterval.label xs i hx).val = (CreationInterval.label ys i hy).val := by
  let x := CreationInterval.label xs i hx
  let y := CreationInterval.label ys i hy
  have hp := CreationInterval.label_contains xs i hx
  have hq := CreationInterval.label_contains ys i hy
  have hcast : ((CreationInterval.coalesce ys).get (Fin.cast (congrArg List.length h) x)).Contains i := by
    have hget (a b : List (CreationInterval ℓ)) (e : a = b) (j : Fin a.length) :
        b.get (Fin.cast (congrArg List.length e) j) = a.get j := by
      subst b
      rfl
    rw [hget _ _ h x]
    exact hp
  have he := CreationInterval.containing_index_unique (CreationInterval.coalesce_partition ys).separated hcast hq
  exact congrArg Fin.val he

private theorem incidence_append (data : Fin d × Fin s → GateData ℓ (Fin q))
    (added : Fin s → GateData ℓ (Fin q)) :
    let old := PatchTable.intervals data
    let new := fun j => (added j).interval
    let a := PatchTable.incidence data
    let next := extendIncidence old new a
    (CreationInterval.coalesce (PatchTable.intervals (appendData data added))).length =
      (CreationInterval.coalesce (CreationInterval.coalesce old ++ (List.finRange s).map new)).length ∧
    ∀ i j, (PatchTable.incidence (appendData data added) (i,j)).val = (next (i,j)).val := by
  dsimp only
  let old := PatchTable.intervals data
  let new := fun j : Fin s => (added j).interval
  let batch := (List.finRange s).map new
  have hi : PatchTable.intervals (appendData data added) = old ++ batch := intervals_append data added
  have hc := CreationInterval.coalesce_append_patches old batch
  refine ⟨congrArg List.length ((congrArg CreationInterval.coalesce hi).trans hc.symm),?_⟩
  intro i j
  induction i using Fin.lastCases with
  | last =>
    let z := (added j).interval
    have hz : z ∈ batch := List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩
    have hadded : (appendData data added (Fin.last d,j)).interval = z := by simp [appendData,z]
    have ht : z ∈ PatchTable.intervals (appendData data added) := hi.symm ▸ List.mem_append_right _ hz
    have hindex : (PatchTable.incidence (appendData data added) (Fin.last d,j)).val =
        (CreationInterval.label (PatchTable.intervals (appendData data added)) z ht).val := by
      unfold PatchTable.incidence
      exact congrArg (fun x => (CreationInterval.label (PatchTable.intervals (appendData data added)) x.1 x.2).val)
        (Subtype.ext hadded : (⟨_,PatchTable.interval_mem _ _⟩ : ↥{x | x ∈ PatchTable.intervals (appendData data added)}) = ⟨z,ht⟩)
    rw [hindex]
    simp only [extendIncidence,Fin.lastCases_last]
    exact label_eq_of_coalesce ((congrArg CreationInterval.coalesce hi).trans hc.symm) ht (List.mem_append_right _ hz)
  | cast i =>
    let z := (data (i,j)).interval
    have hgate : (appendData data added (i.castSucc,j)).interval = z := by simp [appendData,z]
    have ho : z ∈ old := PatchTable.interval_mem data (i,j)
    have hz : z ∈ PatchTable.intervals (appendData data added) := hi.symm ▸ List.mem_append_left _ ho
    have hindex : (PatchTable.incidence (appendData data added) (i.castSucc,j)).val =
        (CreationInterval.label (PatchTable.intervals (appendData data added)) z hz).val := by
      unfold PatchTable.incidence
      exact congrArg (fun x => (CreationInterval.label (PatchTable.intervals (appendData data added)) x.1 x.2).val)
        (Subtype.ext hgate : (⟨_,PatchTable.interval_mem _ _⟩ : ↥{x | x ∈ PatchTable.intervals (appendData data added)}) = ⟨z,hz⟩)
    rw [hindex]
    have hsame := label_eq_of_coalesce (congrArg CreationInterval.coalesce hi) hz (List.mem_append_left batch ho)
    have hlabel := CreationInterval.label_append_old old batch ho (PatchTable.incidence data (i,j)) rfl
    dsimp only at hlabel
    have hv := congrArg Fin.val hlabel
    simp only [extendIncidence,Fin.lastCases_castSucc]
    exact hsame.trans hv.symm

/-- The executable test on an appended rule agrees with the certified
component update, including the other components' event thresholds. -/
theorem all_after_appendData (data : Fin d × Fin s → GateData ℓ (Fin q))
    (added : Fin s → GateData ℓ (Fin q)) (R : ℕ)
    (hbefore : ∀ i, componentEvent (PatchTable.incidence data) R i = false)
    (hlast : componentEvent (PatchTable.incidence (appendData data added)) R (Fin.last d) = false) :
    ∀ i, componentEvent (PatchTable.incidence (appendData data added)) R i = false := by
  let next := extendIncidence (PatchTable.intervals data) (fun j => (added j).interval) (PatchTable.incidence data)
  obtain ⟨hc,he⟩ := incidence_append data added
  have h (i : Fin (d+1)) :
      componentEvent (PatchTable.incidence (appendData data added)) R i = componentEvent next R i :=
    event_congr rfl hc _ next he R i
  have hx := all_preEvent_of_last _ _ (PatchTable.incidence data) R hbefore
    ((h (Fin.last d)).symm.trans hlast)
  exact fun i => (h i).trans (hx i)

private theorem event_data_congr {n : ℕ} (hd : d = n)
    (a : Fin d × Fin s → GateData ℓ (Fin q)) (a' : Fin n × Fin s → GateData ℓ (Fin q))
    (he : ∀ i j, a (i,j) = a' (Fin.cast hd i,j)) (R : ℕ) (i : Fin d) :
    componentEvent (PatchTable.incidence a) R i =
      componentEvent (PatchTable.incidence a') R (Fin.cast hd i) := by
  subst n
  have h : a = a' := funext (fun e => he e.1 e.2)
  subst a'
  rfl

private theorem snapshot_append_data (hs : History ℓ q L s) (p : Batch ℓ q L s)
    (i : Fin (hs.length+1)) (j : Fin s) :
    appendData (gates hs) (fun j => (p.bubbles j).data) (i,j) =
      gates (hs++[p]) (Fin.cast (by simp) i,j) := by
  induction i using Fin.lastCases with
  | last =>
    simp only [appendData,Fin.lastCases_last,gates]
    change (p.bubbles j).data = (((hs++[p]).get ⟨hs.length,by simp⟩).bubbles j).data
    have hget : (hs++[p]).get ⟨hs.length,by simp⟩ = p := by
      change (hs++[p])[hs.length]'(by simp) = p
      rw [List.getElem_append_right le_rfl]
      simp
    rw [hget]
  | cast i =>
    simp only [appendData,Fin.lastCases_castSucc,gates]
    change ((hs.get i).bubbles j).data =
      (((hs++[p]).get ⟨i.val,by simp [i.isLt.trans_le (Nat.le_succ _)]⟩).bubbles j).data
    exact congrArg (fun w : Batch ℓ q L s => (w.bubbles j).data)
      (List.getElem_append_left i.isLt).symm

/-- It suffices to test the last added rule. A quiet last component
implies every component is quiet. -/
theorem beforeEvent_append (hs : History ℓ q L s) (p : Batch ℓ q L s) (R : ℕ)
    (hbefore : ∀ i, componentEvent (PatchTable.incidence (gates hs)) R i = false)
    (hlast : componentEvent (PatchTable.incidence (gates (hs++[p]))) R
      ⟨hs.length,by simp⟩ = false) :
    ∀ i, componentEvent (PatchTable.incidence (gates (hs++[p]))) R i = false := by
  let ds := appendData (gates hs) (fun j => (p.bubbles j).data)
  have hlen : hs.length+1 = (hs++[p]).length := by simp
  have hsame := snapshot_append_data hs p
  have he := event_data_congr hlen ds (gates (hs++[p])) hsame R
  have hterminal : componentEvent (PatchTable.incidence ds) R (Fin.last hs.length) = false :=
    (he _).trans hlast
  have hall := all_after_appendData (gates hs) (fun j => (p.bubbles j).data) R hbefore hterminal
  intro i
  let i' := Fin.cast hlen.symm i
  have hi : Fin.cast hlen i' = i := Fin.ext rfl
  simpa only [hi] using (he i').symm.trans (hall i')


/-- Size and cycle counts for the component where the recognizer stops. -/
def WitnessBounds (a : Incidence d s c) (R : ℕ) (i : Fin d) : Prop :=
  let root := Sum.inl i
  let r := (componentRules a root).card
  let p := (componentPatches a root).card
  let g := cycles r s p
  r ≤ 8*s*R+1 ∧ g ≤ 10*s ∧ p = (s-1)*r+1-g ∧ (g = 0 ∧ R < r ∨ 0 < g)

private theorem witnessBounds_congr {d' : ℕ} (hd : d = d') (hc : c = c')
    (a : Incidence d s c) (a' : Incidence d' s c')
    (ha : ∀ i j, (a (i,j)).val = (a' (Fin.cast hd i,j)).val) (R : ℕ) (i : Fin d) :
    WitnessBounds a R i ↔ WitnessBounds a' R (Fin.cast hd i) := by
  subst d'
  subst c'
  have he : a = a' := funext fun e => Fin.ext (ha e.1 e.2)
  subst a'
  rfl

/-- Instantiate the first-event count with the actual gate intervals of the
recognizer's last rule and its previous history. -/
theorem witnessBounds_append (hs : History ℓ q L s) (p : Batch ℓ q L s) (R : ℕ)
    (hL : 0 < L) (hspos : 0 < s)
    (hlow : ∀ e, L ≤ 2*(gates (hs++[p]) e).interval.width)
    (hhigh : ∀ e, (gates (hs++[p]) e).interval.width ≤ 3*L)
    (hbefore : ∀ i, componentEvent (PatchTable.incidence (gates hs)) R i = false)
    (hevent : componentEvent (PatchTable.incidence (gates (hs++[p]))) R ⟨hs.length,by simp⟩ = true) :
    WitnessBounds (PatchTable.incidence (gates (hs++[p]))) R ⟨hs.length,by simp⟩ := by
  let added := fun j => (p.bubbles j).data
  let new := fun j => (added j).interval
  let old := PatchTable.intervals (gates hs)
  let a := PatchTable.incidence (gates hs)
  let data := appendData (gates hs) added
  let next := extendIncidence old new a
  let i := Fin.last hs.length
  have hlen : hs.length+1 = (hs++[p]).length := by simp
  have heq : componentEvent (PatchTable.incidence data) R i =
      componentEvent (PatchTable.incidence (gates (hs++[p]))) R ⟨hs.length,by simp⟩ :=
    event_data_congr hlen data (gates (hs++[p])) (snapshot_append_data hs p) R i
  obtain ⟨hc,he⟩ := incidence_append (gates hs) added
  have hlast : componentEvent next R i = true :=
    (event_congr rfl hc _ next he R i).symm.trans (heq.trans hevent)
  have hpwidth : ∀ k, L ≤ 2*((CreationInterval.patches old).positions k).card := by
    apply PatchTable.patch_width (gates hs)
    intro e
    have H := hlow (Fin.cast hlen e.1.castSucc,e.2)
    rw [← snapshot_append_data hs p] at H
    simpa only [appendData,Fin.lastCases_castSucc,CreationInterval.width] using H
  have hnew : ∀ j, (new j).last.val+1-(new j).first.val ≤ 3*L := by
    intro j
    have H := hhigh (Fin.cast hlen i,j)
    rw [← snapshot_append_data hs p] at H
    simpa only [appendData,i,new,added,Fin.lastCases_last,CreationInterval.width] using H
  have hw : WitnessBounds next R i :=
    (first_event_witness old new a (PatchTable.incidence_surjective _) hL hspos
      hpwidth hnew hbefore hlast).2
  have hd : WitnessBounds (PatchTable.incidence data) R i :=
    (witnessBounds_congr rfl hc _ next he R i).mpr hw
  have hdata (n : ℕ) (hn : hs.length+1 = n)
      (D : Fin n × Fin s → GateData ℓ (Fin q))
      (H : ∀ j k, data (j,k) = D (Fin.cast hn j,k)) :
      WitnessBounds (PatchTable.incidence D) R (Fin.cast hn i) := by
    subst n
    have H' : data = D := funext fun e => H e.1 e.2
    subst D
    exact hd
  exact hdata _ hlen _ (snapshot_append_data hs p)

#print axioms witnessBounds_append

#print axioms all_after_appendData
#print axioms beforeEvent_append

end DeletionCode.Explicit.Recognizer
