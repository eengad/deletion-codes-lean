import DeletionCode.Explicit.WitnessMarks
import DeletionCode.Explicit.WitnessFamilies
import DeletionCode.Explicit.ReplayPayload

/-! Encode the backward slice of one selected witness bubble. -/

namespace DeletionCode.Explicit.Recognizer

open LetterGraphCuts RulePatch ReplayEntry ReplayGrammar LetterSequence PatchSupport

variable {ℓ q K b L Λ R s E : ℕ}

def singleDescription (E b : ℕ) (hs : History ℓ q L s) (root : RuleVertex hs)
    (pad : Fin q) (x : Fin ℓ → Fin q) (j : Fin (hs.length*s)) :
    Option (DescriptionCode E L b q × Fin ℓ) := do
  let T := witnessSlice hs root x {j}
  let mark := fun k => decide (k = j)
  let code ← encodeDescription E L b q pad (descriptions hs root x T mark mark)
  some (code,patchAnchor hs (PatchTable.incidence (gates hs) (finProdFinEquiv.symm j)))

private theorem filter_only {α : Type*} [DecidableEq α] (xs : List α) (a : α)
    (hn : xs.Nodup) (ha : a ∈ xs) :
    xs.filter (fun z => decide (z = a)) = [a] := by
  induction xs with
  | nil => simp at ha
  | cons j js ih =>
    obtain ⟨hj,hjs⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ha with rfl | hm
    · have he : js.filter (fun z => decide (z = a)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro k hk
        simp only [decide_eq_true_eq]
        exact fun he => hj (he ▸ hk)
      simp [he]
    · have hne : j ≠ a := fun h => hj (h.symm ▸ hm)
      simp [hne,ih hjs hm]

theorem singleDescription_correct
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs) (hc : Chronological hs)
    (hx : Strong x K Λ) (hf : LiftsFit (gates hs) (lifts hs) Λ) (hL : K+2*Λ ≤ L)
    (hwidth : ∀ e, (gates hs e).interval.width ≤ 3*L)
    (i : Fin hs.length) (hspos : 0 < s) (hE : (retainedEntries hs (.inl i)).card ≤ E)
    (j : Fin (hs.length*s)) (hj : j ∈ retainedEntries hs (.inl i)) :
    let root : RuleVertex hs := .inl i
    let T := witnessSlice hs root x {j}
    ∃ code anchor, singleDescription E b hs root pad x j = some (code,anchor) ∧
      ReplayPayload.materialize code anchor = some (sliceRecord hs root x T j) := by
  dsimp only
  let root : RuleVertex hs := .inl i
  let T := witnessSlice hs root x {j}
  let mark (k : Fin (hs.length*s)) := decide (k = j)
  let ds := descriptions hs root x T mark mark
  let patch (k : Fin (hs.length*s)) := PatchTable.incidence (gates hs) (finProdFinEquiv.symm k)
  let anchor := patchAnchor hs (patch j)
  have he : ({j} : Finset (Fin (hs.length*s))) ⊆ retainedEntries hs root :=
    Finset.singleton_subset_iff.mpr hj
  obtain ⟨hfinal,hclosed,_⟩ := BackwardSlice.slice_spec (witnessSuppliers hs root x) {j}
  have hsub := witnessSlice_subset h hc hx hf hL root {j} he
  have hbound := witness_description_fits h hc hx hf hL hwidth i hspos T hsub hE hclosed mark mark
  obtain ⟨code,hcode,hdecoded⟩ := encodeDescription_roundtrip pad ds
    (by have hh := P.window; omega) hbound.1 hbound.2
  refine ⟨code,anchor,?_,?_⟩
  · change (encodeDescription E L b q pad ds >>= fun c => some (c,anchor)) = _
    rw [hcode]
    rfl
  have hjT : j ∈ T := hfinal (Finset.mem_singleton_self _)
  let p := sliceRecord hs root x T j
  let d : DecodedEntry q := ⟨p.1,true,true⟩
  have hselected : ds.filter (·.finalBubble) = [d] := by
    unfold ds
    rw [descriptions_eq_sorted,List.filter_map]
    have H := filter_only T.sort j (Finset.sort_nodup _ _) ((Finset.mem_sort _).mpr hjT)
    change List.map _ (T.sort.filter (fun k => decide (k = j))) = _
    rw [H]
    simp [mark,d,p,sliceRecord]
  have hpatch (v : Fin (hs.length*s)) (hv : v ∈ T) : patch v = patch j := by
    have H := Finset.mem_image_of_mem patch hv
    rw [witnessSlice_patches h hc hx hf hL root {j}] at H
    simpa only [Finset.image_singleton,Finset.mem_singleton] using H
  have hall (z : DecodedEntry q) (hz : z ∈ ds) : z.entry.patch = d.entry.patch := by
    change z ∈ descriptions hs root x T mark mark at hz
    rw [descriptions_eq_sorted] at hz
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hz
    exact congrArg (witnessPatchNumber hs root) (hpatch u ((Finset.mem_sort _).mp hu))
  have hp : patch j ∈ componentPatches (PatchTable.incidence (gates hs)) root :=
    witnessEntry_patch hs root _ (Finset.mem_filter.mp hj).2
  have hanchor : witnessAnchor hs root d.entry.patch = some anchor :=
    witnessAnchor_at hs root _ hp
  let out := (List.ofFn fun k => (sliceRecord hs root x T (BackwardSlice.original T k)).2).toArray
  have hrun : replay L (fun n => if n = d.entry.patch then some anchor else none)
      (ds.map (·.entry)) = some out := by
    rw [replay_anchor_congr (L := L) _ _ (witnessAnchor hs root)]
    · exact replay_witnessSlice h hc hx hf hL root {j} he mark mark
    · intro e he
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
      have heq := hall v hv
      simp [heq,hanchor]
  have ht : true ∈ ds.map (·.finalBubble) := by
    have hm : d ∈ ds.filter (·.finalBubble) := by simp [hselected]
    exact List.mem_map.mpr ⟨d,(List.mem_filter.mp hm).1,rfl⟩
  have hl : (ds.map (·.finalBubble)).idxOf true < T.card := by
    simpa [ds,descriptions] using List.idxOf_lt_length_iff.mpr ht
  let k' : Fin T.card := ⟨(ds.map (·.finalBubble)).idxOf true,hl⟩
  have hidx := List.idxOf_lt_length_iff.mpr ht
  have hgetTrue : (ds.map (·.finalBubble))[k'.val]? = some true :=
    (List.getElem?_eq_getElem hidx).trans (congrArg some (List.getElem_idxOf hidx))
  have hlist : ds.map (·.finalBubble) = List.ofFn (fun i : Fin T.card => mark (BackwardSlice.original T i)) := by
    rw [show ds = descriptions hs root x T mark mark from rfl,descriptions,List.map_ofFn]
    rfl
  have hkey : BackwardSlice.original T k' = j := by
    rw [hlist,List.getElem?_ofFn,dite_eq_left k'.isLt] at hgetTrue
    exact of_decide_eq_true (Option.some.inj hgetTrue)
  have hget : out[(ds.map (·.finalBubble)).idxOf true]? = some p.2 := by
    change out[k'.val]? = some p.2
    simp [out,k'.isLt,hkey,p]
  exact ReplayPayload.materialize_of_replay code anchor ds d hdecoded hselected hall out hrun p.2 hget

#print axioms singleDescription_correct

end DeletionCode.Explicit.Recognizer
