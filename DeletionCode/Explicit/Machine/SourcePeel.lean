import DeletionCode.Explicit.Machine.SourceWitness
import DeletionCode.Explicit.RulePatchCore

/-! Execute the first-pivot rule of the abstract peeling process. -/
namespace DeletionCode.Explicit.Machine.SourcePeel

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open SourceWitness

abbrev State := List ℕ × List Bool
abbrev configEncoding := encPair PatchGraph.graphEncoding encUnary
abbrev stateEncoding := encPair PatchGraph.rowEncoding PatchGraph.flagsEncoding

variable {d s c : ℕ}

private def edgeNumber (e : Fin d × Fin s) : ℕ := (finProdFinEquiv e).val

private theorem edgeNumber_div (e : Fin d × Fin s) : edgeNumber e / s = e.1.val := by
  change (finProdFinEquiv.symm (finProdFinEquiv e)).1.val = _
  rw [Equiv.symm_apply_apply]

private theorem edgeList_eq (d s : ℕ) :
    RulePatch.edgeList d s = List.ofFn (finProdFinEquiv (m := d) (n := s)).symm := by
  rw [List.ofFn_mul]
  unfold RulePatch.edgeList
  rw [List.flatMap_def]
  congr 1
  simp only [show List.finRange d = List.ofFn (fun i : Fin d => i) from rfl,
    show List.finRange s = List.ofFn (fun i : Fin s => i) from rfl, List.map_ofFn, Function.comp_def]
  congr 1
  funext i
  congr 1
  funext j
  apply finProdFinEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  change j.val+s*i.val = i.val*s+j.val
  ac_rfl

private theorem edgeNumbers (d s : ℕ) :
    (RulePatch.edgeList d s).map edgeNumber = List.range (d*s) := by
  rw [edgeList_eq, List.map_ofFn]
  have h : (edgeNumber ∘ (finProdFinEquiv (m := d) (n := s)).symm) = (fun i => i.val) := by
    funext i
    change (finProdFinEquiv (finProdFinEquiv.symm i)).val = i.val
    rw [Equiv.apply_symm_apply]
  rw [h]
  simpa using (SourceLists.range_map_eq (k := d*s) (@id ℕ)).symm

private theorem edgeList_nodup (d s : ℕ) : (RulePatch.edgeList d s).Nodup := by
  rw [edgeList_eq]
  exact List.nodup_ofFn.mpr finProdFinEquiv.symm.injective

private theorem graphRules (a : RulePatch.Incidence d s c) : (PatchGraph.graphData a).2.length = d := by
  simp [PatchGraph.graphData]

private theorem flagAt (live : Finset (Fin d)) (i : Fin d) :
    (SourceSlice.flags live).getD i.val false = decide (i ∈ live) :=
  BooleanFibres.ofFn_getD _ i false

private theorem patchAt (a : RulePatch.Incidence d s c) (edge : Fin d × Fin s) :
    patchOfEntry (PatchGraph.graphData a) s (edgeNumber edge) = (a edge).val := by
  unfold edgeNumber
  rw [patchOfEntry_eq, Equiv.symm_apply_apply]

def degree (g : PatchGraph.Graph) (s : ℕ) (live : List Bool) (patch : ℕ) : ℕ :=
  ((List.range (g.2.length*s)).filter (fun j =>
    live.getD (j / s) false && decide (patchOfEntry g s j = patch))).length

private theorem degree_eq (a : RulePatch.Incidence d s c) (live : Finset (Fin d)) (p : Fin c) :
    degree (PatchGraph.graphData a) s (SourceSlice.flags live) p.val = (RulePatch.atPatch a live p).card := by
  unfold degree
  rw [graphRules, ← edgeNumbers d s, List.filter_map, List.length_map]
  simp only [Function.comp_def]
  let picked := (RulePatch.edgeList d s).filter (fun e => decide (e.1 ∈ live ∧ a e = p))
  have h : ((RulePatch.edgeList d s).filter (fun e => (SourceSlice.flags live).getD (edgeNumber e / s) false &&
        decide (patchOfEntry (PatchGraph.graphData a) s (edgeNumber e) = p.val))) = picked := by
    apply List.filter_congr
    intro e _
    rw [edgeNumber_div, flagAt, patchAt]
    apply Bool.eq_iff_iff.mpr
    simp [Fin.ext_iff]
  rw [h]
  have hp : picked.toFinset = RulePatch.atPatch a live p := by
    ext e
    simp [picked, RulePatch.atPatch, RulePatch.edges]
  have hn : picked.Nodup := (edgeList_nodup d s).filter _
  rw [← hp, List.toFinset_card_of_nodup hn]

def pivot (g : PatchGraph.Graph) (s : ℕ) (live : List Bool) : Option ℕ :=
  (List.range (g.2.length*s)).find? fun j => live.getD (j / s) false &&
    decide (degree g s live (patchOfEntry g s j) = 1)

private theorem pivot_eq (a : RulePatch.Incidence d s c) (live : Finset (Fin d)) :
    pivot (PatchGraph.graphData a) s (SourceSlice.flags live) = (RulePatch.pivot a live).map edgeNumber := by
  unfold pivot RulePatch.pivot
  rw [graphRules, ← edgeNumbers d s, List.find?_map]
  congr 1
  apply List.find?_congr
  intro e _
  simp only [Function.comp_def]
  rw [edgeNumber_div, flagAt, patchAt, degree_eq]
  simp

def step (g : PatchGraph.Graph) (s : ℕ) (state : State) : State :=
  (pivot g s state.2).elim state (fun edge => (edge :: state.1, state.2.set (edge / s) false))

private theorem flags_erase (live : Finset (Fin d)) (i : Fin d) :
    (SourceSlice.flags live).set i.val false = SourceSlice.flags (live.erase i) := by
  apply List.ext_getElem (by simp [SourceSlice.flags])
  intro k hk hk'
  have hi : k < d := by simpa [SourceSlice.flags] using hk'
  simp [SourceSlice.flags, List.getElem_set, Finset.mem_erase, Fin.ext_iff, eq_comm]

private theorem peel_stop (a : RulePatch.Incidence d s c) (live : Finset (Fin d))
    (h : RulePatch.pivot a live = none) : RulePatch.peel a live = ([], live) := by
  conv_lhs => rw [RulePatch.peel]
  split
  · rfl
  · rename_i edge hp
    simp [h] at hp

private theorem peel_advance (a : RulePatch.Incidence d s c) (live : Finset (Fin d))
    (edge : Fin d × Fin s) (h : RulePatch.pivot a live = some edge) : RulePatch.peel a live =
      (edge :: (RulePatch.peel a (live.erase edge.1)).1, (RulePatch.peel a (live.erase edge.1)).2) := by
  conv_lhs => rw [RulePatch.peel]
  split
  · rename_i hp
    simp [h] at hp
  · rename_i e hp
    have he : e = edge := Option.some.inj (hp.symm.trans h)
    subst e
    rfl

private theorem loop_eq (a : RulePatch.Incidence d s c) (fuel : ℕ) (live : Finset (Fin d))
    (hfuel : live.card ≤ fuel) (rev : List ℕ) :
    (step (PatchGraph.graphData a) s)^[fuel] (rev, SourceSlice.flags live) =
      ((RulePatch.peel a live).1.reverse.map edgeNumber ++ rev, SourceSlice.flags (RulePatch.peel a live).2) := by
  induction fuel generalizing live rev with
  | zero =>
    have h : RulePatch.pivot a live = none := by
      apply (RulePatch.pivot_none_iff a live).mpr
      have hz : live = ∅ := Finset.card_eq_zero.mp (by omega)
      simp [hz]
    rw [Function.iterate_zero_apply, peel_stop a live h]
    rfl
  | succ fuel ih =>
    cases hp : RulePatch.pivot a live with
    | none =>
      have h : step (PatchGraph.graphData a) s (rev, SourceSlice.flags live) = (rev, SourceSlice.flags live) := by
        simp [step, pivot_eq, hp]
      rw [Function.iterate_fixed h, peel_stop a live hp]
      rfl
    | some edge =>
      have hcard := Finset.card_erase_lt_of_mem (RulePatch.pivot_spec hp).1
      rw [Function.iterate_succ_apply, show step (PatchGraph.graphData a) s (rev, SourceSlice.flags live) =
        (edgeNumber edge :: rev, SourceSlice.flags (live.erase edge.1)) by simp [step, pivot_eq, hp, edgeNumber_div, flags_erase]]
      rw [ih _ (by omega), peel_advance a live edge hp]
      simp [List.reverse_cons, List.append_assoc]

def run (g : PatchGraph.Graph) (s : ℕ) : State :=
  let result := (step g s)^[g.2.length] ([], List.replicate g.2.length true)
  (result.1.reverse, result.2)

theorem run_eq (a : RulePatch.Incidence d s c) :
    run (PatchGraph.graphData a) s =
      ((RulePatch.peel a Finset.univ).1.map edgeNumber, SourceSlice.flags (RulePatch.peel a Finset.univ).2) := by
  have hinit : List.replicate d true = SourceSlice.flags (Finset.univ : Finset (Fin d)) := by
    apply List.ext_getElem (by simp [SourceSlice.flags])
    intro i _ _
    simp [SourceSlice.flags]
  unfold run
  rw [graphRules, hinit, loop_eq a d Finset.univ (by simp)]
  simp

private abbrev liveEncoding := encPair configEncoding PatchGraph.flagsEncoding

private theorem edgeCount_polyTime : ComputableInPolyTime
    (fun p : PatchGraph.Graph × ℕ => p.1.2.length * p.2) configEncoding encUnary :=
  unary_mul' ((length_list PatchGraph.rowEncoding).comp (fst PatchGraph.graphEncoding encUnary).snd')
    (snd PatchGraph.graphEncoding encUnary)

private theorem degree_polyTime : ComputableInPolyTime
    (fun p : ((PatchGraph.Graph × ℕ) × List Bool) × ℕ => degree p.1.1.1 p.1.1.2 p.1.2 p.2)
    (encPair liveEncoding encUnary) encUnary := by
  let e := encPair liveEncoding encUnary
  let a := encPair e encUnary
  have hp := fst liveEncoding encUnary
  have ha := fst e encUnary
  have he := snd e encUnary
  have hx := hp.comp ha
  have hs := hx.fst'.snd'
  have hf := listGetDWithInput hx.snd' (unary_div' he hs) false
  have hpId := patchOfEntry_polyTime.comp (encIn := a) (hx.fst'.fst'.prod (hs.prod he))
  have htest := bool_and' hf (hpId.decide_eq' ((snd liveEncoding encUnary).comp ha))
  have hi := unary_range' (edgeCount_polyTime.comp hp.fst')
  exact (length_list encUnary).comp (filterWithInput (encIn := e) (encA := encUnary)
    (test := fun p j => p.1.2.getD (j / p.1.1.2) false && decide (patchOfEntry p.1.1.1 p.1.1.2 j = p.2)) hi htest)

private theorem pivot_polyTime : ComputableInPolyTime
    (fun p : (PatchGraph.Graph × ℕ) × List Bool => pivot p.1.1 p.1.2 p.2)
    liveEncoding (encOption encUnary) := by
  let e := liveEncoding
  let a := encPair e encUnary
  have hconfig := fst configEncoding PatchGraph.flagsEncoding
  have hflags := snd configEncoding PatchGraph.flagsEncoding
  have h := fst e encUnary
  have hj := snd e encUnary
  have hg := hconfig.comp h
  have hpatch := patchOfEntry_polyTime.comp (encIn := a) (hg.fst'.prod (hg.snd'.prod hj))
  have hd := degree_polyTime.comp (h.prod hpatch)
  have hlive := listGetDWithInput (hflags.comp h) (unary_div' hj hg.snd') false
  exact findWithInput (encIn := e) (encA := encUnary)
    (test := fun p j => p.2.getD (j / p.1.2) false && decide (degree p.1.1 p.1.2 p.2 (patchOfEntry p.1.1 p.1.2 j) = 1))
    (unary_range' (edgeCount_polyTime.comp hconfig)) (bool_and' hlive (hd.decide_eq' (const 1)))

private theorem step_polyTime : ComputableInPolyTime
    (fun p : (PatchGraph.Graph × ℕ) × State => step p.1.1 p.1.2 p.2)
    (encPair configEncoding stateEncoding) stateEncoding := by
  let e := encPair configEncoding stateEncoding
  have hc := fst configEncoding stateEncoding
  have hs := snd configEncoding stateEncoding
  have hp := pivot_polyTime.comp (hc.prod hs.snd')
  have h := fst e encUnary
  have hj := snd e encUnary
  have hr := cons' hj (hs.fst'.comp h)
  have hf := listSetWithInput encBool (hs.snd'.comp h) (unary_div' hj (hc.snd'.comp h)) (const false)
  have hout := optionElimWithInput (encA := e) (encB := encUnary) (encC := stateEncoding)
    (body := fun p j => (j :: p.2.1, p.2.2.set (j / p.1.2) false)) hp hs (hr.prod hf)
  exact hout.of_enc_eq (fun _ => rfl)

private theorem traceEncoding_le (m : ℕ) (trace : List ℕ) (h : ∀ j ∈ trace, j < m) :
    (PatchGraph.rowEncoding trace).length ≤ (2*m+1)*trace.length := by
  induction trace with
  | nil => rfl
  | cons j trace ih =>
    have hj := h j (by simp)
    have ht := ih (fun v hv => h v (by simp [hv]))
    simp only [PatchGraph.rowEncoding, encList_cons, List.length_append, length_frame, encUnary_apply,
      List.length_replicate, List.length_cons, Nat.mul_succ] at ht ⊢
    omega

private theorem flagsEncoding_length (flags : List Bool) :
    (PatchGraph.flagsEncoding flags).length = 3 * flags.length := by
  induction flags with
  | nil => rfl
  | cons flag flags ih =>
    change (encList encBool (flag :: flags)).length = _
    rw [encList_cons, List.length_append, length_frame]
    change 2 * 1 + 1 + (PatchGraph.flagsEncoding flags).length = _
    rw [ih]
    simp only [List.length_cons, Nat.mul_succ]
    omega

private theorem step_invariant (g : PatchGraph.Graph) (s i : ℕ) (st : State)
    (h : st.1.length ≤ i ∧ (∀ j ∈ st.1, j < g.2.length*s) ∧ st.2.length = g.2.length) :
    (step g s st).1.length ≤ i+1 ∧ (∀ j ∈ (step g s st).1, j < g.2.length*s) ∧
      (step g s st).2.length = g.2.length := by
  unfold step
  cases hp : pivot g s st.2 with
  | none => simp only [Option.elim_none]; exact ⟨by omega, h.2⟩
  | some j =>
    have hj : j < g.2.length*s := List.mem_range.mp (List.mem_of_find?_eq_some hp)
    simp only [Option.elim_some, List.length_cons, List.mem_cons, List.length_set, forall_eq_or_imp]
    exact ⟨by omega, ⟨hj, h.2.1⟩, h.2.2⟩

set_option maxHeartbeats 1500000 in
theorem run_polyTime : ComputableInPolyTime (fun p : PatchGraph.Graph × ℕ => run p.1 p.2)
    configEncoding stateEncoding := by
  let e := configEncoding
  let rules := fun p : PatchGraph.Graph × ℕ => p.1.2.length
  let edges := fun p : PatchGraph.Graph × ℕ => p.1.2.length*p.2
  let init := fun p : PatchGraph.Graph × ℕ => (([] : List ℕ), List.replicate (rules p) true)
  have hr : ComputableInPolyTime rules e encUnary :=
    (length_list PatchGraph.rowEncoding).comp (fst PatchGraph.graphEncoding encUnary).snd'
  have hinit : ComputableInPolyTime init e stateEncoding :=
    (const (encOut := PatchGraph.rowEncoding) ([] : List ℕ)).prod (replicate (encA := encBool) hr (const true))
  have hRules : PolyBounded (fun p : PatchGraph.Graph × ℕ => (e p).length) rules := by
    simpa only [encUnary_apply, List.length_replicate] using hr.polyBounded_length
  have hEdges : PolyBounded (fun p : PatchGraph.Graph × ℕ => (e p).length) edges := by
    simpa only [encUnary_apply, List.length_replicate] using edgeCount_polyTime.polyBounded_length
  have hsize : PolyBounded (fun p : PatchGraph.Graph × ℕ => (e p).length)
      (fun p => 2*((2*edges p+1)*rules p)+1+3*rules p) :=
    (((PolyBounded.const 2).mul ((((PolyBounded.const 2).mul hEdges).add (PolyBounded.const 1)).mul hRules)).add
      (PolyBounded.const 1)).add ((PolyBounded.const 3).mul hRules)
  let I := fun p i (st : State) => st.1.length ≤ i ∧ (∀ j ∈ st.1, j < edges p) ∧ st.2.length = rules p
  have hbase (p) : I p 0 (init p) := by simp [I, init]
  have hstep (p i st) (_ : i < rules p) (hs : I p i st) : I p (i+1) (step p.1 p.2 st) :=
    step_invariant p.1 p.2 i st hs
  have hbound (p i st) (hi : i ≤ rules p) (hs : I p i st) :
      (stateEncoding st).length ≤ 2*((2*edges p+1)*rules p)+1+3*rules p := by
    obtain ⟨hlen, hj, hf⟩ := hs
    have ht := (traceEncoding_le (edges p) st.1 hj).trans (Nat.mul_le_mul_left _ (hlen.trans hi))
    simp only [stateEncoding, length_encPair, flagsEncoding_length, hf]
    omega
  have h : ComputableInPolyTime (fun p : PatchGraph.Graph × ℕ => (step p.1 p.2)^[rules p] (init p))
      e stateEncoding := by
    have hv := iterateWith_spec (encIn := e) (encState := stateEncoding) (encPar := e)
      (par := fun p : PatchGraph.Graph × ℕ => p) (count := rules) (init := init)
      (step := fun p => step p.1 p.2) id' hr hinit step_polyTime I hbase hstep hsize hbound
    exact hv.1
  have hs := (listReverse encUnary).comp (fst PatchGraph.rowEncoding PatchGraph.flagsEncoding)
  exact (hs.prod (snd PatchGraph.rowEncoding PatchGraph.flagsEncoding)).comp h

#print axioms run_eq
#print axioms run_polyTime

end DeletionCode.Explicit.Machine.SourcePeel
