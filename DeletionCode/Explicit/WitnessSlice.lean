import DeletionCode.Explicit.WitnessGeometry

/-! Backward slicing of an actual first-event history. -/

namespace DeletionCode.Explicit.Recognizer

open LetterGraphCuts LetterSequence RulePatch ReplayEntry PatchSupport

variable {ℓ q K b L Λ R s : ℕ}

def witnessSuppliers (hs : History ℓ q L s) (root : RuleVertex hs) (x : Fin ℓ → Fin q)
    (j : Fin (hs.length*s)) : Finset (Fin (hs.length*s)) :=
  if j ∈ retainedEntries hs root then
    Finset.univ.filter fun k => k.val ∈ (witnessEntry hs root x j).suppliers
  else ∅

def witnessSlice (hs : History ℓ q L s) (root : RuleVertex hs) (x : Fin ℓ → Fin q)
    (ends : Finset (Fin (hs.length*s))) : Finset (Fin (hs.length*s)) :=
  BackwardSlice.slice (witnessSuppliers hs root x) ends

private theorem rule_number_lt (T : Finset (Fin N)) {i j : Fin N}
    (hi : i ∈ T) (hj : j ∈ T) :
    compactIndex T i.val < compactIndex T j.val ↔ i < j := by
  unfold compactIndex
  simp only [dite_eq_left i.isLt,dite_eq_left hi,dite_eq_left j.isLt,dite_eq_left hj]
  exact (T.orderIsoOfFin rfl).symm.lt_iff_lt

theorem witnessSlice_subset
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs) (hc : Chronological hs)
    (hx : Strong x K Λ) (hf : LiftsFit (gates hs) (lifts hs) Λ) (hL : K+2*Λ ≤ L)
    (root : RuleVertex hs) (ends : Finset (Fin (hs.length*s))) (he : ends ⊆ retainedEntries hs root) :
    witnessSlice hs root x ends ⊆ retainedEntries hs root := by
  apply (BackwardSlice.slice_spec (witnessSuppliers hs root x) ends).2.2 _ he
  intro i hi j hj
  have hm : j.val ∈ (witnessEntry hs root x i).suppliers := by
    simpa [witnessSuppliers,hi] using hj
  obtain ⟨z,hz,hval,_⟩ := witness_suppliers_retained h hc hx hf hL root i hi j.val hm
  simpa only [Fin.ext hval] using hz

theorem witnessSlice_patches
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs) (hc : Chronological hs)
    (hx : Strong x K Λ) (hf : LiftsFit (gates hs) (lifts hs) Λ) (hL : K+2*Λ ≤ L)
    (root : RuleVertex hs) (ends : Finset (Fin (hs.length*s))) :
    let patch j := PatchTable.incidence (gates hs) (finProdFinEquiv.symm j)
    (witnessSlice hs root x ends).image patch = ends.image patch := by
  apply BackwardSlice.patches_eq
  intro i j hm
  by_cases hi : i ∈ retainedEntries hs root
  · have hm' : j.val ∈ (witnessEntry hs root x i).suppliers := by
      simpa [witnessSuppliers,hi] using hm
    obtain ⟨z,hval,_,hp⟩ := witness_supplier_patch h hc hx hf hL root i hi j.val hm'
    simpa only [Fin.ext hval] using hp
  · simp [witnessSuppliers,hi] at hm

theorem replay_witnessSlice
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs) (hc : Chronological hs)
    (hx : Strong x K Λ) (hf : LiftsFit (gates hs) (lifts hs) Λ) (hL : K+2*Λ ≤ L)
    (root : RuleVertex hs) (ends : Finset (Fin (hs.length*s))) (he : ends ⊆ retainedEntries hs root)
    (inner outer : Fin (hs.length*s) → Bool) :
    let T := witnessSlice hs root x ends
    replay L (witnessAnchor hs root) ((descriptions hs root x T inner outer).map (·.entry)) =
      some (List.ofFn fun i => (witnessLifts hs (BackwardSlice.original T i)).relabel
        (compactIndex T) (witnessRuleNumber hs root)).toArray := by
  let T := witnessSlice hs root x ends
  have sub := witnessSlice_subset h hc hx hf hL root ends he
  have hsupply := (BackwardSlice.slice_spec (witnessSuppliers hs root x) ends).2.1
  have hm (i : Fin (hs.length*s)) (hi : i ∈ T) (j : ℕ) (hj : j ∈ (witnessEntry hs root x i).suppliers) :
      ∃ k ∈ T, k.val = j ∧ k < i := by
    obtain ⟨k,hk,hval,hlt⟩ := witness_suppliers_retained h hc hx hf hL root i (sub hi) j hj
    have hmem : k ∈ witnessSuppliers hs root x i := by
      simpa [witnessSuppliers,sub hi,hval] using hj
    exact ⟨k,hsupply i hi hmem,hval,hlt⟩
  dsimp only
  unfold descriptions
  rw [List.map_ofFn]
  apply replay_compact L (witnessAnchor hs root) (witnessEntry hs root x)
    (witnessLifts hs) T (witnessRuleNumber hs root)
  · exact fun i hi => witnessEntry_evaluates h hc root i (sub hi)
  · exact hm
  · intro i hi j hj
    rw [witnessEntry_rule hs hc,witnessLifts_rule hs hc]
    exact (rule_number_lt _ (Finset.mem_filter.mp (sub hj)).2 (Finset.mem_filter.mp (sub hi)).2).symm

#print axioms witnessSlice_subset
#print axioms witnessSlice_patches
#print axioms replay_witnessSlice

end DeletionCode.Explicit.Recognizer
