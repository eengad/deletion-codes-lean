import DeletionCode.Explicit.WitnessGrammar
import DeletionCode.Explicit.CoreReplay

/-! The anchor list of a slice is read from its final patches. -/

namespace DeletionCode.Explicit.Recognizer

open LetterGraphCuts RulePatch ReplayEntry ReplayGrammar CoreWeight LetterSequence PatchSupport

variable {ℓ q K b L Λ R s E : ℕ}

def sliceRoots (hs : History ℓ q L s) (root : RuleVertex hs) (zero : Fin ℓ)
    (ds : List (DecodedEntry q)) (p : ↥(patchKeys E ds)) : Fin ℓ :=
  (witnessAnchor hs root p.val.val).getD zero

theorem mem_patchKeys {ds : List (DecodedEntry q)} (p : Fin E) :
    p ∈ patchKeys E ds ↔ ∃ d ∈ ds, d.entry.patch = p.val := by
  simp [patchKeys,List.any_eq_true,beq_iff_eq]

theorem description_patches (hs : History ℓ q L s) (root : RuleVertex hs) (x : Fin ℓ → Fin q)
    (T : Finset (Fin (hs.length*s))) (inner outer : Fin (hs.length*s) → Bool)
    (hfit : ∀ d ∈ descriptions hs root x T inner outer, d.entry.patch < E) :
    let ds := descriptions hs root x T inner outer
    let patch j := PatchTable.incidence (gates hs) (finProdFinEquiv.symm j)
    (patchKeys E ds).image Fin.val = (T.image patch).image (witnessPatchNumber hs root) := by
  dsimp only
  ext p
  constructor
  · intro hp
    obtain ⟨ix,hix,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨d,hd,he⟩ := (mem_patchKeys ix).mp hix
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hd
    let j := BackwardSlice.original T i
    have hj : j ∈ T := (T.orderIsoOfFin rfl i).property
    exact Finset.mem_image.mpr ⟨_,Finset.mem_image_of_mem _ hj,he⟩
  · intro hp
    obtain ⟨a,ha,hval⟩ := Finset.mem_image.mp hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ha
    let k := BackwardSlice.number T ⟨j,hj⟩
    have hk : BackwardSlice.original T k = j := congrArg Subtype.val
      ((T.orderIsoOfFin rfl).apply_symm_apply ⟨j,hj⟩)
    let v := BackwardSlice.original T k
    let d : DecodedEntry q := ⟨(witnessEntry hs root x v).relabel (compactIndex T)
      (witnessRuleNumber hs root), inner v, outer v⟩
    have hd : d ∈ descriptions hs root x T inner outer := List.mem_ofFn.mpr ⟨k,rfl⟩
    have hd' : d.entry.patch = p := by
      change (witnessEntry hs root x (BackwardSlice.original T k)).patch = p
      rw [hk]
      exact hval
    let ix : Fin E := ⟨d.entry.patch,hfit d hd⟩
    exact Finset.mem_image.mpr ⟨ix,(mem_patchKeys ix).mpr ⟨d,hd,rfl⟩,hd'⟩

theorem slice_anchor_count
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs) (hc : Chronological hs)
    (hx : Strong x K Λ) (hf : LiftsFit (gates hs) (lifts hs) Λ) (hL : K+2*Λ ≤ L)
    (root : RuleVertex hs) (ends : Finset (Fin (hs.length*s))) (inner outer : Fin (hs.length*s) → Bool)
    (hfit : ∀ d ∈ descriptions hs root x (witnessSlice hs root x ends) inner outer, d.entry.patch < E) :
    let ds := descriptions hs root x (witnessSlice hs root x ends) inner outer
    let patch j := PatchTable.incidence (gates hs) (finProdFinEquiv.symm j)
    (patchKeys E ds).card ≤ (ends.image patch).card := by
  dsimp only
  rw [← Finset.card_image_of_injective _ Fin.val_injective,
    description_patches hs root x _ inner outer hfit,
    witnessSlice_patches h hc hx hf hL root ends]
  exact Finset.card_image_le

/-- The anchor table recoverable from the serialized tuple is sufficient
for every entry of the slice. -/
theorem replay_slice_anchors
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs) (hc : Chronological hs)
    (hx : Strong x K Λ) (hf : LiftsFit (gates hs) (lifts hs) Λ) (hL : K+2*Λ ≤ L)
    (root : RuleVertex hs) (ends : Finset (Fin (hs.length*s))) (he : ends ⊆ retainedEntries hs root)
    (inner outer : Fin (hs.length*s) → Bool)
    (hfit : ∀ d ∈ descriptions hs root x (witnessSlice hs root x ends) inner outer, d.entry.patch < E) :
    let T := witnessSlice hs root x ends
    let ds := descriptions hs root x T inner outer
    replay L (anchorLookup (patchKeys E ds) (sliceRoots hs root origin ds)) (ds.map (·.entry)) =
      some (List.ofFn fun i => (witnessLifts hs (BackwardSlice.original T i)).relabel
        (compactIndex T) (witnessRuleNumber hs root)).toArray := by
  dsimp only
  let T := witnessSlice hs root x ends
  let ds := descriptions hs root x T inner outer
  have hSub := witnessSlice_subset h hc hx hf hL root ends he
  rw [replay_anchor_congr (L := L) _ _ (witnessAnchor hs root)]
  · exact replay_witnessSlice h hc hx hf hL root ends he inner outer
  · intro entry hentry
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hentry
    let index : Fin E := ⟨d.entry.patch,hfit d hd⟩
    have hi : index ∈ patchKeys E ds := (mem_patchKeys index).mpr ⟨d,hd,rfl⟩
    have hb : d.entry.patch < E := index.isLt
    have hk : (⟨d.entry.patch,hb⟩ : Fin E) ∈ patchKeys E ds := hi
    have hv : ∃ r : Fin ℓ, witnessAnchor hs root d.entry.patch = some r := by
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hd
      let j := BackwardSlice.original T i
      let e := finProdFinEquiv.symm j
      let p := PatchTable.incidence (gates hs) e
      have hj : j ∈ T := (T.orderIsoOfFin rfl i).property
      have hp := witnessEntry_patch hs root e (Finset.mem_filter.mp (hSub hj)).2
      exact ⟨patchAnchor hs p, witnessAnchor_at hs root p hp⟩
    obtain ⟨r,hr⟩ := hv
    change anchorLookup (patchKeys E ds) (sliceRoots hs root origin ds) d.entry.patch = _
    simp [anchorLookup,hb,hk,sliceRoots,hr]

#print axioms slice_anchor_count
#print axioms replay_slice_anchors

end DeletionCode.Explicit.Recognizer
