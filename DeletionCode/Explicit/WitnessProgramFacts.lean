import DeletionCode.Explicit.WitnessFull

/-! The packed witness preserves patch ownership and the kernel equations. -/

namespace DeletionCode.Explicit.Recognizer

open LetterGraphCuts LetterSequence RulePatch PatchSupport ReplayEntry BubbleFamilies
open FieldHash PeelingBuckets
open scoped BigOperators

variable {ℓ q L s Λ θ : ℕ}

/-- Every active source position of a replayed bubble belongs to its
original patch. Distinct patches therefore have disjoint active sets. -/
theorem fullProgram_owner (hs : History ℓ q L s) (i : Fin hs.length) (x : Fin ℓ → Fin q)
    (hf : LiftsFit (gates hs) (lifts hs) Λ) :
    let p := fullProgram hs i x
    ∃ owner : Fin ℓ → Option (Fin (s*ruleCount hs i)),
      ∀ e k, k ∈ active (p.record e).2.negative.2 → owner k = some (p.incidence e) := by
  classical
  dsimp only
  let a := PatchTable.incidence (gates hs)
  let root : RuleVertex hs := .inl i
  let p := fullProgram hs i x
  let old (e : Fin (ruleCount hs i) × Fin s) := ((originalRule a root e.1).val,e.2)
  let patch (e : Fin (ruleCount hs i) × Fin s) := a (old e)
  let xs := PatchTable.intervals (gates hs)
  have hpos (e : Fin (ruleCount hs i) × Fin s) (k : Fin ℓ)
      (hk : k ∈ active (p.record e).2.negative.2) :
      ((CreationInterval.coalesce xs).get (patch e)).Contains ⟨k,k,le_rfl⟩ := by
    have hslot := (active_iff _ _).mp hk
    simp only [p,fullProgram,sliceRecord,witnessLifts,Completed.relabel,Lift.positions_renameEntries] at hslot
    have heq : finProdFinEquiv.symm (finProdFinEquiv (old e)) = old e := Equiv.symm_apply_apply _ _
    rw [heq] at hslot
    have hIn := (hf (old e) Side.negative).1 hslot
    obtain ⟨ha,hb⟩ := Finset.mem_Icc.mp hIn
    have hcap := PatchTable.incidence_contains (gates hs) (old e)
    exact ⟨hcap.1.trans ha,hb.trans hcap.2⟩
  have hsame (e f : Fin (ruleCount hs i) × Fin s) (k : Fin ℓ)
      (he : k ∈ active (p.record e).2.negative.2) (hh : k ∈ active (p.record f).2.negative.2) :
      p.incidence e = p.incidence f := by
    have hh' := CreationInterval.containing_index_unique (CreationInterval.coalesce_partition xs).separated
      (hpos e k he) (hpos f k hh)
    have h' : (originalPatch a root (componentIncidence a root e)).val =
        (originalPatch a root (componentIncidence a root f)).val := by
      rw [componentIncidence_original a root e.1 e.2,componentIncidence_original a root f.1 f.2]
      exact hh'
    have heq := ((componentPatches a root).orderIsoOfFin rfl).injective (Subtype.ext h')
    exact congrArg (Fin.castLE (patchCount_le hs i)) heq
  refine ⟨fun k => if h : ∃ e, k ∈ active (p.record e).2.negative.2 then some (p.incidence h.choose) else none,?_⟩
  intro e k hk
  have hw : ∃ z, k ∈ active (p.record z).2.negative.2 := ⟨e,hk⟩
  change (if h : ∃ z, k ∈ active (p.record z).2.negative.2 then some (p.incidence h.choose) else none) =
    some (p.incidence e)
  rw [dite_eq_left hw]
  exact congrArg some (hsame hw.choose e k hw.choose_spec hk)

theorem fullProgram_positive_subset (hs : History ℓ q L s) (i : Fin hs.length) (x : Fin ℓ → Fin q)
    (e : Fin (ruleCount hs i) × Fin s) :
    let r := (fullProgram hs i x).record e
    r.2.positive.2.positions ⊆ r.2.negative.2.positions := by
  dsimp only
  let a := PatchTable.incidence (gates hs)
  let root : RuleVertex hs := .inl i
  let j := (originalRule a root e.1).val
  let gate := (hs.get j).bubbles e.2
  have h : (fullProgram hs i x).record e =
      sliceRecord hs root x (retainedEntries hs root) (finProdFinEquiv (j,e.2)) := rfl
  rw [h]
  simp only [sliceRecord,witnessLifts,lifts,Completed.relabel,Lift.positions_renameEntries]
  have heq : finProdFinEquiv.symm (finProdFinEquiv (j,e.2)) = (j,e.2) := Equiv.symm_apply_apply _ _
  rw [heq]
  change gate.gate.positive.positions ⊆ gate.gate.negative.positions
  exact Lift.gate_positions_subset gate.gate.negative _ _

theorem fullProgram_kernel
    {K b R : ℕ} {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs)
    (i : Fin hs.length) (H : TernaryMatrix θ (q^L)) (hk : AllKernel H (.firstEvent hs i)) :
    ∀ j : Fin (ruleCount hs i),
      ∑ k : Fin s, H.mulVec (vectorOf L pad ((fullProgram hs i x).record (j,k)) x) = 0 := by
  intro j
  let a := PatchTable.incidence (gates hs)
  let root : RuleVertex hs := .inl i
  let r := (originalRule a root j).val
  let T := retainedEntries hs root
  obtain ⟨words,_,hrow,hwords⟩ := slice_rule_families h root T r
  have hv (k : Fin s) : vectorOf L pad ((fullProgram hs i x).record (j,k)) x = vector pad (words k) :=
    (hwords k).2.1.symm
  simp only [hv,← Matrix.mulVec_sum]
  have hsum : (∑ k : Fin s, vector pad (words k)) = (hs.get r).row := by
    rw [hrow]
    funext col
    simp [CatalogueEnumeration.row]
  rw [hsum]
  exact hk _ (List.get_mem ..)

#print axioms fullProgram_owner
#print axioms fullProgram_kernel

end DeletionCode.Explicit.Recognizer
