import DeletionCode.Explicit.WitnessTables
import DeletionCode.Explicit.PatchRestriction

/-! Only the retained witness intervals contribute to its patch widths. -/

namespace DeletionCode.Explicit.Recognizer

open LetterGraphCuts RulePatch LocalBudget

variable {ℓ q L s : ℕ}

private def witnessIntervals (hs : History ℓ q L s) (root : RuleVertex hs) :
    List (CreationInterval ℓ) :=
  ((retainedEntries hs root).sort (· ≤ ·)).map
    (fun j => (gates hs (finProdFinEquiv.symm j)).interval)

theorem witness_patch_width (hs : History ℓ q L s) (root : RuleVertex hs)
    (p : Fin (PatchTable.patchCount (gates hs)))
    (hp : p ∈ componentPatches (PatchTable.incidence (gates hs)) root)
    {E : ℕ} (hE : (retainedEntries hs root).card ≤ E)
    (hwidth : ∀ e, (gates hs e).interval.width ≤ 3*L) :
    ((CreationInterval.coalesce (PatchTable.intervals (gates hs))).get p).width ≤ 3*E*L := by
  let xs := PatchTable.intervals (gates hs)
  let kept := witnessIntervals hs root
  let patch := (CreationInterval.coalesce xs).get p
  have hkept : kept ⊆ xs := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
    exact PatchTable.interval_mem _ _
  have hp' : patch ∈ CreationInterval.coalesce xs := List.get_mem ..
  have hsub := CreationInterval.patch_mem_coalesce_of_inputs patch hp' ?_ hkept
  · obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hsub
    have hk : kept.length ≤ E := by simpa [kept,witnessIntervals] using hE
    have hw : ∀ i ∈ kept, i.width ≤ 3*L := by
      intro u hu
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hu
      exact hwidth _
    have H := CreationInterval.patch_width_upper kept hk hw ⟨i,hi⟩
    rw [Patches.positions,Nat.card_Icc] at H
    change ((CreationInterval.coalesce kept).get ⟨i,hi⟩).width ≤ _ at H
    change patch.width ≤ 3*E*L
    simpa only [List.get_eq_getElem,he] using H
  · intro i hi hpi
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp hi
    have hlabel : PatchTable.incidence (gates hs) e = p :=
      CreationInterval.containing_index_unique (CreationInterval.coalesce_partition xs).separated
        (PatchTable.incidence_contains (gates hs) e) hpi
    have hcomp := (mem_componentPatches (PatchTable.incidence (gates hs)) root p).mp hp
    rw [← hlabel] at hcomp
    have hr := (mem_componentRules (PatchTable.incidence (gates hs)) root e.1).mpr
      (hcomp.trans ((bubble_reaches (PatchTable.incidence (gates hs)) e.1 e.2).symm))
    apply List.mem_map.mpr
    refine ⟨finProdFinEquiv e,?_,?_⟩
    · apply (Finset.mem_sort _).mpr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [Equiv.symm_apply_apply] using hr⟩
    · rw [Equiv.symm_apply_apply]

#print axioms witness_patch_width

end DeletionCode.Explicit.Recognizer
