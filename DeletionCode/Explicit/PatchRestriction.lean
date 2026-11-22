import DeletionCode.Explicit.PatchIntervals

/-! Restrict interval coalescing to one already established patch. -/

namespace DeletionCode.Explicit.LetterGraphCuts.CreationInterval

variable {ℓ : ℕ}

/-- If a sublist keeps all inputs in a patch, it preserves that patch. -/
theorem patch_mem_coalesce_of_inputs {all kept : List (CreationInterval ℓ)}
    (p : CreationInterval ℓ) (hp : p ∈ coalesce all)
    (h : ∀ i ∈ all, p.Contains i → i ∈ kept) (hkept : kept ⊆ all) :
    p ∈ coalesce kept := by
  classical
  let inside := kept.filter fun i => decide (p.Contains i)
  have hlocal : ∀ i ∈ inside, p.Contains i := fun i hi => of_decide_eq_true (List.mem_filter.mp hi).2
  have hparts : ∀ i ∈ coalesce inside, p.Contains i := by
    intro i hi
    obtain ⟨j,hj,hji⟩ := (coalesce_partition inside).finest [p] (by simp [Separated])
      (fun j hj => ⟨p,by simp,hlocal j hj⟩) i hi
    simpa only [List.mem_singleton.mp hj] using hji
  have splitAt (xs : List (CreationInterval ℓ)) (hmem : p ∈ xs) :
      ∃ before after, xs = before ++ p :: after := by
    induction xs with
    | nil => simp at hmem
    | cons j js ih =>
      rcases List.mem_cons.mp hmem with rfl | hj
      · exact ⟨[],js,rfl⟩
      · obtain ⟨before,after,he⟩ := ih hj
        exact ⟨j::before,after,congrArg (j::·) he⟩
  obtain ⟨before,after,hall⟩ := splitAt (coalesce all) hp
  have hsep := (coalesce_partition all).separated
  rw [hall] at hsep
  obtain ⟨hbefore,htail,hcross⟩ := List.pairwise_append.mp hsep
  obtain ⟨hafterp,hafter⟩ := List.pairwise_cons.mp htail
  let cover := (before ++ coalesce inside) ++ after
  have hcover_sep : Separated cover := by
    change Separated ((before ++ coalesce inside) ++ after)
    rw [List.append_assoc]
    apply List.pairwise_append.mpr
    refine ⟨hbefore,List.pairwise_append.mpr ⟨(coalesce_partition inside).separated,hafter,?_⟩,?_⟩
    · intro i hi j hj
      exact (hparts i hi).2.trans_lt (hafterp j hj)
    · intro i hi j hj
      rcases List.mem_append.mp hj with hj | hj
      · exact (hcross i hi p List.mem_cons_self).trans_le (hparts j hj).1
      · exact hcross i hi j (List.mem_cons_of_mem _ hj)
  have hcover : Covers cover all := by
    intro i hi
    obtain ⟨j,hj,hji⟩ := (coalesce_partition all).covers i hi
    rw [hall] at hj
    rcases List.mem_append.mp hj with hj | hj
    · exact ⟨j,List.mem_append_left _ (List.mem_append_left _ hj),hji⟩
    · rcases List.mem_cons.mp hj with rfl | hj
      · obtain ⟨r,hr,hri⟩ := (coalesce_partition inside).covers i
          (List.mem_filter.mpr ⟨h i hi hji,decide_eq_true hji⟩)
        exact ⟨r,List.mem_append_left _ (List.mem_append_right _ hr),hri⟩
      · exact ⟨j,List.mem_append_right _ hj,hji⟩
  obtain ⟨r,hr,hrp⟩ := (coalesce_partition all).finest cover hcover_sep hcover p hp
  have hr' : r ∈ coalesce inside := by
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact (not_lt_of_ge (p.first_le_last.trans hrp.2) (hcross r hr p List.mem_cons_self)).elim
      · exact hr
    · exact (not_lt_of_ge (hrp.1.trans p.first_le_last) (hafterp r hr)).elim
  obtain ⟨z,hz,hzr⟩  := (coalesce_partition inside).finest _ (coalesce_partition kept).separated
    (fun i hi => (coalesce_partition kept).covers i (List.mem_filter.mp hi).1) r hr'
  obtain ⟨w,hw,hwz⟩ := (coalesce_partition kept).finest _ (coalesce_partition all).separated
    (fun i hi => (coalesce_partition all).covers i (hkept hi)) z hz
  have hwp := hwz.trans (hzr.trans hrp)
  obtain ⟨a,ha,har⟩ := List.mem_iff_getElem.mp hp
  let ia : Fin (coalesce all).length := ⟨a,ha⟩
  have hia : (coalesce all).get ia = p := har
  obtain ⟨c,hc,hcw⟩ := List.mem_iff_getElem.mp hw
  let ic : Fin (coalesce all).length := ⟨c,hc⟩
  have hic : (coalesce all).get ic = w := hcw
  have hidx := containing_index_unique (coalesce_partition all).separated
    (i := p) (p := ia) (q := ic) (hia ▸ Contains.refl _) (hic ▸ hwp)
  have heq : w = p := hic.symm.trans (congrArg (coalesce all).get hidx.symm |>.trans hia)
  have hzp : z.Contains p := hzr.trans hrp
  have hpz : p.Contains z := heq ▸ hwz
  have hval : z = p := by
    cases z
    cases p
    have hf := le_antisymm hzp.1 hpz.1
    have hl := le_antisymm hpz.2 hzp.2
    cases hf
    cases hl
    rfl
  exact hval ▸ hz

#print axioms patch_mem_coalesce_of_inputs

end DeletionCode.Explicit.LetterGraphCuts.CreationInterval
