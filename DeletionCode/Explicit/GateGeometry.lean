import DeletionCode.Explicit.PatchIntervals

/-! The creation interval of a negative lift and its width bounds (`d:creation-interval`). -/

namespace DeletionCode.Explicit.LetterGraphCuts
open LetterSequence LocalBudget
variable {ℓ a u v r n : ℕ} {α : Type*}

private theorem window_has_original (w : Lift ℓ n α) {start len : ℕ}
    (h : start+len ≤ n) (hf : w.freshOffsets.card < len) :
    ∃ (i : Fin len) (p : Fin ℓ), w.letters ⟨start+i.val,by omega⟩ = .original p := by
  let s := w.window start len h
  by_contra hno
  have hall : (Finset.univ : Finset (Fin len)) ⊆ s.freshOffsets := by
    intro i _
    cases hi : s.letters i with
    | original p => exact (hno ⟨i,p,hi⟩).elim
    | fresh g k x => exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [hi,Letter.position]⟩
  have hbound := (Finset.card_le_card hall).trans (w.window_fresh_le h)
  simpa using (not_le_of_gt hf (by simpa using hbound))

theorem Gate.inPatch_of_fresh (g : Gate ℓ a u v r α) {c : ℕ} (P : Patches ℓ c) (p : Fin c)
    (hl : g.negative.freshOffsets.card < a) (hr : g.negative.freshOffsets.card < r)
    (hcover : g.negative.positions ⊆ P.positions p) : Nonempty (g.InPatch P p) := by
  obtain ⟨i,lo,hlo⟩ := window_has_original g.negative (start := 0) (len := a) (by omega) hl
  obtain ⟨j,hi,hhi⟩ := window_has_original g.negative (start := a+u) (len := r) (by omega) hr
  have hlo' : g.negative.letters ⟨i.val,by omega⟩ = .original lo := by
    simpa [Nat.zero_add] using hlo
  have hleft : lo.val ∈ P.positions p := hcover (g.negative.mem_positions.mpr
    ⟨⟨i.val,by omega⟩,lo,by simp [hlo',Letter.position],rfl⟩)
  have hright : hi.val ∈ P.positions p := hcover (g.negative.mem_positions.mpr
    ⟨⟨a+u+j.val,by omega⟩,hi,by simp [hhi,Letter.position],rfl⟩)
  exact ⟨⟨i,j,lo,hi,hlo',hhi,(Finset.mem_Icc.mp hleft).1,(Finset.mem_Icc.mp hright).2⟩⟩


theorem positions_add_fresh (w : Lift ℓ n α) :
    w.positions.card + w.freshOffsets.card = n := by
  let old : Finset (Fin n) := Finset.univ \ w.freshOffsets
  have hasPos (i : Fin n) (hi : i ∈ old) : ∃ p, (w.letters i).position = some p := by
    cases h : (w.letters i).position with
    | some p => exact ⟨p,rfl⟩
    | none =>
      exact ((Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)).elim
  choose pos hpos using hasPos
  have hcard : old.card = w.positions.card := by
    apply Finset.card_bij (fun i hi => (pos i hi).val)
    · intro i hi
      exact w.mem_positions.mpr ⟨i,pos i hi,hpos i hi,rfl⟩
    · intro i hi j hj h
      have he : pos i hi = pos j hj := Fin.ext h
      rcases lt_trichotomy i j with hij | hij | hij
      · exact (ne_of_lt (w.increasing hij (hpos i hi) (hpos j hj)) he).elim
      · exact hij
      · exact (ne_of_gt (w.increasing hij (hpos j hj) (hpos i hi)) he).elim
    · intro p hp
      obtain ⟨i,j,hj,rfl⟩ := w.mem_positions.mp hp
      have hi : i ∈ old := by simp [old,Lift.freshOffsets,hj]
      have he : pos i hi = j := Option.some.inj ((hpos i hi).symm.trans hj)
      exact ⟨i,hi,congrArg Fin.val he⟩
  rw [← hcard]
  have hsub : w.freshOffsets ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
  simp only [old,Finset.card_sdiff_of_subset hsub,Finset.card_univ,Fintype.card_fin]
  have hle := Finset.card_le_card hsub
  simp only [Finset.card_univ,Fintype.card_fin] at hle
  omega

private theorem width_eq (w : Lift ℓ n α) (hn : w.positions.Nonempty) :
    w.positions.max' hn + 1 - w.positions.min' hn = w.positions.card + w.omissions.card := by
  let lo := w.positions.min' hn
  let hi := w.positions.max' hn
  have hlo := w.positions.min'_mem hn
  have hhi := w.positions.max'_mem hn
  have hin : w.positions ⊆ Finset.Icc lo hi := fun p hp =>
    Finset.mem_Icc.mpr ⟨w.positions.min'_le p hp,w.positions.le_max' p hp⟩
  have hr : hi < ℓ := by
    obtain ⟨_,p,_,hp⟩ := w.mem_positions.mp hhi
    change w.positions.max' hn < ℓ
    exact hp ▸ p.isLt
  have hdiff : Finset.Icc lo hi \ w.positions = w.omissions := by
    ext p
    constructor
    · intro hp
      obtain ⟨hi',hn'⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hl,hh⟩ := Finset.mem_Icc.mp hi'
      have hl' : lo < p := lt_of_le_of_ne hl (fun h => hn' (h ▸ hlo))
      have hh' : p < hi := lt_of_le_of_ne hh (fun h => hn' (h.symm ▸ hhi))
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (hh.trans_lt hr),hn',⟨lo,hlo,hl'⟩,⟨hi,hhi,hh'⟩⟩
    · intro hp
      obtain ⟨_,hn',⟨l,hl,hl'⟩,⟨h,hh,hh'⟩⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_Icc.mpr ⟨(w.positions.min'_le l hl).trans hl'.le,
          hh'.le.trans (w.positions.le_max' h hh)⟩,hn'⟩
  have hsize := Finset.card_le_card hin
  have hcard := Finset.card_sdiff_of_subset hin
  rw [Nat.card_Icc] at hsize
  rw [hdiff,Nat.card_Icc] at hcard
  change hi+1-lo = w.positions.card+w.omissions.card
  omega

private theorem positions_inside (w : Lift ℓ n α) {k : ℕ} (h : k ∈ w.positions) :
    k < ℓ := by
  obtain ⟨_,p,_,rfl⟩ := w.mem_positions.mp h
  exact p.isLt

/-- The inclusive interval from the first to the last original position of
a lift. The nonemptiness proof is erased by the executable definition. -/
def CreationInterval.ofLift (w : Lift ℓ n α) (h : w.positions.Nonempty) : CreationInterval ℓ where
  first := ⟨w.positions.min' h,positions_inside w (w.positions.min'_mem h)⟩
  last := ⟨w.positions.max' h,positions_inside w (w.positions.max'_mem h)⟩
  first_le_last := w.positions.min'_le _ (w.positions.max'_mem h)

theorem CreationInterval.ofLift_contains_position (w : Lift ℓ n α) (h : w.positions.Nonempty)
    {k : ℕ} (hk : k ∈ w.positions) :
    (ofLift w h).first.val ≤ k ∧ k ≤ (ofLift w h).last.val :=
  ⟨w.positions.min'_le k hk,w.positions.le_max' k hk⟩

theorem Gate.positions_nonempty (g : Gate ℓ a u v r α)
    (hl : g.negative.freshOffsets.card < a) : g.negative.positions.Nonempty := by
  obtain ⟨i,p,hp⟩ := window_has_original g.negative (start := 0) (len := a) (by omega) hl
  exact ⟨p.val,g.negative.mem_positions.mpr ⟨⟨0+i.val,by omega⟩,p,by rw [hp]; rfl,rfl⟩⟩

/-- A gate's creation interval comes from its stored negative lift. -/
def Gate.creationInterval (g : Gate ℓ a u v r α) (h : g.negative.positions.Nonempty) :
    CreationInterval ℓ :=
  CreationInterval.ofLift g.negative h

theorem Gate.inPatch_of_creation (g : Gate ℓ a u v r α) {c : ℕ} (P : Patches ℓ c) (p : Fin c)
    (hn : g.negative.positions.Nonempty)
    (hl : g.negative.freshOffsets.card < a) (hr : g.negative.freshOffsets.card < r)
    (hlo : P.first p ≤ (g.creationInterval hn).first.val)
    (hhi : (g.creationInterval hn).last.val ≤ P.last p) : Nonempty (g.InPatch P p) := by
  apply g.inPatch_of_fresh P p hl hr
  intro k hk
  obtain ⟨kl,kr⟩ := CreationInterval.ofLift_contains_position g.negative hn hk
  exact Finset.mem_Icc.mpr ⟨hlo.trans kl,kr.trans hhi⟩

theorem Gate.creation_width (g : Gate ℓ a u v r α) (hn : g.negative.positions.Nonempty)
    {bound : ℕ} (hf : g.negative.freshOffsets.card ≤ bound) (ho : g.negative.omissions.card ≤ bound) :
    let i := g.creationInterval hn
    a+u+r-bound ≤ i.last.val+1-i.first.val ∧ i.last.val+1-i.first.val ≤ a+u+r+bound := by
  dsimp [Gate.creationInterval,CreationInterval.ofLift]
  rw [width_eq g.negative hn]
  have hcard := positions_add_fresh g.negative
  omega

private theorem Gate.positions_survive_or_marked (g : Gate ℓ a u v r α) :
    g.negative.positions ⊆ g.positive.positions ∪ g.marks := by
  intro p hp
  obtain ⟨i,z,hi,rfl⟩ := g.negative.mem_positions.mp hp
  by_cases hl : i.val < a
  · have same := g.negative.gate_left_letter g.entry g.replacement i.val hl
    change g.positive.letters _ = _ at same
    exact Finset.mem_union_left _ (g.positive.mem_positions.mpr
      ⟨⟨i.val,by omega⟩,z,by rw [same]; exact hi,rfl⟩)
  by_cases hm : i.val < a+u
  · let j : Fin u := ⟨i.val-a,by omega⟩
    have e : (⟨a+j.val,by omega⟩ : Fin (a+u+r)) = i :=
      Fin.ext (by change a+(i.val-a) = i.val; omega)
    apply Finset.mem_union_right
    apply g.mem_marks.mpr
    refine ⟨z,List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨g.negative.letters i,?_,hi⟩),rfl⟩
    exact List.mem_ofFn.mpr ⟨j,congrArg g.negative.letters e⟩
  · let j := i.val-(a+u)
    have hj : j < r := by dsimp [j]; omega
    have e : (⟨a+u+j,by omega⟩ : Fin (a+u+r)) = i :=
      Fin.ext (by change a+u+(i.val-(a+u)) = i.val; omega)
    have same := g.negative.gate_right_letter g.entry g.replacement j hj
    change g.positive.letters _ = _ at same
    exact Finset.mem_union_left _ (g.positive.mem_positions.mpr
      ⟨⟨a+v+j,by omega⟩,z,by rw [same,e]; exact hi,rfl⟩)

/-- At most the inserted length is added to the fresh count. -/
theorem Gate.positive_fresh_le (g : Gate ℓ a u v r α) :
    g.positive.freshOffsets.card ≤ g.negative.freshOffsets.card + v := by
  have h := (Finset.card_le_card g.positions_survive_or_marked).trans (Finset.card_union_le _ _)
  have hc := g.marks_card_le
  have hn := positions_add_fresh g.negative
  have hp := positions_add_fresh g.positive
  omega

/-- Every additional omission of the positive lift lies in the removed segment. -/
theorem Gate.positive_omissions_le (g : Gate ℓ a u v r α) :
    g.positive.omissions.card ≤ g.negative.omissions.card + u := by
  have hsub : g.positive.omissions ⊆ g.negative.omissions ∪ g.marks := by
    intro p hp
    obtain ⟨hr,hmiss,⟨lo,hlo,hl⟩,⟨hi,hhi,hh⟩⟩ := Finset.mem_filter.mp hp
    by_cases h : p ∈ g.negative.positions
    · rcases Finset.mem_union.mp (g.positions_survive_or_marked h) with ho | hm
      · exact (hmiss ho).elim
      · exact Finset.mem_union_right _ hm
    · have hin := g.negative.gate_positions_subset g.entry g.replacement
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hr,h,⟨lo,hin hlo,hl⟩,⟨hi,hin hhi,hh⟩⟩)
  exact ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _)).trans
    (Nat.add_le_add_left g.marks_card_le _)

theorem Gate.positive_enclosed (g : Gate ℓ a u v r α) (h : g.negative.positions.Nonempty)
    {k : ℕ} (hk : k ∈ g.positive.positions) :
    (g.creationInterval h).first.val ≤ k ∧ k ≤ (g.creationInterval h).last.val :=
  CreationInterval.ofLift_contains_position g.negative h
    (g.negative.gate_positions_subset g.entry g.replacement hk)

#print axioms Gate.inPatch_of_creation
#print axioms Gate.creation_width
#print axioms Gate.positive_fresh_le
#print axioms Gate.positive_omissions_le

end DeletionCode.Explicit.LetterGraphCuts
