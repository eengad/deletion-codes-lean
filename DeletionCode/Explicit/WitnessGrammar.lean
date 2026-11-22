import DeletionCode.Explicit.WitnessSlice
import DeletionCode.Explicit.WitnessPatchWidth
import DeletionCode.Explicit.ReplayDescriptionFacts

/-! Bounded descriptions of actual gate histories and their backward slices. -/

namespace DeletionCode.Explicit.Recognizer

open LetterGraphCuts LetterSequence RulePatch ReplayEntry ReplayGrammar PatchSupport Borrowed

variable {ℓ q K b L Λ R s E : ℕ}

private theorem compactIndex_bound (T : Finset (Fin N)) (i : Fin N) (hi : i ∈ T) :
    compactIndex T i.val < T.card := by
  unfold compactIndex
  rw [dite_eq_left i.isLt,dite_eq_left hi]
  exact (BackwardSlice.number T ⟨i,hi⟩).isLt

theorem saved_lengths
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs)
    (root : RuleVertex hs) (j : Fin (hs.length*s)) :
    let e := witnessEntry hs root x j
    e.left < L ∧ e.right < L ∧ e.removed.length ≤ b ∧ e.replacement.length ≤ b ∧
      (∀ side, ((witnessLifts hs j).lift side).1 ≤ 2*L+b) := by
  dsimp only
  let e := finProdFinEquiv.symm j
  obtain ⟨words,_,_,_,hw⟩ := (h.batch_at e.1).fromCatalogue
  have hspec := (hw e.2).2
  let w := words e.2
  have hl := w.left_upper
  have hr := w.right_upper
  have hrem := w.removed_bound
  have hins := w.replacement_bound
  have hL : 0 < L := by have h := P.window; omega
  have hap : (witnessEntry hs root x j).left = w.left.length := hspec.left
  have hbp : (witnessEntry hs root x j).right = w.right.length := hspec.right
  have hcp : (witnessEntry hs root x j).removed.length = w.removed.length := by
    change (List.ofFn (_ : Fin ((hs.get e.1).bubbles e.2).removed → Fin q)).length = _
    simpa only [List.length_ofFn] using hspec.removed
  have hdp : (witnessEntry hs root x j).replacement.length = w.replacement.length := by
    change (List.ofFn (_ : Fin ((hs.get e.1).bubbles e.2).inserted → Fin q)).length = _
    simpa only [List.length_ofFn] using hspec.inserted
  refine ⟨by omega,by omega,hcp.trans_le hrem,hdp.trans_le hins,?_⟩
  dsimp only [w] at hl hr hrem hins
  intro side
  cases side
  · change ((hs.get e.1).bubbles e.2).left + ((hs.get e.1).bubbles e.2).removed +
        ((hs.get e.1).bubbles e.2).right ≤ _
    rw [hspec.left,hspec.right,hspec.removed]
    omega
  · change ((hs.get e.1).bubbles e.2).left + ((hs.get e.1).bubbles e.2).inserted +
        ((hs.get e.1).bubbles e.2).right ≤ _
    rw [hspec.left,hspec.right,hspec.inserted]
    omega

private theorem reference_fits
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs) (hc : Chronological hs)
    (hx : Strong x K Λ) (hf : LiftsFit (gates hs) (lifts hs) Λ) (hL : K+2*Λ ≤ L)
    (hwidth : ∀ e, (gates hs e).interval.width ≤ 3*L)
    (root : RuleVertex hs) (T : Finset (Fin (hs.length*s)))
    (hT : T ⊆ retainedEntries hs root) (hE : (retainedEntries hs root).card ≤ E)
    (hclosed : BackwardSlice.Closed (witnessSuppliers hs root x) T)
    (j : Fin (hs.length*s)) (hj : j ∈ T) (r : Reference)
    (hr : r ∈ (witnessEntry hs root x j).references) :
    ReferenceFits E L (renameRef (compactIndex T) r) := by
  let e := finProdFinEquiv.symm j
  let p := PatchTable.incidence (gates hs) e
  let a0 := patchAnchor hs p
  let I := (CreationInterval.coalesce (PatchTable.intervals (gates hs))).get p
  have hpatch : p ∈ componentPatches (PatchTable.incidence (gates hs)) root :=
    witnessEntry_patch hs root e (Finset.mem_filter.mp (hT hj)).2
  obtain ⟨o,ho,he⟩ := List.mem_map.mp hr
  obtain ⟨a,ha,hspell,hread⟩ := saved_read h hc root j (hT hj) o ho
  have hanchor := witnessAnchor_at hs root p hpatch
  change witnessAnchor hs root (witnessEntry hs root x j).patch = some a0 at hanchor
  rw [hanchor,he] at hread
  generalize hLift : o.lift = u at hspell hread
  cases r with
  | source delta =>
    cases hread with
    | source anchor _ hroot hnon hlen =>
      have hroot' : a0 = anchor := Option.some.inj hroot
      subst anchor
      have H := hf e Side.negative
      have hIw : I.width ≤ 3*E*L := witness_patch_width hs root p hpatch hE hwidth
      have hI (k : ℕ) (hk : k ∈ (witnessLifts hs j).negative.2.positions) :
          a0.val ≤ k ∧ k < a0.val+I.width := by
        have hk' := Finset.mem_Icc.mp (H.1 hk)
        have hh := PatchTable.incidence_contains (gates hs) e
        change I.Contains (gates hs e).interval at hh
        have hlo : I.first.val ≤ (gates hs e).interval.first.val := hh.1
        have hhi : (gates hs e).interval.last.val ≤ I.last.val := hh.2
        have hFirst : a0.val = I.first.val := rfl
        have hIl : I.first.val ≤ I.last.val := I.first_le_last
        unfold CreationInterval.width
        omega
      have bound := source_reference_bounds hx (witnessLifts hs j).negative.2 hlen ha hL
        hspell H.2.1 H.2.2 hI
      have hpos : 0 < E := (Finset.card_pos.mpr ⟨j,hT hj⟩).trans_le hE
      have hmin : L ≤ 8*E*L := Nat.le_mul_of_pos_left _ (by omega)
      have hmax : 3*E*L ≤ 8*E*L := Nat.mul_le_mul_right L (by omega)
      simp only [renameRef,ReferenceFits]
      have hmin' : (L : ℤ) ≤ 8*(E : ℤ)*L := by exact_mod_cast hmin
      have hmax' : (I.width : ℤ) ≤ 8*(E : ℤ)*L := by exact_mod_cast hIw.trans hmax
      have hd : (((a0.val : ℤ)+delta).toNat : ℤ) - (a0.val : ℤ) = delta := by omega
      rw [hd] at bound
      exact ⟨(neg_le_neg hmin').trans bound.1,(le_of_lt bound.2).trans hmax'⟩
  | supplier k side offset =>
    cases hread with
    | supplier _ _ _ supplier hlt hget _ hw =>
      have hk : k < hs.length*s := hlt.trans j.isLt
      let idx : Fin (hs.length*s) := ⟨k,hk⟩
      have hpair : k < hs.length*s ∧ k < j.val := ⟨hk,hlt⟩
      have hp : witnessLifts hs idx = supplier := Option.some.inj
        (by simpa only [prior,dite_eq_left hpair] using hget)
      have hlen := (saved_lengths h root idx).2.2.2.2 side
      rw [hp] at hlen
      have hm : k ∈ (witnessEntry hs root x j).suppliers := by
        simp only [Entry.suppliers,List.mem_toFinset,List.mem_filterMap]
        exact ⟨.supplier k side offset,hr,rfl⟩
      have hi : idx ∈ witnessSuppliers hs root x j := by
        simpa [witnessSuppliers,hT hj,idx] using hm
      have hi' := hclosed j hj hi
      have hcard : T.card ≤ E := (Finset.card_le_card hT).trans hE
      have hindex : compactIndex T k < E := (compactIndex_bound T idx hi').trans_le hcard
      have hw' : (supplier.lift side).1 ≤ 2*L+b := hlen
      have hbl : b ≤ L := by have hh := P.window; omega
      exact ⟨hindex,by omega⟩

/-- The actual compact witness satisfies the grammar with the manuscript's
single history bound, even when its slice drops most of that history. -/
theorem witness_description_fits
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs) (hc : Chronological hs)
    (hx : Strong x K Λ) (hf : LiftsFit (gates hs) (lifts hs) Λ) (hL : K+2*Λ ≤ L)
    (hwidth : ∀ e, (gates hs e).interval.width ≤ 3*L)
    (i : Fin hs.length) (hspos : 0 < s) (T : Finset (Fin (hs.length*s)))
    (hT : T ⊆ retainedEntries hs (.inl i)) (hE : (retainedEntries hs (.inl i)).card ≤ E)
    (hclosed : BackwardSlice.Closed (witnessSuppliers hs (.inl i) x) T)
    (inner outer : Fin (hs.length*s) → Bool) :
    let ds := descriptions hs (.inl i) x T inner outer
    ds.length ≤ E ∧ ∀ d ∈ ds, EntryFits E L b d.entry := by
  dsimp only
  let root : RuleVertex hs := .inl i
  let a := PatchTable.incidence (gates hs)
  have hrules : (componentRules a root).card * s ≤ E :=
    (retainedEntries_card hs root).symm ▸ hE
  have hpatches : (componentPatches a root).card ≤ E := by
    rw [componentPatches_eq_incidence]
    apply Finset.card_image_le.trans
    simpa [edges,Finset.card_product] using hrules
  refine ⟨by simpa [descriptions] using (Finset.card_le_card hT).trans hE,?_⟩
  intro d hd
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
  let j := BackwardSlice.original T k
  let e := finProdFinEquiv.symm j
  have hj : j ∈ T := (T.orderIsoOfFin rfl k).property
  have hi := (Finset.mem_filter.mp (hT hj)).2
  have hp := witnessEntry_patch hs root e hi
  obtain ⟨hleft,hright,hu,hv,_⟩ := saved_lengths h root j
  have hcount := evaluate_reference_count (witnessEntry_evaluates h hc root j (hT hj))
  refine ⟨?_,?_,hleft,hright,hu,hv,?_,?_⟩
  · change witnessRuleNumber hs root (witnessEntry hs root x j).rule < E
    rw [witnessEntry_rule hs hc]
    exact (compactIndex_bound _ _ hi).trans_le ((Nat.le_mul_of_pos_right _ hspos).trans hrules)
  · exact (compactIndex_bound _ _ hp).trans_le hpatches
  · intro r hr
    obtain ⟨ref,hm,rfl⟩ := List.mem_map.mp hr
    exact reference_fits h hc hx hf hL hwidth root T hT hE hclosed j hj ref hm
  · simpa only [Entry.relabel,List.length_map,Entry.negativeLength] using hcount

#print axioms witness_description_fits

end DeletionCode.Explicit.Recognizer
