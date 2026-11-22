import DeletionCode.Explicit.WitnessPeelGraph
import DeletionCode.Explicit.WitnessCoreRows
import DeletionCode.Explicit.RecognizerRecords
import DeletionCode.Explicit.RecognizerWitness

/-! Coverage of the executable core catalogue by the actual witness slices. -/

namespace DeletionCode.Explicit.Recognizer

open LetterGraphCuts LetterSequence PatchSupport ReplayEntry ReplayGrammar CoreWeight FieldHash RulePatch

variable {ℓ q L E K b Λ R t θ r₀ : ℕ}

/-- A nonempty set of surviving rules with the core's two size bounds gives
an actual kept slot in the core catalogue at this word. -/
theorem core_weight_pos_of_rules
    {P : RuleAddition.Bounds K b L Λ (2*t) R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L (2*t)} (records : RecordedBatches P pad x origin hs)
    (hc : Chronological hs) (hx : Strong x K Λ) (hf : LiftsFit (gates hs) (lifts hs) Λ)
    (hL : K+2*Λ ≤ L) (hℓ : 0 < ℓ) (ht : 2 ≤ t)
    (hwidth : ∀ e, (gates hs e).interval.width ≤ 3*L)
    (i : Fin hs.length) (hE : (retainedEntries hs (.inl i)).card ≤ E)
    (H : TernaryMatrix θ (q^L)) (hk : ∀ r ∈ hs, H.mulVec r.row = 0)
    (S : Finset (Fin hs.length)) (hS : S ⊆ componentRules (PatchTable.incidence (gates hs)) (.inl i))
    (hn : 0 < S.card) (hr₀ : S.card ≤ r₀)
    (hp : (patches (PatchTable.incidence (gates hs)) S).card ≤ t*S.card) :
    0 < weight (coreReplayData ℓ q E L b t r₀ K Λ pad).object H x := by
  let root : RuleVertex hs := .inl i
  let a := PatchTable.incidence (gates hs)
  let ends := ruleEntries S (2*t)
  let T := witnessSlice hs root x ends
  let ds := descriptions hs root x T (markRule S) (markRule S)
  let keys := finalRuleKeys E ds
  let f (r : Fin hs.length) := witnessRuleNumber hs root r.val
  let j : Fin r₀ := ⟨S.card-1,by omega⟩
  have hj : j.val+1 = S.card := by dsimp [j]; omega
  have hspos : 0 < 2*t := by omega
  have he : ends ⊆ retainedEntries hs root := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hS ((mem_ruleEntries S k).mp hk)⟩
  have hsSpec := BackwardSlice.slice_spec (witnessSuppliers hs root x) ends
  have hends : ends ⊆ T := hsSpec.1
  have hT := witnessSlice_subset records hc hx hf hL root ends he
  have hfits : ds.length ≤ E ∧ ∀ e ∈ ds, EntryFits E L b e.entry :=
    witness_description_fits records hc hx hf hL hwidth i hspos T hT hE hsSpec.2.1 (markRule S) (markRule S)
  have hkeyImage : keys.image Fin.val = S.image f :=
    marked_keys hs root x hc S hspos T hends (fun d hd => (hfits.2 d hd).rule)
  have hkeyFor (id : Fin E) (hid : id ∈ keys) : ∃ r ∈ S, f r = id.val := by
    apply Finset.mem_image.mp
    rw [← hkeyImage]
    exact Finset.mem_image_of_mem _ hid
  have hkeys : keys.card = j.val+1 := by
    rw [hj,← Finset.card_image_of_injective _ Fin.val_injective,hkeyImage]
    apply Finset.card_image_of_injOn
    intro a ha b hb he
    exact compactIndex_inj (hS ha) (hS hb) he
  have hCount (id : Fin E) (hid : id ∈ keys) :
      (ds.filter (fun d => d.finalBubble && d.entry.rule == id.val)).length = 2*t := by
    obtain ⟨r,hr,hnum⟩ := hkeyFor id hid
    have hordered := filter_replayedPairs hs root x hc T S hends hT r hr id.val hnum hspos
    have hd : (replayedPairs hs root x T S).map Prod.fst = ds := by
      unfold ds
      rw [descriptions_eq_sorted]
      simp only [replayedPairs,List.map_map,Function.comp_def,sliceRecord]
    have H : ds.filter (fun d => d.finalBubble && d.entry.rule == id.val) =
        ((replayedPairs hs root x T S).filter (fun p => p.1.finalBubble && p.1.entry.rule == id.val)).map Prod.fst := by
      rw [← hd,List.filter_map]
      rfl
    rw [H,hordered,List.length_map,List.length_ofFn]
  have hTagged (d : DecodedEntry q) (hd : d ∈ ds) (hd' : d.finalBubble = true) :
      ∃ id ∈ keys, d.entry.rule = id.val := by
    have hfr : d.finalRule = true := by
      change d ∈ descriptions hs root x T (markRule S) (markRule S) at hd
      rw [descriptions_eq_sorted] at hd
      obtain ⟨_,_,rfl⟩ := List.mem_map.mp hd
      exact hd'
    let id : Fin E := ⟨d.entry.rule,(hfits.2 d hd).rule⟩
    exact ⟨id,(finalKeys_iff id).mpr ⟨d,hd,hfr,rfl⟩,rfl⟩
  have hp' : (patchKeys E ds).card ≤ t*(j.val+1) := by
    have B := slice_anchor_count records hc hx hf hL root ends (markRule S) (markRule S)
      (fun d hd => (hfits.2 d hd).patch)
    dsimp only at B
    change (patchKeys E ds).card ≤ (ends.image _).card at B
    rw [show ends = ruleEntries S (2*t) from rfl,ruleEntries_patches] at B
    rw [hj]
    exact B.trans hp
  let roots := sliceRoots (E := E) hs root origin ds
  let outs := List.ofFn (fun k => (sliceRecord hs root x T (BackwardSlice.original T k)).2)
  have hrun : replay L (anchorLookup (patchKeys E ds) roots) (ds.map (·.entry)) = some outs.toArray :=
    replay_slice_anchors records hc hx hf hL root ends he (markRule S) (markRule S)
      (fun d hd => (hfits.2 d hd).patch)
  obtain ⟨code,_,hm⟩ := materialize_of_encoding pad ds j hℓ (by have h := P.window; omega)
    hfits.1 hfits.2 hkeys hCount hTagged hp' roots outs.toArray hrun
  let k : ReplaySlot ℓ q E L b t r₀ :=
    ⟨j,packDescription code,packAnchors hℓ (patchKeys E ds) hp' roots⟩
  let m : Materialized ℓ q E (j.val+1) := ⟨ds.zip outs,keys,hkeys⟩
  have hmaterial : materialize k = some m := by simpa only [k,m,List.toList_toArray] using hm
  have hmEntries : m.entries = replayedPairs hs root x T S := zip_slice hs root x T S
  have hvalid : coreCheck K b L Λ (2*t) pad m x = true := by
    apply coreCheck_of_families
    intro id hid
    obtain ⟨r,hr,hnum⟩ := hkeyFor id hid
    rw [hmEntries]
    exact (replayed_rule records hc root T S hends hT r hr id.val hnum hspos).1
  let codeRule := keys.orderEmbOfFin hkeys
  have hrow (p : Fin (j.val+1)) : ∃ r ∈ S, f r = (codeRule p).val :=
    hkeyFor (codeRule p) (Finset.orderEmbOfFin_mem _ _ _)
  choose r hr hcode using hrow
  have hmat : m.matrix L pad x = fun p => (hs.get (r p)).row := by
    funext p col
    change ((m.entries.filter (fun e => e.1.finalBubble && e.1.entry.rule == (codeRule p).val)).map
      (fun e => LiftDictionary.bubbleVector (L := L) pad x e.2 (finFunctionFinEquiv.symm col))).sum =
      (hs.get (r p)).row col
    rw [hmEntries]
    exact (replayed_rule records hc root T S hends hT (r p) (hr p) _ (hcode p) hspos).2 col
  have hinj : Function.Injective r := by
    intro a b h
    apply codeRule.injective
    apply Fin.ext
    rw [← hcode a,← hcode b,h]
  have hind : LinearIndependent F₃ (m.matrix L pad x).row := by
    change LinearIndependent F₃ (m.matrix L pad x)
    rw [hmat]
    exact records.independent.comp _ hinj
  have hker (p : Fin θ) : (m.matrix L pad x).mulVec (H p) = 0 := by
    funext a
    rw [hmat]
    have hz := congrFun (hk (hs.get (r a)) (List.get_mem ..)) p
    change (hs.get (r a)).row ⬝ᵥ H p = 0
    rw [dotProduct_comm]
    exact hz
  exact ReplayData.weight_pos_of_replay _ H x k (m.matrix L pad x)
    (core_rules_from_source pad k x hmaterial hvalid) hind hker

/-- A nonempty core found by the executable witness peeler makes the
word's core weight positive. -/
theorem firstEvent_core_weight_pos
    {P : RuleAddition.Bounds K b L Λ (2*t) R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L (2*t)} (records : RecordedBatches P pad x origin hs)
    (hx : Strong x K Λ) (hL : K+2*Λ ≤ L) (hℓ : 0 < ℓ) (ht : 2 ≤ t)
    (H : TernaryMatrix θ (q^L)) (i : Fin hs.length)
    (hv : ResultValid H pad x K b Λ R (.firstEvent hs i))
    (hk : AllKernel H (.firstEvent hs i))
    (hn : (core (componentIncidence (PatchTable.incidence (gates hs)) (.inl i))).Nonempty) :
    0 < weight (coreReplayData ℓ q ((2*t)*(8*(2*t)*R+1)) L b t ((10*(2*t)-1)/(t-1)) K Λ pad).object H x := by
  let a := PatchTable.incidence (gates hs)
  let root : RuleVertex hs := .inl i
  let C := componentIncidence a root
  let S := core C
  let selected := S.image (fun j => (originalRule a root j).val)
  have hp : 0 < L := by have hw := P.window; omega
  have hspos : 0 < 2*t := by omega
  have hE := firstEvent_witnessEntries H pad x hp hspos hv
  have hB := firstEvent_witnessBounds H pad x hp hspos hv
  obtain ⟨_,_,graph,_,_⟩ := hv
  obtain ⟨hpatch,hpos,hcard,_⟩ := peeled_core_bounds ht C (componentIncidence_connected a root) hB.2.1 hn
  have hS : selected ⊆ componentRules a root := by
    intro j hj
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hj
    exact (originalRule a root r).property
  have hcount : selected.card = S.card :=
    Finset.card_image_of_injective _ (Subtype.val_injective.comp ((componentRules a root).orderIsoOfFin rfl).injective)
  have hP : (patches a selected).card ≤ t*selected.card := by
    rw [hcount,patches_original]
    exact Finset.card_image_le.trans hpatch
  exact core_weight_pos_of_rules records graph.chronology hx graph.fit hL hℓ ht graph.highWidth
    i hE H hk selected hS (hcount.symm ▸ hpos) (hcount.symm ▸ hcard) hP

#print axioms core_weight_pos_of_rules
#print axioms firstEvent_core_weight_pos

end DeletionCode.Explicit.Recognizer
