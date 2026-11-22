import DeletionCode.Explicit.WitnessFamilies
import DeletionCode.Explicit.WitnessPeelGraph
import DeletionCode.Explicit.PeelingFrame

/-! Compile the whole first-event witness for the reverse-peeling parser. -/

namespace DeletionCode.Explicit.Recognizer

open LetterGraphCuts LetterSequence RulePatch PatchSupport
open ReplayEntry ReplayGrammar CoreWeight PeelingFrame

variable {ℓ q K b L Λ R s D : ℕ}

abbrev ruleCount (hs : History ℓ q L s) (i : Fin hs.length) :=
  (componentRules (PatchTable.incidence (gates hs)) (.inl i)).card

abbrev patchCount (hs : History ℓ q L s) (i : Fin hs.length) :=
  (componentPatches (PatchTable.incidence (gates hs)) (.inl i)).card

theorem patchCount_le (hs : History ℓ q L s) (i : Fin hs.length) :
    patchCount hs i ≤ s*ruleCount hs i := by
  unfold patchCount
  rw [componentPatches_eq_incidence]
  exact Finset.card_image_le.trans (by simp [edges,Finset.card_product,ruleCount,Nat.mul_comm])

def fullDescription (hs : History ℓ q L s) (i : Fin hs.length) (x : Fin ℓ → Fin q) :
    List (DecodedEntry q) :=
  descriptions hs (.inl i) x (retainedEntries hs (.inl i)) (fun _ => true) (fun _ => true)

def fullProgram (hs : History ℓ q L s) (i : Fin hs.length) (x : Fin ℓ → Fin q) :
    PeelingFrame.Program ℓ q (ruleCount hs i) s :=
  let a := PatchTable.incidence (gates hs)
  let root : RuleVertex hs := .inl i
  ⟨fun e => sliceRecord hs root x (retainedEntries hs root)
      (finProdFinEquiv ((originalRule a root e.1).val,e.2)),
    Fin.castLE (patchCount_le hs i) ∘ componentIncidence a root⟩

theorem fullProgram_peel (hs : History ℓ q L s) (i : Fin hs.length) (x : Fin ℓ → Fin q)
    (S : Finset (Fin (ruleCount hs i))) :
    peel (fullProgram hs i x).incidence S =
      peel (componentIncidence (PatchTable.incidence (gates hs)) (.inl i)) S :=
  peel_embed (componentIncidence (PatchTable.incidence (gates hs)) (.inl i)) (Fin.castLE (patchCount_le hs i))
    (fun _ _ h => Fin.ext (congrArg (fun p : Fin (s*ruleCount hs i) => p.val) h)) S

theorem fullPatch_keys (hs : History ℓ q L s) (i : Fin hs.length) (x : Fin ℓ → Fin q)
    (hfit : ∀ d ∈ fullDescription hs i x, d.entry.patch < s*ruleCount hs i) :
    (patchKeys (s*ruleCount hs i) (fullDescription hs i x)).card = patchCount hs i := by
  let a := PatchTable.incidence (gates hs)
  let root : RuleVertex hs := .inl i
  let S := componentRules a root
  let T := retainedEntries hs root
  have hT : T = ruleEntries S s := by
    ext j
    simp [T,retainedEntries,S,a]
  have hp := description_patches hs root x T (fun _ => true) (fun _ => true) hfit
  dsimp only at hp
  change (patchKeys (s*ruleCount hs i) (fullDescription hs i x)).image Fin.val =
    (T.image (fun j => a (finProdFinEquiv.symm j))).image (witnessPatchNumber hs root) at hp
  rw [hT,ruleEntries_patches,← componentPatches_eq_incidence] at hp
  rw [← Finset.card_image_of_injective _ Fin.val_injective,hp]
  exact Finset.card_image_of_injOn (fun _ hp _ hq e => compactIndex_inj hp hq e)

private theorem program_eq {d : ℕ} {p p' : PeelingFrame.Program ℓ q d s}
    (hr : p.record = p'.record) (hi : p.incidence = p'.incidence) : p = p' := by
  cases p
  cases p'
  simp_all

set_option maxHeartbeats 1000000 in
theorem fullDescription_roundtrip
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (records : RecordedBatches P pad x origin hs)
    (hc : Chronological hs) (hx : Strong x K Λ) (hf : LiftsFit (gates hs) (lifts hs) Λ) (hL : K+2*Λ ≤ L)
    (hwidth : ∀ e, (gates hs e).interval.width ≤ 3*L)
    (i : Fin hs.length) (hspos : 0 < s) (hD : ruleCount hs i ≤ D) :
    let d : Fin (D+1) := ⟨ruleCount hs i,by omega⟩
    let ds := fullDescription hs i x
    ∃ code : DescriptionCode (s*d.val) L b q,
      encodeDescription (s*d.val) L b q pad ds = some code ∧
      decodeDescription code = some ds ∧ (patchKeys (s*d.val) ds).card = patchCount hs i ∧
      PeelingFrame.materialize d ds (sliceRoots hs (.inl i) origin ds) L = some (fullProgram hs i x) := by
  dsimp only
  let a := PatchTable.incidence (gates hs)
  let root : RuleVertex hs := .inl i
  let T := retainedEntries hs root
  let d : Fin (D+1) := ⟨ruleCount hs i,by omega⟩
  let ds := fullDescription hs i x
  have hslice := BackwardSlice.slice_spec (witnessSuppliers hs root x) T
  have hSub := witnessSlice_subset records hc hx hf hL root T (by rfl)
  have hEq : witnessSlice hs root x T = T := Finset.Subset.antisymm hSub hslice.1
  have hclosed : BackwardSlice.Closed (witnessSuppliers hs root x) T := by
    have h := hslice.2.1
    change BackwardSlice.Closed _ (witnessSlice hs root x T) at h
    rwa [hEq] at h
  have hE : T.card ≤ s*d.val := by rw [retainedEntries_card,Nat.mul_comm]
  have hfit : ds.length ≤ s*d.val ∧ ∀ p ∈ ds, EntryFits (s*d.val) L b p.entry :=
    witness_description_fits records hc hx hf hL hwidth i hspos T (by rfl) hE hclosed (fun _ => true) (fun _ => true)
  obtain ⟨code,hcode,hdec⟩ := encodeDescription_roundtrip pad ds (by have h := P.window; omega) hfit.1 hfit.2
  refine ⟨code,hcode,hdec,fullPatch_keys hs i x (fun p hp => (hfit.2 p hp).patch),?_⟩
  let prog := fullProgram hs i x
  let rows (k : Fin (d.val*s)) : DecodedEntry q × Completed ℓ (Fin q) :=
    let e := finProdFinEquiv.symm k
    (⟨(prog.record e).1,true,true⟩,(prog.record e).2)
  have hxFull :
      ∀ k : Fin (d.val*s), BackwardSlice.original T (Fin.cast (retainedEntries_card hs root).symm k) =
        finProdFinEquiv ((originalRule a root (finProdFinEquiv.symm k).1).val,(finProdFinEquiv.symm k).2) := by
    intro k
    have h := original_entry hs root (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    simpa only [Prod.eta,Equiv.apply_symm_apply] using h
  have hrows1 : ds = List.ofFn (fun k => (rows k).1) := by
    apply List.ext_getElem
    · simp [ds,fullDescription,descriptions,T,retainedEntries_card,d,ruleCount,root]
    · intro k h₁ h₂
      have hk : k < d.val*s := by simpa using h₂
      have hidx := hxFull ⟨k,hk⟩
      change (descriptions hs root x T (fun _ => true) (fun _ => true))[k] = _
      simp only [descriptions,List.getElem_ofFn]
      have hkt : k < T.card := by
        change k < (retainedEntries hs root).card
        rwa [retainedEntries_card]
      have hidx' : BackwardSlice.original T ⟨k,hkt⟩ = _ := hidx
      rw [hidx']
      rfl
  have hrows2 : (List.ofFn fun k => (sliceRecord hs root x T (BackwardSlice.original T k)).2) =
      List.ofFn (fun k => (rows k).2) := by
    apply List.ext_getElem
    · simp only [List.length_ofFn]
      exact retainedEntries_card hs root
    · intro k h₁ h₂
      have hk : k < d.val*s := by simpa using h₂
      have he := hxFull ⟨k,hk⟩
      simp only [List.getElem_ofFn]
      change (sliceRecord hs root x T (BackwardSlice.original T
        (Fin.cast (retainedEntries_card hs root).symm ⟨k,hk⟩))).2 = _
      rw [he]
      rfl
  have hA : ∀ p ∈ descriptions hs root x (witnessSlice hs root x T) (fun _ => true) (fun _ => true),
      p.entry.patch < s*d.val := by
    rw [hEq]
    exact fun p hp => (hfit.2 p hp).patch
  have hrun := replay_slice_anchors records hc hx hf hL root T (by rfl) (fun _ => true) (fun _ => true) hA
  dsimp only at hrun
  rw [hEq] at hrun
  change replay L (anchorLookup (patchKeys (s*d.val) ds) (sliceRoots hs root origin ds))
      (ds.map (·.entry)) = some (List.ofFn fun k => (sliceRecord hs root x T (BackwardSlice.original T k)).2).toArray at hrun
  rw [hrows2] at hrun
  have hmatch (xs : List (DecodedEntry q)) (heq : xs = List.ofFn fun k => (rows k).1)
      (H : replay L (anchorLookup (patchKeys (s*d.val) xs) (sliceRoots hs root origin xs))
          (xs.map (·.entry)) = some (List.ofFn fun k => (rows k).2).toArray) :
      PeelingFrame.materialize d xs (sliceRoots hs root origin xs) L = some prog := by
    subst xs
    have hb (k : Fin (d.val*s)) : (rows k).1.entry.patch < s*d.val := by
      have hmem : (rows k).1 ∈ ds := by rw [hrows1]; exact List.mem_ofFn.mpr ⟨k,rfl⟩
      exact (hfit.2 _ hmem).patch
    rw [PeelingFrame.materialize_of_table d rows _ H hb]
    congr 1
    apply program_eq
    · funext e
      simp [rows]
    · funext e
      apply Fin.ext
      change (rows (finProdFinEquiv e)).1.entry.patch = (prog.incidence e).val
      simp only [rows,Equiv.symm_apply_apply]
      have hp := componentIncidence_original a root e.1 e.2
      simp only [prog,fullProgram,sliceRecord,witnessEntry,Equiv.symm_apply_apply,
        Entry.relabel,PreparedBubble.replayEntry,Function.comp_apply,Fin.val_castLE]
      change witnessPatchNumber hs root (a ((originalRule a root e.1).val,e.2)) =
        (componentIncidence a root e).val
      rw [← hp]
      exact compactIndex_original _ _
  exact hmatch ds hrows1 hrun

#print axioms fullProgram_peel
#print axioms fullDescription_roundtrip

end DeletionCode.Explicit.Recognizer
