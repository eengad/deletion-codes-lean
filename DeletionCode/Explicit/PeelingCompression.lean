import DeletionCode.Explicit.PeelingFamilyBounds
import DeletionCode.Explicit.WitnessProgramFacts

/-! Reverse-peeling compression for the concrete first-event component. -/

namespace DeletionCode.Explicit.PeelingCompression

open UniformParameters ConcreteSource PeelingFamilyBounds
open Recognizer LetterGraphCuts LetterSequence RulePatch FirstEvent
open ReplayEntry ReplayGrammar PeelingBuckets BubbleFamilies CompressorFrame

variable {q b t ℓ : ℕ}

def packWitness (hq : 1 < q) (hℓ : 0 < ℓ) (pad : Fin q) (H : Hash q b t ℓ)
    (x : Fin ℓ → Fin q) (hs : History ℓ q (gram q b t ℓ) (edits t))
    (i : Fin hs.length) : Option (QWord q) := do
  let p := fullProgram hs i x
  if core p.incidence ≠ ∅ then none else
    if !(PeelingFrame.trace p).all (fun j => !SmallCompression.isSmall (b := b) (t := t) pad (p.record j)) then none
    else if hD : ruleCount hs i ≤ witnessLimit q b t ℓ then
      let d : Fin (witnessLimit q b t ℓ+1) := ⟨ruleCount hs i,by omega⟩
      let code ← encodeDescription (edits t*d.val) (gram q b t ℓ) b q pad (fullDescription hs i x)
      PeelingFrame.encode hq hℓ (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ)
        pad d code (fun k => (witnessAnchor hs (.inl i) k).getD ⟨0,hℓ⟩) H x
    else none

def read (pad : Fin q) (H : Hash q b t ℓ) (payload : QWord q) : Option (Fin ℓ → Fin q) :=
  PeelingFrame.decode ℓ (edits t) (witnessLimit q b t ℓ) (windowLength q ℓ) b (gram q b t ℓ)
    (omittedLetters q b t ℓ) pad H payload

private theorem mixed_capacity_positive (hq : 1 < q) {digits values : List ℕ}
    {v : Fin (MixedRadix.width q digits) → Fin q}
    (h : MixedRadix.encode hq digits values = some v) :
    0 < digits.prod := by
  cases hr : MixedRadix.rank digits values with
  | none => simp [MixedRadix.encode,hr] at h
  | some rank => exact Nat.zero_lt_of_lt rank.isLt

theorem noSmall_full (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (pad : Fin q) (H : Hash q b t ℓ) (x : Fin ℓ → Fin q) (hstart : minLength q b t ≤ ℓ)
    (hx : Strong x (windowLength q ℓ) (omittedLetters q b t ℓ))
    {hs : History ℓ q (gram q b t ℓ) (edits t)} {i : Fin hs.length}
    (hv : ResultValid H pad x (windowLength q ℓ) b (omittedLetters q b t ℓ) (componentCutoff q b t ℓ)
      (.firstEvent hs i))
    {origin : Fin ℓ} (records : RecordedBatches (recognizerBounds (basicBounds hq hb ht hstart)) pad x origin hs)
    (h : SmallCompression.packWitness (show 1 < q by omega) pad x hs i = none)
    (e : Fin (ruleCount hs i) × Fin (edits t)) :
    SmallCompression.isSmall (b := b) (t := t) pad ((fullProgram hs i x).record e) = false := by
  let root : RuleVertex hs := .inl i
  let a := PatchTable.incidence (gates hs)
  let j := finProdFinEquiv ((originalRule a root e.1).val,e.2)
  have hj : j ∈ retainedEntries hs root := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simpa only [j,Equiv.symm_apply_apply] using (originalRule a root e.1).property
  have hsmall := SmallCompression.noSmall_when_none hq hb ht pad H x hstart hx hv records h j hj
  have he := sliceRecord_shape hs root x (retainedEntries hs root) (witnessSlice hs root x {j}) j
  unfold SmallCompression.isSmall at hsmall ⊢
  change decide (((replayShape (sliceRecord hs root x (retainedEntries hs root) j)).members _ _ _ _ _).length < _) = _
  rw [he]
  exact hsmall

set_option maxHeartbeats 1500000 in
theorem packWitness_complete (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (pad : Fin q) (H : Hash q b t ℓ) (hH : Balanced pad H)
    (x : Fin ℓ → Fin q) (hstart : minLength q b t ≤ ℓ) (hℓ : 0 < ℓ)
    (hx : Strong x (windowLength q ℓ) (omittedLetters q b t ℓ))
    {hs : History ℓ q (gram q b t ℓ) (edits t)} {i : Fin hs.length}
    (hv : ResultValid H pad x (windowLength q ℓ) b (omittedLetters q b t ℓ) (componentCutoff q b t ℓ)
      (.firstEvent hs i))
    (hk : AllKernel H (.firstEvent hs i))
    (records : RecordedBatches (recognizerBounds (basicBounds hq hb ht hstart)) pad x ⟨0,hℓ⟩ hs)
    (hcore : core (fullProgram hs i x).incidence = ∅)
    (hlarge : ∀ e ∈ PeelingFrame.trace (fullProgram hs i x),
      SmallCompression.isSmall (b := b) (t := t) pad ((fullProgram hs i x).record e) = false) :
    ∃ payload, packWitness (show 1 < q by omega) hℓ pad H x hs i = some payload ∧
      payload.length+8 ≤ ℓ ∧ ∀ rest, read pad H (payload++rest) = some x := by
  let K := windowLength q ℓ
  let L := gram q b t ℓ
  let Λ := omittedLetters q b t ℓ
  let s := edits t
  let R := componentCutoff q b t ℓ
  let D := witnessLimit q b t ℓ
  let a := PatchTable.incidence (gates hs)
  let root : RuleVertex hs := .inl i
  let p := fullProgram hs i x
  let τ := PeelingFrame.trace p
  let C := componentIncidence a root
  let d₀ := ruleCount hs i
  let c₀ := patchCount hs i
  let g := cycles d₀ s c₀
  have hbasic := basicBounds hq hb ht hstart
  have hL : 0 < L := by have h := hbasic.local_gram; omega
  have hwindow : K+2*Λ ≤ L := (Nat.le_succ _).trans (recognizer_window hbasic)
  have hspos : 0 < s := by dsimp [s,edits]; omega
  have hfirst := firstEvent_witnessBounds H pad x hL hspos hv
  have hD : d₀ ≤ D := hfirst.1
  have hbounds : c₀ = (s-1)*d₀ + 1-g ∧ (g = 0 ∧ R < d₀ ∨ 0 < g) := hfirst.2.2
  obtain ⟨_,_,hgraph,_,_⟩ := hv
  let d : Fin (D+1) := ⟨d₀,by omega⟩
  let ds := fullDescription hs i x
  let roots (j : ℕ) := (witnessAnchor hs root j).getD ⟨0,hℓ⟩
  obtain ⟨code,henc,hdec,hPatches,hprog⟩ := fullDescription_roundtrip records hgraph.chronology hx hgraph.fit
    hwindow hgraph.highWidth i hspos hD
  have hlegal : LegalTrace p.incidence Finset.univ τ ∅ := by
    have hh := peel_legal p.incidence Finset.univ
    change LegalTrace p.incidence Finset.univ τ (core p.incidence) at hh
    rwa [hcore] at hh
  obtain ⟨owner,ho⟩ := fullProgram_owner hs i x hgraph.fit
  have hpos := fullProgram_positive_subset hs i x
  have hzero := fullProgram_kernel records i H hk
  have hfam (e : Fin d₀ × Fin s) :
      ∃ w : Borrowed.BubbleWord (Fin q) K b L,
        (replayShape (p.record e)).member K b L Λ pad (originalValues (p.record e).2.negative.2 x) = some w ∧
        vector pad w = vectorOf L pad (p.record e) x := by
    obtain ⟨words,_,_,hb⟩ := slice_rule_families records root (retainedEntries hs root) (originalRule a root e.1).val
    exact ⟨words e.2,(hb e.2).1,(hb e.2).2.1⟩
  have hdigit (e : Fin d₀ × Fin s) (he : e ∈ τ) :
      hashCount q b t ℓ ≤ ((replayShape (p.record e)).members K b L Λ pad).length ∧
        pivotDigit K b L Λ pad H (p.record e) x <
          pivotRadix ((replayShape (p.record e)).members K b L Λ pad).length (hashCount q b t ℓ) := by
    obtain ⟨w,hw,hvec⟩ := hfam e
    have fields := saved_lengths records root (finProdFinEquiv ((originalRule a root e.1).val,e.2))
    exact large_record_bounds pad H hH hL (p.record e) x fields.1 fields.2.1 fields.2.2.1 fields.2.2.2.1
      hw hvec (hlarge e he)
  obtain ⟨u,hu,hinv⟩ := PeelingPayload.encode_roundtrip (show 1 < q by omega) K b L Λ pad
    p.incidence τ ∅ hlegal p.record owner ho H x hpos hzero (fun e _ => hfam e) (fun e he => (hdigit e he).2)
  have hprog' : PeelingFrame.materialize d ds (fun j => roots j.val.val) L = some p := hprog
  obtain ⟨payload,hpayload,hsize,hround⟩ := PeelingFrame.encode_roundtrip (show 1 < q by omega) hℓ K b L Λ pad
    d code roots H x hdec hprog' hu hinv
  have hlrg : (PeelingFrame.trace p).all (fun e => !SmallCompression.isSmall (b := b) (t := t) pad (p.record e)) = true :=
    List.all_eq_true.mpr (fun e he => by rw [hlarge e he]; rfl)
  refine ⟨payload,?_,?_,hround⟩
  · unfold packWitness
    dsimp only
    have hc : ¬ core (fullProgram hs i x).incidence ≠ ∅ := fun h => h hcore
    rw [ite_eq_right hc]
    have hb : ((PeelingFrame.trace (fullProgram hs i x)).all
        (fun e => !SmallCompression.isSmall (b := b) (t := t) pad ((fullProgram hs i x).record e))) = true := hlrg
    rw [hb]
    simp only [Bool.not_true,Bool.false_eq_true,ite_false]
    have hDb : ruleCount hs i ≤ witnessLimit q b t ℓ := hD
    rw [dite_eq_left hDb]
    change (encodeDescription (edits t*d.val) L b q pad ds >>= fun code =>
      PeelingFrame.encode (by omega) hℓ K b L Λ pad d code roots H x) = _
    rw [henc]
    exact hpayload
  · let data := (PeelingPayload.radices K b L Λ pad p.record τ (hashCount q b t ℓ)).prod
    have hdata : 0 < data := mixed_capacity_positive (by omega) hu
    have hcapacity := PeelingPayload.capacity K b L Λ pad hL p.incidence τ hlegal p.record owner ho
      (hashCount q b t ℓ) (fun e he => (hdigit e he).1)
    have hcount : 0 < d₀ := Finset.card_pos.mpr ⟨i,(mem_componentRules a root i).mpr SimpleGraph.Reachable.rfl⟩
    have hvertices : d₀+c₀ ≤ d₀*s+1 := connected_vertices_le C (componentIncidence_connected a root) (.inl ⟨0,hcount⟩)
    have hmul : d₀*s = (s-1)*d₀+d₀ := by
      calc
        _ = d₀*((s-1)+1) := congrArg (d₀*·) (by omega)
        _ = _ := by ring
    have hc : c₀+g = (edits t-1)*d₀+1 := by
      change c₀+(d₀*s+1-(d₀+c₀)) = (s-1)*d₀+1
      omega
    have htree : g = 0 → R < d₀ := by
      intro h
      rcases hbounds.2 with h' | h'
      · exact h'.2
      · omega
    have hbnd := peeled_saves_eight hq hb ht hstart hcount hD hc htree hdata hcapacity
    change payload.length ≤ Nat.clog q (D+1)+Nat.clog q (replayBound q b L (s*d₀)) +
      (CoreWeight.patchKeys (s*d.val) ds).card*eta q ℓ+Nat.clog q data at hsize
    have hPatches' : (CoreWeight.patchKeys (s*d.val) ds).card = c₀ := hPatches
    rw [hPatches'] at hsize
    exact (Nat.add_le_add_right hsize 8).trans hbnd

def pack (hq : 1 < q) (pad : Fin q) (strong : (Fin ℓ → Fin q) → Bool)
    (H : Hash q b t ℓ) (x : Fin ℓ → Fin q) : Option (QWord q) :=
  if hℓ : 0 < ℓ then
    if minLength q b t ≤ ℓ ∧ strong x = true then
      match runAt pad H x with
      | some (.firstEvent hs i) => packWitness hq hℓ pad H x hs i
      | _ => none
    else none
  else none

def branch (hq : 1 < q) (pad : Fin q) (strong : (Fin ℓ → Fin q) → Bool) (H : Hash q b t ℓ) :
    Branch q :=
  fixedBranch (pack hq pad strong H) (read pad H)

theorem branch_laws (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) (pad : Fin q)
    (strong : (Fin ℓ → Fin q) → Bool)
    (hs : ∀ x, strong x = true → Strong x (windowLength q ℓ) (omittedLetters q b t ℓ))
    (H : Hash q b t ℓ) (hH : Balanced pad H) : (branch (by omega) pad strong H).Laws pad := by
  have spec {x : Fin ℓ → Fin q} {v : QWord q} (h : pack (by omega) pad strong H x = some v) :
      v.length+8 ≤ ℓ ∧ ∀ rest, read pad H (v++rest) = some x := by
    unfold pack at h
    split at h
    next hℓ =>
      split at h
      next good =>
        have hB := basicBounds hq hb ht good.1
        obtain ⟨out,hr,hv,records⟩ := recognize_verified
          (recognizerBounds hB) H pad x (hs x good.2) (recognizer_window hB) hℓ
        have hk := recognize_kernel H pad x hr
        change runAt pad H x = some out at hr
        rw [hr] at h
        cases out with
        | complete hist => contradiction
        | firstEvent hist i =>
          let p := fullProgram hist i x
          have hc : core p.incidence = ∅ := by
            by_contra hn
            have bad := h
            change packWitness (by omega) hℓ pad H x hist i = some v at bad
            unfold packWitness at bad
            change (if core p.incidence ≠ ∅ then none else _) = some v at bad
            rw [ite_eq_left hn] at bad
            contradiction
          have hl : (PeelingFrame.trace p).all
              (fun e => !SmallCompression.isSmall (b := b) (t := t) pad (p.record e)) = true := by
            by_contra hn
            let allLarge := (PeelingFrame.trace p).all
              (fun e => !SmallCompression.isSmall (b := b) (t := t) pad (p.record e))
            have hfalse : allLarge = false := Bool.eq_false_iff.mpr hn
            have bad := h
            change packWitness (by omega) hℓ pad H x hist i = some v at bad
            unfold packWitness at bad
            change (if core p.incidence ≠ ∅ then none else if !allLarge then none else _) = some v at bad
            simp [hc,hfalse] at bad
          have hl' : ∀ e ∈ PeelingFrame.trace p,
              SmallCompression.isSmall (b := b) (t := t) pad (p.record e) = false := by
            intro e he
            simpa using (List.all_eq_true.mp hl) e he
          obtain ⟨w,hw,hlen,hinv⟩ := packWitness_complete hq hb ht pad H hH x good.1 hℓ (hs x good.2)
            hv hk records hc hl'
          have he : w = v := Option.some.inj (hw.symm.trans h)
          subst v
          exact ⟨hlen,hinv⟩
      next => contradiction
    next => contradiction
  unfold branch
  apply fixedBranch_laws
  · intro x w hw
    have hlen := (spec hw).1
    have hheader := headerLength_le (q := q) (by omega)
    omega
  · intro x w h n
    exact (spec h).2 _

#print axioms branch_laws
#print axioms noSmall_full
#print axioms packWitness_complete

end DeletionCode.Explicit.PeelingCompression
