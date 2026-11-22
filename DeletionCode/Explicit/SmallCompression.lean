import DeletionCode.Explicit.WitnessSingle
import DeletionCode.Explicit.RecognizerWitness
import DeletionCode.Explicit.ParameterSavings
import DeletionCode.Explicit.FamilyEnumeration
import DeletionCode.Explicit.ConcreteSource
import DeletionCode.Explicit.LengthBranch

/-! The small-family branch for an actual first-event witness. -/

namespace DeletionCode.Explicit.SmallCompression

open UniformParameters Recognizer ReplayGrammar ReplayEntry BubbleFamilies
open LetterSequence LetterGraphCuts RuleAddition CompressorFrame ConcreteSource

variable {q b t ℓ : ℕ}


def familyCount (q b t ℓ : ℕ) (pad : Fin q) : ℕ :=
  (BubbleFamilies.families q (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ) pad).length

def isSmall (pad : Fin q) (r : PeelingBuckets.Recorded ℓ q) : Bool :=
  decide (((replayShape r).members (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ) pad).length <
    12*familyCount q b t ℓ pad * (hashCount q b t ℓ)^2)

def tryGate (hq : 1 < q) (pad : Fin q) (x : Fin ℓ → Fin q)
    (hs : History ℓ q (gram q b t ℓ) (edits t)) (root : RuleVertex hs) (j : Fin (hs.length*edits t)) :
    Option (QWord q) := do
  let (code,anchor) ← singleDescription (edits t*witnessLimit q b t ℓ) b hs root pad x j
  let r ← ReplayPayload.materialize code anchor
  if isSmall (b := b) (t := t) pad r then
    ReplayPayload.encode hq (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ) pad code anchor x
  else none

def packWitness (hq : 1 < q) (pad : Fin q) (x : Fin ℓ → Fin q)
    (hs : History ℓ q (gram q b t ℓ) (edits t)) (i : Fin hs.length) : Option (QWord q) :=
  ((retainedEntries hs (.inl i)).sort).findSome? (tryGate hq pad x hs (.inl i))

def read (q b t ℓ : ℕ) (pad : Fin q) (payload : QWord q) : Option (Fin ℓ → Fin q) :=
  ReplayPayload.decode ℓ (edits t*witnessLimit q b t ℓ) (windowLength q ℓ) b (gram q b t ℓ)
    (omittedLetters q b t ℓ) pad payload

private theorem header_bound (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : minLength q b t ≤ ℓ) :
    Nat.clog q (descriptionBound (edits t*witnessLimit q b t ℓ) (gram q b t ℓ) b q*ℓ)
      ≤ 2*eta q ℓ := by
  have he := (enumerationBounds hq hb ht hstart).1
  have hcap : gamma q b t ℓ ≤ ℓ := by
    by_cases hzero : gamma q b t ℓ = 0
    · simp [hzero]
    · have hpos : 1 ≤ gamma q b t ℓ := Nat.pos_of_ne_zero hzero
      have h := Nat.pow_le_pow_right hpos (show 1 ≤ 8 by decide)
      simpa using h.trans he
  apply (Nat.clog_le_iff_le_pow (by omega)).mpr
  calc
    _ = gamma q b t ℓ*ℓ := rfl
    _ ≤ ℓ*ℓ := Nat.mul_le_mul_right _ hcap
    _ ≤ (q^eta q ℓ)*(q^eta q ℓ) := Nat.mul_le_mul
      (Nat.le_pow_clog (by omega) ℓ) (Nat.le_pow_clog (by omega) ℓ)
    _ = _ := by rw [← Nat.pow_add]; congr 1; omega

private theorem familyCount_bound (hq : 2 ≤ q) (pad : Fin q) :
    familyCount q b t ℓ pad ≤ UniformParameters.families q b t ℓ := by
  have h := BubbleFamilies.families_count q (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ) pad hq
  dsimp only [familyCount,UniformParameters.families]
  apply h.trans
  unfold BubbleFamilies.familyBound UniformParameters.familyBound
  ring_nf
  exact le_rfl

set_option maxHeartbeats 1200000 in
theorem tryGate_spec (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (pad : Fin q) (H : Hash q b t ℓ) (x : Fin ℓ → Fin q) (hstart : minLength q b t ≤ ℓ)
    (hx : Strong x (windowLength q ℓ) (omittedLetters q b t ℓ))
    {hs : History ℓ q (gram q b t ℓ) (edits t)} {i : Fin hs.length}
    (hv : ResultValid H pad x (windowLength q ℓ) b (omittedLetters q b t ℓ) (componentCutoff q b t ℓ)
      (.firstEvent hs i))
    {origin : Fin ℓ} (records : RecordedBatches (recognizerBounds (basicBounds hq hb ht hstart)) pad x origin hs)
    (j : Fin (hs.length*edits t)) (hj : j ∈ retainedEntries hs (.inl i)) :
    let T := witnessSlice hs (.inl i) x {j}
    let p := sliceRecord hs (.inl i) x T j
    let attempt := tryGate (show 1 < q by omega) pad x hs (.inl i) j
    (attempt.isSome = isSmall (b := b) (t := t) pad p) ∧
      ∀ v, attempt = some v → v.length+8 ≤ ℓ ∧
        ∀ rest, read q b t ℓ pad (v++rest) = some x := by
  dsimp only
  let basic := basicBounds hq hb ht hstart
  have hlocal := recognizer_window basic
  have hL : 0 < gram q b t ℓ := by have hh := basic.local_gram; omega
  have hspos : 0 < edits t := by unfold edits; omega
  have hE : (retainedEntries hs (.inl i)).card ≤ edits t*witnessLimit q b t ℓ :=
    firstEvent_witnessEntries H pad x hL hspos hv
  obtain ⟨_,_,v,_,_⟩ := hv
  let T := witnessSlice hs (.inl i) x {j}
  let p := sliceRecord hs (.inl i) x T j
  obtain ⟨code,anchor,hcode,hp⟩ := singleDescription_correct records v.chronology hx v.fit
    (by omega) v.highWidth i hspos hE j hj
  let e := finProdFinEquiv.symm j
  obtain ⟨words,_,_,hwords⟩ := slice_rule_families records (.inl i) T e.1
  have hi : finProdFinEquiv (e.1,e.2) = j := Equiv.apply_symm_apply _ _
  have hm := (hwords e.2).1
  rw [hi] at hm
  obtain ⟨payload,hen,hsize,hround⟩ := ReplayPayload.encode_roundtrip (show 1 < q by omega)
    (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ) pad code anchor x hp hm
  have htry : tryGate (show 1 < q by omega) pad x hs (.inl i) j =
      if isSmall (b := b) (t := t) pad p then some payload else none := by
    have hcode' : singleDescription (edits t*witnessLimit q b t ℓ) b hs (.inl i) pad x j =
        some (code,anchor) := hcode
    unfold tryGate
    rw [hcode']
    change (ReplayPayload.materialize code anchor >>= fun r =>
      if isSmall (b := b) (t := t) pad r then
        ReplayPayload.encode (by omega) (windowLength q ℓ) b (gram q b t ℓ)
          (omittedLetters q b t ℓ) pad code anchor x else none) = _
    rw [hp]
    change (if isSmall (b := b) (t := t) pad p then
      ReplayPayload.encode (by omega) (windowLength q ℓ) b (gram q b t ℓ)
        (omittedLetters q b t ℓ) pad code anchor x else none) = _
    rw [hen]
  rw [htry]
  by_cases hs : isSmall (b := b) (t := t) pad p = true
  · rw [hs]
    refine ⟨rfl,?_⟩
    intro result hr
    have he : payload = result := Option.some.inj hr
    subst result
    have hM := of_decide_eq_true hs
    have hlen : (replayAssignments (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ) pad p).length ≤
        ((replayShape p).members (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ) pad).length := by
      simp only [replayAssignments,List.length_map,SmallFamilyCodec.shapeAssignments]
      exact List.length_filterMap_le _ _
    have hM' := hlen.trans_lt hM
    have hact := sliceRecord_active_lower records v.fit (.inl i) T j
    have hact' : (active p.2.negative.2).card ≤ ℓ := by simpa using Finset.card_le_univ (active p.2.negative.2)
    have hhead := header_bound hq hb ht hstart
    have hbnd := smallFamily_saves_eight hq hb ht hstart (familyCount_bound (b := b) (t := t) (ℓ := ℓ) hq pad)
      hM' hact hact' (show Nat.clog q (descriptionBound (edits t*witnessLimit q b t ℓ) (gram q b t ℓ) b q*ℓ) ≤
        2*eta q ℓ+3*Nat.clog q (gram q b t ℓ)+5 by omega)
    change payload.length ≤ Nat.clog q (descriptionBound (edits t*witnessLimit q b t ℓ) (gram q b t ℓ) b q*ℓ) +
      (ℓ-(active p.2.negative.2).card) + Nat.clog q
        (replayAssignments (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ) pad p).length at hsize
    refine ⟨?_,hround⟩
    let activeSize := (active p.2.negative.2).card
    let headerSize := Nat.clog q (descriptionBound (edits t*witnessLimit q b t ℓ) (gram q b t ℓ) b q*ℓ)
    let digitSize := Nat.clog q
      (replayAssignments (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ) pad p).length
    change payload.length ≤ headerSize+(ℓ-activeSize)+digitSize at hsize
    change (ℓ-activeSize)+digitSize+headerSize+8 ≤ ℓ at hbnd
    omega
  · have hf : isSmall (b := b) (t := t) pad p = false := by cases h : isSmall (b := b) (t := t) pad p <;> simp_all
    rw [hf]
    refine ⟨rfl,?_⟩
    intro _ hh
    contradiction

theorem packWitness_some (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (pad : Fin q) (H : Hash q b t ℓ) (x : Fin ℓ → Fin q) (hstart : minLength q b t ≤ ℓ)
    (hx : Strong x (windowLength q ℓ) (omittedLetters q b t ℓ))
    {hs : History ℓ q (gram q b t ℓ) (edits t)} {i : Fin hs.length}
    (hv : ResultValid H pad x (windowLength q ℓ) b (omittedLetters q b t ℓ) (componentCutoff q b t ℓ)
      (.firstEvent hs i))
    {origin : Fin ℓ} (records : RecordedBatches (recognizerBounds (basicBounds hq hb ht hstart)) pad x origin hs)
    {v : QWord q} (h : packWitness (show 1 < q by omega) pad x hs i = some v) :
    v.length+8 ≤ ℓ ∧ ∀ rest, read q b t ℓ pad (v++rest) = some x := by
  obtain ⟨j,hj,he⟩ := List.exists_of_findSome?_eq_some h
  exact (tryGate_spec hq hb ht pad H x hstart hx hv records j ((Finset.mem_sort _).mp hj)).2 v he

theorem noSmall_when_none (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (pad : Fin q) (H : Hash q b t ℓ) (x : Fin ℓ → Fin q) (hstart : minLength q b t ≤ ℓ)
    (hx : Strong x (windowLength q ℓ) (omittedLetters q b t ℓ))
    {hs : History ℓ q (gram q b t ℓ) (edits t)} {i : Fin hs.length}
    (hv : ResultValid H pad x (windowLength q ℓ) b (omittedLetters q b t ℓ) (componentCutoff q b t ℓ)
      (.firstEvent hs i))
    {origin : Fin ℓ} (records : RecordedBatches (recognizerBounds (basicBounds hq hb ht hstart)) pad x origin hs)
    (h : packWitness (show 1 < q by omega) pad x hs i = none)
    (j : Fin (hs.length*edits t)) (hj : j ∈ retainedEntries hs (.inl i)) :
    isSmall (b := b) (t := t) pad (sliceRecord hs (.inl i) x (witnessSlice hs (.inl i) x {j}) j) = false := by
  change (((retainedEntries hs (.inl i)).sort).findSome? (tryGate (by omega) pad x hs (.inl i))) = none at h
  have hj' := (List.findSome?_eq_none_iff.mp h) j ((Finset.mem_sort _).mpr hj)
  have hj'' := (tryGate_spec hq hb ht pad H x hstart hx hv records j hj).1
  rw [hj'] at hj''
  exact hj''.symm

def pack (hq : 1 < q) (pad : Fin q) (strong : (Fin ℓ → Fin q) → Bool)
    (H : Hash q b t ℓ) (x : Fin ℓ → Fin q) : Option (QWord q) :=
  if minLength q b t ≤ ℓ ∧ strong x = true then
    match runAt pad H x with
    | some (.firstEvent hs i) => packWitness hq pad x hs i
    | _ => none
  else none

def branch (hq : 1 < q) (pad : Fin q) (strong : (Fin ℓ → Fin q) → Bool) (H : Hash q b t ℓ) :
    Branch q :=
  fixedBranch (pack hq pad strong H) (read q b t ℓ pad)

theorem branch_laws (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) (pad : Fin q)
    (strong : (Fin ℓ → Fin q) → Bool)
    (hs : ∀ x, strong x = true → Strong x (windowLength q ℓ) (omittedLetters q b t ℓ))
    (H : Hash q b t ℓ) : (branch (by omega) pad strong H).Laws pad := by
  have spec {x : Fin ℓ → Fin q} {v : QWord q} (h : pack (by omega) pad strong H x = some v) :
      v.length+8 ≤ ℓ ∧ ∀ rest, read q b t ℓ pad (v++rest) = some x := by
    unfold pack at h
    split at h
    next good =>
      have hB := basicBounds hq hb ht good.1
      have hℓ : 0 < ℓ := by have h' := hB.record_length; omega
      obtain ⟨out,hr,hv,records⟩ := recognize_verified
        (recognizerBounds hB) H pad x (hs x good.2) (recognizer_window hB) hℓ
      change runAt pad H x = some out at hr
      rw [hr] at h
      cases out with
      | complete hist => contradiction
      | firstEvent hist i => exact packWitness_some hq hb ht pad H x good.1 (hs x good.2) hv records h
    next => contradiction
  unfold branch
  apply fixedBranch_laws
  · intro x w hw
    have hlen := (spec hw).1
    have hheader := headerLength_le (q := q) (by omega)
    omega
  · intro x w h n
    exact (spec h).2 _

#print axioms tryGate_spec
#print axioms branch_laws

end DeletionCode.Explicit.SmallCompression
