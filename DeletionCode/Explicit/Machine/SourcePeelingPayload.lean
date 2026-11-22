import DeletionCode.Explicit.Machine.SourcePeelingBuckets
import DeletionCode.Explicit.Machine.SourceWitness
import DeletionCode.Explicit.Machine.SourceMixedRadix
import DeletionCode.Explicit.PeelingFrame
import Batteries.Tactic.OpenPrivate

/-! Serialize the literal and pivot digits of one reverse-peeling program. -/
namespace DeletionCode.Explicit.Machine.SourcePeelingPayload

open FieldHash Ternary CataloguePrefix SourceGrammar SourceLists
open SourceReplayPayload (Record recordEncoding recordData keys)
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open _root_.DeletionCode.Explicit.UniformParameters
open private ofDigits_ofFn from DeletionCode.Explicit.Machine.GramOrder
open scoped BigOperators
set_option maxHeartbeats 1500000

variable {q l d s θ : ℕ}

structure Input (q : ℕ) where
  length : ℕ
  arity : ℕ
  hash : Rows
  records : List (Record q)
  trace : List ℕ

enc_structure inputEncoding (q : ℕ) : Input q where
  length : encUnary, arity : encUnary, hash : rowsEncoding,
  records : (encList (recordEncoding q)), trace : PatchGraph.rowEncoding

private def fallback (q : ℕ) : Record q := (⟨0,0,0,0,[],[],[],false,false⟩,0,[],[])

def recordAt (r : List (Record q)) (j : ℕ) : Record q := r.getD j (fallback q)

def recordsData (r : Fin d × Fin s → PeelingBuckets.Recorded l q) : List (Record q) :=
  List.ofFn fun j => recordData (r (finProdFinEquiv.symm j))

def traceData (trace : List (Fin d × Fin s)) : List ℕ := trace.map (fun e => (finProdFinEquiv e).val)

theorem recordAt_eq (r : Fin d × Fin s → PeelingBuckets.Recorded l q) (e : Fin d × Fin s) :
    recordAt (recordsData r) (finProdFinEquiv e).val = recordData (r e) := by
  unfold recordAt recordsData
  rw [BooleanFibres.ofFn_getD _ (finProdFinEquiv e) _, Equiv.symm_apply_apply]

def active (x : Input q) : List ℕ :=
  (List.range x.length).filter fun i => x.trace.any (fun j => (keys (recordAt x.records j)).contains i)

private theorem active_eq (H : Rows) (r : Fin d × Fin s → PeelingBuckets.Recorded l q)
    (tr : List (Fin d × Fin s)) : active ⟨l,s,H,recordsData r,traceData tr⟩ =
      SourceSmallCodec.names (PeelingPayload.activeSet r tr) := by
  unfold active SourceSmallCodec.names PeelingPayload.activeSet
  dsimp only
  rw [← SourceWitness.filter_finRange_eq_sort, show List.range l = (List.finRange l).map Fin.val by simp, List.filter_map]
  congr 1
  apply List.filter_congr
  intro i _
  apply Bool.eq_iff_iff.mpr
  simp only [traceData, List.any_map, Function.comp_def, List.any_eq_true, List.contains_iff_mem,
    decide_eq_true_eq, Finset.mem_biUnion, List.mem_toFinset, recordAt_eq]
  exact exists_congr (fun e => and_congr_right fun _ => by
    obtain ⟨entry, v⟩ := r e
    change i.val ∈ keys (decodedData ⟨entry,false,false⟩, SourceDictionary.store v) ↔
      i ∈ BubbleFamilies.active v.negative.2
    rw [SourceReplayPayload.keys_eq]
    exact SourceSmallCodec.names_mem_iff _ _)

def familySize (pad : Fin q) (b t l : ℕ) (r : Record q) : ℕ :=
  (SourceFamilyMembers.members pad b t l (SourceReplayFamily.shape r.1 r.2)).length

private theorem familySize_eq (pad : Fin q) (b t : ℕ) (r : PeelingBuckets.Recorded l q) :
    familySize pad b t l (recordData r) = ((BubbleFamilies.replayShape r).members
      (windowLength q l) b (gram q b t l) (omittedLetters q b t l) pad).length := by
  obtain ⟨d, v⟩ := r
  unfold familySize
  change (SourceFamilyMembers.members pad b t l
    (SourceReplayFamily.shape (decodedData ⟨d,false,false⟩) (SourceDictionary.store v))).length = _
  rw [SourceReplayFamily.shape_eq, SourceFamilyMembers.members_eq, List.length_map]

def radices (pad : Fin q) (b t : ℕ) (x : Input q) : List ℕ :=
  q^(SourceSmallCodec.outside x.length (active x)).length ::
    x.trace.map (fun j => BubbleFamilies.pivotRadix (familySize pad b t x.length (recordAt x.records j)) (3^x.hash.length))

private theorem radices_eq (pad : Fin q) (b t : ℕ) (H : TernaryMatrix θ (q^gram q b t l))
    (r : Fin d × Fin s → PeelingBuckets.Recorded l q) (tr : List (Fin d × Fin s)) :
    radices pad b t ⟨l,s,matrixRows H,recordsData r,traceData tr⟩ =
      PeelingPayload.radices (windowLength q l) b (gram q b t l) (omittedLetters q b t l) pad r tr (3^θ) := by
  unfold radices PeelingPayload.radices
  dsimp only
  rw [active_eq, SourceSmallCodec.outside_eq, SourceSmallCodec.names_length]
  simp only [traceData, List.map_map, Function.comp_def, recordAt_eq, familySize_eq, matrixRows, List.length_ofFn]

private def literalRank (pad : Fin q) (x : Input q) (word : QWord q) : ℕ :=
  SourceRadix.littleValue q ((SourceSmallCodec.select pad (SourceSmallCodec.outside x.length (active x)) word).map Fin.val)

private theorem literalRank_eq (pad : Fin q) (rows : Rows) (r : Fin d × Fin s → PeelingBuckets.Recorded l q)
    (tr : List (Fin d × Fin s)) (word : Fin l → Fin q) :
    literalRank pad ⟨l,s,rows,recordsData r,traceData tr⟩ (List.ofFn word) =
      (finFunctionFinEquiv (SmallFamilyCodec.select (PeelingPayload.activeSet r tr)ᶜ word)).val := by
  unfold literalRank
  dsimp only
  rw [active_eq, SourceSmallCodec.outside_eq, SourceSmallCodec.select_eq, SourceRadix.littleValue_eq,
    List.map_ofFn, ofDigits_ofFn, finFunctionFinEquiv_apply]
  rfl

def values (pad : Fin q) (b t : ℕ) (x : Input q) (word : QWord q) : List ℕ :=
  literalRank pad x word :: x.trace.map (fun j =>
    SourcePeelingBuckets.pivotDigit pad b t x.length x.hash (recordAt x.records j) word)

private theorem values_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (H : TernaryMatrix θ (q^gram q b t l))
    (r : Fin d × Fin s → PeelingBuckets.Recorded l q) (tr : List (Fin d × Fin s)) (word : Fin l → Fin q) :
    values pad b t ⟨l,s,matrixRows H,recordsData r,traceData tr⟩ (List.ofFn word) =
      PeelingPayload.values (windowLength q l) b (gram q b t l) (omittedLetters q b t l) pad r tr H word := by
  unfold values PeelingPayload.values
  dsimp only
  rw [literalRank_eq]
  congr 1
  simp only [traceData, List.map_map, Function.comp_def, recordAt_eq]
  apply List.map_congr_left
  intro e _
  obtain ⟨a,v⟩ := r e
  exact SourcePeelingBuckets.pivotDigit_eq pad b t hq H ⟨a,false,false⟩ v word

def encode (pad : Fin q) (b t : ℕ) (x : Input q) (word : QWord q) : Option (QWord q) :=
  SourceMixedRadix.encode pad (radices pad b t x) (values pad b t x word)

theorem encode_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (H : TernaryMatrix θ (q^gram q b t l))
    (r : Fin d × Fin s → PeelingBuckets.Recorded l q) (tr : List (Fin d × Fin s)) (word : Fin l → Fin q) :
    encode pad b t ⟨l,s,matrixRows H,recordsData r,traceData tr⟩ (List.ofFn word) =
      (PeelingPayload.encode (by omega) (windowLength q l) b (gram q b t l) (omittedLetters q b t l)
        pad r tr H word).map List.ofFn := by
  unfold encode PeelingPayload.encode
  rw [radices_eq, values_eq pad b t hq, SourceMixedRadix.encode_eq pad hq]

theorem recordAt_polyTime (q : ℕ) :
    ComputableInPolyTime (fun p : List (Record q) × ℕ => recordAt p.1 p.2)
      (encPair (encList (recordEncoding q)) encUnary) (recordEncoding q) :=
  listGetDWithInput (fst (encList (recordEncoding q)) encUnary)
    (snd (encList (recordEncoding q)) encUnary) (fallback q)

theorem active_polyTime (q : ℕ) : ComputableInPolyTime (active (q := q)) (inputEncoding q) PatchGraph.rowEncoding := by
  let e := inputEncoding q
  let a := encPair e encUnary
  let h := fst e encUnary
  let ha := fst a encUnary
  let hj := snd a encUnary
  have hr := (recordAt_polyTime q).comp ((inputEncoding_records_polyTime q (h.comp ha)).prod hj)
  have hk := (SourceReplayPayload.keys_polyTime q).comp hr
  have hi := (idxOf?_polyTime 0 encUnary).comp (hk.prod ((snd e encUnary).comp ha))
  have ht := hi.decide_ne (const none)
  have hc : ComputableInPolyTime (fun p : (Input q × ℕ) × ℕ =>
      (keys (recordAt p.1.1.records p.2)).contains p.1.2) (encPair a encUnary) encBool := by
    refine ht.of_enc_eq ?_
    intro p
    simp [Function.comp_def, List.idxOf?_eq_none_iff]
  have hAny := anyWithInput (test := fun p j => (keys (recordAt p.1.records j)).contains p.2)
    (inputEncoding_trace_polyTime q h) hc
  exact filterWithInput (test := fun x i => x.trace.any (fun j => (keys (recordAt x.records j)).contains i))
    (unary_range' (inputEncoding_length_polyTime q (id' (encIn := e)))) hAny

private def outside (x : Input q) : List ℕ := SourceSmallCodec.outside x.length (active x)

private theorem outside_polyTime (q : ℕ) :
    ComputableInPolyTime (outside (q := q)) (inputEncoding q) PatchGraph.rowEncoding :=
  SourceSmallCodec.outside_polyTime.comp
    ((inputEncoding_length_polyTime q (id' (encIn := inputEncoding q))).prod (active_polyTime q))

private theorem familySize_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : ℕ × Record q => familySize pad b t p.1 p.2)
      (encPair encUnary (recordEncoding q)) encUnary := by
  let r := recordEncoding q
  have hl := fst encUnary r
  have hv := snd encUnary r
  have hs := (SourceReplayFamily.shape_polyTime q).comp hv
  exact (length_list (SourceFamilyMembers.memberDataEncoding q)).comp ((SourceFamilyMembers.members_polyTime pad b t hq).comp (hl.prod hs))

private abbrev digitsEncoding := SourceRadix.numbersEncoding

theorem radices_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (radices pad b t) (inputEncoding q) digitsEncoding := by
  let e := inputEncoding q
  have he := id' (encIn := e)
  have hx := fst e encUnary
  have hj := snd e encUnary
  have hlen := (length_list encUnary).comp (outside_polyTime q)
  have hfirst := binary_pow.comp ((const q).prod hlen)
  have hr := (recordAt_polyTime q).comp ((inputEncoding_records_polyTime q hx).prod hj)
  have hm := (familySize_polyTime pad b t hq).comp ((inputEncoding_length_polyTime q hx).prod hr)
  have hh := (length_list rowEncoding).comp (inputEncoding_hash_polyTime q hx)
  have hp := binary_pow.comp ((const 3).prod hh)
  have hb := SourceMixedRadix.pivotRadix_polyTime.comp ((unary_to_binary.comp hm).prod hp)
  have ht := mapWithInput (encIn := e) (encA := encUnary) (encB := encNat)
    (f := fun x j => BubbleFamilies.pivotRadix (familySize pad b t x.length (recordAt x.records j)) (3^x.hash.length))
    (inputEncoding_trace_polyTime q he) hb
  have h := cons' hfirst ht
  exact h.of_enc_eq (fun _ => rfl)

private theorem literalRank_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun p : Input q × QWord q => literalRank pad p.1 p.2)
      (encPair (inputEncoding q) (wordEncoding q)) encNat := by
  let e := inputEncoding q
  let w := wordEncoding q
  have ho := (outside_polyTime q).comp (fst e w)
  have hs := (SourceSmallCodec.select_polyTime pad).comp (ho.prod (snd e w))
  have hv : ComputableInPolyTime (fun a : Fin q => a.val) (ExceptionalRecords.letterEncoding q) encUnary :=
    (id' (encIn := ExceptionalRecords.letterEncoding q)).of_enc_eq (fun _ => rfl)
  have hval := ComputableInPolyTime.map (unary_to_binary.comp hv)
  exact SourceRadix.littleValue_polyTime.comp ((const q).prod (hval.comp hs))

theorem values_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : Input q × QWord q => values pad b t p.1 p.2)
      (encPair (inputEncoding q) (wordEncoding q)) digitsEncoding := by
  let e := inputEncoding q
  let w := wordEncoding q
  let a := encPair e w
  have hx := (fst e w).comp (fst a encUnary)
  have hw := (snd e w).comp (fst a encUnary)
  have hj := snd a encUnary
  have hr := (recordAt_polyTime q).comp ((inputEncoding_records_polyTime q hx).prod hj)
  have hd := (SourcePeelingBuckets.pivotDigit_polyTime pad b t hq).comp
    (((inputEncoding_length_polyTime q hx).prod (inputEncoding_hash_polyTime q hx)).prod (hr.prod hw))
  have ht := mapWithInput (encIn := a) (encA := encUnary) (encB := encNat)
    (f := fun p j => SourcePeelingBuckets.pivotDigit pad b t p.1.length p.1.hash (recordAt p.1.records j) p.2)
    (inputEncoding_trace_polyTime q (fst e w)) hd
  have h := cons' (literalRank_polyTime pad) ht
  exact h.of_enc_eq (fun _ => rfl)

theorem encode_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : Input q × QWord q => encode pad b t p.1 p.2)
      (encPair (inputEncoding q) (wordEncoding q)) (encOption (wordEncoding q)) := by
  have h := (SourceMixedRadix.encode_polyTime pad hq).comp
    (((radices_polyTime pad b t hq).comp (fst (inputEncoding q) (wordEncoding q))).prod (values_polyTime pad b t hq))
  exact h.of_enc_eq (fun _ => rfl)

private def siblings (x : Input q) (j : ℕ) : List (Record q) :=
  ((List.range x.arity).filter (· ≠ j%x.arity)).map fun i => recordAt x.records (i+x.arity*(j/x.arity))

private def step (pad : Fin q) (b t : ℕ) (x : Input q) (digits : List ℕ) (j : ℕ) (old : QWord q) :
    Option (QWord q) :=
  SourcePeelingBuckets.restoreWithHash pad b t x.length x.hash (recordAt x.records j)
    (SourcePeelingBuckets.neededHash pad b t x.length x.hash (siblings x j) old)
    (digits.getD (x.trace.idxOf j) 0) old

private def replay (pad : Fin q) (b t : ℕ) (x : Input q) (digits : List ℕ) (start : QWord q) :
    Option (QWord q) :=
  x.trace.reverse.foldl (fun word j => word.bind (step pad b t x digits j)) (some start)

private def unpack (pad : Fin q) (b t : ℕ) (x : Input q) : List ℕ → Option (QWord q)
  | [] => none
  | first::rest =>
    let S := active x
    let n := (outside x).length
    if first < q^n then
      let literal := (_root_.DeletionCode.Explicit.RareAddress.fixedDigits pad n first).reverse
      let start := SourceSmallCodec.assemble pad x.length S (List.replicate S.length pad) literal
      replay pad b t x rest start
    else none

def decode (pad : Fin q) (b t : ℕ) (x : Input q) (word : QWord q) : Option (QWord q) :=
  (SourceMixedRadix.decode (radices pad b t x) word).bind (unpack pad b t x)

private theorem siblings_eq (H : Rows) (r : Fin d × Fin s → PeelingBuckets.Recorded l q)
    (tr : List (Fin d × Fin s)) (e : Fin d × Fin s) :
    siblings ⟨l,s,H,recordsData r,traceData tr⟩ (finProdFinEquiv e).val =
      ((List.finRange s).filter (· ≠ e.2)).map (fun j => recordData (r (e.1,j))) := by
  obtain ⟨i,j⟩ := e
  have hs : 0 < s := j.isLt.pos
  have hn : (finProdFinEquiv (i,j)).val = j.val + s*i.val := rfl
  have hm : (j.val + s*i.val)%s = j.val := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
  have hd : (j.val + s*i.val)/s = i.val := by
    rw [Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  unfold siblings
  dsimp only
  rw [hn,hm,hd,show List.range s = (List.finRange s).map Fin.val by simp, List.filter_map, List.map_map]
  simp only [Function.comp_def, ne_eq, Fin.val_inj]
  apply List.map_congr_left
  intro a _
  exact recordAt_eq r (i,a)

private theorem traceIndex_eq (tr : List (Fin d × Fin s)) (e : Fin d × Fin s) :
    (traceData tr).idxOf (finProdFinEquiv e).val = tr.idxOf e := by
  induction tr with
  | nil => rfl
  | cons j tr ih =>
    have h (z : Fin d × Fin s) : (finProdFinEquiv z).val = (finProdFinEquiv e).val ↔ z = e :=
      Fin.val_inj.trans finProdFinEquiv.injective.eq_iff
    change (traceData (j::tr)).idxOf (finProdFinEquiv e).val = (j::tr).idxOf e
    rw [show traceData (j::tr) = (finProdFinEquiv j).val :: traceData tr from rfl]
    simp only [List.idxOf_cons, beq_iff_eq, h, ih]

private theorem step_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (H : TernaryMatrix θ (q^gram q b t l))
    (r : Fin d × Fin s → PeelingBuckets.Recorded l q) (tr : List (Fin d × Fin s)) (e : Fin d × Fin s)
    (rest : List ℕ) (old : Fin l → Fin q) :
    let digit := rest.getD (tr.idxOf e) 0
    step pad b t ⟨l,s,matrixRows H,recordsData r,traceData tr⟩ rest (finProdFinEquiv e).val (List.ofFn old) =
      (PeelingBuckets.readPivot (windowLength q l) b (gram q b t l) (omittedLetters q b t l)
        pad H r e digit old).map (fun v => List.ofFn (RulePatch.restorePositions (BubbleFamilies.active (r e).2.negative.2) v old)) := by
  dsimp only
  unfold step
  rw [siblings_eq]
  let rows := fun j => ((⟨(r j).1,false,false⟩ : ReplayGrammar.DecodedEntry q), (r j).2)
  have hh := SourcePeelingBuckets.neededHash_eq pad b t hq H rows e old
  change SourcePeelingBuckets.neededHash pad b t l (matrixRows H)
    (((List.finRange s).filter (· ≠ e.2)).map fun j => recordData (r (e.1,j))) (List.ofFn old) = _ at hh
  rw [hh]
  change SourcePeelingBuckets.restoreWithHash pad b t l (matrixRows H)
    (recordAt (recordsData r) (finProdFinEquiv e).val) _ (rest.getD ((traceData tr).idxOf (finProdFinEquiv e).val) 0) _ = _
  rw [recordAt_eq, traceIndex_eq]
  have he := SourcePeelingBuckets.restoreWithHash_eq pad b t hq H (rows e).1 (rows e).2
    (PeelingBuckets.neededHash (gram q b t l) pad H r e old) (rest.getD (tr.idxOf e) 0) old
  rw [show r e = ((rows e).1.entry, (rows e).2) from rfl]
  change _ = _ at he
  erw [he]
  unfold PeelingBuckets.readPivot
  dsimp only [rows]
  cases (PeelingBuckets.bucketValues (windowLength q l) b (gram q b t l) (omittedLetters q b t l)
      pad H (r e) (PeelingBuckets.neededHash (gram q b t l) pad H r e old))[rest.getD (tr.idxOf e) 0]? with
  | none => rfl
  | some vs =>
    simp only [bind,Option.bind]
    split
    · simp only [Option.map_some]
      congr 2
      funext i
      by_cases h : i ∈ BubbleFamilies.active (r e).2.negative.2
      · simp [RulePatch.restorePositions, h]
      · simp [RulePatch.restorePositions, SmallFamilyCodec.assemble, SmallFamilyCodec.select, h]
    · rfl

private theorem replay_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (H : TernaryMatrix θ (q^gram q b t l))
    (r : Fin d × Fin s → PeelingBuckets.Recorded l q) (tr : List (Fin d × Fin s))
    (rest : List ℕ) (start : Fin l → Fin q) :
    replay pad b t ⟨l,s,matrixRows H,recordsData r,traceData tr⟩ rest (List.ofFn start) =
      (RulePatch.restore (fun e => BubbleFamilies.active (r e).2.negative.2) (fun e => rest.getD (tr.idxOf e) 0)
        (PeelingBuckets.readPivot (windowLength q l) b (gram q b t l) (omittedLetters q b t l) pad H r) tr start).map List.ofFn := by
  let x : Input q := ⟨l,s,matrixRows H,recordsData r,traceData tr⟩
  let f := fun (word : Option (QWord q)) j => word.bind (step pad b t x rest j)
  let read := PeelingBuckets.readPivot (windowLength q l) b (gram q b t l) (omittedLetters q b t l) pad H r
  let act := fun e => BubbleFamilies.active (r e).2.negative.2
  let digit := fun e => rest.getD (tr.idxOf e) 0
  change (traceData tr).reverse.foldl f (some (List.ofFn start)) = _
  have aux (es : List (Fin d × Fin s)) :
      (traceData es).reverse.foldl f (some (List.ofFn start)) =
        (RulePatch.restore act digit read es start).map List.ofFn := by
    induction es with
    | nil => rfl
    | cons e es ih =>
      simp only [traceData, List.map_cons, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change f ((traceData es).reverse.foldl f (some (List.ofFn start))) _ = _
      rw [ih]
      rcases he : RulePatch.restore act digit read es start with _ | old
      · simp [RulePatch.restore, f, he]
      · simp only [Option.map_some, f, x, Option.bind_some, RulePatch.restore, he]
        rw [step_eq pad b t hq H r tr e rest old]
        change (read e (digit e) old).map _ =
          (do
            let v ← read e (digit e) old
            some (RulePatch.restorePositions (act e) v old)).map List.ofFn
        cases read e (digit e) old <;> rfl
  exact aux tr

theorem decode_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (H : TernaryMatrix θ (q^gram q b t l))
    (r : Fin d × Fin s → PeelingBuckets.Recorded l q) (tr : List (Fin d × Fin s))
    (word : Fin (MixedRadix.width q (PeelingPayload.radices (windowLength q l) b (gram q b t l)
      (omittedLetters q b t l) pad r tr (3^θ))) → Fin q) :
    decode pad b t ⟨l,s,matrixRows H,recordsData r,traceData tr⟩ (List.ofFn word) =
      (PeelingPayload.decode (windowLength q l) b (gram q b t l) (omittedLetters q b t l)
        pad r tr H word).map List.ofFn := by
  unfold decode PeelingPayload.decode
  rw [radices_eq, SourceMixedRadix.decode_eq]
  cases MixedRadix.decode _ word with
  | none => rfl
  | some ds =>
    cases ds with
    | nil => rfl
    | cons i ds =>
      let S := PeelingPayload.activeSet r tr
      have ha := active_eq (matrixRows H) r tr
      have ho : (outside (⟨l,s,matrixRows H,recordsData r,traceData tr⟩ : Input q)).length = Sᶜ.card := by
        unfold outside
        rw [ha]
        simp only [SourceSmallCodec.outside_eq, SourceSmallCodec.names_length]
        rfl
      simp only [Option.bind_some, Option.bind_eq_bind, unpack, ho]
      change (if i < q^Sᶜ.card then _ else none) =
        (if h : i < q^Sᶜ.card then RulePatch.restore _ _ _ tr
          (SmallFamilyCodec.assemble S (fun _ => pad) (finFunctionFinEquiv.symm ⟨i,h⟩)) else none).map List.ofFn
      by_cases h : i < q^Sᶜ.card
      · rw [ite_eq_left h,dite_eq_left h,ha,SourceSmallCodec.names_length, GramOrder.mainWord_eq pad hq _ ⟨i,h⟩]
        rw [show List.replicate S.card pad = List.ofFn (fun _ : Fin S.card => pad) by simp]
        rw [SourceSmallCodec.assemble_eq, replay_eq pad b t hq]
      · rw [ite_eq_right h,dite_eq_right h]
        rfl

def decodePrefix (pad : Fin q) (b t : ℕ) (x : Input q) (tail : QWord q) : Option (QWord q) := do
  let (data,_) ← SourcePayloadIndex.split (MixedRadix.width q (radices pad b t x)) tail
  decode pad b t x data

theorem decodePrefix_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (H : TernaryMatrix θ (q^gram q b t l))
    (r : Fin d × Fin s → PeelingBuckets.Recorded l q) (tr : List (Fin d × Fin s)) (tail : QWord q) :
    decodePrefix pad b t ⟨l,s,matrixRows H,recordsData r,traceData tr⟩ tail =
      (do
        let (data,_) ← ReplayPayload.readPrefix
          (MixedRadix.width q (PeelingPayload.radices (windowLength q l) b (gram q b t l)
            (omittedLetters q b t l) pad r tr (3^θ))) tail
        PeelingPayload.decode (windowLength q l) b (gram q b t l) (omittedLetters q b t l) pad r tr H data).map List.ofFn := by
  unfold decodePrefix
  rw [radices_eq, SourcePayloadIndex.split_eq]
  cases ReplayPayload.readPrefix _ tail with
  | none => rfl
  | some p => exact decode_eq pad b t hq H r tr p.1

private theorem siblings_polyTime (q : ℕ) :
    ComputableInPolyTime (fun p : Input q × ℕ => siblings p.1 p.2)
      (encPair (inputEncoding q) encUnary) (encList (recordEncoding q)) := by
  let e := inputEncoding q
  let a := encPair e encUnary
  let x := fst e encUnary
  let j := snd e encUnary
  have hs := inputEncoding_arity_polyTime q x
  have hx := fst a encUnary
  have hi := snd a encUnary
  have hm := unary_mod' j hs
  have ht := hi.decide_ne (hm.comp hx)
  have hf := filterWithInput (test := fun p i => decide (i ≠ p.2%p.1.arity)) (unary_range' hs) ht
  have hbase := unary_mul' hs (unary_div' j hs)
  have hk := unary_add' hi (hbase.comp hx)
  have hr := (recordAt_polyTime q).comp ((inputEncoding_records_polyTime q (x.comp hx)).prod hk)
  have h : ComputableInPolyTime (fun u : (Input q × ℕ) × ℕ =>
      recordAt u.1.1.records (u.2+u.1.1.arity*(u.1.2/u.1.1.arity)))
      (encPair a encUnary) (recordEncoding q) := hr.of_enc_eq (fun _ => rfl)
  exact mapWithInput (f := fun (p : Input q × ℕ) i => recordAt p.1.records (i+p.1.arity*(p.2/p.1.arity))) hf h

private abbrev replayParamEncoding (q : ℕ) := encPair (inputEncoding q) digitsEncoding
private abbrev stepEncoding (q : ℕ) := encPair (encPair (replayParamEncoding q) encUnary) (wordEncoding q)

private theorem step_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : ((Input q × List ℕ) × ℕ) × QWord q =>
      step pad b t p.1.1.1 p.1.1.2 p.1.2 p.2) (stepEncoding q) (encOption (wordEncoding q)) := by
  let e := inputEncoding q
  let w := wordEncoding q
  let a := replayParamEncoding q
  have hp := fst (encPair a encUnary) w
  have hx := hp.fst'.fst'
  have hd := hp.fst'.snd'
  have hj := hp.snd'
  have hw := snd (encPair a encUnary) w
  have hsrc := (inputEncoding_length_polyTime q hx).prod (inputEncoding_hash_polyTime q hx)
  have hr := (recordAt_polyTime q).comp ((inputEncoding_records_polyTime q hx).prod hj)
  have hs := (siblings_polyTime q).comp (hx.prod hj)
  have hz := (SourcePeelingBuckets.neededHash_polyTime pad b t hq).comp (hsrc.prod (hs.prod hw))
  have ht := inputEncoding_trace_polyTime q hx
  have hi := (idxOf?_polyTime 0 encUnary).comp (ht.prod hj)
  have hn := (length_list encUnary).comp ht
  have hk := listGetDWithInput hd (optionGetDWithInput hi hn) 0
  have h := (SourcePeelingBuckets.restoreWithHash_polyTime pad b t hq).comp
    ((hsrc.prod (hr.prod hz)).prod (hk.prod hw))
  exact h.of_enc_eq (fun _ => by simp [step, idxOf_eq_getD])

private theorem step_length (pad : Fin q) (b t : ℕ) (x : Input q) (digits : List ℕ)
    (j : ℕ) (old out : QWord q) (h : step pad b t x digits j old = some out) :
    out.length = x.length := by
  unfold step SourcePeelingBuckets.restoreWithHash at h
  dsimp only at h
  cases hh : (SourcePeelingBuckets.bucketValues pad b t x.length x.hash (recordAt x.records j)
      (SourcePeelingBuckets.neededHash pad b t x.length x.hash (siblings x j) old))[digits.getD (x.trace.idxOf j) 0]? with
  | none =>
    rw [hh] at h
    contradiction
  | some v =>
    rw [hh] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · obtain rfl := Option.some.inj h
      simp [SourceSmallCodec.assemble]
    · contradiction

private abbrev replayEncoding (q : ℕ) := encPair (replayParamEncoding q) (wordEncoding q)

private theorem replay_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : (Input q × List ℕ) × QWord q => replay pad b t p.1.1 p.1.2 p.2)
      (replayEncoding q) (encOption (wordEncoding q)) := by
  let e := replayEncoding q
  let a := replayParamEncoding q
  let w := wordEncoding q
  let ow := encOption w
  let f := encPair (encPair a ow) encUnary
  have hp := fst a w
  have hw := snd a w
  have hx := hp.fst'
  have htr := (listReverse encUnary).comp (inputEncoding_trace_polyTime q hx)
  have hi := (optionSome w).comp hw
  have hf := fst (encPair a ow) encUnary
  have hj := snd (encPair a ow) encUnary
  have hstep := (step_polyTime pad b t hq).comp (encIn := encPair f w)
    (((hf.fst'.prod hj).comp (fst f w)).prod (snd f w))
  have hb := optionBindWithInput (ea := f) (eb := w) (ec := w)
    (f := fun p word => step pad b t p.1.1.1 p.1.1.2 p.2 word) hf.snd' hstep
  have hs := (inputEncoding_length_polyTime q hx).polyBounded_length
  have hl := (length_list (ExceptionalRecords.letterEncoding q)).comp hw
  simp only [encUnary_apply, List.length_replicate] at hs
  have hsize := (PolyBounded.const 1).add ((PolyBounded.const (2*q+1)).mul (hs.add (by
    simpa only [encUnary_apply, List.length_replicate] using hl.polyBounded_length)))
  have hfold := (foldlWith_spec (encIn := e) (step := fun p word j => word.bind (step pad b t p.1 p.2 j))
    hp htr hi hb (fun (p : (Input q × List ℕ) × QWord q) _ (word : Option (QWord q)) =>
      ∀ out, word = some out → out.length ≤ p.1.1.length+p.2.length)
    (by intro p out h; cases h; simp)
    (by
      intro p consumed word j _ _ out h
      cases word with
      | none => contradiction
      | some old =>
        have hl := step_length pad b t p.1.1 p.1.2 j old out h
        omega)
    hsize
    (by
      intro p consumed word _ h
      cases word with
      | none => simp
      | some out =>
        have hl := h out rfl
        rw [encOption_some, List.length_cons]
        have hlen := (encoded_word_length_le out).trans (Nat.mul_le_mul_left _ hl)
        change (wordEncoding q out).length + 1 ≤ 1 + (2*q+1)*(p.1.1.length+p.2.length)
        omega)).1
  exact hfold.of_enc_eq (fun _ => rfl)

private theorem unpack_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : Input q × List ℕ => unpack pad b t p.1 p.2)
      (replayParamEncoding q) (encOption (wordEncoding q)) := by
  let e := inputEncoding q
  let a := replayParamEncoding q
  let w := wordEncoding q
  let v := ExceptionalRecords.letterEncoding q
  have hx := fst e digitsEncoding
  have hd := snd e digitsEncoding
  have hS := (active_polyTime q).comp hx
  have hn := (length_list encUnary).comp ((outside_polyTime q).comp hx)
  have hf := binary_pow.comp ((const q).prod hn)
  have hi := listHeadDWithInput hd (const 0)
  have htail := (listTail encNat).comp hd
  have hlit := (listReverse v).comp ((Machine.RareAddress.fixedDigits_polyTime pad).comp (hn.prod hi))
  have hpad := replicate ((length_list encUnary).comp hS) (const (encOut := v) pad)
  have hs := (SourceSmallCodec.assemble_polyTime pad).comp
    (((inputEncoding_length_polyTime q hx).prod hS).prod (hpad.prod hlit))
  have ho := (replay_polyTime pad b t hq).comp ((hx.prod htail).prod hs)
  have hc := (binary_lt' hi hf).ite' ho (const none)
  have hm := ((listIsEmpty' encNat).comp hd).ite' (const none) hc
  exact hm.of_enc_eq (fun p => by rcases p with ⟨x,_ | ⟨i,ds⟩⟩ <;>
    simp [unpack, Function.comp_def])

theorem decode_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : Input q × QWord q => decode pad b t p.1 p.2)
      (encPair (inputEncoding q) (wordEncoding q)) (encOption (wordEncoding q)) := by
  let e := inputEncoding q
  let w := wordEncoding q
  let a := encPair e w
  have hr := (radices_polyTime pad b t hq).comp (fst e w)
  have hd := (SourceMixedRadix.decode_polyTime q hq).comp (hr.prod (snd e w))
  have hu := (unpack_polyTime pad b t hq).comp (((fst e w).comp (fst a digitsEncoding)).prod (snd a digitsEncoding))
  have h := optionBindWithInput (ea := a) (eb := digitsEncoding) (ec := w)
    (f := fun p ds => unpack pad b t p.1 ds) hd hu
  exact h.of_enc_eq (fun _ => rfl)

theorem decodePrefix_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun p : Input q × QWord q => decodePrefix pad b t p.1 p.2)
      (encPair (inputEncoding q) (wordEncoding q)) (encOption (wordEncoding q)) := by
  let e := inputEncoding q
  let w := wordEncoding q
  let a := encPair e w
  let u := SourcePayloadIndex.splitOutput q
  have hr := (radices_polyTime pad b t hq).comp (fst e w)
  have hn := (SourceMixedRadix.width_polyTime q hq).comp hr
  have hs := (SourcePayloadIndex.split_polyTime q).comp (hn.prod (snd e w))
  have hd := (decode_polyTime pad b t hq).comp (((fst e w).comp (fst a u)).prod (snd a u).fst')
  have hf : ComputableInPolyTime (fun p : (Input q × QWord q) × (QWord q × QWord q) =>
      decode pad b t p.1.1 p.2.1) (encPair a u) (encOption w) := hd.of_enc_eq (fun _ => rfl)
  have h := optionBindWithInput (ea := a) (eb := u) (ec := w)
    (f := fun p data => decode pad b t p.1 data.1) hs hf
  exact h.of_enc_eq (fun _ => rfl)

#print axioms encode_eq
#print axioms encode_polyTime
#print axioms decode_eq
#print axioms decodePrefix_polyTime

end DeletionCode.Explicit.Machine.SourcePeelingPayload
