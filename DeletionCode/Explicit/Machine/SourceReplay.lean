import DeletionCode.Explicit.Machine.SourceGrammar
import DeletionCode.Explicit.Machine.SourceRunBounds
import DeletionCode.Explicit.CompactReplay

/-! Replay a chronological description and retain both symbolic lifts of every gate. -/
namespace DeletionCode.Explicit.Machine.SourceReplay

open ReplayEntry SourceGrammar SourceLetters SourceLists
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open SourceDictionary (Stored store historyData)

variable {q ℓ : ℕ}

abbrev Anchors := List (Option ℕ)
abbrev anchorsEncoding := encList (encOption encUnary)
abbrev Params := (ℕ × ℕ) × Anchors
abbrev paramsEncoding := encPair SourceReference.fieldsEncoding anchorsEncoding
abbrev evaluateEncoding (q : ℕ) :=
  encPair (encPair paramsEncoding (SourceDictionary.historyEncoding q)) (decodedEncoding q)
abbrev outputEncoding (q : ℕ) := encOption (SourceDictionary.historyEncoding q)
abbrev replayEncoding (q : ℕ) := encPair paramsEncoding (decodedListEncoding q)

def anchorAt (roots : Anchors) (p : ℕ) : Option ℕ := roots.getD p none

def negative (par : Params) (es : List (Stored q)) (d : Decoded q) : Option (LiftData q) :=
  SourceNegative.negativeWith par.1.2 (d.left+d.removed.length+d.right) d.refs
    (SourceReference.read (par.1,(es.length,d.rule)) (anchorAt par.2 d.patch) es)

def completed (pad : Fin q) (current : ℕ) (d : Decoded q) (w : LiftData q) : Stored q :=
  (d.rule,(w,install pad current d.left d.removed.length w d.replacement))

def evaluate (pad : Fin q) (par : Params) (es : List (Stored q)) (d : Decoded q) : Option (Stored q) :=
  (negative par es d).map (completed pad es.length d)

private theorem negative_eq (L : ℕ) (es : Array (Completed ℓ (Fin q))) (d : ReplayGrammar.DecodedEntry q)
    (roots : Anchors) (a : Option (Fin ℓ)) (ha : anchorAt roots d.entry.patch = a.map Fin.val) :
    negative ((ℓ,L),roots) (historyData es) (decodedData d) =
      (negativeLift L es.size d.entry a (fun j => es[j]?)).map liftData := by
  unfold negative decodedData
  simp only [historyData,List.length_map,Array.length_toList]
  change SourceNegative.negativeWith L d.entry.negativeLength (d.entry.references.map SourceReference.referenceData)
    (SourceReference.read ((ℓ,L),(es.size,d.entry.rule)) (anchorAt roots d.entry.patch) (historyData es)) = _
  rw [ha]
  apply SourceNegative.negativeWith_eq L es.size d.entry a (fun j => es[j]?)
  · simp
  · rw [List.mapM_map]
    simp only [Function.comp_def,SourceReference.read_eq]
    exact SourceNegative.mapM_map_result _ _ _

theorem evaluate_eq (pad : Fin q) (L : ℕ) (es : Array (Completed ℓ (Fin q)))
    (d : ReplayGrammar.DecodedEntry q) (roots : Anchors) (anchors : ℕ → Option (Fin ℓ))
    (ha : anchorAt roots d.entry.patch = (anchors d.entry.patch).map Fin.val) :
    evaluate pad ((ℓ,L),roots) (historyData es) (decodedData d) =
      (ReplayEntry.evaluate L es.size anchors (fun j => es[j]?) d.entry).map store := by
  unfold evaluate ReplayEntry.evaluate
  rw [negative_eq L es d roots _ ha]
  cases h : negativeLift L es.size d.entry (anchors d.entry.patch) (fun j => es[j]?) with
  | none => rfl
  | some neg =>
    have hlen : (historyData es).length = es.size := by simp [historyData]
    simp only [Option.map_some,Option.bind_some,completed,hlen,decodedData,completedOf,store]
    have hr : List.ofFn (fun i : Fin d.entry.replacement.length => d.entry.replacement[i]) =
        d.entry.replacement := List.ofFn_getElem
    have hi := install_eq (pad := pad) (current := es.size) neg
      (fun i : Fin d.entry.replacement.length => d.entry.replacement[i])
    rw [hr] at hi
    exact congrArg (fun w => some (d.entry.rule,liftData neg,w)) hi

def step (pad : Fin q) (par : Params) (done : Option (List (Stored q))) (d : Decoded q) :
    Option (List (Stored q)) :=
  done.bind (fun es => (evaluate pad par es d).map (fun out => es++[out]))

def replay (pad : Fin q) (par : Params) (ds : List (Decoded q)) : Option (List (Stored q)) :=
  ds.foldl (step pad par) (some [])

theorem replay_eq (pad : Fin q) (L : ℕ) (ds : List (ReplayGrammar.DecodedEntry q))
    (roots : Anchors) (anchors : ℕ → Option (Fin ℓ))
    (ha : ∀ d ∈ ds, anchorAt roots d.entry.patch = (anchors d.entry.patch).map Fin.val) :
    replay pad ((ℓ,L),roots) (ds.map decodedData) =
      (ReplayEntry.replay L anchors (ds.map ReplayGrammar.DecodedEntry.entry)).map historyData := by
  unfold replay ReplayEntry.replay
  have stop (ds : List (Decoded q)) : ds.foldl (step pad ((ℓ,L),roots)) none = none := by
    induction ds with
    | nil => rfl
    | cons a ds ih => exact ih
  have go (es : Array (Completed ℓ (Fin q))) (ds : List (ReplayGrammar.DecodedEntry q))
      (ha : ∀ d ∈ ds, anchorAt roots d.entry.patch = (anchors d.entry.patch).map Fin.val) :
      (ds.map decodedData).foldl (step pad ((ℓ,L),roots)) (some (historyData es)) =
        ((ds.map ReplayGrammar.DecodedEntry.entry).foldlM
          (fun (done : Array (Completed ℓ (Fin q))) (e : Entry (Fin q)) => do
            let next ← ReplayEntry.evaluate L done.size anchors (fun j => done[j]?) e
            pure (done.push next)) es).map historyData := by
    induction ds generalizing es with
    | nil => rfl
    | cons d ds ih =>
      have hread := evaluate_eq pad L es d roots anchors (ha d List.mem_cons_self)
      simp only [List.map_cons,List.foldl_cons,List.foldlM_cons,step,Option.bind_some,hread]
      cases h : ReplayEntry.evaluate L es.size anchors (fun j => es[j]?) d.entry with
      | none => simpa [Option.bind,bind] using stop (ds.map decodedData)
      | some v =>
        have hpush : historyData (es.push v) = historyData es++[store v] := by
          simp [historyData,Array.toList_push]
        simpa only [Option.map_some,bind,Option.bind,pure,hpush] using
          ih (es.push v) (fun d hd => ha d (List.mem_cons_of_mem _ hd))
  exact go #[] ds ha

private theorem negative_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (Params × List (Stored q)) × Decoded q => negative x.1.1 x.1.2 x.2)
      (evaluateEncoding q) (SourceNegative.resultEncoding q) := by
  let e := evaluateEncoding q
  let d := decodedEncoding q
  let h := SourceDictionary.historyEncoding q
  let r := SourceReference.refEncoding
  let a := encPair e r
  have hp := (fst paramsEncoding h).comp (fst (encPair paramsEncoding h) d)
  have hs := (snd paramsEncoding h).comp (fst (encPair paramsEncoding h) d)
  have hx := snd (encPair paramsEncoding h) d
  have hL := hp.fst'.snd'
  have hleft := decodedEncoding_left_polyTime q hx
  have hright := decodedEncoding_right_polyTime q hx
  have hmm := (length_list (ExceptionalRecords.letterEncoding q)).comp (decodedEncoding_removed_polyTime q hx)
  have hn := unary_add' (unary_add' hleft hmm) hright
  have hcur := (length_list (SourceDictionary.storedEncoding q)).comp hs
  have hrule := decodedEncoding_rule_polyTime q hx
  have hcfg := hp.fst'.prod (hcur.prod hrule)
  have hroots := listGetDWithInput hp.snd' (decodedEncoding_patch_polyTime q hx) (none : Option ℕ)
  have hrefs := decodedEncoding_refs_polyTime q hx
  have hread := (SourceReference.read_polyTime q).comp (encIn := a)
    ((((hcfg.prod hroots).prod hs).comp (fst e r)).prod (snd e r))
  exact SourceNegative.negativeWith_polyTime hL hn hrefs (hread.of_enc_eq (fun _ => rfl))

theorem evaluate_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : (Params × List (Stored q)) × Decoded q => evaluate pad x.1.1 x.1.2 x.2)
      (evaluateEncoding q) (encOption (SourceDictionary.storedEncoding q)) := by
  let e := evaluateEncoding q
  let h := SourceDictionary.historyEncoding q
  let d := decodedEncoding q
  let w := liftEncoding q
  let a := encPair e w
  have hx := (snd (encPair paramsEncoding h) d).comp (fst e w)
  have hs := (fst (encPair paramsEncoding h) d).snd'.comp (fst e w)
  have hcur := (length_list (SourceDictionary.storedEncoding q)).comp hs
  have hleft := decodedEncoding_left_polyTime q hx
  have hu := (length_list (ExceptionalRecords.letterEncoding q)).comp (decodedEncoding_removed_polyTime q hx)
  have hv := decodedEncoding_replacement_polyTime q hx
  have hneg := snd e w
  have hpos := (install_polyTime pad).comp (encIn := a) ((hcur.prod (hleft.prod hu)).prod (hneg.prod hv))
  have hout := (decodedEncoding_rule_polyTime q hx).prod (hneg.prod hpos)
  exact optionMapWithInput (encA := e) (encB := w) (encC := SourceDictionary.storedEncoding q)
    (f := fun x u => completed pad x.1.2.length x.2 u) (negative_polyTime q)
    (hout.of_enc_eq (fun _ => rfl))

theorem step_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : (Params × Option (List (Stored q))) × Decoded q =>
        step pad x.1.1 x.1.2 x.2)
      (encPair (encPair paramsEncoding (outputEncoding q)) (decodedEncoding q)) (outputEncoding q) := by
  let m := outputEncoding q
  let d := decodedEncoding q
  let h := SourceDictionary.historyEncoding q
  let e := encPair (encPair paramsEncoding m) d
  let a := encPair e h
  let s := SourceDictionary.storedEncoding q
  let b := encPair a s
  have hc := fst (encPair paramsEncoding m) d
  have hx := fst e h
  have he := (evaluate_polyTime pad).comp (encIn := a)
    (((hc.fst'.comp hx).prod (snd e h)).prod ((snd (encPair paramsEncoding m) d).comp hx))
  have hs := listAppend' ((snd e h).comp (fst a s)) (cons' (snd a s) (const []))
  have hh := optionMapWithInput (encA := a) (encB := s) (encC := h)
    (f := fun x out => x.2++[out]) (he.of_enc_eq (fun _ => rfl)) (hs.of_enc_eq (fun _ => rfl))
  exact optionBindWithInput (ea := e) (eb := h) (ec := h)
    (f := fun x es => (evaluate pad x.1.1 es x.2).map (fun out => es++[out]))
    hc.snd' hh

private def entriesSize (x : Params × List (Decoded q)) : ℕ := (replayEncoding q x).length

private theorem sourceLength_le (x : Params × List (Decoded q)) : x.1.1.1 ≤ entriesSize x := by
  simp only [replayEncoding,paramsEncoding,SourceReference.fieldsEncoding,length_encPair,
    encUnary_apply,List.length_replicate,entriesSize]
  omega

private theorem entryCount_le (x : Params × List (Decoded q)) : x.2.length ≤ entriesSize x := by
  have h := SizedListEncoding.length_le (encA := decodedEncoding q) (encL := decodedListEncoding q) x.2
  exact h.trans (length_le_encPair_right paramsEncoding (decodedListEncoding q) x)

private theorem entrySize_le (x : Params × List (Decoded q)) {d : Decoded q} (hd : d ∈ x.2) :
    (decodedEncoding q d).length ≤ entriesSize x :=
  (SizedListEncoding.length_elem_le x.2 d hd).trans (length_le_encPair_right paramsEncoding (decodedListEncoding q) x)

private theorem read_bound {par : Params} {current rule patch M N : ℕ} {es : List (Stored q)}
    {ref : SourceReference.Ref} {w : LiftData q} (he : SourceRunBounds.validStores M N es)
    (hl : par.1.1 ≤ M)
    (h : SourceReference.read (par.1,(current,rule)) (anchorAt par.2 patch) es ref = some w) :
    SourceRunBounds.letters M w := by
  rcases ref with ⟨delta,a⟩
  cases a with
  | some v =>
    exact SourceRunBounds.read_bound (cfg := (par.1,(current,rule))) (loc := (v.1,some v.2)) he hl h
  | none =>
    simp only [SourceReference.read,Option.elim_none] at h
    cases ha : anchorAt par.2 patch with
    | none => rw [ha] at h; contradiction
    | some x =>
      simp only [ha,Option.bind_some,SourceReference.readSource] at h
      split at h
      · rename_i hw
        injection h with hr
        subst w
        exact SourceRunBounds.original_bound (hw.2.trans hl)
      · contradiction

private theorem negative_bound {par : Params} {es : List (Stored q)} {d : Decoded q}
    {w : LiftData q} {N : ℕ} (he : SourceRunBounds.validStores N N es) (hl : par.1.1 ≤ N)
    (h : negative par es d = some w) :
    w.length = d.left+d.removed.length+d.right ∧ SourceRunBounds.letters N w := by
  dsimp only [negative,SourceNegative.negativeWith] at h
  split at h
  · cases hm : d.refs.mapM (SourceReference.read (par.1,(es.length,d.rule)) (anchorAt par.2 d.patch) es) with
    | none => rw [hm] at h; contradiction
    | some ws =>
      simp only [hm,Option.bind_some] at h
      apply SourceRunBounds.assemble_bound _ h
      intro v hv
      obtain ⟨r,_,hr⟩ := (SourceRunBounds.mapM_some hm).2 v hv
      exact read_bound he hl hr
  · contradiction

private def storesBound (N : ℕ) (es : List (Stored q)) : Prop :=
  ∀ e ∈ es, e.1 ≤ N ∧ e.2.1.length ≤ 4*N ∧ SourceRunBounds.letters N e.2.1 ∧
    e.2.2.length ≤ 4*N ∧ SourceRunBounds.letters N e.2.2

private def invariant (x : Params × List (Decoded q)) (consumed : List (Decoded q))
    (st : Option (List (Stored q))) : Prop :=
  ∀ es ∈ st, es.length = consumed.length ∧ storesBound (entriesSize x) es

private theorem invariant_step (pad : Fin q) (x : Params × List (Decoded q))
    (prefixes : List (Decoded q)) (st : Option (List (Stored q))) (value : Decoded q)
    (hpre : prefixes++[value] <+: x.2) (h : invariant x prefixes st) :
    invariant x (prefixes++[value]) (step pad x.1 st value) := by
  cases st with
  | none => simp [step,invariant]
  | some es =>
    have ⟨hlen,hstores⟩ := h es (by simp)
    have he (e : Stored q) (hm : e ∈ es) :
        e.2.1.length ≤ 5*entriesSize x ∧ SourceRunBounds.letters (entriesSize x) e.2.1 ∧
          e.2.2.length ≤ 5*entriesSize x ∧ SourceRunBounds.letters (entriesSize x) e.2.2 := by
      obtain ⟨_,h₁,h₂,h₃,h₄⟩ := hstores e hm
      exact ⟨by omega,h₂,by omega,h₄⟩
    have hm := entrySize_le x (hpre.subset (by simp : value ∈ prefixes++[value]))
    have hsize (w : QWord q) (hw : (wordEncoding q w).length ≤ entriesSize x) :
        w.length ≤ entriesSize x := by
      change (encList (ExceptionalRecords.letterEncoding q) w).length ≤ entriesSize x at hw
      exact (SizedListEncoding.length_le (encA := ExceptionalRecords.letterEncoding q)
        (encL := encList (ExceptionalRecords.letterEncoding q)) w).trans hw
    have hl : value.left ≤ entriesSize x := by
      simpa [encUnary_apply] using (decodedEncoding_left_length_le q value).trans hm
    have hr : value.right ≤ entriesSize x := by
      simpa [encUnary_apply] using (decodedEncoding_right_length_le q value).trans hm
    have hd : value.rule ≤ entriesSize x := by
      simpa [encUnary_apply] using (decodedEncoding_rule_length_le q value).trans hm
    have hu := hsize value.removed ((decodedEncoding_removed_length_le q value).trans hm)
    have hv := hsize value.replacement ((decodedEncoding_replacement_length_le q value).trans hm)
    have hcur : es.length ≤ entriesSize x := by
      have hp := hpre.length_le.trans (entryCount_le x)
      simp only [List.length_append,List.length_singleton] at hp
      omega
    cases hw : negative x.1 es value with
    | none => simp [step,evaluate,hw,invariant]
    | some w =>
      obtain ⟨hwl,hwc⟩ := negative_bound he (sourceLength_le x) hw
      simp only [step,Option.bind_some,evaluate,hw,Option.map_some]
      intro ls hls
      have hl' : es++[completed pad es.length value w] = ls := Option.some.inj (Option.mem_def.mp hls)
      subst ls
      refine ⟨by simp [hlen],?_⟩
      intro e hmem
      rcases List.mem_append.mp hmem with old | new
      · exact hstores e old
      · have ee : e = completed pad es.length value w := by simpa using new
        subst e
        refine ⟨hd,?_,hwc,?_,SourceRunBounds.install_bound pad hwc hcur hv⟩
        · change w.length ≤ 4*entriesSize x
          omega
        · dsimp [completed,install]
          simp only [List.length_map,List.length_range]
          omega

private def stateBits (q N : ℕ) : ℕ :=
  let lift := SourceRunBounds.liftBits q N (4*N)
  let stored := 2*N+2+3*lift
  1+N*(2*stored+1)

private theorem invariant_size (x : Params × List (Decoded q)) (ps : List (Decoded q))
    (st : Option (List (Stored q))) (hp : ps <+: x.2) (h : invariant x ps st) :
    (outputEncoding q st).length ≤ stateBits q (entriesSize x) := by
  let N := entriesSize x
  let lift := SourceRunBounds.liftBits q N (4*N)
  let sb := 2*N+2+3*lift
  cases st with
  | none => simp [outputEncoding]
  | some es =>
    obtain ⟨hn,hb⟩ := h es (by simp)
    have hN : es.length ≤ N := hn.le.trans (hp.length_le.trans (entryCount_le x))
    have he (e : Stored q) (he : e ∈ es) : (SourceDictionary.storedEncoding q e).length ≤ sb := by
      obtain ⟨h₀,h₁,h₂,h₃,h₄⟩ := hb e he
      have hn := SourceRunBounds.lift_size_le h₁ h₂
      have hp := SourceRunBounds.lift_size_le h₃ h₄
      simp only [SourceDictionary.storedEncoding,length_encPair,encUnary_apply,List.length_replicate]
      change _ ≤ 2*N+2+3*lift
      change _ ≤ lift at hn hp
      omega
    have henc := (length_encList_le (SourceDictionary.storedEncoding q) es he).trans
      (Nat.mul_le_mul_right _ hN)
    simp only [outputEncoding,encOption_some,List.length_cons]
    change (encList (SourceDictionary.storedEncoding q) es).length+1 ≤ 1+N*(2*sb+1)
    omega

private theorem stateBits_polyBounded (q : ℕ) :
    PolyBounded (fun x : Params × List (Decoded q) => (replayEncoding q x).length)
      (fun x => stateBits q (entriesSize x)) := by
  have n : PolyBounded (fun x : Params × List (Decoded q) => (replayEncoding q x).length)
      (entriesSize (q := q)) := PolyBounded.self
  have c (v : ℕ) : PolyBounded (fun x : Params × List (Decoded q) => (replayEncoding q x).length)
      (fun _ => v) := PolyBounded.const v
  have hn := (c 4).mul n
  have hl := hn.mul (((c 2).mul (hn.add (c q) |>.add (c 4))).add (c 1))
  have hs := ((c 2).mul n).add (c 2) |>.add ((c 3).mul hl)
  exact (c 1).add (n.mul (((c 2).mul hs).add (c 1)))

theorem replay_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : Params × List (Decoded q) => replay pad x.1 x.2)
      (replayEncoding q) (outputEncoding q) :=
  (foldlWith_spec (step := step pad) (fst paramsEncoding (decodedListEncoding q))
    (snd paramsEncoding (decodedListEncoding q)) (const (some [])) (step_polyTime pad)
    invariant (fun _ => by simp [invariant,storesBound]) (invariant_step pad)
    (stateBits_polyBounded q) invariant_size).1

theorem replay_length (pad : Fin q) (par : Params) (ds : List (Decoded q))
    (es : List (Stored q)) (h : replay pad par ds = some es) : es.length = ds.length := by
  have hpost := (foldlWith_spec (step := step pad) (fst paramsEncoding (decodedListEncoding q))
    (snd paramsEncoding (decodedListEncoding q)) (const (some [])) (step_polyTime pad)
    invariant (fun _ => by simp [invariant,storesBound]) (invariant_step pad)
    (stateBits_polyBounded q) invariant_size).2 (par,ds)
  exact (hpost es (Option.mem_def.mpr h)).1

#print axioms evaluate_eq
#print axioms replay_eq
#print axioms evaluate_polyTime
#print axioms step_polyTime
#print axioms replay_polyTime
#print axioms replay_length

end DeletionCode.Explicit.Machine.SourceReplay
