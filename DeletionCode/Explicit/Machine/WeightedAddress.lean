import DeletionCode.Explicit.WeightedAddress
import DeletionCode.Explicit.Machine.WordEnumeration
import DeletionCode.Explicit.Machine.Repair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives

/-! Uniform weighted addressing from a jointly certified prefix evaluator. -/
namespace DeletionCode.Explicit.Machine.WeightedAddresses

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open WeightedAddress

variable {q : ℕ} {π : Type} {enc : π ↪ List Bool}
variable {mass : π × QWord q → ℕ}

private abbrev symbolEncoding (q : ℕ) : Fin q ↪ List Bool :=
  ⟨fun a => encUnary a.val, fun _ _ h => Fin.ext (encUnary.injective h)⟩

private abbrev evalEnc (enc : π ↪ List Bool) (q : ℕ) := encPair enc (wordEncoding q)
private abbrev beforeEnc (enc : π ↪ List Bool) (q : ℕ) :=
  encPair (evalEnc enc q) (symbolEncoding q)

private theorem before_polyTime (hm : ComputableInPolyTime mass (evalEnc enc q) encNat) :
    ComputableInPolyTime (fun x : (π × QWord q) × Fin q => before (fun p => mass (x.1.1, p))
      x.1.2 x.2) (beforeEnc enc q) encNat := by
  have he : ComputableInPolyTime (earlier (q := q)) (symbolEncoding q)
      (encList (symbolEncoding q)) := of_finite _
  have ha := he.comp (snd (evalEnc enc q) (symbolEncoding q))
  let src := beforeEnc enc q
  have hp := (fst enc (wordEncoding q)).comp
    ((fst (evalEnc enc q) (symbolEncoding q)).comp (fst src (symbolEncoding q)))
  have hw := (snd enc (wordEncoding q)).comp
    ((fst (evalEnc enc q) (symbolEncoding q)).comp (fst src (symbolEncoding q)))
  have hd := snd src (symbolEncoding q)
  have hword : ComputableInPolyTime (fun x : ((π × QWord q) × Fin q) × Fin q =>
      x.1.1.2 ++ [x.2]) (encPair src (symbolEncoding q)) (wordEncoding q) := by
    unfold wordEncoding
    exact listAppend' hw (cons' hd (const []))
  exact binary_sum.comp (mapWithInput ha (hm.comp (hp.prod hword)))

private def offsetByIndex (zero : Fin q) (mass : Mass q) (p w : QWord q) : ℕ :=
  ((List.range w.length).map fun i => before mass (p ++ w.take i) (w.getD i zero)).sum

private theorem offsetByIndex_eq (zero : Fin q) (mass : Mass q) (p w : QWord q) :
    offsetByIndex zero mass p w = offset mass p w := by
  induction w generalizing p with
  | nil => simp [offsetByIndex, offset]
  | cons a w ih =>
    rw [offsetByIndex, offset, List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.sum_cons, Function.comp_def, List.take_zero,
      List.append_nil, List.getD_cons_zero, List.take_succ_cons, List.getD_cons_succ]
    rw [← ih (p ++ [a])]
    simp [offsetByIndex, List.append_assoc]

/-- Forward addressing is polynomial using the exact binary mass callback.
The certificate also runs on inputs whose callback does not satisfy the
prefix identities. -/
theorem encode_polyTime (hq : 0 < q)
    (hm : ComputableInPolyTime mass (evalEnc enc q) encNat) :
    ComputableInPolyTime (fun x : π × QWord q => encode (fun p => mass (x.1, p)) x.2)
      (evalEnc enc q) encNat := by
  let zero : Fin q := ⟨0, hq⟩
  let src := evalEnc enc q
  let arg := encPair src encUnary
  have hw := snd enc (wordEncoding q)
  have hr := range.comp ((wordLength_polyTime q).comp hw)
  have hwi := hw.comp (fst src encUnary)
  have hi := snd src encUnary
  have ht : ComputableInPolyTime (fun x : (π × QWord q) × ℕ => x.1.2.take x.2)
      arg (wordEncoding q) :=
    (takeUnary (symbolEncoding q)).comp (hwi.prod hi)
  have hd := listGetDWithInput hwi hi zero
  have hb := (before_polyTime hm).comp
    ((((fst enc (wordEncoding q)).comp (fst src encUnary)).prod ht).prod hd)
  have h := binary_sum.comp (mapWithInput (f := fun (x : π × QWord q) i =>
    before (fun p => mass (x.1, p)) (x.2.take i) (x.2.getD i zero)) hr hb)
  exact h.of_enc_eq (fun x => congrArg encNat (offsetByIndex_eq zero _ [] x.2).symm)

private abbrev pickEnc (q : ℕ) := encOption (encPair (symbolEncoding q) encNat)
private abbrev wordNatEnc (q : ℕ) := encPair (wordEncoding q) encNat
private abbrev stateEnc (q : ℕ) := encOption (wordNatEnc q)

private theorem pick_polyTime (hm : ComputableInPolyTime mass (evalEnc enc q) encNat)
    (xs : List (Fin q)) :
    ComputableInPolyTime (fun x : (π × QWord q) × ℕ =>
        pick (fun a => mass (x.1.1, x.1.2 ++ [a])) xs x.2)
      (encPair (evalEnc enc q) encNat) (pickEnc q) := by
  induction xs with
  | nil => exact const none
  | cons a xs ih =>
    let src := evalEnc enc q
    have hp := fst src encNat
    have hr := snd src encNat
    have ha : ComputableInPolyTime (fun x : (π × QWord q) × ℕ => x.1.2 ++ [a])
        (encPair src encNat) (wordEncoding q) := by
      unfold wordEncoding
      exact listAppend' ((snd enc (wordEncoding q)).comp hp) (const [a])
    have hz := hm.comp (((fst enc (wordEncoding q)).comp hp).prod ha)
    exact ite_decide (binary_lt.comp (hr.prod hz))
      ((optionSome (encPair (symbolEncoding q) encNat)).comp ((const a).prod hr))
      (ih.comp (hp.prod (binary_sub' hr hz)))

private theorem step_polyTime (hm : ComputableInPolyTime mass (evalEnc enc q) encNat) :
    ComputableInPolyTime (fun x : π × State q => decodeStep (fun p => mass (x.1, p)) x.2)
      (encPair enc (stateEnc q)) (stateEnc q) := by
  let src := encPair enc (stateEnc q)
  let arg := encPair src (wordNatEnc q)
  have hp := fst src (wordNatEnc q)
  have hs := snd src (wordNatEnc q)
  have hcall := (pick_polyTime hm (List.finRange q)).comp
    (((hp.fst').prod hs.fst').prod hs.snd')
  have hbody : ComputableInPolyTime
      (fun x : (π × State q) × (QWord q × ℕ) =>
        (pick (fun a => mass (x.1.1, x.2.1 ++ [a])) (List.finRange q) x.2.2).map
          (fun (a, r) => (x.2.1 ++ [a], r))) arg (stateEnc q) := by
    apply optionMapWithInput hcall
    let res := encPair (symbolEncoding q) encNat
    have hword : ComputableInPolyTime
        (fun x : ((π × State q) × (QWord q × ℕ)) × (Fin q × ℕ) =>
          x.1.2.1 ++ [x.2.1]) (encPair arg res) (wordEncoding q) := by
      unfold wordEncoding
      exact listAppend' (hs.fst'.comp (fst arg res))
        (cons' (snd arg res).fst' (const []))
    exact hword.prod (snd arg res).snd'
  have h := optionElimWithInput (body := fun x (p, r) =>
    (pick (fun a => mass (x.1, p ++ [a])) (List.finRange q) r).map
      (fun (a, s) => (p ++ [a], s))) (snd enc (stateEnc q)) (const none) hbody
  apply h.of_enc_eq
  rintro ⟨p, _ | ⟨w, r⟩⟩ <;> rfl

private theorem step_some {mass : Mass q} {state : State q} {p : QWord q} {r : ℕ}
    (h : decodeStep mass state = some (p, r)) :
    ∃ p₀ r₀, state = some (p₀, r₀) ∧ p.length = p₀.length + 1 ∧ r ≤ r₀ := by
  rcases state with _ | ⟨p₀, r₀⟩
  · simp [decodeStep] at h
  · cases hp : pick (fun a => mass (p₀ ++ [a])) (List.finRange q) r₀ with
    | none => simp [decodeStep, hp] at h
    | some y =>
      obtain ⟨a, s⟩ := y
      have h' : (p₀ ++ [a], s) = (p, r) := by simpa [decodeStep, hp] using h
      cases h'
      exact ⟨p₀, r₀, rfl, by simp, pick_residual_le hp⟩

/-- Inversion is polynomial in unary word length, binary address, and
serialized evaluator data. The residual address never grows, even on
inputs whose callback does not satisfy the prefix identities. -/
theorem decode_polyTime (hm : ComputableInPolyTime mass (evalEnc enc q) encNat) :
    ComputableInPolyTime (fun x : π × (ℕ × ℕ) =>
      decode (fun p => mass (x.1, p)) x.2.1 x.2.2)
      (encPair enc (encPair encUnary encNat)) (encOption (wordEncoding q)) := by
  let rest := encPair encUnary encNat
  let src := encPair enc rest
  have hp := fst enc rest
  have hfuel := (snd enc rest).fst'
  have hr := (snd enc rest).snd'
  have hinit := (optionSome (wordNatEnc q)).comp ((const []).prod hr)
  let size (x : π × (ℕ × ℕ)) :=
    2 * ((2 * q + 1) * x.2.1) + (encNat x.2.2).length + 2
  have hsize : PolyBounded (fun x => (src x).length) size := by
    have hf : PolyBounded (fun x => (src x).length) (fun x => x.2.1) := by
      simpa only [encUnary_apply, List.length_replicate] using hfuel.polyBounded_length
    exact (((PolyBounded.const (2 * (2 * q + 1))).mul hf).add
      hr.polyBounded_length |>.add (.const 2)).mono (fun x => by simp [size, Nat.mul_assoc])
  have hloop := (iterateWith_spec (step := fun par state =>
    decodeStep (fun p => mass (par, p)) state) hp hfuel hinit (step_polyTime hm)
    (fun x i state => ∀ p r, state = some (p, r) → p.length ≤ i ∧ r ≤ x.2.2)
    (by intro x p r h; cases h; simp)
    (by
      intro x i state _ hs p r h
      obtain ⟨p₀, r₀, h₀, hlen, hr⟩ := step_some h
      obtain ⟨hl, haddr⟩ := hs p₀ r₀ h₀
      exact ⟨hlen ▸ Nat.succ_le_succ hl, hr.trans haddr⟩)
    hsize (by
      intro x i state hi hs
      rcases state with _ | ⟨p, r⟩
      · exact Nat.zero_le _
      obtain ⟨hl, hr⟩ := hs p r rfl
      have hword := (encoded_word_length_le p).trans (Nat.mul_le_mul_left _ (hl.trans hi))
      have hbits : (encNat r).length ≤ (encNat x.2.2).length := by
        simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le_size hr
      simp only [wordNatEnc, encOption_some, List.length_cons, length_encPair]
      unfold size
      omega)).1
  have hout := optionMapWithInput (f := fun _ (y : QWord q × ℕ) => y.1) hloop
    ((snd src (wordNatEnc q)).fst')
  have hroot := hm.comp (hp.prod (const []))
  exact ite_decide (binary_lt.comp (hr.prod hroot)) hout (const none)

#print axioms encode_polyTime
#print axioms decode_polyTime

end DeletionCode.Explicit.Machine.WeightedAddresses
