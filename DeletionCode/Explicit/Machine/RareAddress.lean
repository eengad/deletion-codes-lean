import DeletionCode.Explicit.RareAddress
import DeletionCode.Explicit.Machine.WordRank
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup

/-! Polynomial-time machines for the combined weight and its padded payload. -/
namespace DeletionCode.Explicit.Machine.RareAddress

open _root_.DeletionCode.Explicit.RareAddress
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open MatchingPrefixes (symbolEncoding)

variable {q b t : ℕ} {π : Type} {enc : π ↪ List Bool}

abbrev massEncoding (enc : π ↪ List Bool) (q : ℕ) := encPair (encPair enc encUnary) (wordEncoding q)

abbrev CombinedInput (π : Type) (q : ℕ) := ((π × Ternary.Rows) × ℕ) × QWord q
abbrev combinedEncoding (enc : π ↪ List Bool) (q : ℕ) := massEncoding (encPair enc Ternary.rowsEncoding) q

def combined (pad : Fin q) (b t : ℕ) (core : (π × ℕ) × QWord q → ℕ) (x : CombinedInput π q) : ℕ :=
  prefixMass pad b t x.1.2 x.1.1.2 (fun p => core ((x.1.1.1,x.1.2),p)) x.2

theorem combined_polyTime (pad : Fin q) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (core : (π × ℕ) × QWord q → ℕ) (hc : ComputableInPolyTime core (massEncoding enc q) encNat) :
    ComputableInPolyTime (combined pad b t core) (combinedEncoding enc q) encNat := by
  let data := encPair enc Ternary.rowsEncoding
  let src := encPair data encUnary
  have hp := fst src (wordEncoding q)
  have hw := snd src (wordEncoding q)
  have hmatch := (MatchingPrefixes.mass_polyTime pad hq hb ht).comp (hp.snd'.prod hw)
  have hexc := (CataloguePrefix.exceptionalPrefixMass_polyTime pad b t hq).comp
    (hp.snd'.prod (hp.fst'.snd'.prod hw))
  have hcore := hc.comp ((hp.fst'.fst'.prod hp.snd').prod hw)
  exact binary_add' (binary_add' hmatch hexc) hcore

private def digitStep (pad : Fin q) (s : ℕ × QWord q) : ℕ × QWord q :=
  (s.1/q,digit pad s.1 :: s.2)

private theorem digitIterate (pad : Fin q) (m r : ℕ) (w : QWord q) :
    ((digitStep pad)^[m] (r,w)).2 = fixedDigits pad m r ++ w := by
  induction m generalizing r w with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    change ((digitStep pad)^[m] (r/q,digit pad r::w)).2 = _
    rw [ih]
    simp [fixedDigits,List.append_assoc]

private theorem digitStep_polyTime (pad : Fin q) :
    ComputableInPolyTime (digitStep pad) (encPair encNat (wordEncoding q)) (encPair encNat (wordEncoding q)) := by
  have hr := fst encNat (wordEncoding q)
  have hw := snd encNat (wordEncoding q)
  have hd := listGetD_binary (encA := symbolEncoding q) (encL := encList (symbolEncoding q)) pad (const (List.finRange q))
    (binary_mod' hr (const q))
  exact (binary_div' hr (const q)).prod (cons' hd hw)

theorem fixedDigits_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : ℕ × ℕ => fixedDigits pad x.1 x.2)
      (encPair encUnary encNat) (wordEncoding q) := by
  let src := encPair encUnary encNat
  let out := encPair encNat (wordEncoding q)
  have hn := fst encUnary encNat
  have hr := snd encUnary encNat
  have hn' : PolyBounded (fun x : ℕ × ℕ => (src x).length) (fun x => x.1) := by
    simpa only [encUnary_apply,List.length_replicate] using hn.polyBounded_length
  have hsize := (((PolyBounded.const 2).mul hr.polyBounded_length).add (PolyBounded.const 1)).add
    ((PolyBounded.const (2*q+1)).mul hn')
  let inv (x : ℕ × ℕ) (i : ℕ) (s : ℕ × QWord q) := s.1 ≤ x.2 ∧ s.2.length = i
  have h := (iterate_spec (step := digitStep pad) hn (hr.prod (const []))
    (digitStep_polyTime pad) inv (fun _ => ⟨le_rfl,rfl⟩)
    (fun _ _ s _ hs => ⟨(Nat.div_le_self _ _).trans hs.1,by simp [digitStep,hs.2]⟩) hsize
    (fun x i s hi hs => by
      have hv : (encNat s.1).length ≤ (encNat x.2).length := by
        simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le_size hs.1
      have hw := (encoded_word_length_le s.2).trans (Nat.mul_le_mul_left _ (hs.2 ▸ hi))
      change (out s).length ≤ _
      simp only [out,length_encPair]
      omega)).1.snd'
  exact h.of_enc_eq (fun x => congrArg (wordEncoding q) (by simp [digitIterate]))

variable {mass : (π × ℕ) × QWord q → ℕ}

/-- A word fixes the unary length used by every trial prefix of the address. -/
theorem encodePayload_polyTime (pad : Fin q) (hq : 2 ≤ q) (start : ℕ)
    (hm : ComputableInPolyTime mass (massEncoding enc q) encNat) :
    ComputableInPolyTime (fun x : π × QWord q => encodePayload pad start (fun l w => mass ((x.1,l),w)) x.2)
      (encPair enc (wordEncoding q)) (encOption (wordEncoding q)) := by
  let src := encPair enc (wordEncoding q)
  have hp := fst enc (wordEncoding q)
  have hw := snd enc (wordEncoding q)
  have hl := (wordLength_polyTime q).comp hw
  have hpack : ComputableInPolyTime (fun x : π × QWord q => ((x.1,x.2.length),x.2))
      src (massEncoding enc q) := (hp.prod hl).prod hw
  have hm' := hm.comp (encIn := src) (encMid := massEncoding enc q) hpack
  have ha := (WeightedAddresses.encode_polyTime (by omega) hm).comp
    (encIn := src) (encMid := massEncoding enc q) hpack
  have hn := unary_sub' hl (const 6)
  have hcap := binary_pow.comp ((const (encOut := encNat) q).prod hn)
  have hresult := (optionSome (wordEncoding q)).comp
    ((fixedDigits_polyTime pad).comp (hn.prod ha))
  have hguard := bool_and' (unary_le' (const (max 8 start)) hl) (binary_lt' (const 0) hm')
  have h := ite hguard (ite (binary_lt' ha hcap) hresult (const none)) (const none)
  exact h.of_enc_eq (fun x => by simp [encodePayload,Function.comp_def, Bool.and_eq_true])

theorem decodePayload_polyTime (hq : 2 ≤ q) (start : ℕ)
    (hm : ComputableInPolyTime mass (massEncoding enc q) encNat) :
    ComputableInPolyTime (fun x : (π × ℕ) × QWord q =>
      decodePayload start (fun l w => mass ((x.1.1,l),w)) x.1.2 x.2)
      (massEncoding enc q) (encOption (wordEncoding q)) := by
  let e := massEncoding enc q
  let src := encPair enc encUnary
  let ew := wordEncoding q
  have hd := fst src ew
  have hw := snd src ew
  have hl := hd.snd'
  have hn := unary_sub' hl (const 6)
  have hslice := (takeUnary (symbolEncoding q)).comp (hw.prod hn)
  have hr := (wordRank_polyTime hq).comp hslice
  have hi := (WeightedAddresses.decode_polyTime hm).comp (hd.prod (hl.prod hr))
  have hx := snd e ew
  have hc := ((wordLength_polyTime q).comp hx).decide_eq' (hl.comp (fst e ew))
  have hf := optionElimWithInput (body := fun x w => if w.length = x.1.2 then some w else none)
    hi (const none) (ite_decide hc ((optionSome ew).comp hx) (const none))
  have hg := bool_and' (unary_le' (const (max 8 start)) hl) (unary_le' hn ((wordLength_polyTime q).comp hw))
  have h := ite hg hf (const none)
  refine h.of_enc_eq (fun x => ?_)
  apply congrArg (encOption ew)
  unfold decodePayload
  dsimp only [Function.comp_def]
  cases WeightedAddress.decode (fun p => mass (x.1,p)) x.1.2 (wordRank (x.2.take (x.1.2-6))) <;>
    simp [Bool.and_eq_true,Option.filter]

#print axioms combined_polyTime
#print axioms fixedDigits_polyTime
#print axioms encodePayload_polyTime
#print axioms decodePayload_polyTime

end DeletionCode.Explicit.Machine.RareAddress
