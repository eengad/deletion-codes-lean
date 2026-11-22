import DeletionCode.Explicit.Machine.SourcePublicHash
import DeletionCode.Explicit.Machine.SourceAcceptance
import DeletionCode.Explicit.Machine.SourceRareBranch
import DeletionCode.Explicit.Machine.SourceSmallBranch
import DeletionCode.Explicit.Machine.SourcePeelingBranch
import DeletionCode.Explicit.Machine.SourceFrame
import DeletionCode.Explicit.SourceSetup

/-! Polynomial-time certificates for the concrete source callbacks. -/

namespace DeletionCode.Explicit.Machine.SourceCallbacks

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Ternary CataloguePrefix SourcePublicHash
open _root_.DeletionCode.Explicit.UniformParameters (minLength)

variable {q l : ℕ}
set_option maxHeartbeats 1400000

private theorem onHash_polyTime {α : Type} {enc : α ↪ List Bool} (b t : ℕ) (hq : 2 ≤ q)
    {length : SourceInput q → ℕ}
    (hLength : ComputableInPolyTime length (Explicit.inputEncoding q) encUnary)
    {f : SourceAcceptance.Input q → α}
    (hf : ComputableInPolyTime f (SourceAcceptance.inputEncoding q) enc) (fallback : α) :
    ComputableInPolyTime (fun p : SourceInput q =>
      (lookupRows q b t p.1 (length p)).elim fallback (fun rows => f (length p, rows, p.2)))
      (Explicit.inputEncoding q) enc := by
  let e := Explicit.inputEncoding q
  let w := wordEncoding q
  have h := (lookupRows_polyTime q b t hq).comp ((fst encBits w).prod hLength)
  have hp := fst e rowsEncoding
  have hw := (snd encBits w).comp hp
  exact optionElimWithInput (encA := e) (encB := rowsEncoding) (encC := enc)
    (body := fun p rows => f (length p, rows, p.2)) h (const fallback)
    (hf.comp ((hLength.comp hp).prod ((snd e rowsEncoding).prod hw)))

theorem concreteAccepted_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q)
    (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (SourceSetup.sourceCallbacks (by omega) b t pad).accepted
      (Explicit.inputEncoding q) encBool := by
  have hl := (wordLength_polyTime q).comp (snd encBits (wordEncoding q))
  refine (onHash_polyTime b t hq hl (SourceAcceptance.accepted_polyTime pad b t hq hb ht) true).of_enc_eq ?_
  intro p
  apply congrArg encBool
  symm
  let C := OperationalSource.procedures (show 1 < q by omega) pad (SourceSetup.inputs q b t pad)
  change (lookupRows q b t p.1 p.2.length).elim true (fun rows =>
    SourceAcceptance.accepted pad b t (p.2.length, rows, p.2)) =
    (ConcreteSource.callbacks (show 1 < q by omega) pad C).accepted p
  by_cases hs : p.2.length < minLength q b t
  · simp [lookupRows, ConcreteSource.callbacks, hs]
  · rw [lookupRows_eq]
    change ((SourceHashTable.lookup q b t p.1 p.2.length).map matrixRows).elim true _ =
      if p.2.length < minLength q b t then true else
        (SourceHashTable.lookup q b t p.1 p.2.length).elim true
          (fun H => ConcreteSource.acceptedAt C pad H p.2.get)
    rw [ite_eq_right hs]
    cases h : SourceHashTable.lookup q b t p.1 p.2.length with
    | none => rfl
    | some H =>
      have he := SourceAcceptance.accepted_eq pad C hq H p.2.get
      rw [List.ofFn_get] at he
      exact he.trans (by
        simp [ConcreteSource.acceptedAt, SourceAcceptance.withDeciders, SourceAcceptance.exceptionalAt,
          C, OperationalSource.procedures, SourceSetup.inputs, hs])

theorem concreteLabel_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (SourceSetup.sourceCallbacks (by omega) b t pad).label
      (Explicit.inputEncoding q) encNat := by
  have hl := (wordLength_polyTime q).comp (snd encBits (wordEncoding q))
  refine (onHash_polyTime b t hq hl (SourceAcceptance.label_polyTime pad b t hq) 0).of_enc_eq ?_
  intro p
  apply congrArg encNat
  symm
  change (lookupRows q b t p.1 p.2.length).elim 0 (fun rows =>
    SourceAcceptance.label pad b t (p.2.length, rows, p.2)) =
    (SourceHashTable.lookup q b t p.1 p.2.length).elim 0 (fun H => ConcreteSource.rankAt pad H p.2.get)
  rw [lookupRows_eq]
  cases h : SourceHashTable.lookup q b t p.1 p.2.length with
  | none => rfl
  | some H => simpa only [List.ofFn_get, Option.map_some, Option.elim_some] using SourceAcceptance.label_eq pad b t hq H p.2.get


private abbrev HashInput := ℕ × Rows
private abbrev hashEncoding := encPair encUnary rowsEncoding

private def encodeBranch (pad : Fin q) (b t j : ℕ) (m : HashInput) (word : QWord q) :
    Option (QWord q) :=
  if j = 0 then SourceRareBranch.encode pad b t m word
  else if j = 1 then SourceSmallBranch.encode pad b t (m.1,m.2,word)
  else SourcePeelingBranch.encode pad b t (m.1,m.2,word)

private theorem encodeBranch_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (fun p : (HashInput × QWord q) × ℕ => encodeBranch pad b t p.2 p.1.1 p.1.2)
      (encPair (encPair hashEncoding (wordEncoding q)) encUnary) (encOption (wordEncoding q)) := by
  let w := wordEncoding q
  let e := encPair hashEncoding w
  have hp := fst e encUnary
  have hj := snd e encUnary
  have hm := hp.fst'
  have hw := hp.snd'
  have hrare := (SourceRareBranch.encode_polyTime pad b t hq hb ht).comp hp
  have hinput := hm.fst'.prod (hm.snd'.prod hw)
  have hsmall := (SourceSmallBranch.encode_polyTime pad b t hq hb ht).comp hinput
  have hpeel := (SourcePeelingBranch.encode_polyTime pad b t hq hb ht).comp hinput
  have hc := (hj.decide_eq' (const 0)).ite' hrare ((hj.decide_eq' (const 1)).ite' hsmall hpeel)
  exact hc.of_enc_eq (fun _ => by simp [encodeBranch])

private def decodeBranch (pad : Fin q) (b t j : ℕ) (m : HashInput) (n : ℕ) (word : QWord q) :
    Option (QWord q) :=
  if j = 0 then SourceRareBranch.decode pad b t m n word
  else if j = 1 then SourceReplayPayload.decode pad b t n word
  else SourcePeelingBranch.decode pad b t (n,m.2,word)

private theorem decodeBranch_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (fun p : ((HashInput × QWord q) × ℕ) × ℕ =>
      decodeBranch pad b t p.2 p.1.1.1 p.1.2 p.1.1.2)
      (encPair (encPair (encPair hashEncoding (wordEncoding q)) encUnary) encNat) (encOption (wordEncoding q)) := by
  let w := wordEncoding q
  let e := encPair (encPair hashEncoding w) encUnary
  have hp := fst e encNat
  have hj := snd e encNat
  have hm := hp.fst'.fst'
  have hw := hp.fst'.snd'
  have hn := hp.snd'
  have hrare := (SourceRareBranch.decode_polyTime pad b t hq hb ht).comp ((hm.prod hn).prod hw)
  have hsmall := (SourceReplayPayload.decode_polyTime pad hq b t).comp (hn.prod hw)
  have hpeel := (SourcePeelingBranch.decode_polyTime pad b t hq).comp (hn.prod (hm.snd'.prod hw))
  have hc := (hj.decide_eq' (const 0)).ite' hrare ((hj.decide_eq' (const 1)).ite' hsmall hpeel)
  exact hc.of_enc_eq (fun _ => by simp [decodeBranch])

private theorem encodeBranch_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (H : ConcreteSource.Hash q b t l) (x : QWord q) (hx : x.length = l)
    (hl : minLength q b t ≤ l) (j : Fin 3) :
    encodeBranch pad b t j.val (l,matrixRows H) x =
      ((OperationalSource.procedures (by omega : 1 < q) pad (SourceSetup.inputs q b t pad)).branch l H j).encode x := by
  subst l
  fin_cases j
  · exact SourceRareBranch.encode_eq pad b t hq hb ht hl H x
  · have h := SourceSmallBranch.encode_eq pad b t hq hb ht H x.get
    rw [List.ofFn_get] at h
    change SourceSmallBranch.encode pad b t (x.length,matrixRows H,x) =
      (if he : x.length = x.length then
        SmallCompression.pack (by omega) pad (fun v => AcceptanceWeights.strong pad b t x.length (List.ofFn v))
          H (fun i => x.get (Fin.cast he.symm i)) else none)
    rw [dite_eq_left rfl]
    exact h
  · have h := SourcePeelingBranch.encode_eq pad b t hq hb ht H x.get
    rw [List.ofFn_get] at h
    change SourcePeelingBranch.encode pad b t (x.length,matrixRows H,x) =
      (if he : x.length = x.length then
        PeelingCompression.pack (by omega) pad (fun v => AcceptanceWeights.strong pad b t x.length (List.ofFn v))
          H (fun i => x.get (Fin.cast he.symm i)) else none)
    rw [dite_eq_left rfl]
    exact h

private theorem decodeBranch_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (H : ConcreteSource.Hash q b t l) (hl : minLength q b t ≤ l) (j : Fin 3) (word : QWord q) :
    decodeBranch pad b t j.val (l,matrixRows H) l word =
      ((OperationalSource.procedures (by omega : 1 < q) pad (SourceSetup.inputs q b t pad)).branch l H j).decode l word := by
  fin_cases j
  · exact SourceRareBranch.decode_eq pad b t hq hb ht hl H l word
  · change SourceReplayPayload.decode pad b t l word =
      (if l = l then (SmallCompression.read q b t l pad word).map List.ofFn else none)
    rw [ite_eq_left rfl]
    exact SourceSmallBranch.decode_eq pad b t l hq word
  · change SourcePeelingBranch.decode pad b t (l,matrixRows H,word) =
      (if l = l then (PeelingCompression.read pad H word).map List.ofFn else none)
    rw [ite_eq_left rfl]
    exact SourcePeelingBranch.decode_eq pad b t hq H word

private theorem lookup_min (b t : ℕ) (bits : List Bool) (H : ConcreteSource.Hash q b t l)
    (h : SourceHashTable.lookup q b t bits l = some H) : minLength q b t ≤ l := by
  by_contra hn
  have hh : l < minLength q b t := by omega
  simp [SourceHashTable.lookup,hh] at h

theorem concreteCompress_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (SourceSetup.sourceCallbacks (by omega) b t pad).compress
      (Explicit.inputEncoding q) (wordEncoding q) := by
  let w := wordEncoding q
  have hl := (wordLength_polyTime q).comp (snd encBits w)
  have h := SourceFrame.compress_polyTime pad hq hashEncoding (encodeBranch pad b t)
    (encodeBranch_polyTime pad b t hq hb ht)
  have hd := h.comp (((fst encUnary (encPair rowsEncoding w)).prod
      (snd encUnary (encPair rowsEncoding w)).fst').prod (snd encUnary (encPair rowsEncoding w)).snd')
  have hf := optionGetDWithInput hd (const [])
  have hc := onHash_polyTime b t hq hl hf []
  refine hc.of_enc_eq ?_
  intro p
  apply congrArg w
  symm
  let C := OperationalSource.procedures (show 1 < q by omega) pad (SourceSetup.inputs q b t pad)
  change (lookupRows q b t p.1 p.2.length).elim [] (fun rows =>
      (SourceFrame.compress pad (encodeBranch pad b t) (p.2.length,rows) p.2).getD []) =
    ((SourceHashTable.lookup q b t p.1 p.2.length).bind fun H =>
      CompressorFrame.compress (by omega) pad (C.branch p.2.length H) p.2).getD []
  rw [lookupRows_eq]
  cases hH : SourceHashTable.lookup q b t p.1 p.2.length with
  | none => rfl
  | some H =>
    simp only [Option.map_some, Option.elim_some, Option.bind_some]
    rw [SourceFrame.compress_eq pad hq _ _ _ _ (encodeBranch_eq pad b t hq hb ht H p.2 rfl
      (lookup_min b t p.1 H hH))]

theorem concreteExpand_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (SourceSetup.sourceCallbacks (by omega) b t pad).expand
      (Explicit.inputEncoding q) (encOption (wordEncoding q)) := by
  let w := wordEncoding q
  have hl := unary_add' ((wordLength_polyTime q).comp (snd encBits w)) (const 1)
  have h := SourceFrame.expand_polyTime hq hashEncoding (decodeBranch pad b t)
    (decodeBranch_polyTime pad b t hq hb ht)
  have hd := h.comp (((fst encUnary (encPair rowsEncoding w)).prod
      (snd encUnary (encPair rowsEncoding w)).fst').prod (snd encUnary (encPair rowsEncoding w)).snd')
  have hc := onHash_polyTime b t hq hl hd none
  refine hc.of_enc_eq ?_
  intro p
  apply congrArg (encOption w)
  symm
  let C := OperationalSource.procedures (show 1 < q by omega) pad (SourceSetup.inputs q b t pad)
  change (lookupRows q b t p.1 (p.2.length+1)).elim none (fun rows =>
      SourceFrame.expand (decodeBranch pad b t) (p.2.length+1,rows) p.2) =
    (SourceHashTable.lookup q b t p.1 (p.2.length+1)).bind (fun H =>
      CompressorFrame.decompress (C.branch (p.2.length+1) H) p.2)
  rw [lookupRows_eq]
  cases hH : SourceHashTable.lookup q b t p.1 (p.2.length+1) with
  | none => rfl
  | some H =>
    simp only [Option.map_some, Option.elim_some, Option.bind_some]
    exact SourceFrame.expand_eq _ _ _ _ (decodeBranch_eq pad b t hq hb ht H (lookup_min b t p.1 H hH))

theorem certified (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    (SourceSetup.sourceCallbacks (by omega) b t pad).Certified where
  accepted := concreteAccepted_polyTime pad b t hq hb ht
  compress := concreteCompress_polyTime pad b t hq hb ht
  expand := concreteExpand_polyTime pad b t hq hb ht
  label := concreteLabel_polyTime pad b t hq

#print axioms concreteAccepted_polyTime
#print axioms concreteLabel_polyTime
#print axioms concreteCompress_polyTime
#print axioms concreteExpand_polyTime
#print axioms certified

end DeletionCode.Explicit.Machine.SourceCallbacks
