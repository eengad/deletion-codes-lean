import DeletionCode.Explicit.Machine.SourceNegative
import DeletionCode.Explicit.ReplayGrammar
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-! Signed source coordinates and the bounded reference fields of a replay code. -/
namespace DeletionCode.Explicit.Machine.SourceReference

open ReplayEntry SourceLetters SourceLists
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open private sideCode from DeletionCode.Explicit.ReplayGrammar

variable {q ℓ E L : ℕ}

abbrev Supplier := ℕ × (Bool × ℕ)
abbrev Ref := ℤ × Option Supplier
abbrev supplierEncoding := encPair encUnary (encPair encBool encUnary)
abbrev refEncoding := encPair encIntBin (encOption supplierEncoding)
abbrev referenceEncoding := encOption refEncoding
abbrev fieldsEncoding := encPair encUnary encUnary

def referenceData : Reference → Ref
  | .source delta => (delta,none)
  | .supplier j s off => (0,some (j,(SourceDictionary.side s,off)))

def readSource (ℓ L root : ℕ) (delta : ℤ) : Option (LiftData q) :=
  let start := (root : ℤ)+delta
  if 0 ≤ start ∧ start.toNat+L ≤ ℓ then some (original q start.toNat L) else none

def read (cfg : SourceNegative.ReadConfig) (anchor : Option ℕ)
    (es : List (SourceDictionary.Stored q)) (ref : Ref) : Option (LiftData q) :=
  ref.2.elim (anchor.bind (fun root => readSource cfg.1.1 cfg.1.2 root ref.1))
    (fun s => SourceNegative.readLocation cfg es (s.1,some s.2))

theorem read_eq (es : Array (Completed ℓ (Fin q))) (L current rule : ℕ)
    (anchor : Option (Fin ℓ)) (r : Reference) :
    read ((ℓ,L),(current,rule)) (anchor.map Fin.val) (SourceDictionary.historyData es) (referenceData r) =
      (readReference L current rule anchor (fun k => es[k]?) r).map liftData := by
  cases r with
  | source delta =>
    cases anchor with
    | none => rfl
    | some root =>
      by_cases hs : 0 ≤ (root.val : ℤ)+delta
      · by_cases hl : ((root.val : ℤ)+delta).toNat+L ≤ ℓ
        · simp [read,referenceData,readSource,readReference,hs,hl,original_eq _ _ _ hl]
        · simp [read,referenceData,readSource,readReference,hs,hl]
      · simp [read,referenceData,readSource,readReference,hs]
  | supplier j s off => exact SourceNegative.readSupplier_eq es L current rule anchor j s off

def boundary (E L : ℕ) : ℕ := 8*E*L

def decode (E L code : ℕ) : Option (Option Ref) :=
  if code = 0 then some none
  else if code ≤ 2*boundary E L+1 then some (some (((code : ℤ)-1-boundary E L),none))
  else
    let raw := code-(2*boundary E L+2)
    let width := 3*L+1
    let i := raw/(2*width)
    if i < E then some (some (0,some (i,(!decide (raw/width%2 = 0),raw%width))))
    else none

theorem decode_eq (c : Fin (ReplayGrammar.radix E L)) :
    decode E L c.val = (ReplayGrammar.decodeReference E L c).map
      (Option.map referenceData) := by
  unfold decode ReplayGrammar.decodeReference
  simp only [boundary,show 2*(8*E*L) = 16*E*L by ring]
  by_cases hz : c.val = 0
  · simp [hz]
  · simp only [hz,↓reduceIte]
    split
    · rfl
    · split
      · simp only [Option.map_some]
        split <;> simp_all [referenceData,SourceDictionary.side]
      · rfl

def encodeSource (E L : ℕ) (delta : ℤ) : Option ℕ :=
  let b := boundary E L
  if -(b : ℤ) ≤ delta ∧ delta ≤ b then some (delta+b+1).toNat else none

def encodeSupplier (E L : ℕ) (r : Supplier) : Option ℕ :=
  if r.1 < E ∧ r.2.2 ≤ 3*L then
    some (2*boundary E L+2+(2*r.1+r.2.1.toNat)*(3*L+1)+r.2.2)
  else none

def encode (E L : ℕ) (r : Option Ref) : Option ℕ :=
  r.elim (some 0) fun a => a.2.elim (encodeSource E L a.1) (encodeSupplier E L)

theorem encode_eq (r : Option Reference) :
    encode E L (r.map referenceData) = (ReplayGrammar.encodeReference E L r).map Fin.val := by
  rcases r with _ | (_ | ⟨j,s,off⟩)
  · rfl
  · unfold encode ReplayGrammar.encodeReference
    simp only [Option.map_some,Option.elim_some,referenceData,Option.elim_none,encodeSource,boundary,
      Nat.cast_mul,Nat.cast_ofNat]
    split <;> simp_all
  · unfold encode ReplayGrammar.encodeReference
    simp only [Option.map_some,Option.elim_some,referenceData,encodeSupplier,boundary,
      show 2*(8*E*L) = 16*E*L by ring]
    cases s <;> simp [SourceDictionary.side,sideCode] <;> split <;> simp_all <;> omega

private theorem boundary_polyTime :
    ComputableInPolyTime (fun x : ℕ × ℕ => boundary x.1 x.2) fieldsEncoding encUnary :=
  (unary_mul' (unary_mul' (const 8) (fst encUnary encUnary)) (snd encUnary encUnary)).of_enc_eq
    (fun _ => rfl)

theorem readSource_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : ((ℕ × ℕ) × ℕ) × ℤ => readSource x.1.1.1 x.1.1.2 x.1.2 x.2)
      (encPair (encPair fieldsEncoding encUnary) encIntBin) (SourceNegative.resultEncoding q) := by
  let e := encPair (encPair fieldsEncoding encUnary) encIntBin
  have h := fst (encPair fieldsEncoding encUnary) encIntBin
  have hl := h.fst'.fst'
  have hL := h.fst'.snd'
  have hr := intBin_natCast.comp (unary_to_binary.comp h.snd')
  have hs := intBin_add' hr (snd (encPair fieldsEncoding encUnary) encIntBin)
  have hn := intBin_toNat.comp hs
  have hL' := unary_to_binary.comp hL
  have hl' := unary_to_binary.comp hl
  have hv := bool_and' (intBin_le' (const 0) hs) (binary_le' (binary_add' hn hL') hl')
  have hc := binary_to_unary_bounded (binary_min' hn hl') hl (fun _ => Nat.min_le_right ..)
  have ho := (original_polyTime q).comp (hc.prod hL)
  have hresult := hv.ite' ((optionSome (liftEncoding q)).comp ho) (const none)
  refine hresult.of_enc_eq (g := fun x => readSource x.1.1.1 x.1.1.2 x.1.2 x.2) ?_
  intro x
  simp only [readSource,Function.comp_def,Bool.and_eq_true_iff,decide_eq_true_eq]
  split
  · rename_i h
    rw [Nat.min_eq_left (by omega)]
  · rfl

abbrev readEncoding (q : ℕ) :=
  encPair (encPair (encPair SourceNegative.configEncoding (encOption encUnary))
    (SourceDictionary.historyEncoding q)) refEncoding

theorem read_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : ((SourceNegative.ReadConfig × Option ℕ) ×
      List (SourceDictionary.Stored q)) × Ref => read x.1.1.1 x.1.1.2 x.1.2 x.2)
      (readEncoding q) (SourceNegative.resultEncoding q) := by
  let e := readEncoding q
  let o := encOption encUnary
  let h := SourceDictionary.historyEncoding q
  let c := SourceNegative.configEncoding
  let a := encPair e encUnary
  let t := encPair e supplierEncoding
  have he := fst (encPair (encPair c o) h) refEncoding
  have hr := snd (encPair (encPair c o) h) refEncoding
  have hf := fst e encUnary
  have hs := (readSource_polyTime q).comp (encIn := a) (encMid := encPair (encPair fieldsEncoding encUnary) encIntBin)
    (((((he.fst'.fst'.fst').comp hf).prod (snd e encUnary))).prod (hr.fst'.comp hf))
  have hsource := optionBindWithInput (ea := e)
    (f := fun x root => readSource x.1.1.1.1.1 x.1.1.1.1.2 root x.2.1)
    he.fst'.snd' (hs.of_enc_eq (fun _ => rfl))
  have ht := fst e supplierEncoding
  have hs := snd e supplierEncoding
  have hsup := (SourceNegative.readLocation_polyTime q).comp (encIn := t)
    (encMid := SourceNegative.readEncoding q)
    (((he.fst'.fst'.prod he.snd').comp ht).prod (hs.fst'.prod
      ((optionSome (encPair encBool encUnary)).comp hs.snd')))
  exact optionElimWithInput (encA := e) (encB := supplierEncoding) (encC := SourceNegative.resultEncoding q)
    (body := fun x s => SourceNegative.readLocation x.1.1.1 x.1.2 (s.1,some s.2))
    hr.snd' hsource (hsup.of_enc_eq (fun _ => rfl))

abbrev codeEncoding := encPair fieldsEncoding encUnary

theorem decode_polyTime :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × ℕ => decode x.1.1 x.1.2 x.2)
      codeEncoding (encOption referenceEncoding) := by
  let r := referenceEncoding
  let e := codeEncoding
  have hp := fst fieldsEncoding encUnary
  have hz := snd fieldsEncoding encUnary
  have hb := boundary_polyTime.comp hp
  have h2 := unary_mul' (const 2) hb
  have hlim := unary_add' h2 (const 1)
  have hstart := intBin_sub' (intBin_sub' (intBin_natCast.comp (unary_to_binary.comp hz)) (const 1))
    (intBin_natCast.comp (unary_to_binary.comp hb))
  have hsrc := (optionSome r).comp ((optionSome refEncoding).comp (hstart.prod (const none)))
  have hw := unary_add' (unary_mul' (const 3) hp.snd') (const 1)
  have hraw := unary_sub' hz (unary_add' h2 (const 2))
  have hi := unary_div' hraw (unary_mul' (const 2) hw)
  have hside := bool_not.comp ((unary_mod' (unary_div' hraw hw) (const 2)).decide_eq' (const 0))
  have hoff := unary_mod' hraw hw
  have hsupData := (const (encOut := encIntBin) 0).prod
    ((optionSome supplierEncoding).comp (hi.prod (hside.prod hoff)))
  have hsup := (optionSome r).comp ((optionSome refEncoding).comp hsupData)
  have hu := (unary_lt' hi hp.fst').ite' hsup (const none)
  have h := (hz.decide_eq' (const 0)).ite' (const (some none)) ((unary_le' hz hlim).ite' hsrc hu)
  refine h.of_enc_eq (g := fun x => decode x.1.1 x.1.2 x.2) (encD := encOption r) ?_
  intro x
  simp only [decode,Function.comp_def,decide_eq_true_eq] <;> rfl

private theorem encodeSource_polyTime :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × ℤ => encodeSource x.1.1 x.1.2 x.2)
      (encPair fieldsEncoding encIntBin) (encOption encUnary) := by
  let e := encPair fieldsEncoding encIntBin
  have hb := boundary_polyTime.comp (fst fieldsEncoding encIntBin)
  have hb' := intBin_natCast.comp (unary_to_binary.comp hb)
  have hd := snd fieldsEncoding encIntBin
  have hv := bool_and' (intBin_le' (intBin_neg.comp hb') hd) (intBin_le' hd hb')
  have hn := intBin_toNat.comp (intBin_add' (intBin_add' hd hb') (const 1))
  have hcap := unary_add' (unary_mul' (const 2) hb) (const 1)
  have hclamp := binary_to_unary_bounded (binary_min' hn (unary_to_binary.comp hcap)) hcap
    (fun _ => Nat.min_le_right ..)
  have h := hv.ite' ((optionSome encUnary).comp hclamp) (const none)
  refine h.of_enc_eq (g := fun x => encodeSource x.1.1 x.1.2 x.2) ?_
  intro x
  simp only [encodeSource,Function.comp_def,Bool.and_eq_true_iff,decide_eq_true_eq]
  split
  · rename_i hb
    have hc : (x.2 + (boundary x.1.1 x.1.2 : ℤ) + 1).toNat ≤ 2*boundary x.1.1 x.1.2+1 := by
      omega
    rw [Nat.min_eq_left hc]
  · rfl

private theorem encodeSupplier_polyTime :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × Supplier => encodeSupplier x.1.1 x.1.2 x.2)
      (encPair fieldsEncoding supplierEncoding) (encOption encUnary) := by
  have hx := fst fieldsEncoding supplierEncoding
  have hy := snd fieldsEncoding supplierEncoding
  have hL := unary_mul' (const 3) hx.snd'
  have hw := unary_add' hL (const 1)
  have hi := hy.fst'
  have hs := ((of_finite (encIn := encBool) (encOut := encUnary) Bool.toNat)).comp hy.snd'.fst'
  have ha := hy.snd'.snd'
  have hv := bool_and' (unary_lt' hi hx.fst') (unary_le' ha hL)
  have hb := unary_add' (unary_mul' (const 2) (boundary_polyTime.comp hx)) (const 2)
  have h := unary_add' (unary_add' hb (unary_mul' (unary_add' (unary_mul' (const 2) hi) hs) hw)) ha
  exact (hv.ite' ((optionSome encUnary).comp h) (const none)).of_enc_eq
    (fun _ => by simp [encodeSupplier,Function.comp_def,Bool.and_eq_true_iff])

abbrev encodeEncoding := encPair fieldsEncoding referenceEncoding

theorem encode_polyTime :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × Option Ref => encode x.1.1 x.1.2 x.2)
      encodeEncoding (encOption encUnary) := by
  let e := encodeEncoding
  let r := referenceEncoding
  let t := encPair e refEncoding
  let p := encPair t supplierEncoding
  have hcfg := (fst fieldsEncoding r).comp (fst e refEncoding)
  have harg := snd e refEncoding
  have hsrc := encodeSource_polyTime.comp (encIn := t) (hcfg.prod harg.fst')
  have hsup := encodeSupplier_polyTime.comp (encIn := p)
    ((hcfg.comp (fst t supplierEncoding)).prod (snd t supplierEncoding))
  have h := optionElimWithInput (encA := t) (encB := supplierEncoding) (encC := encOption encUnary)
    (body := fun x s => encodeSupplier x.1.1.1 x.1.1.2 s) harg.snd'
    (hsrc.of_enc_eq (fun _ => rfl)) (hsup.of_enc_eq (fun _ => rfl))
  exact optionElimWithInput (encA := e) (encB := refEncoding) (encC := encOption encUnary)
    (body := fun x a => a.2.elim (encodeSource x.1.1 x.1.2 a.1) (encodeSupplier x.1.1 x.1.2))
    (snd fieldsEncoding r) (const (some 0)) (h.of_enc_eq (fun _ => rfl))

#print axioms read_eq
#print axioms read_polyTime
#print axioms decode_eq
#print axioms encode_eq
#print axioms decode_polyTime
#print axioms encode_polyTime

end DeletionCode.Explicit.Machine.SourceReference
