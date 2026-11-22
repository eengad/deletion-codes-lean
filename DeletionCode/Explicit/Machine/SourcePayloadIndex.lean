import DeletionCode.Explicit.Machine.SourceMixedRadix
import DeletionCode.Explicit.ReplayPayload

/-! Prefix and index fields of the source compression formats. -/
namespace DeletionCode.Explicit.Machine.SourcePayloadIndex

open SourceMixedRadix SourceLists
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {q : ℕ}

def split (n : ℕ) (w : QWord q) : Option (QWord q × QWord q) :=
  if n ≤ w.length then some (w.take n,w.drop n) else none

theorem split_eq (n : ℕ) (w : QWord q) :
    split n w = (ReplayPayload.readPrefix n w).map (fun (u,t) => (List.ofFn u,t)) := by
  unfold split ReplayPayload.readPrefix
  by_cases h : n ≤ w.length
  · rw [if_pos h,dite_eq_left h,Option.map_some]
    congr 2
    apply List.ext_getElem (by simp [Nat.min_eq_left h])
    intro i hi hj
    simp
  · rw [if_neg h,dite_eq_right h]
    rfl

def writeIndex (pad : Fin q) (bound value : ℕ) : QWord q :=
  (RareAddress.fixedDigits pad (Nat.clog q bound) value).reverse

theorem writeIndex_eq (pad : Fin q) (hq : 2 ≤ q) {M : ℕ} (i : Fin M) :
    writeIndex pad M i.val = List.ofFn (ReplayPayload.indexWord (by omega) i) :=
  GramOrder.mainWord_eq pad hq _ (Fin.castLE (Nat.le_pow_clog (by omega) _) i)

def readIndex (q M : ℕ) (w : QWord q) : Option (ℕ × QWord q) := do
  let (a,tail) ← split (Nat.clog q M) w
  let i := wordRank a.reverse
  if i < M then some (i,tail) else none

theorem readIndex_eq (M : ℕ) (w : QWord q) :
    readIndex q M w = (ReplayPayload.readIndex M w).map (fun (i,tail) => (i.val,tail)) := by
  unfold readIndex ReplayPayload.readIndex
  rw [split_eq]
  cases h : ReplayPayload.readPrefix (Nat.clog q M) w with
  | none => rfl
  | some p =>
    obtain ⟨a,tail⟩ := p
    simp only [Option.map_some,Option.bind_eq_bind,Option.bind_some,GramOrder.reversed_rank]
    by_cases hi : (finFunctionFinEquiv a).val < M
    · rw [if_pos hi,dite_eq_left hi]
      rfl
    · rw [if_neg hi,dite_eq_right hi]
      rfl

theorem readIndex_bound (q M : ℕ) (w : QWord q) (p : ℕ × QWord q)
    (h : readIndex q M w = some p) : p.1 < M := by
  unfold readIndex at h
  cases hs : split (Nat.clog q M) w with
  | none => simp [hs] at h
  | some v =>
    have h' : (if wordRank v.1.reverse < M then some (wordRank v.1.reverse,v.2) else none) = some p := by
      simpa [hs] using h
    split at h'
    · cases h'
      assumption
    · contradiction

abbrev splitEncoding (q : ℕ) := encPair encUnary (wordEncoding q)
abbrev splitOutput (q : ℕ) := encPair (wordEncoding q) (wordEncoding q)

theorem split_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : ℕ × QWord q => split x.1 x.2)
      (splitEncoding q) (encOption (splitOutput q)) := by
  let w := wordEncoding q
  have hn := fst encUnary w
  have hw := snd encUnary w
  have hl := (length_list (ExceptionalRecords.letterEncoding q)).comp hw
  have ht := listTakeWithInput hw hn
  have hd := listDropWithInput hw hn
  exact ((unary_le' hn hl).ite' ((optionSome (splitOutput q)).comp (ht.prod hd)) (const none)).of_enc_eq
    (fun _ => by simp [Function.comp_def,split] <;> rfl)

theorem writeIndex_polyTime (pad : Fin q) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : ℕ × ℕ => writeIndex pad x.1 x.2)
      (encPair encNat encNat) (wordEncoding q) := by
  have hb := (widthAt_polyTime q).comp (fst encNat encNat)
  have hd := (RareAddress.fixedDigits_polyTime pad).comp (hb.prod (snd encNat encNat))
  exact ((listReverse (ExceptionalRecords.letterEncoding q)).comp hd).of_enc_eq (fun x => by
    simp only [Function.comp_def,widthAt_eq hq]
    rfl)

abbrev readEncoding (q : ℕ) := encPair encNat (wordEncoding q)

theorem readIndex_polyTime (q : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : ℕ × QWord q => readIndex q x.1 x.2)
      (readEncoding q) (encOption (readEncoding q)) := by
  let w := wordEncoding q
  let e := readEncoding q
  let a := encPair e (splitOutput q)
  have hb := fst encNat w
  have hl := (widthAt_polyTime q).comp hb
  have hp := (split_polyTime q).comp (hl.prod (snd encNat w))
  have hsplit := hp.of_enc_eq (encD := encOption (splitOutput q)) (g := fun x => split (Nat.clog q x.1) x.2) (fun x => by
    simp [Function.comp_def,widthAt_eq hq])
  have hs := snd e (splitOutput q)
  have hr := (wordRank_polyTime hq).comp ((listReverse (ExceptionalRecords.letterEncoding q)).comp hs.fst')
  have ht := binary_lt' hr (hb.comp (fst e (splitOutput q)))
  have h := ht.ite' ((optionSome e).comp (hr.prod hs.snd')) (const none)
  exact optionBindWithInput (ea := e) (eb := splitOutput q) (ec := e)
    (f := fun x p => if wordRank p.1.reverse < x.1 then some (wordRank p.1.reverse,p.2) else none)
    hsplit (h.of_enc_eq (fun x => by simp [Function.comp_def] <;> rfl))

theorem descriptionBound_polyTime (q b : ℕ) :
    ComputableInPolyTime (fun x : ℕ × ℕ => ReplayGrammar.descriptionBound x.1 x.2 b q)
      (encPair encUnary encUnary) encNat := by
  have hE := fst encUnary encUnary
  have hL := snd encUnary encUnary
  have hE' := unary_add' hE (const 1)
  have hL' := unary_add' hL (const 1)
  have hR := unary_to_binary.comp (unary_mul' (const 100) (unary_mul' hE' hL'))
  have hP := binary_pow' hR (unary_mul' (const 20) hE)
  have hQ := binary_pow' (const q) (unary_mul' (const (4*b)) hE)
  exact (binary_mul' (binary_mul' (unary_to_binary.comp hE') hP) hQ).of_enc_eq (fun x => by
    simp only [Function.comp_def,ReplayGrammar.descriptionBound,ReplayGrammar.radix,← Nat.mul_assoc])

#print axioms split_eq
#print axioms writeIndex_eq
#print axioms readIndex_eq
#print axioms split_polyTime
#print axioms writeIndex_polyTime
#print axioms readIndex_polyTime
#print axioms descriptionBound_polyTime

end DeletionCode.Explicit.Machine.SourcePayloadIndex
