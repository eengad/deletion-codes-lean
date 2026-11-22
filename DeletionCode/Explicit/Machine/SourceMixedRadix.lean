import DeletionCode.Explicit.Machine.SourceRadix
import DeletionCode.Explicit.Machine.GramOrder
import DeletionCode.Explicit.PivotRadix

/-! Mixed-radix payloads and the public pivot radix, using binary arithmetic. -/
namespace DeletionCode.Explicit.Machine.SourceMixedRadix

open SourceRadix SourceLists
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {q : ℕ}

def widthAt (q n : ℕ) : ℕ :=
  ((List.range (n.size+1)).find? (fun i => decide (n ≤ q^i))).getD 0

theorem widthAt_eq (hq : 2 ≤ q) (n : ℕ) : widthAt q n = Nat.clog q n := by
  have hp : n ≤ q^n.size := (Nat.lt_size_self n).le.trans (Nat.pow_le_pow_left hq _)
  have hw : Nat.clog q n ≤ n.size := (Nat.clog_le_iff_le_pow (by omega)).mpr hp
  have hle : n ≤ q^(Nat.clog q n) := Nat.le_pow_clog (by omega) n
  unfold widthAt
  rw [findRange_first _ _ (Nat.clog q n) (by omega) (decide_eq_true hle)]
  · rfl
  · intro i hi
    exact decide_eq_false_iff_not.mpr (fun h => (Nat.not_le_of_lt hi)
      ((Nat.clog_le_iff_le_pow (show 1 < q by omega)).mpr h))

theorem widthAt_polyTime (q : ℕ) : ComputableInPolyTime (widthAt q) encNat encUnary := by
  let e := encPair encNat encUnary
  have ht := binary_le' (fst encNat encUnary) (binary_pow' (const q) (snd encNat encUnary))
  have hf := findWithInput (encIn := encNat) (encA := encUnary)
    (test := fun x i => decide (x ≤ q^i)) (unary_range' (unary_add' binary_size (const 1))) ht
  have h := optionElimWithInput (encA := encNat) (encB := encUnary) (encC := encUnary)
    (body := fun _ x => x) hf (const 0) (snd encNat encUnary)
  exact h.of_enc_eq (fun x => by
    unfold widthAt
    cases (List.range (x.size+1)).find? (fun i => decide (x ≤ q^i)) <;> rfl)

theorem width_polyTime (q : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (MixedRadix.width q) numbersEncoding encUnary := by
  have h := (widthAt_polyTime q).comp binary_prod
  exact h.of_enc_eq (fun rs => congrArg encUnary (widthAt_eq hq rs.prod).symm)

def encode (pad : Fin q) (rs vs : List ℕ) : Option (QWord q) :=
  (SourceRadix.rank rs vs).map fun k => (RareAddress.fixedDigits pad (MixedRadix.width q rs) k).reverse

theorem encode_eq (pad : Fin q) (hq : 2 ≤ q) (rs vs : List ℕ) :
    encode pad rs vs = (MixedRadix.encode (by omega : 1 < q) rs vs).map List.ofFn := by
  unfold encode MixedRadix.encode
  rw [rank_eq]
  cases MixedRadix.rank rs vs with
  | none => rfl
  | some k =>
    exact congrArg some (GramOrder.mainWord_eq pad hq _ (Fin.castLE (Nat.le_pow_clog (by omega) _) k))

abbrev decodeEncoding (q : ℕ) := encPair numbersEncoding (wordEncoding q)

def decode (rs : List ℕ) (w : QWord q) : Option (List ℕ) :=
  let r := wordRank w.reverse
  if r < rs.prod then some (SourceRadix.unrank rs r) else none

theorem decode_eq (rs : List ℕ) (w : Fin (MixedRadix.width q rs) → Fin q) :
    decode rs (List.ofFn w) = MixedRadix.decode rs w := by
  dsimp only [decode,MixedRadix.decode]
  rw [GramOrder.reversed_rank w]
  split
  · rename_i h
    exact congrArg some (unrank_eq rs ⟨_,h⟩)
  · simp_all

theorem encode_polyTime (pad : Fin q) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : List ℕ × List ℕ => encode pad x.1 x.2)
      rankEncoding (encOption (wordEncoding q)) := by
  let e := rankEncoding
  let w := wordEncoding q
  let p := encPair e encNat
  have hwidth := (width_polyTime q hq).comp ((fst numbersEncoding numbersEncoding).comp (fst e encNat))
  have hd := (Machine.RareAddress.fixedDigits_polyTime pad).comp (encIn := p)
    (hwidth.prod (snd e encNat))
  have hr := (listReverse (ExceptionalRecords.letterEncoding q)).comp hd
  exact optionMapWithInput (encA := e) (encB := encNat) (encC := w)
    (f := fun x k => (RareAddress.fixedDigits pad (MixedRadix.width q x.1) k).reverse) rank_polyTime hr

theorem decode_polyTime (q : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : List ℕ × QWord q => decode x.1 x.2)
      (decodeEncoding q) (encOption numbersEncoding) := by
  let e := decodeEncoding q
  let w := wordEncoding q
  have hf := fst numbersEncoding w
  have hw := snd numbersEncoding w
  have hprod := binary_prod.comp hf
  have hval := (wordRank_polyTime hq).comp ((listReverse (ExceptionalRecords.letterEncoding q)).comp hw)
  have hgood := (optionSome numbersEncoding).comp (unrank_polyTime.comp (hf.prod hval))
  exact ((binary_lt' hval hprod).ite' hgood (const none)).of_enc_eq
    (fun _ => by simp [decode,Function.comp_def] <;> rfl)

theorem pivotRadix_polyTime :
    ComputableInPolyTime (fun x : ℕ × ℕ => BubbleFamilies.pivotRadix x.1 x.2)
      (encPair encNat encNat) encNat := by
  have hx := fst encNat encNat
  have hy := snd encNat encNat
  exact binary_div' (binary_add' (binary_mul' (const 2) hx) (binary_sub' hy (const 1))) hy

#print axioms widthAt_eq
#print axioms width_polyTime
#print axioms encode_eq
#print axioms decode_eq
#print axioms encode_polyTime
#print axioms decode_polyTime
#print axioms pivotRadix_polyTime

end DeletionCode.Explicit.Machine.SourceMixedRadix
