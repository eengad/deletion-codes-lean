import DeletionCode.Explicit.TagTables
import DeletionCode.Explicit.Machine.GreedyTags
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Partial

/-! Polynomial-time computation of the existing tag tables and their public-bit encoding. -/
namespace DeletionCode.Explicit.Machine

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

private abbrev pairUnary := encPair encUnary encUnary

private theorem tagLength_polyTime {α : Type} {enc : α ↪ List Bool}
    {M e : α → ℕ} (hM : ComputableInPolyTime M enc encUnary)
    (he : ComputableInPolyTime e enc encUnary) (q b s : ℕ) :
    ComputableInPolyTime (fun a => tagLength q b s (M a) (e a)) enc encUnary := by
  unfold tagLength
  fun_prop

private theorem tagCount_polyTime {α : Type} {enc : α ↪ List Bool}
    {M e : α → ℕ} (hM : ComputableInPolyTime M enc encUnary)
    (he : ComputableInPolyTime e enc encUnary) (q b s : ℕ) :
    ComputableInPolyTime (fun a => q ^ tagLength q b s (M a) (e a)) enc encUnary := by
  have hlog := (unary_clog_const q).comp hM
  have harg : ComputableInPolyTime (fun a => Nat.clog q (M a) + e a + s * b + 2)
      enc encUnary := by fun_prop
  have hcount := unary_mul'
    (unary_mul' (unary_pow_clog_const hM q q)
      ((unary_pow s).comp (unary_pow_clog_const harg q q)))
    (const (q ^ tagConstant b s))
  refine hcount.of_enc_eq (fun a => congrArg encUnary ?_)
  simp only [tagLength, pow_add, pow_mul, Nat.mul_comm s, Function.comp_apply]

private theorem unary_values_polyBounded {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    (h : ComputableInPolyTime n enc encUnary) : PolyBounded (fun a => (enc a).length) n := by
  simpa only [encUnary_apply, List.length_replicate] using h.polyBounded_length

private abbrev TagFields (q : ℕ) :=
  ℕ × ℕ × ℕ × ℕ × List (List (QWord q)) × List (QWord q)

private def tagFields {q : ℕ} (T : TagTables q) : TagFields q :=
  (T.k, T.m₀, T.mOut, T.labelCount, T.innerCodes, T.outerCode)

private abbrev tagFieldsEncoding (q : ℕ) : TagFields q ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary
    (encPair (encList (encList (wordEncoding q))) (encList (wordEncoding q))))))

/-- Framed public data containing all six fields of the existing tag tables. -/
def tagTablesEncoding (q : ℕ) : TagTables q ↪ List Bool :=
  ⟨fun T => tagFieldsEncoding q (tagFields T), fun a b h => by
    have heq := (tagFieldsEncoding q).injective h
    cases a
    cases b
    simpa [tagFields] using heq⟩

private def maxBin (q n : ℕ) := Nat.clog q (n + 1)

private theorem maxBin_polyTime (q : ℕ) :
    ComputableInPolyTime (maxBin q) encUnary encUnary := by
  unfold maxBin
  fun_prop

private theorem innerCodes_polyTime {q : ℕ} (hq : 2 ≤ q) (b s : ℕ) :
    ComputableInPolyTime (fun p : ℕ × ℕ =>
      (List.range (maxBin q p.1 + 1)).map fun j =>
        greedyTags q b s (tagLength q b s p.2 (maxBin q p.1) + j))
      pairUnary (encList (encList (wordEncoding q))) := by
  have hrows : ComputableInPolyTime (fun p : ℕ × ℕ => List.range (maxBin q p.1 + 1))
      pairUnary (encList encUnary) := by
    have := (maxBin_polyTime q).comp (fst encUnary encUnary)
    fun_prop
  let cap (p : (ℕ × ℕ) × ℕ) := maxBin q p.1.1
  have hcap : ComputableInPolyTime cap (encPair pairUnary encUnary) encUnary :=
    (maxBin_polyTime q).comp ((fst encUnary encUnary).comp (fst pairUnary encUnary))
  have hB := (snd encUnary encUnary).comp (fst pairUnary encUnary)
  let m (p : (ℕ × ℕ) × ℕ) := tagLength q b s p.1.2 (cap p) + min p.2 (cap p)
  have hm : ComputableInPolyTime m (encPair pairUnary encUnary) encUnary := by
    unfold m
    exact unary_add' (tagLength_polyTime hB hcap q b s)
      (unary_min.comp ((snd pairUnary encUnary).prod hcap))
  have hcount : PolyBounded (fun p => (encPair pairUnary encUnary p).length) (fun p => q ^ m p) := by
    have hupper := unary_values_polyBounded
      (unary_mul' (tagCount_polyTime hB hcap q b s)
        (unary_pow_clog_const
          (unary_add' ((fst encUnary encUnary).comp (fst pairUnary encUnary)) (const 1)) q q))
    refine hupper.mono (fun p => ?_)
    unfold m
    rw [pow_add]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.min_le_right _ _))
  have hmap := mapWithInput (f := fun p j => greedyTags q b s (m (p, j)))
    hrows (greedyTags_polyTime_of_length hq b s hm hcount)
  refine hmap.of_enc_eq (fun p => congrArg (encList (encList (wordEncoding q))) ?_)
  apply List.map_congr_left
  intro j hj
  have hle : j ≤ maxBin q p.1 := by have := List.mem_range.mp hj; omega
  simp [m, cap, Nat.min_eq_left hle]

/-- The exact existing table generator, with one fixed machine for each `q`, `b`, and `t`.
Both the block length and the number of labels are supplied as unary inputs. -/
theorem prepareTags_polyTime {q : ℕ} (hq : 2 ≤ q) (b t : ℕ) :
    ComputableInPolyTime (fun p : ℕ × ℕ => prepareTags q b t p.1 p.2)
      (encPair encUnary encUnary) (tagTablesEncoding q) := by
  let s := 2 * t
  have hn := fst encUnary encUnary
  have hB := snd encUnary encUnary
  have hcap := (maxBin_polyTime q).comp hn
  have houterCount := unary_add' hcap (const 1)
  have hm0 := tagLength_polyTime hB hcap q b s
  have hmOut := tagLength_polyTime houterCount (const 0) q b s
  have hk := unary_sub' (unary_sub' hn hm0) hmOut
  have houter := greedyTags_polyTime_of_length hq b s hmOut
    (unary_values_polyBounded (tagCount_polyTime houterCount (const 0) q b s))
  have hfields := hk.prod (hm0.prod (hmOut.prod (hB.prod
    ((innerCodes_polyTime hq b s).prod houter))))
  exact hfields.of_enc_eq (fun _ => rfl)

/-- Return the exact table fields as public bits, using the final theorem's output encoding. -/
theorem prepareTags_bits_polyTime {q : ℕ} (hq : 2 ≤ q) (b t : ℕ) :
    ComputableInPolyTime (fun p : ℕ × ℕ => tagTablesEncoding q (prepareTags q b t p.1 p.2))
      (encPair encUnary encUnary) encBits :=
  (prepareTags_polyTime hq b t).of_enc_eq (fun _ => rfl)

/-- In a unary block-length setup, the label capacity can be computed within the same machine. -/
theorem prepareTags_setup_polyTime {q : ℕ} (hq : 2 ≤ q) (b t : ℕ) {B : ℕ → ℕ}
    (hB : ComputableInPolyTime B encUnary encUnary) :
    ComputableInPolyTime (fun n => tagTablesEncoding q (prepareTags q b t n (B n)))
      encUnary encBits := by
  have hpair : ComputableInPolyTime (fun n : ℕ => (n, B n))
      encUnary (encPair encUnary encUnary) :=
    (id' (encIn := encUnary)).prod hB
  have h := (prepareTags_bits_polyTime hq b t).comp hpair
  simpa only [Function.comp_def] using h

private abbrev symbolEncoding (q : ℕ) : Fin q ↪ List Bool :=
  ⟨fun a => encUnary a.val, fun _ _ h => Fin.ext (encUnary.injective h)⟩

private def symbolDecoder (q : ℕ) : PartialDecoder (symbolEncoding q) := by
  let test (bits : List Bool) (a : Fin q) := decide (symbolEncoding q a = bits)
  refine PartialDecoder.checked (fun bits => (List.finRange q).find? (test bits)) ?_ ?_
  · intro a
    cases h : (List.finRange q).find? (test (symbolEncoding q a)) with
    | none =>
      have hn := List.find?_eq_none.mp h a (by simp)
      exact False.elim (hn (by simp [test]))
    | some b =>
      have hhit : test (symbolEncoding q a) b = true := List.find?_some h
      have hb : symbolEncoding q b = symbolEncoding q a := of_decide_eq_true hhit
      exact congrArg some ((symbolEncoding q).injective hb)
  · have hsymbol := snd encBits (symbolEncoding q)
    have hbits : ComputableInPolyTime (fun p : List Bool × Fin q => symbolEncoding q p.2)
        (encPair encBits (symbolEncoding q)) encBits := hsymbol.of_enc_eq (fun _ => rfl)
    exact findWithInput (test := test) (const _) (hbits.decide_eq' (fst _ _))

private def tagFieldsDecoder (q : ℕ) : PartialDecoder (tagFieldsEncoding q) :=
  let count := PartialDecoder.ofDecoder Decoder.unary
  let word := (symbolDecoder q).list
  let code := word.list
  count.pair (count.pair (count.pair (count.pair (code.list.pair code))))

private def tablesOfFields {q : ℕ} (p : TagFields q) : TagTables q :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩

/-- Parse the framed public bits produced by the table machine. -/
def parseTagTables (q : ℕ) (bits : List Bool) : Option (TagTables q) :=
  ((tagFieldsDecoder q).decode bits).map tablesOfFields

theorem parseTagTables_encoding {q : ℕ} (T : TagTables q) :
    parseTagTables q (tagTablesEncoding q T) = some T := by
  change ((tagFieldsDecoder q).decode (tagFieldsEncoding q (tagFields T))).map _ = some T
  rw [PartialDecoder.decode_enc]
  cases T
  rfl

theorem parseTagTables_polyTime (q : ℕ) :
    ComputableInPolyTime (parseTagTables q) encBits (encOption (tagTablesEncoding q)) := by
  refine (tagFieldsDecoder q).computable.of_enc_eq (fun bits => ?_)
  unfold parseTagTables
  cases (tagFieldsDecoder q).decode bits with
  | none => rfl
  | some fields =>
    obtain ⟨k, m₀, mOut, labelCount, innerCodes, outerCode⟩ := fields
    rfl

#print axioms prepareTags_polyTime
#print axioms prepareTags_bits_polyTime
#print axioms prepareTags_setup_polyTime
#print axioms parseTagTables_encoding
#print axioms parseTagTables_polyTime

end DeletionCode.Explicit.Machine
