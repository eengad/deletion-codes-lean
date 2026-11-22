import DeletionCode.Explicit.MatchingPatterns
import DeletionCode.Explicit.Machine.UniformParameters
import DeletionCode.Explicit.Machine.WordEnumeration
import DeletionCode.Explicit.ParameterSavings

/-! Polynomial enumeration for the manuscript's varying matching parameters. -/
namespace DeletionCode.Explicit.Machine.MatchingPrefixes

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open MatchingEnumeration _root_.DeletionCode.Explicit.UniformParameters

abbrev symbolEncoding (q : ℕ) : Fin q ↪ List Bool :=
  ⟨fun a => encUnary a.val, fun _ _ h => Fin.ext (encUnary.injective h)⟩
abbrev positionEncoding := encList encUnary
abbrev pairEncoding := encPair positionEncoding positionEncoding
abbrev edgeEncoding := encPair encUnary encUnary
abbrev edgesEncoding := encList edgeEncoding

def span (q b t ℓ : ℕ) : ℕ := windowLength q ℓ + 3 * omittedLetters q b t ℓ

private theorem span_polyTime (q b t : ℕ) : ComputableInPolyTime (span q b t) encUnary encUnary :=
  unary_add' (Machine.UniformParameters.window_machine q)
    (unary_mul' (const 3) (Machine.UniformParameters.omitted_machine q b t))

theorem mask_bound (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    PolyBounded (fun ℓ : ℕ => ℓ) (fun ℓ => 2 ^ span q b t ℓ) := by
  let start := minLength q b t
  let B := windowLength q start + 3 * (16 * (edits t)^2 * b * (start+1))
  let C := q^(gramMultiplier t*(b+4))
  refine .of_forall_le (C + 2^B) (gramMultiplier t) ?_
  intro l
  by_cases h : start ≤ l
  · have ha := (basicBounds hq hb ht h).omitted_le
    have hC := multiplier_ge t
    have hL : span q b t l ≤ gram q b t l := by
      unfold span windowLength gram gramLength
      refine (show 3 * eta q l + 4 + 3 * omittedLetters q b t l ≤ 4 * (eta q l + b + 3) by omega).trans ?_
      exact Nat.mul_le_mul_right _ (by omega)
    have hstart : 1 < start := by
      unfold start minLength
      exact Nat.one_lt_pow (by positivity) hq
    calc
      2 ^ span q b t l ≤ q ^ span q b t l := Nat.pow_le_pow_left hq _
      _ ≤ q ^ gram q b t l := Nat.pow_le_pow_right (by omega) hL
      _ ≤ C * l^(gramMultiplier t) := gram_dictionary_bound hq (hstart.trans_le h)
      _ ≤ (C+2^B) * (l+1)^(gramMultiplier t) :=
        Nat.mul_le_mul (Nat.le_add_right ..) (Nat.pow_le_pow_left (Nat.le_succ _) _)
  · have hη : eta q l ≤ eta q start := Nat.clog_mono_right _ (by omega)
    have hr : componentCutoff q b t l ≤ start :=
      (Nat.div_le_self ..).trans ((Nat.log_le_self 2 l).trans (by omega))
    have hb' : span q b t l ≤ B := by
      unfold B span windowLength omittedLetters
      exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left _ hη) _)
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right hr _)))
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb').trans
      ((Nat.le_add_left ..).trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))))

theorem uniform_pattern_bound (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    PolyBounded (fun ℓ : ℕ => ℓ) (fun ℓ =>
      (patternList ℓ (windowLength q ℓ) (omittedLetters q b t ℓ)).length) := by
  refine (PolyBounded.self.pow 2 |>.mul ((mask_bound hq hb ht).pow 2)).mono ?_
  intro l
  have he := patternList_length_le (ℓ := l) (Λ := omittedLetters q b t l)
    (K := windowLength q l) (by unfold windowLength; omega)
  simpa only [span, ← pow_mul, Nat.mul_comm _ 2] using he

private theorem selected_polyTime :
    ComputableInPolyTime (fun x : ℕ × QWord 2 => selected x.1 x.2)
      (encPair encUnary (wordEncoding 2)) positionEncoding := by
  let src := encPair encUnary (wordEncoding 2)
  have ha := fst encUnary (wordEncoding 2)
  have hb := snd encUnary (wordEncoding 2)
  have hi := snd src encUnary
  have hg := listGetDWithInput (hb.comp (fst src encUnary)) hi (0 : Fin 2)
  have hl := filterWithInput (test := fun x i => decide (x.2.getD i 0 = 1))
    (range.comp ((length_list (symbolEncoding 2)).comp hb)) (hg.decide_eq' (const 1))
  have ht := mapWithInput (f := fun x i => x.1+1+i) hl
    (unary_add' (unary_add' (ha.comp (fst src encUnary)) (const 1)) hi)
  exact cons' ha ht

private theorem admissible_polyTime :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × Positions => admissible x.1.1 x.1.2 x.2)
      (encPair (encPair encUnary encUnary) positionEncoding) encBool := by
  let e := encPair (encPair encUnary encUnary) positionEncoding
  have hp := fst (encPair encUnary encUnary) positionEncoding
  have hw := snd (encPair encUnary encUnary) positionEncoding
  have hs := allWithInput (test := fun x i => decide (i < x.1.1)) hw
    (unary_lt' (snd e encUnary) (hp.fst'.comp (fst e encUnary)))
  exact bool_and' (((length_list encUnary).comp hw).decide_eq' hp.snd') hs

private theorem positionLists_polyTime (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (fun l => positionLists l (windowLength q l) (span q b t l))
      encUnary (encList positionEncoding) := by
  let src := encPair encUnary encUnary
  have hn := unary_sub' (span_polyTime q b t) (const 1)
  have hb' := (mask_bound hq hb ht).mono (fun l =>
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.sub_le (span q b t l) 1))
  have hw := wordsOfLength_polyTime (q := 2) (by decide) hn
    (by simpa only [encUnary_apply, List.length_replicate] using hb')
  have ha := fst encUnary encUnary
  have hsel : ComputableInPolyTime (fun x : (ℕ × ℕ) × QWord 2 => selected x.1.2 x.2)
      (encPair src (wordEncoding 2)) positionEncoding :=
    selected_polyTime.comp (((snd encUnary encUnary).comp (fst src (wordEncoding 2))).prod
      (snd src (wordEncoding 2)))
  have hm := mapWithInput (encIn := src) (encA := wordEncoding 2)
    (f := fun (x : ℕ × ℕ) w => selected x.2 w) (hw.comp ha) hsel
  have hg := filterWithInput (test := fun x w => admissible x.1 (windowLength q x.1) w) hm (by
    have hh := ha.comp (fst src positionEncoding)
    exact admissible_polyTime.comp ((hh.prod ((Machine.UniformParameters.window_machine q).comp hh)).prod
      (snd src positionEncoding)))
  have hf := flatMapWithInput (f := fun l a =>
    ((wordsOfLength 2 (span q b t l - 1)).map (selected a)).filter (admissible l (windowLength q l)))
    range hg
  exact hf.of_enc_eq (fun l => by simp [positionLists, windowLength])

theorem edges_polyTime : ComputableInPolyTime edges pairEncoding edgesEncoding := by
  have hf := fst positionEncoding positionEncoding
  have hg := snd positionEncoding positionEncoding
  have hj := snd pairEncoding encUnary
  have hl := length_list encUnary
  have hn := unary_min.comp ((hl.comp hf).prod (hl.comp hg))
  unfold edges
  exact mapWithInput (encA := encUnary) (f := fun p j => (p.1.getD j 0,p.2.getD j 0)) (range.comp hn)
    ((listGetDWithInput (hf.comp (fst pairEncoding encUnary)) hj 0).prod
      (listGetDWithInput (hg.comp (fst pairEncoding encUnary)) hj 0))

private theorem distinct_polyTime : ComputableInPolyTime distinct pairEncoding encBool := by
  have he := snd pairEncoding edgeEncoding
  exact allWithInput (test := fun _ e => decide (e.1 ≠ e.2)) edges_polyTime
    (bool_not.comp (he.fst'.decide_eq' he.snd'))

theorem patternList_polyTime (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (fun l => patternList l (windowLength q l) (omittedLetters q b t l))
      encUnary (encList pairEncoding) := by
  let src := encPair encUnary positionEncoding
  let xs (l : ℕ) := positionLists l (windowLength q l) (span q b t l)
  have h := positionLists_polyTime hq hb ht
  have ha := fst encUnary positionEncoding
  have hs := mapWithInput (f := fun x g => (x.2,g)) (h.comp ha)
    (((snd encUnary positionEncoding).comp (fst src positionEncoding)).prod (snd src positionEncoding))
  have hpair := flatMapWithInput (f := fun l f => (xs l).map fun g => (f,g)) h hs
  exact filterWithInput (test := fun _ p => distinct p) hpair
    (distinct_polyTime.comp (snd encUnary pairEncoding))

#print axioms patternList_polyTime
#print axioms uniform_pattern_bound

end DeletionCode.Explicit.Machine.MatchingPrefixes
