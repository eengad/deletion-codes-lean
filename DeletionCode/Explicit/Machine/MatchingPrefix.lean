import DeletionCode.Explicit.MatchingPrefix
import DeletionCode.Explicit.Machine.MatchingPatterns
import DeletionCode.Explicit.Machine.WeightedAddress
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPower

/-! Exact matching prefix counts, uniformly from the unary word length. -/
namespace DeletionCode.Explicit.Machine.MatchingPrefixes

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open MatchingEnumeration _root_.DeletionCode.Explicit.UniformParameters

private abbrev mergeEncoding := encPair positionEncoding edgeEncoding

private theorem mergeLabels_polyTime :
    ComputableInPolyTime (fun x : Labels × (ℕ × ℕ) => mergeLabels x.1 x.2)
      mergeEncoding positionEncoding := by
  have hs := fst positionEncoding edgeEncoding
  have he := snd positionEncoding edgeEncoding
  have hp := fst mergeEncoding encUnary
  have hi := snd mergeEncoding encUnary
  have hl := hs.comp hp
  have ha := listGetDWithInput hl (he.fst'.comp hp) 0
  have hb := listGetDWithInput hl (he.snd'.comp hp) 0
  have hm := mapWithInput (encIn := mergeEncoding) (encA := encUnary)
    (f := fun x i => if i = MatchingEnumeration.labelAt x.1 x.2.2 then MatchingEnumeration.labelAt x.1 x.2.1 else i) hs
    (ite_decide (hi.decide_eq' hb) ha hi)
  exact ite_decide (unary_lt' he.fst' ((length_list encUnary).comp hs)) hm hs

private theorem mergeLabels_bounded (l : ℕ) (xs : Labels) (e : ℕ × ℕ)
    (hlen : xs.length = l) (hvals : ∀ a ∈ xs, a < l) :
    (mergeLabels xs e).length = l ∧ ∀ a ∈ mergeLabels xs e, a < l := by
  unfold mergeLabels
  split_ifs with h
  · refine ⟨by simp [hlen], ?_⟩
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    split_ifs
    · apply hvals
      unfold MatchingEnumeration.labelAt
      rw [List.getD_eq_getElem _ _ h]
      exact List.getElem_mem _
    · exact hvals _ hi
  · exact ⟨hlen,hvals⟩

private abbrev ComponentsInput := ℕ × Edges
private abbrev componentsEncoding := encPair encUnary edgesEncoding

theorem components_polyTime : ComputableInPolyTime (fun x : ComponentsInput => components x.1 x.2)
    componentsEncoding positionEncoding := by
  have hl := fst encUnary edgesEncoding
  have he := snd encUnary edgesEncoding
  let src := encPair (encPair encBool positionEncoding) edgeEncoding
  have hs : ComputableInPolyTime (fun x : (Bool × Labels) × (ℕ × ℕ) => mergeLabels x.1.2 x.2)
      src positionEncoding := mergeLabels_polyTime.comp
        ((fst (encPair encBool positionEncoding) edgeEncoding).snd'.prod
          (snd (encPair encBool positionEncoding) edgeEncoding))
  have hlen : PolyBounded (fun x : ComponentsInput => (componentsEncoding x).length) (fun x => x.1) := by
    simpa only [encUnary_apply,List.length_replicate] using hl.polyBounded_length
  have hsize := hlen.mul (((PolyBounded.const 2).mul hlen).add (PolyBounded.const 1))
  exact (foldlWith_spec (par := fun _ => false) (step := fun _ => mergeLabels)
    (const false) he (range.comp hl) hs
    (fun x _ ls => ls.length = x.1 ∧ ∀ a ∈ ls, a < x.1) (fun _ => by simp)
    (fun x _ ls e _ h => mergeLabels_bounded x.1 ls e h.1 h.2) hsize
    (fun x _ ls _ h => by
      rw [← h.1]
      apply length_encList_le (enc := encUnary)
      intro a ha
      simp only [encUnary_apply,List.length_replicate]
      rw [h.1]
      exact (h.2 _ ha).le)).1

private abbrev ConsistencyInput (q : ℕ) := QWord q × Labels
private abbrev consistencyEncoding (q : ℕ) := encPair (wordEncoding q) positionEncoding

private theorem consistent_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : ConsistencyInput q => consistent pad x.1 x.2)
      (consistencyEncoding q) encBool := by
  let enc := consistencyEncoding q
  let src := encPair enc encUnary
  let arg := encPair src encUnary
  have hp := fst (wordEncoding q) positionEncoding
  have hs := snd (wordEncoding q) positionEncoding
  have hlen := (length_list (symbolEncoding q)).comp hp
  have hxs := (fst enc encUnary).comp (fst src encUnary)
  have hi := (snd enc encUnary).comp (fst src encUnary)
  have hj := snd src encUnary
  have hletters := hp.comp hxs
  have hlabels := hs.comp hxs
  have h₁ := listGetDWithInput hlabels hi 0
  have h₂ := listGetDWithInput hlabels hj 0
  have ha := listGetDWithInput hletters hi pad
  have hb := listGetDWithInput hletters hj pad
  have htest := bool_or' (bool_not.comp (h₁.decide_eq' h₂)) (ha.decide_eq' hb)
  have hrow : ComputableInPolyTime (fun x : ConsistencyInput q × ℕ =>
      (List.range x.1.1.length).all (fun j => decide (MatchingEnumeration.labelAt x.1.2 x.2 ≠ MatchingEnumeration.labelAt x.1.2 j) ||
        decide (x.1.1.getD x.2 pad = x.1.1.getD j pad))) src encBool :=
    allWithInput (encIn := src) (encA := encUnary) (unary_range' (hlen.comp (fst enc encUnary))) htest
  unfold consistent
  exact allWithInput (encIn := enc) (encA := encUnary) (unary_range' hlen) hrow

private abbrev CountInput := (ℕ × ℕ) × Labels
private abbrev countEncoding := encPair (encPair encUnary encUnary) positionEncoding

private theorem freeCount_polyTime :
    ComputableInPolyTime (fun x : CountInput => freeCount x.1.1 x.1.2 x.2) countEncoding encUnary := by
  let src := encPair countEncoding encUnary
  let arg := encPair src encUnary
  have hd := fst (encPair encUnary encUnary) positionEncoding
  have hs := snd (encPair encUnary encUnary) positionEncoding
  have hfirst := fst countEncoding encUnary
  have hi := snd countEncoding encUnary
  have hinner := fst src encUnary
  have hj := snd src encUnary
  have hs' := hs.comp hfirst
  have hh := listGetDWithInput (hs'.comp hinner) hj 0
  have ha := anyWithInput (encIn := src) (encA := encUnary)
    (test := fun x j => decide (MatchingEnumeration.labelAt x.1.2 j = x.2))
    (unary_range' (hd.snd'.comp hfirst)) (hh.decide_eq' (hi.comp hinner))
  unfold freeCount
  exact countPWithInput (encIn := countEncoding) (encA := encUnary)
    (test := fun x i => decide (MatchingEnumeration.labelAt x.2 i = i) &&
      !(List.range x.1.2).any (fun j => decide (MatchingEnumeration.labelAt x.2 j = i)))
    (unary_range' hd.fst')
    (bool_and' ((listGetDWithInput hs' hi 0).decide_eq' hi) (bool_not.comp ha))

private abbrev CompletionInput (q : ℕ) := (ℕ × QWord q) × Edges
private abbrev completionEncoding (q : ℕ) := encPair (encPair encUnary (wordEncoding q)) edgesEncoding

theorem completions_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : CompletionInput q => completions pad x.1.1 x.1.2 x.2)
      (completionEncoding q) encNat := by
  have hp := fst (encPair encUnary (wordEncoding q)) edgesEncoding
  have he := snd (encPair encUnary (wordEncoding q)) edgesEncoding
  have hl := components_polyTime.comp (hp.fst'.prod he)
  have hcheck := (consistent_polyTime pad).comp (hp.snd'.prod hl)
  have hlen := (length_list (symbolEncoding q)).comp hp.snd'
  have hfree := freeCount_polyTime.comp ((hp.fst'.prod hlen).prod hl)
  exact ite hcheck (binary_pow.comp ((const (encOut := encNat) q).prod hfree)) (const 0)

def mass (pad : Fin q) (b t : ℕ) (x : ℕ × QWord q) : ℕ :=
  MatchingEnumeration.prefixMass pad x.1 (windowLength q x.1) (omittedLetters q b t x.1) x.2

theorem mass_polyTime (pad : Fin q) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (mass pad b t) (encPair encUnary (wordEncoding q)) encNat := by
  let e := encPair encUnary (wordEncoding q)
  let arg := encPair e pairEncoding
  have hl := fst encUnary (wordEncoding q)
  have hp := snd encUnary (wordEncoding q)
  have hc := (patternList_polyTime hq hb ht).comp hl
  have hw := (takeUnary (symbolEncoding q)).comp (hp.prod hl)
  have hpack : ComputableInPolyTime (fun x : (ℕ × QWord q) × PositionPair =>
      ((x.1.1,x.1.2.take x.1.1),edges x.2)) arg (completionEncoding q) :=
    ((hl.prod hw).comp (fst e pairEncoding)).prod (edges_polyTime.comp (snd e pairEncoding))
  have hterm := (completions_polyTime pad).comp (encIn := arg) (encMid := completionEncoding q) hpack
  have hlist := mapWithInput (encIn := e) (encA := pairEncoding)
    (f := fun x p => completions pad x.1 (x.2.take x.1) (edges p)) hc hterm
  exact binary_sum.comp hlist

theorem mass_eq (pad : Fin q) (b t ℓ : ℕ) (u : Fin k → Fin q) :
    mass pad b t (ℓ,List.ofFn u) = MatchingWeight.prefixMass (ℓ := ℓ)
      (windowLength q ℓ) (omittedLetters q b t ℓ) u := prefixMass_eq pad u

theorem mass_exact (pad : Fin q) (b t ℓ : ℕ) :
    WeightedAddress.Exact (listWeight (q := q) ℓ (windowLength q ℓ) (omittedLetters q b t ℓ))
      (fun p => mass pad b t (ℓ,p)) ℓ := prefixMass_exact pad ℓ (windowLength q ℓ) (omittedLetters q b t ℓ)

theorem encode_polyTime (pad : Fin q) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (fun x : ℕ × QWord q => WeightedAddress.encode
      (fun p => mass pad b t (x.1,p)) x.2) (encPair encUnary (wordEncoding q)) encNat :=
  WeightedAddresses.encode_polyTime (by omega) (mass_polyTime pad hq hb ht)

theorem decode_polyTime (pad : Fin q) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (fun x : ℕ × (ℕ × ℕ) => WeightedAddress.decode
      (fun p => mass pad b t (x.1,p)) x.2.1 x.2.2)
      (encPair encUnary (encPair encUnary encNat)) (encOption (wordEncoding q)) :=
  WeightedAddresses.decode_polyTime (mass_polyTime pad hq hb ht)

#print axioms components_polyTime
#print axioms mass_eq
#print axioms mass_exact
#print axioms mass_polyTime
#print axioms encode_polyTime
#print axioms decode_polyTime

end DeletionCode.Explicit.Machine.MatchingPrefixes
