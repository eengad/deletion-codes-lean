import DeletionCode.Explicit.AcceptanceWeights

/-! Uniform machines for the matching and exceptional acceptance conditions. -/
namespace DeletionCode.Explicit.Machine.AcceptanceWeights

open _root_.DeletionCode.Explicit.AcceptanceWeights
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open MatchingPrefixes (symbolEncoding)

variable {q b t : ℕ}

abbrev WindowInput (q : ℕ) := (ℕ × ℕ) × QWord q
abbrev windowEncoding (q : ℕ) := encPair (encPair encUnary encUnary) (wordEncoding q)

theorem window_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : WindowInput q => window x.1.1 x.1.2 x.2)
      (windowEncoding q) (wordEncoding q) := by
  have hk := (fst (encPair encUnary encUnary) (wordEncoding q)).fst'
  have hi := (fst (encPair encUnary encUnary) (wordEncoding q)).snd'
  have hw := snd (encPair encUnary encUnary) (wordEncoding q)
  exact (takeUnary (symbolEncoding q)).comp ((listDropWithInput hw hi).prod hk)

private abbrev PairScan (q : ℕ) := (WindowInput q × ℕ) × ℕ
private abbrev scanEncoding (q : ℕ) := encPair (encPair (windowEncoding q) encUnary) encUnary

private def uniquePair (x : PairScan q) : Bool :=
  let ℓ := x.1.1.1.1
  let K := x.1.1.1.2
  let w := x.1.1.2
  let i := x.1.2
  let j := x.2
  (decide (i = j) || decide (ℓ < i+K)) || (decide (ℓ < j+K) || decide (window K i w ≠ window K j w))

private theorem uniquePair_polyTime (q : ℕ) :
    ComputableInPolyTime (uniquePair (q := q)) (scanEncoding q) encBool := by
  let src := scanEncoding q
  let e := windowEncoding q
  have hx := (fst e encUnary).comp (fst (encPair e encUnary) encUnary)
  have hi := (snd e encUnary).comp (fst (encPair e encUnary) encUnary)
  have hj := snd (encPair e encUnary) encUnary
  have hl := hx.fst'.fst'
  have hK := hx.fst'.snd'
  have hw := hx.snd'
  have hai : ComputableInPolyTime (fun x : PairScan q => ((x.1.1.1.2,x.1.2),x.1.1.2)) src e :=
    (hK.prod hi).prod hw
  have haj : ComputableInPolyTime (fun x : PairScan q => ((x.1.1.1.2,x.2),x.1.1.2)) src e :=
    (hK.prod hj).prod hw
  have hwi := (window_polyTime q).comp (encIn := src) (encMid := e) hai
  have hwj := (window_polyTime q).comp (encIn := src) (encMid := e) haj
  exact bool_or' (bool_or' (hi.decide_eq' hj) (unary_lt' hl (unary_add' hi hK)))
    (bool_or' (unary_lt' hl (unary_add' hj hK)) (bool_not.comp (hwi.decide_eq' hwj)))

theorem uniqueWindows_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : WindowInput q => uniqueWindows x.1.1 x.1.2 x.2)
      (windowEncoding q) encBool := by
  let e := windowEncoding q
  have hl := (fst (encPair encUnary encUnary) (wordEncoding q)).fst'
  have h := unary_range' (unary_add' hl (const 1))
  unfold uniqueWindows
  exact allWithInput (encIn := e) (encA := encUnary)
    (test := fun x i => (List.range (x.1.1+1)).all fun j => uniquePair ((x,i),j)) h
    (allWithInput (encIn := encPair e encUnary) (encA := encUnary)
      (test := fun x j => uniquePair (x,j)) (h.comp (fst e encUnary)) (uniquePair_polyTime q))

theorem strong_polyTime (pad : Fin q) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (fun x : ℕ × QWord q => strong pad b t x.1 x.2)
      (encPair encUnary (wordEncoding q)) encBool :=
  (MatchingPrefixes.mass_polyTime pad hq hb ht).decide_eq' (const 0)

theorem exceptional_polyTime (pad : Fin q) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : ℕ × (Ternary.Rows × QWord q) => exceptional pad b t x.1 x.2.1 x.2.2)
      (CataloguePrefix.exceptionalPrefixEncoding q) encBool := by
  let e := CataloguePrefix.exceptionalPrefixEncoding q
  have hl := fst encUnary (encPair Ternary.rowsEncoding (wordEncoding q))
  have hw := (snd encUnary (encPair Ternary.rowsEncoding (wordEncoding q))).snd'
  have hs : ComputableInPolyTime (fun x : ℕ × (Ternary.Rows × QWord q) =>
      ((x.1, _root_.DeletionCode.Explicit.UniformParameters.windowLength q x.1),x.2.2))
      e (windowEncoding q) := (hl.prod ((Machine.UniformParameters.window_machine q).comp hl)).prod hw
  have hu := (uniqueWindows_polyTime q).comp (encIn := e) (encMid := windowEncoding q) hs
  exact bool_and' hu (binary_lt' (const 0) (CataloguePrefix.exceptionalPrefixMass_polyTime pad b t hq))

#print axioms uniqueWindows_polyTime
#print axioms strong_polyTime
#print axioms exceptional_polyTime

end DeletionCode.Explicit.Machine.AcceptanceWeights
