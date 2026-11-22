import DeletionCode.Explicit.ExceptionalWeight
import DeletionCode.Explicit.Machine.TernaryPotential
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPower

/-! Conditional means on a serialized exceptional-record catalogue. -/
namespace DeletionCode.Explicit.Machine.Ternary

open FieldHash
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- The row is the spectrum difference. The unary natural counts its
entry's prescribed positions. -/
abbrev ExceptionalRow := Row × ℕ
abbrev exceptionalRowEncoding := encPair rowEncoding encUnary
abbrev ExceptionalInput := (ℕ × PartialRows) × List ExceptionalRow
abbrev exceptionalEncoding := encPair partialHashEncoding (encList exceptionalRowEncoding)

private def exceptionalTerm (q : ℕ) (p : (ℕ × PartialRows) × ExceptionalRow) : ℚ :=
  conditional ((p.1.1, [p.2.1]), p.1.2) / (q : ℚ)^p.2.2

private theorem exceptionalTerm_polyTime (q : ℕ) :
    ComputableInPolyTime (exceptionalTerm q) (encPair partialHashEncoding exceptionalRowEncoding)
      encRat := by
  have hh := fst partialHashEncoding exceptionalRowEncoding
  have hr := snd partialHashEncoding exceptionalRowEncoding
  have hm := hh.fst'.prod (cons' hr.fst' (const []))
  have hp := ratOfNat_polyTime.comp (binary_pow.comp ((const (encOut := encNat) q).prod hr.snd'))
  have hp' : ComputableInPolyTime
      (fun p : (ℕ × PartialRows) × ExceptionalRow => (q : ℚ)^p.2.2)
      (encPair partialHashEncoding exceptionalRowEncoding) encRat := by
    simpa only [Function.comp_def, Nat.cast_pow] using hp
  exact rat_div' (conditional_polyTime.comp (hm.prod hh.snd')) hp'

def exceptionalConditional (q : ℕ) (p : ExceptionalInput) : ℚ :=
  (p.2.map fun row => exceptionalTerm q (p.1, row)).sum

theorem exceptionalConditional_polyTime (q : ℕ) :
    ComputableInPolyTime (exceptionalConditional q) exceptionalEncoding encRat := by
  have h := mapWithInput (f := fun (p : ExceptionalInput) row => exceptionalTerm q (p.1, row))
    (snd partialHashEncoding (encList exceptionalRowEncoding))
    ((exceptionalTerm_polyTime q).comp
      ((fst exceptionalEncoding exceptionalRowEncoding).fst'.prod
        (snd exceptionalEncoding exceptionalRowEncoding)))
  exact ratSum_polyTime.comp h

theorem exceptionalConditional_eq {m ℓ q n : ℕ} (p : PartialRows)
    (C : Fin m → ExceptionalWeight.Entry ℓ q n) (rs : Fin m → ExceptionalRow)
    (hrow : ∀ j, rowOf n (rs j).1 = (C j).changeVector)
    (hcount : ∀ j, (rs j).2 = (C j).assignment.support.card) :
    exceptionalConditional q ((n, p), List.ofFn rs) =
      ExceptionalWeight.conditionalMass C (hashOf n p) := by
  unfold exceptionalConditional ExceptionalWeight.conditionalMass CoreWeight.conditionalMass
  simp only [List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  change conditional ((n, [(rs j).1]), p) / (q : ℚ)^(rs j).2 = _
  rw [conditional_eq, hcount]
  have hm : matrixOf (n, [(rs j).1]) = (C j).object.rules := by
    funext i k
    rw [Fin.eq_zero i]
    exact congrFun (hrow j) k
  rw [hm]
  rfl

#print axioms exceptionalConditional_polyTime
#print axioms exceptionalConditional_eq

end DeletionCode.Explicit.Machine.Ternary
