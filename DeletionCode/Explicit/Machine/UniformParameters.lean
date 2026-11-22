import DeletionCode.Explicit.UniformParameters
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Choose
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPower

/-! One machine emits the exact length-dependent parameter tuple. -/
namespace DeletionCode.Explicit.Machine.UniformParameters

open DeletionCode.Explicit.UniformParameters
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable (q b t : ℕ)

private theorem eta_machine : ComputableInPolyTime (eta q) encUnary encUnary :=
  unary_clog_const q

theorem gram_machine : ComputableInPolyTime (gram q b t) encUnary encUnary :=
  unary_mul' (const (gramMultiplier t))
    (unary_add' (unary_add' (eta_machine q) (const b)) (const 3))

theorem cutoff_machine :
    ComputableInPolyTime (componentCutoff q b t) encUnary encUnary :=
  unary_div' unary_log_two
    (unary_mul' (const (reciprocal q b t)) ((unary_clog_const 2).comp (gram_machine q b t)))

theorem window_machine : ComputableInPolyTime (windowLength q) encUnary encUnary :=
  unary_add' (unary_mul' (const 3) (eta_machine q)) (const 4)

private theorem witness_machine :
    ComputableInPolyTime (witnessLimit q b t) encUnary encUnary :=
  unary_add' (unary_mul' (const (8 * edits t)) (cutoff_machine q b t)) (const 1)

theorem omitted_machine :
    ComputableInPolyTime (omittedLetters q b t) encUnary encUnary :=
  unary_mul' (const (16 * (edits t)^2 * b))
    (unary_add' (cutoff_machine q b t) (const 1))

private theorem local_machine :
    ComputableInPolyTime (localOmitted q b t) encUnary encUnary :=
  unary_mul' (const (14 * edits t * b)) (cutoff_machine q b t)

theorem width_machine :
    ComputableInPolyTime (hashWidth q b t) encUnary encUnary :=
  (unary_clog_const 3).comp (unary_mul' (unary_pow (edits t - 1))
    ((unary_pow (hashExponent q b t)).comp (gram_machine q b t)))

private theorem three_pow_machine :
    ComputableInPolyTime (fun k : ℕ => 3^k) encUnary encNat := by
  have h : ComputableInPolyTime (fun k : ℕ => (3, k)) encUnary
      (encPair encNat encUnary) := (const (3 : ℕ)).prod id'
  exact binary_pow.comp h

private theorem count_machine :
    ComputableInPolyTime (hashCount q b t) encUnary encNat :=
  three_pow_machine.comp (width_machine q b t)

private theorem gamma_machine :
    ComputableInPolyTime (gamma q b t) encUnary encNat := by
  have he := unary_mul' (const (edits t)) (witness_machine q b t)
  have he1 := unary_add' he (const 1)
  have hg := unary_add' (gram_machine q b t) (const 1)
  have hbase := unary_mul' (unary_mul' (const 100) he1) hg
  have hp := binary_pow.comp ((unary_to_binary.comp hbase).prod (unary_mul' (const 20) he))
  have hq := binary_pow.comp
    ((const (encOut := encNat) q).prod (unary_mul' (const (4 * b)) he))
  exact binary_mul' (binary_mul' (unary_to_binary.comp he1) hp) hq

private theorem family_machine :
    ComputableInPolyTime (families q b t) encUnary encNat := by
  have hΛ := omitted_machine q b t
  have hs := unary_add' (unary_add' (gram_machine q b t) (const b)) (const 1)
  have hp := (unary_pow 3).comp hs
  have hbase := unary_mul' (const (3*q)) hs
  have hpow := binary_pow.comp ((unary_to_binary.comp hbase).prod hΛ)
  exact binary_mul'
    (binary_mul' (binary_mul' (binary_mul' (const 12) (unary_to_binary.comp hp))
      (const (q^(2*b)))) (unary_to_binary.comp (unary_add' hΛ (const 1)))) hpow

private theorem match_machine :
    ComputableInPolyTime (matchBound q b t) encUnary encNat := by
  have hK := window_machine q
  have hc := binary_choose' (unary_add' hK (unary_mul' (const 3) (omitted_machine q b t))) hK
  exact binary_pow.comp (hc.prod (const 2))

/-- All varying fields use binary output. The threshold in the ceiling
logarithm for `θ` is computed in unary internally, with fixed exponents;
the much larger replay and family bounds are computed in binary. -/
theorem values_polyTime :
    ComputableInPolyTime (values q b t) encUnary (encList encNat) := by
  unfold values
  exact cons' (unary_to_binary.comp (eta_machine q))
    (cons' (unary_to_binary.comp (window_machine q))
    (cons' (unary_to_binary.comp (gram_machine q b t))
    (cons' (unary_to_binary.comp (cutoff_machine q b t))
    (cons' (unary_to_binary.comp (witness_machine q b t))
    (cons' (unary_to_binary.comp (omitted_machine q b t))
    (cons' (unary_to_binary.comp (local_machine q b t))
    (cons' (unary_to_binary.comp (width_machine q b t))
    (cons' (count_machine q b t)
    (cons' (gamma_machine q b t)
    (cons' (family_machine q b t)
    (cons' (match_machine q b t) (const []))))))))))))

#print axioms values_polyTime

end DeletionCode.Explicit.Machine.UniformParameters
