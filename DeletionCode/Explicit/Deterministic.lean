import DeletionCode.Burst.Basic
import DeletionCode.Explicit.DeterministicEncodings
import DeletionCode.Explicit.Machine.SourceCallbacks
import DeletionCode.Explicit.Machine.SourceSetupTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The review statement for manuscript Theorem `thm:deterministic`. -/

namespace DeletionCode.Explicit

open Turing.MultiTapeTM

/-- Provisional form B. The three machines run in polynomial time in the
length of their encoded inputs. Unary setup input, polynomial public data,
and fixed alphabet and edit parameters make these bounds polynomial in
block length on the displayed inputs. The decoder's value away from
admissible received words is unrestricted. -/
theorem deterministic (t b q : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) (hq : 2 ≤ q) :
    ∃ (C d n₀ : ℕ) (k : ℕ → ℕ) (setup : ℕ → List Bool)
      (encode decode : List Bool × List (Fin q) → List (Fin q)),
      ComputableInPolyTime setup encUnary encBits ∧
      ComputableInPolyTime encode (inputEncoding q) (wordEncoding q) ∧
      ComputableInPolyTime decode (inputEncoding q) (wordEncoding q) ∧
      ∀ n ≥ n₀,
        (setup n).length ≤ C * n ^ d ∧ k n ≤ n ∧
        (n : ℝ) - (k n : ℝ) ≤
          (2 * (t : ℝ) - 1) * Real.logb q n +
            C * Real.logb q (Real.logb q n) ∧
        ∀ u : List (Fin q), u.length = k n →
          let x := encode (setup n, u)
          x.length = n ∧
            ∀ z, Burst.WithinBursts b t x z → decode (setup n, z) = u := by
  let pad : Fin q := ⟨0, by omega⟩
  exact Machine.deterministic_of_source t b q (UniformParameters.gramMultiplier t)
    (UniformParameters.hashExponent q b t) (UniformParameters.minLength q b t) 0 ht hq
    (SourceSetup.sourceBits q b t pad) (SourceSetup.sourceCallbacks (by omega) b t pad)
    (Machine.SourceSetupTime.sourceBits_polyTime pad b t hq hb ht)
    (Machine.SourceCallbacks.certified pad b t hq hb ht)
    (fun n _ => SourceSetup.sourceGuarantees hq hb ht pad n)

#print axioms deterministic

end DeletionCode.Explicit
