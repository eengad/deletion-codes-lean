import DeletionCode.Explicit.Deterministic
import CslibFrontier.Computability.Machines.Turing.TM2.Reverse.Transfer

/-! The Mathlib stack-machine formulation of manuscript Theorem `thm:deterministic`. -/

namespace DeletionCode.Explicit

open Turing.MultiTapeTM

/-- Transfer the three certificates for a fixed choice of setup, encoder, and decoder,
preserving their encodings and certifying a finite alphabet on every stack. -/
theorem tm2_machines_of_polyTime {q : ℕ} {setup : ℕ → List Bool}
    {encode decode : List Bool × List (Fin q) → List (Fin q)}
    (hsetup : ComputableInPolyTime setup encUnary encBits)
    (hencode : ComputableInPolyTime encode (inputEncoding q) (wordEncoding q))
    (hdecode : ComputableInPolyTime decode (inputEncoding q) (wordEncoding q)) :
    (∃ h : Turing.TM2ComputableInPolyTime encUnary encBits setup,
      ∀ stack, Finite (h.tm.Γ stack)) ∧
    (∃ h : Turing.TM2ComputableInPolyTime (inputEncoding q) (wordEncoding q) encode,
      ∀ stack, Finite (h.tm.Γ stack)) ∧
    (∃ h : Turing.TM2ComputableInPolyTime (inputEncoding q) (wordEncoding q) decode,
      ∀ stack, Finite (h.tm.Γ stack)) :=
  ⟨hsetup.exists_tm2ComputableInPolyTime, hencode.exists_tm2ComputableInPolyTime,
    hdecode.exists_tm2ComputableInPolyTime⟩

/-- The deterministic code with polynomial-time certificates on Mathlib stack
machines. All stacks of each machine have finite alphabets. -/
theorem deterministic_tm2 (t b q : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) (hq : 2 ≤ q) :
    ∃ (C d n₀ : ℕ) (k : ℕ → ℕ) (setup : ℕ → List Bool)
      (encode decode : List Bool × List (Fin q) → List (Fin q)),
      (∃ h : Turing.TM2ComputableInPolyTime encUnary encBits setup,
        ∀ stack, Finite (h.tm.Γ stack)) ∧
      (∃ h : Turing.TM2ComputableInPolyTime (inputEncoding q) (wordEncoding q) encode,
        ∀ stack, Finite (h.tm.Γ stack)) ∧
      (∃ h : Turing.TM2ComputableInPolyTime (inputEncoding q) (wordEncoding q) decode,
        ∀ stack, Finite (h.tm.Γ stack)) ∧
      ∀ n ≥ n₀,
        (setup n).length ≤ C * n ^ d ∧ k n ≤ n ∧
        (n : ℝ) - (k n : ℝ) ≤
          (2 * (t : ℝ) - 1) * Real.logb q n +
            C * Real.logb q (Real.logb q n) ∧
        ∀ u : List (Fin q), u.length = k n →
          let x := encode (setup n, u)
          x.length = n ∧
            ∀ z, Burst.WithinBursts b t x z → decode (setup n, z) = u := by
  obtain ⟨C, d, n₀, k, setup, encode, decode, hsetup, hencode, hdecode, hspec⟩ :=
    deterministic t b q ht hb hq
  obtain ⟨hsetup', hencode', hdecode'⟩ := tm2_machines_of_polyTime hsetup hencode hdecode
  exact ⟨C, d, n₀, k, setup, encode, decode, hsetup', hencode', hdecode', hspec⟩

#print axioms Turing.MultiTapeTM.ComputableInPolyTime.exists_tm2ComputableInPolyTime
#print axioms tm2_machines_of_polyTime
#print axioms deterministic_tm2

end DeletionCode.Explicit
