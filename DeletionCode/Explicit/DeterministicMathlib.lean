import DeletionCode.Explicit.Statement
import DeletionCode.Explicit.DeterministicTM2
import Mathlib.Computability.Encoding

/-! The standalone theorem follows from the existing Mathlib machine certificates. -/
namespace DeletionCode.Explicit

open Turing.MultiTapeTM

theorem unaryCode_eq : unaryCode = ⇑encUnary := rfl

/-- `unaryCode` is Mathlib's unary encoding of a natural number. -/
theorem unaryCode_eq_unaryEncodeNat : unaryCode = Computability.unaryEncodeNat := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [unaryCode, List.replicate_succ, Computability.unaryEncodeNat, ← ih, unaryCode]

theorem framed_eq : framed = frame := rfl

theorem wordCode_eq (q : ℕ) : wordCode q = ⇑(wordEncoding q) := rfl

theorem inputCode_eq (q : ℕ) : inputCode q = ⇑(inputEncoding q) := rfl

theorem encBits_eq : ⇑encBits = (fun bits : List Bool => bits) := rfl

theorem unaryCode_injective : Function.Injective unaryCode := unaryCode_eq ▸ encUnary.injective

theorem framed_injective : Function.Injective framed := framed_eq ▸ frame_injective

theorem wordCode_injective (q : ℕ) : Function.Injective (wordCode q) :=
  wordCode_eq q ▸ (wordEncoding q).injective

theorem inputCode_injective (q : ℕ) : Function.Injective (inputCode q) :=
  inputCode_eq q ▸ (inputEncoding q).injective

/-- Change the names of the encodings while preserving the three machine witnesses. -/
theorem statement_machines_of_tm2 {q : ℕ} {setup : ℕ → List Bool}
    {encode decode : List Bool × List (Fin q) → List (Fin q)}
    (hsetup : ∃ h : Turing.TM2ComputableInPolyTime encUnary encBits setup,
      ∀ stack, Finite (h.tm.Γ stack))
    (hencode : ∃ h : Turing.TM2ComputableInPolyTime (inputEncoding q) (wordEncoding q) encode,
      ∀ stack, Finite (h.tm.Γ stack))
    (hdecode : ∃ h : Turing.TM2ComputableInPolyTime (inputEncoding q) (wordEncoding q) decode,
      ∀ stack, Finite (h.tm.Γ stack)) :
    (∃ h : Turing.TM2ComputableInPolyTime unaryCode (fun bits : List Bool => bits) setup,
      ∀ stack, Finite (h.tm.Γ stack)) ∧
    (∃ h : Turing.TM2ComputableInPolyTime (inputCode q) (wordCode q) encode,
      ∀ stack, Finite (h.tm.Γ stack)) ∧
    (∃ h : Turing.TM2ComputableInPolyTime (inputCode q) (wordCode q) decode,
      ∀ stack, Finite (h.tm.Γ stack)) := by
  rw [unaryCode_eq, ← encBits_eq, inputCode_eq, wordCode_eq]
  exact ⟨hsetup, hencode, hdecode⟩

/-- The deterministic theorem stated using Mathlib and the standalone channel and encodings. -/
theorem deterministic_mathlib : DeterministicStatement := by
  intro t b q ht hb hq
  obtain ⟨C, d, n₀, k, setup, encode, decode, hsetup, hencode, hdecode, hspec⟩ :=
    deterministic_tm2 t b q ht hb hq
  obtain ⟨hsetup', hencode', hdecode'⟩ := statement_machines_of_tm2 hsetup hencode hdecode
  exact ⟨C, d, n₀, k, setup, encode, decode, hsetup', hencode', hdecode', hspec⟩

#print axioms unaryCode_eq
#print axioms unaryCode_eq_unaryEncodeNat
#print axioms framed_eq
#print axioms wordCode_eq
#print axioms inputCode_eq
#print axioms encBits_eq
#print axioms unaryCode_injective
#print axioms framed_injective
#print axioms wordCode_injective
#print axioms inputCode_injective
#print axioms statement_machines_of_tm2
#print axioms deterministic_mathlib
#print axioms deterministic_tm2
#print axioms deterministic

end DeletionCode.Explicit
