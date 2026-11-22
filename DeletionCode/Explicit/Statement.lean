import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.TuringMachine.Computable
import DeletionCode.Burst.Channel

namespace DeletionCode.Explicit

/-!
The encodings are spelled out here so that this file can be read on its own.
Mathlib has `Computability.unaryEncodeNat`, which equals `unaryCode`, and encodings of
lists and pairs, `encodingList` and `encodingProd`. Those two write a word in its own
alphabet and a pair in a sum alphabet. The three machines below read and write bits,
so the word and the pair are written in bits here.
-/

/-- Encode a natural by that many `true` bits. -/
def unaryCode (n : ℕ) : List Bool := List.replicate n true

/-- Prefix each bit by `true` and end the frame with `false`. -/
def framed (w : List Bool) : List Bool := w.flatMap (fun b => [true, b]) ++ [false]

/-- Concatenate the framed unary codes of the letters of a word. -/
def wordCode (q : ℕ) (w : List (Fin q)) : List Bool :=
  w.flatMap (fun a => framed (unaryCode a.val))

/-- Frame the setup bits, then append the encoded word. -/
def inputCode (q : ℕ) (p : List Bool × List (Fin q)) : List Bool := framed p.1 ++ wordCode q p.2

-- Three is represented in unary.
example : unaryCode 3 = [true, true, true] := rfl
-- The final `false` terminates the frame after both payload bits.
example : framed [true, false] = [true, true, true, false, false] := rfl
-- The middle letter contributes only its frame terminator.
example : wordCode 3 [2, 0, 1] = [true, true, true, true, false, false, true, true, false] := rfl
-- The first three bits frame the setup bit.
example : inputCode 3 ([false], [1]) = [true, false, false, true, true, false] := rfl

/-- The deterministic code and its three polynomial-time Mathlib stack machines. -/
def DeterministicStatement : Prop :=
  ∀ (t b q : ℕ), 2 ≤ t → 1 ≤ b → 2 ≤ q →
    ∃ (C d n₀ : ℕ) (k : ℕ → ℕ) (setup : ℕ → List Bool)
      (encode decode : List Bool × List (Fin q) → List (Fin q)),
      (∃ h : Turing.TM2ComputableInPolyTime unaryCode (fun bits : List Bool => bits) setup,
        ∀ stack, Finite (h.tm.Γ stack)) ∧
      (∃ h : Turing.TM2ComputableInPolyTime (inputCode q) (wordCode q) encode,
        ∀ stack, Finite (h.tm.Γ stack)) ∧
      (∃ h : Turing.TM2ComputableInPolyTime (inputCode q) (wordCode q) decode,
        ∀ stack, Finite (h.tm.Γ stack)) ∧
      ∀ n ≥ n₀,
        (setup n).length ≤ C * n ^ d ∧ k n ≤ n ∧
        (n : ℝ) - (k n : ℝ) ≤
          (2 * (t : ℝ) - 1) * Real.logb q n +
            C * Real.logb q (Real.logb q n) ∧
        ∀ u : List (Fin q), u.length = k n →
          let x := encode (setup n, u)
          x.length = n ∧
            ∀ z, Burst.WithinBursts b t x z → decode (setup n, z) = u

end DeletionCode.Explicit
