import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair

/-! The public word and machine input encodings for the explicit code. -/

namespace DeletionCode.Explicit

open Turing.MultiTapeTM

/-- An alphabet symbol is its unary rank in the fixed alphabet. Each symbol in
a word is framed by the library's list encoding, using at most `2*q+1` bits. -/
def wordEncoding (q : ℕ) : List (Fin q) ↪ List Bool :=
  encList ⟨fun a => encUnary a.val, fun _ _ h => Fin.ext (encUnary.injective h)⟩

/-- Both coding machines receive the setup bits followed by the word, using
the library's self-delimiting pair encoding. -/
def inputEncoding (q : ℕ) : (List Bool × List (Fin q)) ↪ List Bool :=
  encPair encBits (wordEncoding q)

end DeletionCode.Explicit
