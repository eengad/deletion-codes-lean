import Mathlib.Data.List.Basic

/-!
The bounded substring-replacement channel. Each operation replaces one block
by another; either block may be empty, and successive operations may overlap.
The operation count measures whole replacements, independently of their lengths.
-/
namespace DeletionCode.Burst

abbrev Word (α : Type*) := List α

/-- A history of exactly r nontrivial replacements, each bounded by b.
No separation condition is imposed on the channel. -/
inductive Script {α : Type*} (b : ℕ) : Word α → Word α → ℕ → Prop
  | refl (x : Word α) : Script b x x 0
  | step {x pre suffix U V : Word α} {r : ℕ}
      (hU : U.length ≤ b) (hV : V.length ≤ b) (hne : U ≠ V)
      (history : Script b x (pre ++ U ++ suffix) r) :
      Script b x (pre ++ V ++ suffix) (r + 1)

def WithinBursts {α : Type*} (b t : ℕ) (x y : Word α) : Prop :=
  ∃ r, r ≤ t ∧ Script b x y r

end DeletionCode.Burst
