import DeletionCode.Qary.Windows
import DeletionCode.Qary.CatalogueWords

/-!
The bounded substring-replacement channel. Each operation replaces one block
by another; either block may be empty, and successive operations may overlap.
The operation count measures whole replacements, independently of their lengths.
-/
namespace DeletionCode.Burst

abbrev Word (α : Type*) := List α
abbrev Letters (α : Type*) := Qary.Windows.Letters α

def windowLength (k b : ℕ) : ℕ := 3 * (k + b + 1)

structure Edit (α : Type*) where
  pos : ℕ
  removed : ℕ
  replacement : List α
  deriving DecidableEq, Repr

namespace Edit

variable {α : Type*}

def Bounded (b : ℕ) (e : Edit α) : Prop :=
  e.removed ≤ b ∧ e.replacement.length ≤ b

def InBounds (e : Edit α) (n : ℕ) : Prop := e.pos + e.removed ≤ n

def sourceBlock (e : Edit α) (x : Word α) : Word α :=
  (x.drop e.pos).take e.removed

def Valid (b : ℕ) (e : Edit α) (x : Word α) : Prop :=
  e.Bounded b ∧ e.InBounds x.length ∧ e.sourceBlock x ≠ e.replacement

def apply (e : Edit α) (x : Word α) : Word α :=
  x.take e.pos ++ e.replacement ++ x.drop (e.pos + e.removed)

def outputLength (e : Edit α) (n : ℕ) : ℕ :=
  n - e.removed + e.replacement.length

def origin (e : Edit α) (i : ℕ) : Option ℕ :=
  if i < e.pos then some i
  else if i < e.pos + e.replacement.length then none
  else some (i + e.removed - e.replacement.length)

def word [Inhabited α] (e : Edit α) (x : Letters α) : Letters α :=
  fun i => if i < e.pos then x i
    else if i < e.pos + e.replacement.length then
      e.replacement.getD (i - e.pos) default
    else x (i + e.removed - e.replacement.length)

end Edit

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

def Confusable {α : Type*} (b t : ℕ) (x y : Word α) : Prop :=
  ∃ output, WithinBursts b t x output ∧ WithinBursts b t y output

end DeletionCode.Burst
