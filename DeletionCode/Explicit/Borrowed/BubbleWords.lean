import DeletionCode.Burst.Basic

/-!
Local-word grammar for substring replacements. The two central blocks may
have different lengths and either may be empty. Common boundary windows and
path geometry are proved separately for the actual local construction.
-/
namespace DeletionCode.Explicit.Borrowed

open DeletionCode.Burst

structure BubbleWord (α : Type*) (K b L : ℕ) where
  left : List α
  right : List α
  removed : List α
  replacement : List α
  removed_bound : removed.length ≤ b
  replacement_bound : replacement.length ≤ b
  different : removed ≠ replacement
  left_lower : L - 1 - K - b ≤ left.length
  left_upper : left.length ≤ L - 1
  right_lower : L - 1 - K - b ≤ right.length
  right_upper : right.length ≤ L - 1

namespace BubbleWord

variable {α : Type*} {K b L : ℕ}

def negativeWord (p : BubbleWord α K b L) : Word α := p.left ++ p.removed ++ p.right
def positiveWord (p : BubbleWord α K b L) : Word α := p.left ++ p.replacement ++ p.right

theorem negativeWord_length_bounds (p : BubbleWord α K b L)
    (hwindow : 3 * (K + b + 1) ≤ L) :
    L ≤ p.negativeWord.length ∧
      p.negativeWord.length ≤ 2 * (L - 1) + b := by
  have hl := p.left_lower
  have hr := p.right_lower
  have hl' := p.left_upper
  have hr' := p.right_upper
  have hu := p.removed_bound
  simp only [negativeWord, List.length_append]
  omega

theorem positiveWord_length_bounds (p : BubbleWord α K b L)
    (hwindow : 3 * (K + b + 1) ≤ L) :
    L ≤ p.positiveWord.length ∧
      p.positiveWord.length ≤ 2 * (L - 1) + b := by
  have hl := p.left_lower
  have hr := p.right_lower
  have hl' := p.left_upper
  have hr' := p.right_upper
  have hv := p.replacement_bound
  simp only [positiveWord, List.length_append]
  omega

end BubbleWord
end DeletionCode.Explicit.Borrowed
