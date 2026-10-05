import DeletionCode.Burst.Basic

/-!
Local-word grammar for substring replacements. The two central blocks may
have different lengths and either may be empty. Common boundary windows and
path geometry are proved separately for the actual local construction.
-/
namespace DeletionCode.Burst

structure BubbleWord (α : Type*) (k b : ℕ) where
  left : List α
  right : List α
  removed : List α
  replacement : List α
  removed_bound : removed.length ≤ b
  replacement_bound : replacement.length ≤ b
  different : removed ≠ replacement
  left_lower : windowLength k b - 1 - k - b ≤ left.length
  left_upper : left.length ≤ windowLength k b - 1
  right_lower : windowLength k b - 1 - k - b ≤ right.length
  right_upper : right.length ≤ windowLength k b - 1

namespace BubbleWord

variable {α : Type*} {k b : ℕ}

def negativeWord (p : BubbleWord α k b) : Word α := p.left ++ p.removed ++ p.right
def positiveWord (p : BubbleWord α k b) : Word α := p.left ++ p.replacement ++ p.right
def edit (p : BubbleWord α k b) : Edit α := ⟨p.left.length, p.removed.length, p.replacement⟩

theorem negativeWord_length_bounds (p : BubbleWord α k b) :
    windowLength k b ≤ p.negativeWord.length ∧
      p.negativeWord.length ≤ 2 * (windowLength k b - 1) + b := by
  have hl := p.left_lower
  have hr := p.right_lower
  have hl' := p.left_upper
  have hr' := p.right_upper
  have hu := p.removed_bound
  simp only [negativeWord, List.length_append]
  unfold windowLength at *
  omega

theorem positiveWord_length_bounds (p : BubbleWord α k b) :
    windowLength k b ≤ p.positiveWord.length ∧
      p.positiveWord.length ≤ 2 * (windowLength k b - 1) + b := by
  have hl := p.left_lower
  have hr := p.right_lower
  have hl' := p.left_upper
  have hr' := p.right_upper
  have hv := p.replacement_bound
  simp only [positiveWord, List.length_append]
  unfold windowLength at *
  omega

theorem edit_bounded (p : BubbleWord α k b) : p.edit.Bounded b :=
  ⟨p.removed_bound, p.replacement_bound⟩

theorem edit_inBounds (p : BubbleWord α k b) : p.edit.InBounds p.negativeWord.length := by
  simp [Edit.InBounds, edit, negativeWord]

theorem different_words (p : BubbleWord α k b) : p.negativeWord ≠ p.positiveWord := by
  intro heq
  exact p.different (List.append_cancel_left (List.append_cancel_right heq))

#print axioms negativeWord_length_bounds
#print axioms positiveWord_length_bounds
#print axioms different_words

end BubbleWord
end DeletionCode.Burst
