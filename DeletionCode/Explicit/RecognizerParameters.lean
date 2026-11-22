import DeletionCode.Explicit.RecognizerRun
import DeletionCode.Explicit.UniformParameters

/-! Instantiate the recognizer's local inequalities with the manuscript's parameters. -/

namespace DeletionCode.Explicit.UniformParameters

variable {q b t ℓ : ℕ}

theorem recognizerBounds (h : BasicBounds q b t ℓ) :
    RuleAddition.Bounds (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ)
      (edits t) (componentCutoff q b t ℓ) := by
  have hBudget : localOmitted q b t ℓ = 14*(edits t*b*componentCutoff q b t ℓ) := by
    simp only [localOmitted, Nat.mul_assoc]
  refine ⟨h.borrowed_gram,h.local_removed,?_,?_,?_,?_,?_⟩
  · change 14*(edits t*b*componentCutoff q b t ℓ) < _
    rw [← hBudget]
    have hf := h.local_gap
    omega
  · change 14*(edits t*b*componentCutoff q b t ℓ)+b ≤ _
    rw [← hBudget]
    exact h.local_flank
  · change 2*(14*(edits t*b*componentCutoff q b t ℓ)) ≤ _
    rw [← hBudget]
    exact h.local_omit
  · change b+14*(edits t*b*componentCutoff q b t ℓ) ≤ _
    rw [← hBudget]
    have ha := h.local_omit
    have hb := h.local_flank
    have hc := h.borrowed_gram
    have hd := h.local_gap
    omega
  · have ha := h.overlap_ceil
    have hb := h.local_gram
    omega

theorem recognizer_window (h : BasicBounds q b t ℓ) :
    windowLength q ℓ + 2*omittedLetters q b t ℓ + 1 ≤ gram q b t ℓ := by
  have hw := h.overlap_window
  have hg := h.local_gram
  omega

#print axioms recognizerBounds
#print axioms recognizer_window

end DeletionCode.Explicit.UniformParameters
