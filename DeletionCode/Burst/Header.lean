import DeletionCode.Burst.Basic

/-! Finite header data for a burst bubble. -/
namespace DeletionCode.Burst.HeaderRecovery
open DeletionCode.Qary.Windows
variable {α : Type*} [Inhabited α]

structure Header (α : Type*) where
  leftLength : ℕ
  rightLength : ℕ
  removed : List α
  replacement : List α

structure Header.Valid (k b : ℕ) (h : Header α) : Prop where
  removed_le : h.removed.length ≤ b
  replacement_le : h.replacement.length ≤ b
  left_lower : windowLength k b - 1 - k - b ≤ h.leftLength
  left_upper : h.leftLength ≤ windowLength k b - 1
  right_lower : windowLength k b - 1 - k - b ≤ h.rightLength
  right_upper : h.rightLength ≤ windowLength k b - 1

def Header.Matches (h : Header α) (negative : Letters α) : Prop :=
  ∀ i, i < h.removed.length → h.removed.getD i default = negative (h.leftLength + i)

def negativeLength (h : Header α) : ℕ := h.leftLength + h.removed.length + h.rightLength

def positiveLength (h : Header α) : ℕ := h.leftLength + h.replacement.length + h.rightLength

def negativePath (_h : Header α) (negative : Letters α) : Letters α := negative

def positivePath (h : Header α) (negative : Letters α) : Letters α :=
  (Edit.mk h.leftLength h.removed.length h.replacement).word negative

def negativeExtra (k b : ℕ) (h : Header α) : ℕ := negativeLength h - windowLength k b

def rebuildPositive := @positivePath

theorem negativeLength_bounds {k b : ℕ} {h : Header α} (hv : h.Valid k b) :
    windowLength k b ≤ negativeLength h ∧ negativeLength h ≤ 2 * (windowLength k b - 1) + b := by
  obtain ⟨hu,hv,hal,hah,hbl,hbh⟩ := hv
  unfold negativeLength windowLength at *
  omega

theorem positiveLength_bounds {k b : ℕ} {h : Header α} (hv : h.Valid k b) :
    windowLength k b ≤ positiveLength h ∧ positiveLength h ≤ 2 * (windowLength k b - 1) + b := by
  obtain ⟨hu,hv,hal,hah,hbl,hbh⟩ := hv
  unfold positiveLength windowLength at *
  omega

theorem negativeLength_eq {k b : ℕ} {h : Header α} (hv : h.Valid k b) :
    negativeLength h = windowLength k b + negativeExtra k b h := by
  have := (negativeLength_bounds hv).1
  unfold negativeExtra
  omega

theorem negativeExtra_le {k b : ℕ} {h : Header α} (hv : h.Valid k b) :
    negativeExtra k b h ≤ windowLength k b + b - 2 := by
  have := negativeLength_bounds hv
  unfold negativeExtra windowLength at *
  omega

theorem rightLength_ge {k b : ℕ} {h : Header α} (hv : h.Valid k b) :
    k ≤ h.rightLength := by
  have := hv.right_lower
  unfold windowLength at this
  omega

end DeletionCode.Burst.HeaderRecovery
