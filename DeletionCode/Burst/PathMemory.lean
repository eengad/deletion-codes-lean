import DeletionCode.Burst.HeaderRecovery
import DeletionCode.Qary.PartialWords
import DeletionCode.Burst.SelectedWindows

/-!
Read either path of a bubble from stored negative letters.

Negative reads require just the requested stored block. Positive reads first
require the entire finite negative word, then rebuild the positive word using
its header. All returned data is finite, and every read checks the path bound.
-/

namespace DeletionCode.Burst.PathMemory

variable {α : Type*} [DecidableEq α] [Inhabited α]

open DeletionCode.Qary.Windows DeletionCode.Burst.HeaderRecovery DeletionCode.Qary.PartialWords DeletionCode.Burst.SelectedWindows

def pathLength (k d : ℕ) (h : Header α) (side : Bool) : ℕ :=
  if side then positiveLength h else negativeLength h

def pathLetters (k d : ℕ) (h : Header α) (long : Letters α) (side : Bool) : Letters α :=
  if side then positivePath h long else negativePath h long

/-- A finite subblock; its argument proves that every inspected letter is in range. -/
def extractBits {m : ℕ} (bits : Qary.PartialWords.Bits α m) (start len : ℕ)
    (hbound : start + len ≤ m) : Qary.PartialWords.Bits α len :=
  fun i => bits ⟨start + i.val, by have := i.isLt; omega⟩

/-- Executable checked path read, using no access to the actual unknown word. -/
def readPath (k d : ℕ) (h : Header α) (s : Memory α) (side : Bool)
    (start len : ℕ) : Option (Qary.PartialWords.Bits α len) :=
  match side with
  | false => if start + len ≤ negativeLength h then readBits s start len else none
  | true =>
    if hbound : start + len ≤ positiveLength h then
      (readBits s 0 (negativeLength h)).map fun negative =>
        extractBits (rebuildPositiveFinite h negative) start len hbound
    else none

theorem readPath_bounds (k d : ℕ) (h : Header α) (s : Memory α) (side : Bool)
    (start len : ℕ) (bits : Qary.PartialWords.Bits α len)
    (hread : readPath k d h s side start len = some bits) :
    start + len ≤ pathLength k d h side := by
  cases side with
  | false =>
    simp only [readPath] at hread
    split at hread
    · assumption
    · contradiction
  | true =>
    simp only [readPath] at hread
    split at hread
    · assumption
    · contradiction

theorem readPath_sound (k d : ℕ) (h : Header α) (long : Letters α) (s : Memory α)
    (side : Bool) (start len : ℕ) (bits : Qary.PartialWords.Bits α len)
    (hv : h.Valid k d) (hm : h.Matches long)
    (hs : Sound s (negativePath h long) (negativeLength h))
    (hread : readPath k d h s side start len = some bits) :
    Matches bits (pathLetters k d h long side) start := by
  cases side with
  | false =>
    simp only [readPath] at hread
    split at hread
    · rename_i hbound
      exact readBits_sound s (negativePath h long) (negativeLength h)
        start len hs hbound bits hread
    · contradiction
  | true =>
    simp only [readPath] at hread
    split at hread
    · rename_i hbound
      cases hnegative : readBits s 0 (negativeLength h) with
      | none => simp [hnegative] at hread
      | some negative =>
        have hmatch := readBits_sound s (negativePath h long) (negativeLength h)
          0 (negativeLength h) hs (by omega) negative hnegative
        have hknown : ∀ i : Fin (negativeLength h),
            negative i = negativePath h long i.val := by
          intro i
          simpa only [Nat.zero_add] using hmatch i
        have hpositive := rebuildPositiveFinite_correct h long negative hknown
        simp only [hnegative, Option.map_some] at hread
        have heq := Option.some.inj hread
        intro i
        rw [← heq]
        exact hpositive ⟨start + i.val, by have := i.isLt; omega⟩
    · contradiction

/-- Once all negative letters are stored, every bounded block on either side is readable. -/
theorem readPath_exists_of_complete (k d : ℕ) (h : Header α) (s : Memory α)
    (side : Bool) (start len : ℕ)
    (hknown : WindowKnown s 0 (negativeLength h))
    (hbound : start + len ≤ pathLength k d h side) :
    ∃ bits, readPath k d h s side start len = some bits := by
  cases side with
  | false =>
    have hbound' : start + len ≤ negativeLength h := hbound
    obtain ⟨bits, hbits⟩ := windowKnown_subblock s 0 (negativeLength h)
      start len hknown (Nat.zero_le start) (by simpa only [Nat.zero_add] using hbound')
    exact ⟨bits, by simpa only [readPath, ite_eq_left hbound'] using hbits⟩
  | true =>
    have hbound' : start + len ≤ positiveLength h := hbound
    obtain ⟨negative, hnegative⟩ := hknown
    refine ⟨extractBits (rebuildPositiveFinite h negative) start len hbound', ?_⟩
    simp only [readPath, dite_eq_left hbound', hnegative, Option.map_some]

/-- Completed sound negative memory supplies correct data on either path. -/
theorem readPath_complete (k d : ℕ) (h : Header α) (long : Letters α) (s : Memory α)
    (side : Bool) (start len : ℕ)
    (hv : h.Valid k d) (hm : h.Matches long)
    (hs : Sound s (negativePath h long) (negativeLength h))
    (hknown : WindowKnown s 0 (negativeLength h))
    (hbound : start + len ≤ pathLength k d h side) :
    ∃ bits, readPath k d h s side start len = some bits ∧
      Matches bits (pathLetters k d h long side) start := by
  obtain ⟨bits, hread⟩ := readPath_exists_of_complete k d h s side start len hknown hbound
  exact ⟨bits, hread, readPath_sound k d h long s side start len bits
    hv hm hs hread⟩

#print axioms readPath_sound
#print axioms readPath_complete
end DeletionCode.Burst.PathMemory
