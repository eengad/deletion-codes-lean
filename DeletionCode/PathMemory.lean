import DeletionCode.HeaderRecovery
import DeletionCode.PartialWords
import DeletionCode.SelectedWindows

/-!
Read either path of a bubble from stored negative letters.

Negative reads require just the requested stored block. Positive reads first
require the entire finite negative word, then rebuild the positive word using
its header. All returned data is finite, and every read checks the path bound.
-/

namespace DeletionCode.PathMemory

open Windows HeaderRecovery PartialWords SelectedWindows

def pathLength (k : ℕ) (h : Header) (side : Bool) : ℕ :=
  if side then positiveLength k h else negativeLength k h

def pathLetters (k : ℕ) (h : Header) (long : Letters) (side : Bool) : Letters :=
  if side then positivePath k h long else negativePath k h long

/-- A finite subblock; its argument proves that every inspected bit is in range. -/
def extractBits {m : ℕ} (bits : PartialWords.Bits m) (start len : ℕ)
    (hbound : start + len ≤ m) : PartialWords.Bits len :=
  fun i => bits ⟨start + i.val, by have := i.isLt; omega⟩

/-- Executable checked path read, using no access to the actual unknown word. -/
def readPath (k : ℕ) (h : Header) (s : Memory) (side : Bool)
    (start len : ℕ) : Option (PartialWords.Bits len) :=
  match side with
  | false => if start + len ≤ negativeLength k h then readBits s start len else none
  | true =>
    if hbound : start + len ≤ positiveLength k h then
      (readBits s 0 (negativeLength k h)).map fun negative =>
        extractBits (rebuildPositiveFinite k h negative) start len hbound
    else none

theorem readPath_bounds (k : ℕ) (h : Header) (s : Memory) (side : Bool)
    (start len : ℕ) (bits : PartialWords.Bits len)
    (hread : readPath k h s side start len = some bits) :
    start + len ≤ pathLength k h side := by
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

theorem readPath_sound (k : ℕ) (h : Header) (long : Letters) (s : Memory)
    (side : Bool) (start len : ℕ) (bits : PartialWords.Bits len)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hs : Sound s (negativePath k h long) (negativeLength k h))
    (hread : readPath k h s side start len = some bits) :
    Matches bits (pathLetters k h long side) start := by
  cases side with
  | false =>
    simp only [readPath] at hread
    split at hread
    · rename_i hbound
      exact readBits_sound s (negativePath k h long) (negativeLength k h)
        start len hs hbound bits hread
    · contradiction
  | true =>
    simp only [readPath] at hread
    split at hread
    · rename_i hbound
      cases hnegative : readBits s 0 (negativeLength k h) with
      | none => simp [hnegative] at hread
      | some negative =>
        have hmatch := readBits_sound s (negativePath k h long) (negativeLength k h)
          0 (negativeLength k h) hs (by omega) negative hnegative
        have hknown : ∀ i : Fin (negativeLength k h),
            negative i = negativePath k h long i.val := by
          intro i
          simpa only [Nat.zero_add] using hmatch i
        have hpositive := rebuildPositiveFinite_correct k h long negative
          hrho0 hrho1 hbit hknown
        simp only [hnegative, Option.map_some] at hread
        have heq := Option.some.inj hread
        intro i
        rw [← heq]
        exact hpositive ⟨start + i.val, by have := i.isLt; omega⟩
    · contradiction

/-- Once all negative letters are stored, every bounded block on either side is readable. -/
theorem readPath_exists_of_complete (k : ℕ) (h : Header) (s : Memory)
    (side : Bool) (start len : ℕ)
    (hknown : WindowKnown s 0 (negativeLength k h))
    (hbound : start + len ≤ pathLength k h side) :
    ∃ bits, readPath k h s side start len = some bits := by
  cases side with
  | false =>
    have hbound' : start + len ≤ negativeLength k h := hbound
    obtain ⟨bits, hbits⟩ := windowKnown_subblock s 0 (negativeLength k h)
      start len hknown (Nat.zero_le start) (by simpa only [Nat.zero_add] using hbound')
    exact ⟨bits, by simpa only [readPath, ite_eq_left hbound'] using hbits⟩
  | true =>
    have hbound' : start + len ≤ positiveLength k h := hbound
    obtain ⟨negative, hnegative⟩ := hknown
    refine ⟨extractBits (rebuildPositiveFinite k h negative) start len hbound', ?_⟩
    simp only [readPath, dite_eq_left hbound', hnegative, Option.map_some]

/-- Completed sound negative memory supplies correct data on either path. -/
theorem readPath_complete (k : ℕ) (h : Header) (long : Letters) (s : Memory)
    (side : Bool) (start len : ℕ)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hs : Sound s (negativePath k h long) (negativeLength k h))
    (hknown : WindowKnown s 0 (negativeLength k h))
    (hbound : start + len ≤ pathLength k h side) :
    ∃ bits, readPath k h s side start len = some bits ∧
      Matches bits (pathLetters k h long side) start := by
  obtain ⟨bits, hread⟩ := readPath_exists_of_complete k h s side start len hknown hbound
  exact ⟨bits, hread, readPath_sound k h long s side start len bits
    hrho0 hrho1 hbit hs hread⟩

/-- The two actual paths share their entire initial de Bruijn vertex. -/
theorem pathInitialAgreement (k : ℕ) (h : Header) (long : Letters) :
    Agree (negativePath k h long) 0 (positivePath k h long) 0 (windowLength k - 1) := by
  cases ho : h.orientation with
  | deletion =>
    simp only [negativePath, positivePath, ho]
    intro i hi
    exact (deletion_before long (editOffset k) 0 (windowLength k - 1)
      (by unfold editOffset; omega) i hi).symm
  | insertion =>
    simp only [negativePath, positivePath, ho]
    exact deletion_before long (editOffset k) 0 (windowLength k - 1)
      (by unfold editOffset; omega)
  | substitution =>
    simp only [negativePath, positivePath, ho]
    intro i hi
    exact (flip_agree_of_avoid long (editOffset k) 0 (windowLength k - 1)
      (Or.inl (by unfold editOffset; omega)) i hi).symm

#print axioms readPath_bounds
#print axioms readPath_sound
#print axioms readPath_exists_of_complete
#print axioms readPath_complete
#print axioms pathInitialAgreement

end DeletionCode.PathMemory
