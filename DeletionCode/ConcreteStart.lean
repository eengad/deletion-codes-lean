import DeletionCode.HeaderRecovery
import DeletionCode.SelectedWindows

/-!
Concrete starts from finite seed data. A positive-path seed is transferred
using the header and at most one recorded bit, then written to negative-path
memory. The existence of a valid selected seed slot is derived from the
geometry; the abstract scheduler's arbitrary slot choice is not assumed valid.
-/
namespace DeletionCode.ConcreteStart

open Windows PartialWords SelectedWindows
open HeaderRecovery (Header negativePath positivePath negativeLength positiveLength
  transferFinite windowLength editOffset negativeExtra)

def startNegative (k : ℕ) (h : Header) (offset : ℕ) (bits : PartialWords.Bits k)
    (s : Memory) : Option Memory :=
  writeBits s (negativeLength k h) offset bits

def startPositive (k : ℕ) (h : Header) (offset : ℕ) (bits : PartialWords.Bits k)
    (extra : Bool) (s : Memory) : Option Memory :=
  if offset + k ≤ positiveLength k h then
    let transferred := transferFinite k h offset bits extra
    writeBits s (negativeLength k h) transferred.1 transferred.2
  else none

def StartedCorrectly (k : ℕ) (h : Header) (long : Letters) (s t : Memory) : Prop :=
  Sound t (negativePath k h long) (negativeLength k h) ∧ Extends s t ∧
    ∃ w : Recovery.Slot,
      SeedKnown t (windowStart (negativeExtra k h) w) (windowLength k) k

theorem startNegative_correct (k : ℕ) (h : Header) (long : Letters)
    (offset : ℕ) (bits : PartialWords.Bits k) (s : Memory)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hs : Sound s (negativePath k h long) (negativeLength k h))
    (hbound : offset + k ≤ negativeLength k h)
    (hseed : PartialWords.Matches bits (negativePath k h long) offset) :
    ∃ t, startNegative k h offset bits s = some t ∧ StartedCorrectly k h long s t := by
  obtain ⟨t, ht, hsound, hext, hread⟩ := writeBits_correct
    s (negativePath k h long) (negativeLength k h) offset k hs hbound bits hseed
  refine ⟨t, ht, hsound, hext, ?_⟩
  apply seed_selects_window t (negativeExtra k h) k offset
  · exact HeaderRecovery.negativeExtra_lt k h hrho0 hrho1
  · rw [HeaderRecovery.negativeLength_eq k h hrho0 hrho1] at hbound
    exact hbound
  · exact ⟨bits, hread⟩

/-- The positive start preserves all known data and creates a real selected seed. -/
theorem startPositive_correct (k : ℕ) (h : Header) (long : Letters)
    (offset : ℕ) (bits : PartialWords.Bits k) (extra : Bool) (s : Memory)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hs : Sound s (negativePath k h long) (negativeLength k h))
    (hbound : offset + k ≤ positiveLength k h)
    (hseed : ∀ i : Fin k, positivePath k h long (offset + i.val) = bits i)
    (hextra : h.orientation = .insertion → offset ≤ editOffset k →
      editOffset k < offset + k → extra = negativePath k h long (offset + k - 1)) :
    ∃ t, startPositive k h offset bits extra s = some t ∧
      StartedCorrectly k h long s t := by
  have hvalid := HeaderRecovery.transferFinite_valid k h long offset bits extra
    hrho0 hrho1 hbit hbound hseed hextra
  let transferred := transferFinite k h offset bits extra
  have hmatches : PartialWords.Matches transferred.2 (negativePath k h long)
      transferred.1 := fun i => (hvalid.2 i).symm
  obtain ⟨t, ht, hsound, hext, hread⟩ := writeBits_correct
    s (negativePath k h long) (negativeLength k h) transferred.1 k
    hs hvalid.1 transferred.2 hmatches
  refine ⟨t, ?_, hsound, hext, ?_⟩
  · simpa only [startPositive, ite_eq_left hbound] using ht
  · apply seed_selects_window t (negativeExtra k h) k transferred.1
    · exact HeaderRecovery.negativeExtra_lt k h hrho0 hrho1
    · have hb := hvalid.1
      rw [HeaderRecovery.negativeLength_eq k h hrho0 hrho1] at hb
      exact hb
    · exact ⟨transferred.2, hread⟩

/-- One recorded Boolean always suffices, including when the seed crosses the edit. -/
theorem startPositive_exists (k : ℕ) (h : Header) (long : Letters)
    (offset : ℕ) (bits : PartialWords.Bits k) (s : Memory)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hs : Sound s (negativePath k h long) (negativeLength k h))
    (hbound : offset + k ≤ positiveLength k h)
    (hseed : ∀ i : Fin k, positivePath k h long (offset + i.val) = bits i) :
    ∃ extra t, startPositive k h offset bits extra s = some t ∧
      StartedCorrectly k h long s t := by
  let extra := negativePath k h long (offset + k - 1)
  obtain ⟨t, ht, hcorrect⟩ := startPositive_correct k h long offset bits extra s
    hrho0 hrho1 hbit hs hbound hseed (fun _ _ _ => rfl)
  exact ⟨extra, t, ht, hcorrect⟩

#print axioms startNegative_correct
#print axioms startPositive_correct
#print axioms startPositive_exists

end DeletionCode.ConcreteStart
