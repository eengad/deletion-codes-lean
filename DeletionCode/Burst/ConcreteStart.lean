import DeletionCode.Burst.HeaderRecovery
import DeletionCode.Burst.SelectedWindows

namespace DeletionCode.Burst.ConcreteStart
open DeletionCode.Qary.Windows DeletionCode.Qary.PartialWords
open DeletionCode.Burst.HeaderRecovery DeletionCode.Burst.SelectedWindows
variable {α : Type*} [DecidableEq α] [Inhabited α]

def startNegative (k _d : ℕ) (h : Header α) (offset : ℕ) (bits : Bits α k)
    (s : Memory α) : Option (Memory α) :=
  writeBits s (negativeLength h) offset bits

def startPositive (k d : ℕ) (h : Header α) (offset : ℕ) (bits : Bits α k)
    (extras : Bits α d) (s : Memory α) : Option (Memory α) :=
  if offset + k ≤ positiveLength h then
    let transferred := transferFinite k d h offset bits extras
    writeBits s (negativeLength h) transferred.1 transferred.2
  else none

def StartedCorrectly (k d : ℕ) (h : Header α) (long : Letters α) (s t : Memory α) : Prop :=
  Sound t long (negativeLength h) ∧ Extends s t ∧
    ∃ w : Recovery.Slot, SeedKnown t (windowStart (negativeExtra k d h) w) (windowLength k d) k

theorem startNegative_correct (k d : ℕ) (h : Header α) (long : Letters α)
    (offset : ℕ) (bits : Bits α k) (s : Memory α) (hv : h.Valid k d)
    (hs : Sound s long (negativeLength h)) (hbound : offset + k ≤ negativeLength h)
    (hseed : DeletionCode.Qary.PartialWords.Matches bits long offset) :
    ∃ t, startNegative k d h offset bits s = some t ∧ StartedCorrectly k d h long s t := by
  obtain ⟨t, ht, hsound, hext, hread⟩ := writeBits_correct s long (negativeLength h)
    offset k hs hbound bits hseed
  refine ⟨t, ht, hsound, hext, ?_⟩
  apply seed_selects_window (d := d) t (negativeExtra k d h) k offset
  · exact negativeExtra_le hv
  · rw [negativeLength_eq hv] at hbound
    exact hbound
  · exact ⟨bits, hread⟩

theorem startPositive_exists (k d : ℕ) (h : Header α) (long : Letters α)
    (offset : ℕ) (bits : Bits α k) (s : Memory α) (hv : h.Valid k d) (hm : h.Matches long)
    (hs : Sound s long (negativeLength h)) (hbound : offset + k ≤ positiveLength h)
    (hseed : ∀ i : Fin k, positivePath h long (offset + i.val) = bits i) :
    ∃ extras : Bits α d, ∃ t,
      startPositive k d h offset bits extras s = some t ∧ StartedCorrectly k d h long s t := by
  obtain ⟨extras, hb, htransfer⟩ := transferFinite_exists k d h long offset bits hv hm hbound hseed
  let transferred := transferFinite k d h offset bits extras
  have hm : DeletionCode.Qary.PartialWords.Matches transferred.2 long transferred.1 :=
    fun i => (htransfer i).symm
  obtain ⟨t, ht, hsound, hext, hread⟩ := writeBits_correct s long (negativeLength h)
    transferred.1 k hs hb transferred.2 hm
  refine ⟨extras, t, ?_, hsound, hext, ?_⟩
  · simpa only [startPositive, ite_eq_left hbound] using ht
  · apply seed_selects_window (d := d) t (negativeExtra k d h) k transferred.1
    · exact negativeExtra_le hv
    · rw [negativeLength_eq hv] at hb
      exact hb
    · exact ⟨transferred.2, hread⟩

#print axioms startPositive_exists
end DeletionCode.Burst.ConcreteStart
