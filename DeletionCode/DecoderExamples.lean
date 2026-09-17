import DeletionCode.ConcreteFill
import DeletionCode.ConcreteStart
import Mathlib.Data.List.OfFn

/-!
Small executable regressions for the concrete decoder primitives.

All examples use kernel evaluation through `by decide`, not native_decide.
They check computation and rejection on specific inputs; they do not replace
the general correctness, realization, or bounded-recovery theorems.
-/

namespace DeletionCode.DecoderExamples

open Windows PartialWords

/-- The ten-bit word 0001011100, with an unused zero tail. -/
def sampleWord : Letters :=
  fun i => [false, false, false, true, false, true, true, true, false, false].getD i false

/-- The known seed 101 belongs at relative offset one of the window 01011. -/
def sampleSeed : Bits 3 := fun i => i.val != 1

def sampleMemory : Memory := putBits empty 1 sampleSeed

theorem seed_lookup_finds_position :
    SeedLookup.lookup sampleWord 10 3 5 1 sampleSeed = some 2 := by decide

theorem seed_lookup_recovers_window :
    (SeedLookup.recoverWindow sampleWord 10 3 5 1 sampleSeed).map
      (fun bits => List.ofFn bits) = some [false, true, false, true, true] := by decide

theorem fillFromBase_recovers_window :
    ((ConcreteFill.fillFromBase sampleWord 10 3 5 sampleMemory 5 0 1).bind
      (fun memory => (readBits memory 0 5).map (fun bits => List.ofFn bits))) =
      some [false, true, false, true, true] := by decide

/-- A conflicting bit outside the seed is detected when the whole window is written. -/
theorem fillFromBase_rejects_conflict :
    (ConcreteFill.fillFromBase sampleWord 10 3 5
      (putBits sampleMemory 0 (fun _ : Fin 1 => true)) 5 0 1).isNone = true := by decide

theorem checked_write_rejects_conflict :
    (writeBits (putBits empty 0 (fun _ : Fin 1 => false)) 5 0
      (fun _ : Fin 1 => true)).isNone = true := by decide

theorem checked_write_rejects_out_of_bounds :
    (writeBits empty 5 4 sampleSeed).isNone = true := by decide

/-- The same valid lookup must still reject a destination that is too short. -/
theorem fillFromBase_rejects_out_of_bounds :
    (ConcreteFill.fillFromBase sampleWord 10 3 5 sampleMemory 4 0 1).isNone = true :=
  by decide

theorem fillFromBase_rejects_missing_seed :
    (ConcreteFill.fillFromBase sampleWord 10 3 5 empty 5 0 1).isNone = true := by decide

/-- For k=1, L=6 and rho=1, the positive path is the longer word.
Transferring its seed at the edit deletes the known bit and uses one extension bit. -/
def crossingHeader : HeaderRecovery.Header := ⟨.insertion, 1, true⟩

def crossingLong : Letters := fun i => i == 5

theorem crossing_header_parameters :
    1 ≤ crossingHeader.rho ∧ crossingHeader.rho ≤ 1 + 1 ∧
      HeaderRecovery.windowLength 1 = 6 ∧
      crossingLong (HeaderRecovery.editOffset 1) = crossingHeader.bit := by decide

theorem crossing_transfer_uses_extension_bit :
    let result := HeaderRecovery.transferFinite 1 crossingHeader 5
      (fun _ : Fin 1 => true) false
    (result.1, List.ofFn result.2) = (5, [false]) := by decide

theorem crossing_transfer_agrees_with_negative_word :
    let result := HeaderRecovery.transferFinite 1 crossingHeader 5
      (fun _ : Fin 1 => true) false
    List.ofFn result.2 = List.ofFn (fun i : Fin 1 =>
      HeaderRecovery.negativePath 1 crossingHeader crossingLong (result.1 + i.val)) :=
  by decide

theorem crossing_start_records_transferred_seed :
    ((ConcreteStart.startPositive 1 crossingHeader 5 (fun _ : Fin 1 => true) false empty).bind
      (fun memory => (readBits memory 5 1).map (fun bits => List.ofFn bits))) =
      some [false] := by decide

#print axioms seed_lookup_finds_position
#print axioms fillFromBase_recovers_window
#print axioms fillFromBase_rejects_conflict
#print axioms checked_write_rejects_out_of_bounds
#print axioms crossing_transfer_agrees_with_negative_word
#print axioms crossing_start_records_transferred_seed

end DeletionCode.DecoderExamples
