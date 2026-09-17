import DeletionCode.Windows
import Mathlib.Data.Fintype.Basic

/-!
Executable partial-word storage for the concrete recovery decoder.
Reads require every requested bit to be known. Writes check the finite word
bound and reject disagreements with previously known bits. Neither operation
receives the unknown target word; it appears only in their correctness proofs.
-/
namespace DeletionCode.PartialWords

open Windows

abbrev Memory := ℕ → Option Bool
abbrev Bits (len : ℕ) := Fin len → Bool

def empty : Memory := fun _ => none

def Sound (s : Memory) (p : Letters) (m : ℕ) : Prop :=
  ∀ j, j < m → ∀ b, s j = some b → b = p j

def Extends (s t : Memory) : Prop :=
  ∀ j b, s j = some b → t j = some b

def Matches {len : ℕ} (bits : Bits len) (p : Letters) (start : ℕ) : Prop :=
  ∀ i, bits i = p (start + i.val)

/-- Read finite data without a choice oracle or access to the target word. -/
def readBits (s : Memory) (start len : ℕ) : Option (Bits len) :=
  if ∀ i : Fin len, s (start + i.val) = some ((s (start + i.val)).getD false)
  then some (fun i => (s (start + i.val)).getD false)
  else none

def Compatible (s : Memory) (start : ℕ) {len : ℕ} (bits : Bits len) : Prop :=
  ∀ i, s (start + i.val) = none ∨ s (start + i.val) = some (bits i)

instance (s : Memory) (start : ℕ) {len : ℕ} (bits : Bits len) :
    Decidable (Compatible s start bits) := by
  unfold Compatible
  infer_instance

def putBits (s : Memory) (start : ℕ) {len : ℕ} (bits : Bits len) : Memory :=
  fun j => if h : start ≤ j ∧ j < start + len
    then some (bits ⟨j - start, by omega⟩)
    else s j

/-- Checked write: reject out-of-bounds blocks and inconsistent known letters. -/
def writeBits (s : Memory) (m start : ℕ) {len : ℕ} (bits : Bits len) : Option Memory :=
  if start + len ≤ m ∧ Compatible s start bits
  then some (putBits s start bits)
  else none

theorem empty_sound (p : Letters) (m : ℕ) : Sound empty p m := by
  intro j hj b hb
  simp [empty] at hb

theorem readBits_eq_some_iff (s : Memory) (start len : ℕ) (bits : Bits len) :
    readBits s start len = some bits ↔
      ∀ i, s (start + i.val) = some (bits i) := by
  unfold readBits
  split
  · rename_i h
    constructor
    · intro heq
      have heq' := Option.some.inj heq
      intro i
      rw [← heq']
      exact h i
    · intro hb
      congr 1
      funext i
      simp [hb i]
  · rename_i h
    constructor
    · simp
    · intro hb
      apply False.elim
      apply h
      intro i
      simp [hb i]

theorem readBits_sound (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits len) (hread : readBits s start len = some bits) :
    Matches bits p start := by
  intro i
  exact hs (start + i.val) (by have := i.isLt; omega) (bits i)
    ((readBits_eq_some_iff s start len bits).mp hread i)

theorem compatible_of_sound (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits len) (hbits : Matches bits p start) :
    Compatible s start bits := by
  intro i
  cases h : s (start + i.val) with
  | none => exact Or.inl rfl
  | some b =>
    have hb := hs (start + i.val) (by have := i.isLt; omega) b h
    exact Or.inr (congrArg some (hb.trans (hbits i).symm))

theorem putBits_at (s : Memory) (start len : ℕ) (bits : Bits len) (i : Fin len) :
    putBits s start bits (start + i.val) = some (bits i) := by
  simp [putBits, i.isLt]

theorem putBits_extends (s : Memory) (start len : ℕ) (bits : Bits len)
    (hc : Compatible s start bits) : Extends s (putBits s start bits) := by
  intro j b hb
  unfold putBits
  split
  · rename_i h
    let i : Fin len := ⟨j - start, by omega⟩
    have hi : start + i.val = j := by dsimp [i]; omega
    have hc' := hc i
    rw [hi, hb] at hc'
    rcases hc' with hn | heq
    · contradiction
    · simpa [i] using heq.symm
  · exact hb

theorem putBits_sound (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (bits : Bits len) (hbits : Matches bits p start) :
    Sound (putBits s start bits) p m := by
  intro j hj b hb
  unfold putBits at hb
  split at hb
  · rename_i h
    have heq := Option.some.inj hb
    have hbit := hbits ⟨j - start, by omega⟩
    have hidx : start + (j - start) = j := by omega
    simpa [hidx, heq] using hbit
  · exact hs j hj b hb

theorem readBits_putBits (s : Memory) (start len : ℕ) (bits : Bits len) :
    readBits (putBits s start bits) start len = some bits := by
  apply (readBits_eq_some_iff _ _ _ _).mpr
  exact putBits_at s start len bits

theorem writeBits_success (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits len) (hbits : Matches bits p start) :
    writeBits s m start bits = some (putBits s start bits) := by
  simp [writeBits, hbound, compatible_of_sound s p m start len hs hbound bits hbits]

/-- Every successful checked write preserves all previously known bits. -/
theorem writeBits_extends (s t : Memory) (m start len : ℕ) (bits : Bits len)
    (hwrite : writeBits s m start bits = some t) : Extends s t := by
  unfold writeBits at hwrite
  split at hwrite
  · rename_i h
    cases Option.some.inj hwrite
    exact putBits_extends s start len bits h.2
  · contradiction

/-- Correct data written to correct memory remains correct and can be read back. -/
theorem writeBits_correct (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits len) (hbits : Matches bits p start) :
    ∃ t, writeBits s m start bits = some t ∧ Sound t p m ∧
      Extends s t ∧ readBits t start len = some bits := by
  refine ⟨putBits s start bits,
    writeBits_success s p m start len hs hbound bits hbits,
    putBits_sound s p m start len hs bits hbits, ?_, readBits_putBits s start len bits⟩
  exact putBits_extends s start len bits
    (compatible_of_sound s p m start len hs hbound bits hbits)

#print axioms readBits_eq_some_iff
#print axioms readBits_sound
#print axioms writeBits_extends
#print axioms writeBits_correct

end DeletionCode.PartialWords
