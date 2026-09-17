import DeletionCode.ConcreteFill
import DeletionCode.ConcreteStart
import DeletionCode.SelectedWindows

/-!
Concrete memory operations preserve the scheduler's realization invariant.
Base fills derive their readable seed from readiness. Supplier fills derive
readable source blocks from completed negative paths. Starts choose a slot
whose transferred seed was actually written. These local transitions are used
by ConcreteProgress and the bounded-trace construction in ConcreteRecovery.
-/
namespace DeletionCode.ConcreteTransitions

open Windows PartialWords Recovery SelectedWindows ConcreteFill ConcreteStart
open HeaderRecovery (Header negativePath positivePath negativeLength positiveLength
  negativeExtra editOffset)

variable {B : Type*}

def BankSound (mem : B → Memory) (p : B → Letters) (len : B → ℕ) : Prop :=
  ∀ b, Sound (mem b) (p b) (len b)

theorem bankSound_update [DecidableEq B] (mem : B → Memory) (p : B → Letters)
    (len : B → ℕ) (hs : BankSound mem p len) (b : B) (t : Memory)
    (ht : Sound t (p b) (len b)) : BankSound (Function.update mem b t) p len := by
  intro a
  by_cases hab : a = b
  · subst a
    simpa using ht
  · have hba : b ≠ a := Ne.symm hab
    simpa [Function.update, hab, hba] using hs a

/-- Readiness supplies the seed that makes the executable base fill succeed. -/
theorem ready_base_fill [DecidableEq B]
    (s : State B) (mem : B → Memory) (D : B → ℕ) (p : B → Letters)
    (x : Letters) (n k : ℕ) (b : B) (w : Slot)
    (hreal : Realizes s mem D k)
    (hs : BankSound mem p (fun a => 3 * (k + 1) + D a))
    (hx : KUnique x n k) (hD : D b < 3 * (k + 1)) (hready : s.Ready b w)
    (hocc : ∃ a, a + 3 * (k + 1) ≤ n ∧
      Agree x a (p b) (windowStart (D b) w) (3 * (k + 1))) :
    ∃ r t, fillFromBase x n k (3 * (k + 1)) (mem b)
        (3 * (k + 1) + D b) (windowStart (D b) w) r = some t ∧
      Realizes (s.fill b w) (Function.update mem b t) D k ∧
      BankSound (Function.update mem b t) p (fun a => 3 * (k + 1) + D a) := by
  obtain ⟨r, seed, hr, hread⟩ :=
    hreal.ready_seedKnown s mem D k b w hD hready
  have hstart := windowStart_le (D b) w
  obtain ⟨t, ht, hsound, hext, hknown⟩ := fillFromBase_correct x (p b)
    n k (3 * (k + 1)) (mem b) (3 * (k + 1) + D b)
    (windowStart (D b) w) r seed hx (hs b) (by omega) hr hread hocc
  exact ⟨r, t, ht,
    Realizes.fill_update s mem D k hreal b w t hext ⟨_, hknown⟩,
    bankSound_update mem p _ hs b t hsound⟩

/-- A completed negative supplier makes any in-bounds source window readable. -/
theorem complete_supplier_fill [DecidableEq B]
    (s : State B) (mem : B → Memory) (D : B → ℕ) (p : B → Letters)
    (k : ℕ) (a b : B) (w : Slot) (sourceStart : ℕ)
    (hreal : Realizes s mem D k)
    (hs : BankSound mem p (fun c => 3 * (k + 1) + D c))
    (hD : D a ≤ 3 * (k + 1)) (hcomplete : s.Complete a)
    (hsource : sourceStart ≤ D a)
    (hagree : Agree (p a) sourceStart (p b) (windowStart (D b) w) (3 * (k + 1))) :
    ∃ t, copyFromMemory (mem a) (3 * (k + 1) + D a) sourceStart (3 * (k + 1))
        (mem b) (3 * (k + 1) + D b) (windowStart (D b) w) = some t ∧
      Realizes (s.fill b w) (Function.update mem b t) D k ∧
      BankSound (Function.update mem b t) p (fun c => 3 * (k + 1) + D c) := by
  have hwhole := hreal.complete_wordKnown s mem D k a hD hcomplete
  obtain ⟨bits, hread⟩ := windowKnown_subblock (mem a) 0
    (3 * (k + 1) + D a) sourceStart (3 * (k + 1)) hwhole (by omega) (by omega)
  have hstart := windowStart_le (D b) w
  obtain ⟨t, ht, hsound, hext, hknown⟩ := copyFromMemory_correct
    (mem a) (mem b) (p a) (p b) (3 * (k + 1) + D a) sourceStart
    (3 * (k + 1)) (3 * (k + 1) + D b) (windowStart (D b) w) bits
    (hs a) (hs b) (by omega) (by omega) hread hagree
  exact ⟨t, ht,
    Realizes.fill_update s mem D k hreal b w t hext ⟨_, hknown⟩,
    bankSound_update mem p _ hs b t hsound⟩

/-- A correct negative-path seed produces an actual valid start slot. -/
theorem startNegative_transition [DecidableEq B]
    (s : State B) (mem : B → Memory) (headers : B → Header) (long : B → Letters)
    (k : ℕ) (b : B) (offset : ℕ) (bits : Bits k)
    (hreal : Realizes s mem (fun a => negativeExtra k (headers a)) k)
    (hs : BankSound mem (fun a => negativePath k (headers a) (long a))
      (fun a => negativeLength k (headers a)))
    (hrho0 : 1 ≤ (headers b).rho) (hrho1 : (headers b).rho ≤ k + 1)
    (hbound : offset + k ≤ negativeLength k (headers b))
    (hseed : PartialWords.Matches bits (negativePath k (headers b) (long b)) offset) :
    ∃ w t, startNegative k (headers b) offset bits (mem b) = some t ∧
      Realizes (s.start b w) (Function.update mem b t)
        (fun a => negativeExtra k (headers a)) k ∧
      BankSound (Function.update mem b t)
        (fun a => negativePath k (headers a) (long a)) (fun a => negativeLength k (headers a)) := by
  obtain ⟨t, ht, hsound, hext, w, hknown⟩ := startNegative_correct
    k (headers b) (long b) offset bits (mem b) hrho0 hrho1 (hs b) hbound hseed
  exact ⟨w, t, ht,
    Realizes.start_update s mem _ k hreal b w t hext hknown,
    bankSound_update mem _ _ hs b t hsound⟩

/-- A correct positive-path seed uses at most one recorded bit and a real start slot. -/
theorem startPositive_transition [DecidableEq B]
    (s : State B) (mem : B → Memory) (headers : B → Header) (long : B → Letters)
    (k : ℕ) (b : B) (offset : ℕ) (bits : Bits k)
    (hreal : Realizes s mem (fun a => negativeExtra k (headers a)) k)
    (hs : BankSound mem (fun a => negativePath k (headers a) (long a))
      (fun a => negativeLength k (headers a)))
    (hrho0 : 1 ≤ (headers b).rho) (hrho1 : (headers b).rho ≤ k + 1)
    (hbit : long b (editOffset k) = (headers b).bit)
    (hbound : offset + k ≤ positiveLength k (headers b))
    (hseed : ∀ i : Fin k, positivePath k (headers b) (long b) (offset + i.val) = bits i) :
    ∃ extra w t, startPositive k (headers b) offset bits extra (mem b) = some t ∧
      Realizes (s.start b w) (Function.update mem b t)
        (fun a => negativeExtra k (headers a)) k ∧
      BankSound (Function.update mem b t)
        (fun a => negativePath k (headers a) (long a)) (fun a => negativeLength k (headers a)) := by
  obtain ⟨extra, t, ht, hsound, hext, w, hknown⟩ := startPositive_exists
    k (headers b) (long b) offset bits (mem b) hrho0 hrho1 hbit (hs b) hbound hseed
  exact ⟨extra, w, t, ht,
    Realizes.start_update s mem _ k hreal b w t hext hknown,
    bankSound_update mem _ _ hs b t hsound⟩

#print axioms bankSound_update
#print axioms ready_base_fill
#print axioms complete_supplier_fill
#print axioms startNegative_transition
#print axioms startPositive_transition

end DeletionCode.ConcreteTransitions
