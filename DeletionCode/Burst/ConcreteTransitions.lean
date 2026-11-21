import DeletionCode.Qary.ConcreteFill
import DeletionCode.Burst.ConcreteStart
import DeletionCode.Burst.SelectedWindows

/-!
Concrete memory operations preserve the scheduler's realization invariant.
Base fills derive their readable seed from readiness. Supplier fills derive
readable source blocks from completed negative paths. Starts choose a slot
whose transferred seed was actually written. These local transitions are used
by ConcreteProgress and the bounded-trace construction in ConcreteRecovery.
-/
namespace DeletionCode.Burst.ConcreteTransitions

variable {α : Type*} [DecidableEq α] [Inhabited α]

open DeletionCode.Qary.Windows DeletionCode.Qary.PartialWords DeletionCode.Recovery DeletionCode.Burst.SelectedWindows DeletionCode.Qary.ConcreteFill DeletionCode.Burst.ConcreteStart
open DeletionCode.Burst.HeaderRecovery (Header negativePath positivePath negativeLength positiveLength
  negativeExtra)

variable {B : Type*}

def BankSound (mem : B → Memory α) (p : B → Letters α) (len : B → ℕ) : Prop :=
  ∀ b, Sound (mem b) (p b) (len b)

theorem bankSound_update [DecidableEq B] (mem : B → Memory α) (p : B → Letters α)
    (len : B → ℕ) (hs : BankSound mem p len) (b : B) (t : Memory α)
    (ht : Sound t (p b) (len b)) : BankSound (Function.update mem b t) p len := by
  intro a
  by_cases hab : a = b
  · subst a
    simpa using ht
  · have hba : b ≠ a := Ne.symm hab
    simpa [Function.update, hab, hba] using hs a

/-- Readiness supplies the seed that makes the executable base fill succeed. -/
theorem ready_base_fill [DecidableEq B]
    (s : State B) (mem : B → Memory α) (D : B → ℕ) (p : B → Letters α)
    (x : Letters α) (n k d : ℕ) (b : B) (w : Slot)
    (hreal : Realizes (d := d) s mem D k)
    (hs : BankSound mem p (fun a => windowLength k d + D a))
    (hx : KUnique x n k) (hD : D b ≤ windowLength k d + d - 2) (hready : s.Ready b w)
    (hocc : ∃ a, a + windowLength k d ≤ n ∧
      Agree x a (p b) (windowStart (D b) w) (windowLength k d)) :
    ∃ r t, fillFromBase x n k (windowLength k d) (mem b)
        (windowLength k d + D b) (windowStart (D b) w) r = some t ∧
      Realizes (d := d) (s.fill b w) (Function.update mem b t) D k ∧
      BankSound (Function.update mem b t) p (fun a => windowLength k d + D a) := by
  obtain ⟨r, seed, hr, hread⟩ :=
    hreal.ready_seedKnown s mem D k b w hD hready
  have hstart := windowStart_le (D b) w
  obtain ⟨t, ht, hsound, hext, hknown⟩ := fillFromBase_correct x (p b)
    n k (windowLength k d) (mem b) (windowLength k d + D b)
    (windowStart (D b) w) r seed hx (hs b) (by omega) hr hread hocc
  exact ⟨r, t, ht,
    Realizes.fill_update s mem D k hreal b w t hext ⟨_, hknown⟩,
    bankSound_update mem p _ hs b t hsound⟩

/-- A completed negative supplier makes any in-bounds source window readable. -/
theorem complete_supplier_fill [DecidableEq B]
    (s : State B) (mem : B → Memory α) (D : B → ℕ) (p : B → Letters α)
    (k d : ℕ) (a b : B) (w : Slot) (sourceStart : ℕ)
    (hreal : Realizes (d := d) s mem D k)
    (hs : BankSound mem p (fun c => windowLength k d + D c))
    (hD : D a ≤ windowLength k d + d - 2) (hcomplete : s.Complete a)
    (hsource : sourceStart ≤ D a)
    (hagree : Agree (p a) sourceStart (p b) (windowStart (D b) w) (windowLength k d)) :
    ∃ t, copyFromMemory (mem a) (windowLength k d + D a) sourceStart (windowLength k d)
        (mem b) (windowLength k d + D b) (windowStart (D b) w) = some t ∧
      Realizes (d := d) (s.fill b w) (Function.update mem b t) D k ∧
      BankSound (Function.update mem b t) p (fun c => windowLength k d + D c) := by
  have hwhole := hreal.complete_wordKnown s mem D k a hD hcomplete
  obtain ⟨bits, hread⟩ := windowKnown_subblock (mem a) 0
    (windowLength k d + D a) sourceStart (windowLength k d) hwhole (by omega) (by omega)
  have hstart := windowStart_le (D b) w
  obtain ⟨t, ht, hsound, hext, hknown⟩ := copyFromMemory_correct
    (mem a) (mem b) (p a) (p b) (windowLength k d + D a) sourceStart
    (windowLength k d) (windowLength k d + D b) (windowStart (D b) w) bits
    (hs a) (hs b) (by omega) (by omega) hread hagree
  exact ⟨t, ht,
    Realizes.fill_update s mem D k hreal b w t hext ⟨_, hknown⟩,
    bankSound_update mem p _ hs b t hsound⟩

/-- A correct negative-path seed produces an actual valid start slot. -/
theorem startNegative_transition [DecidableEq B]
    (s : State B) (mem : B → Memory α) (headers : B → Header α) (long : B → Letters α)
    (k d : ℕ) (b : B) (offset : ℕ) (bits : Bits α k)
    (hreal : Realizes (d := d) s mem (fun a => negativeExtra k d (headers a)) k)
    (hs : BankSound mem (fun a => negativePath (headers a) (long a))
      (fun a => negativeLength (headers a)))
    (hv : (headers b).Valid k d)
    (hbound : offset + k ≤ negativeLength (headers b))
    (hseed : Qary.PartialWords.Matches bits (negativePath (headers b) (long b)) offset) :
    ∃ w t, startNegative k d (headers b) offset bits (mem b) = some t ∧
      Realizes (d := d) (s.start b w) (Function.update mem b t)
        (fun a => negativeExtra k d (headers a)) k ∧
      BankSound (Function.update mem b t)
        (fun a => negativePath (headers a) (long a)) (fun a => negativeLength (headers a)) := by
  obtain ⟨t, ht, hsound, hext, w, hknown⟩ := startNegative_correct
    k d (headers b) (long b) offset bits (mem b) hv (hs b) hbound hseed
  exact ⟨w, t, ht,
    Realizes.start_update s mem _ k hreal b w t hext hknown,
    bankSound_update mem _ _ hs b t hsound⟩

/-- A correct positive-path seed uses at most one recorded letter and a real start slot. -/
theorem startPositive_transition [DecidableEq B]
    (s : State B) (mem : B → Memory α) (headers : B → Header α) (long : B → Letters α)
    (k d : ℕ) (b : B) (offset : ℕ) (bits : Bits α k)
    (hreal : Realizes (d := d) s mem (fun a => negativeExtra k d (headers a)) k)
    (hs : BankSound mem (fun a => negativePath (headers a) (long a))
      (fun a => negativeLength (headers a)))
    (hv : (headers b).Valid k d)
    (hm : (headers b).Matches (long b))
    (hbound : offset + k ≤ positiveLength (headers b))
    (hseed : ∀ i : Fin k, positivePath (headers b) (long b) (offset + i.val) = bits i) :
    ∃ extra w t, startPositive k d (headers b) offset bits extra (mem b) = some t ∧
      Realizes (d := d) (s.start b w) (Function.update mem b t)
        (fun a => negativeExtra k d (headers a)) k ∧
      BankSound (Function.update mem b t)
        (fun a => negativePath (headers a) (long a)) (fun a => negativeLength (headers a)) := by
  obtain ⟨extra, t, ht, hsound, hext, w, hknown⟩ := startPositive_exists
    k d (headers b) (long b) offset bits (mem b) hv hm (hs b) hbound hseed
  exact ⟨extra, w, t, ht,
    Realizes.start_update s mem _ k hreal b w t hext hknown,
    bankSound_update mem _ _ hs b t hsound⟩

#print axioms bankSound_update
#print axioms ready_base_fill
#print axioms complete_supplier_fill
#print axioms startNegative_transition
#print axioms startPositive_transition

end DeletionCode.Burst.ConcreteTransitions
