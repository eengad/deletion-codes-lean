import DeletionCode.Burst.ConcreteModel
import DeletionCode.Burst.ConcreteTransitions

/-!
Every available abstract recovery step has a successful concrete realization.
Start steps choose a selected slot containing the seed actually transferred;
they need not retain the arbitrary slot named by the original abstract step.
Lookup and source-read success are derived from stored letters and occurrences.
-/

namespace DeletionCode.Burst.ConcreteProgress

variable {α : Type*} [DecidableEq α] [Inhabited α]

open DeletionCode.Qary.Windows DeletionCode.Burst.HeaderRecovery DeletionCode.Qary.PartialWords DeletionCode.Burst.SelectedWindows DeletionCode.Burst.PathMemory
open DeletionCode.Burst.ConcreteModel DeletionCode.Burst.ConcreteDecoder DeletionCode.Burst.ConcreteStart DeletionCode.Qary.ConcreteFill DeletionCode.Burst.ConcreteTransitions DeletionCode.Recovery

variable {B : Type*} [DecidableEq B] {x : Letters α} {n k d : ℕ}

private theorem execute_start (M : Model B x n k d)
    (s : State B) (mem : Bank α B) (hi : M.Invariant s mem)
    (source : B) (sourceSide : Bool) (sourceOffset : ℕ)
    (dest : B) (destSide : Bool) (destOffset : ℕ) (bits : Qary.PartialWords.Bits α k)
    (hread : readPath k d (M.header source) (mem source) sourceSide sourceOffset k = some bits)
    (hbound : destOffset + k ≤ pathLength k d (M.header dest) destSide)
    (hmatch : Matches bits (pathLetters k d (M.header dest) (M.long dest) destSide) destOffset) :
    ∃ w extra mem',
      execute x n k d M.header mem
        (.start source sourceSide sourceOffset dest destSide destOffset extra) = some mem' ∧
      M.Invariant (s.start dest w) mem' := by
  cases destSide with
  | false =>
    obtain ⟨w, t, ht, hreal, hsound⟩ := startNegative_transition s mem M.header M.long
      k d dest destOffset bits hi.realizes hi.sound (M.valid dest)
      hbound hmatch
    refine ⟨w, default, Function.update mem dest t, ?_, ?_⟩
    · simp only [execute, hread, Option.bind_some, Bool.false_eq_true, ite_false,
        ht, Option.map_some]
    · exact ⟨State.start_wellFormed M.schedule s hi.wellFormed dest w, hsound, hreal⟩
  | true =>
    have hseed : ∀ i : Fin k,
        positivePath (M.header dest) (M.long dest) (destOffset + i.val) = bits i :=
      fun i => (hmatch i).symm
    obtain ⟨extra, w, t, ht, hreal, hsound⟩ := startPositive_transition s mem M.header M.long
      k d dest destOffset bits hi.realizes hi.sound (M.valid dest)
      (M.header_matches dest) hbound hseed
    refine ⟨w, extra, Function.update mem dest t, ?_, ?_⟩
    · simp only [execute, hread, Option.bind_some, ite_true,
        ht, Option.map_some]
    · exact ⟨State.start_wellFormed M.schedule s hi.wellFormed dest w, hsound, hreal⟩

/-- Concrete progress with a real seed slot and a successful executable record. -/
theorem lift_step (M : Model B x n k d) (hx : KUnique x n k)
    (s : State B) (mem : Bank α B) (hi : M.Invariant s mem)
    {q : State B} (step : Recovery.Step M.schedule s q) :
    ∃ q' mem' instruction,
      Recovery.Step M.schedule s q' ∧
      execute x n k d M.header mem instruction = some mem' ∧ M.Invariant q' mem' := by
  cases step with
  | startAdjacent a b w ha hab hb =>
    obtain ⟨sideA, sideB, i, j, hibound, hjbound, hagree⟩ := M.adjacent_seed a b hab
    obtain ⟨bits, hread, hmatch⟩ := readPath_complete k d (M.header a) (M.long a) (mem a)
      sideA i k (M.valid a) (M.header_matches a) (hi.sound a)
      (M.complete_known s mem hi.realizes a ha) hibound
    have htarget : Matches bits (pathLetters k d (M.header b) (M.long b) sideB) j := by
      intro u
      exact (hmatch u).trans (hagree u.val u.isLt)
    obtain ⟨v, extra, mem', hexecute, hinvariant⟩ := execute_start M s mem hi
      a sideA i b sideB j bits hread hjbound htarget
    exact ⟨s.start b v, mem', .start a sideA i b sideB j extra,
      Step.startAdjacent s a b v ha hab hb, hexecute, hinvariant⟩
  | startSupplier b a w v hr hn hsrc ha =>
    obtain ⟨r, seed, hrbound, hseedread⟩ := hi.realizes.ready_seedKnown s mem
      (fun b => negativeExtra k d (M.header b)) k b w
      (negativeExtra_le (M.valid b)) hr
    obtain ⟨side, j, hjbound, hagree⟩ := M.supplier_occurrence b w a hsrc
    have hwindow := M.window_bound b w
    have hsourceBound : windowStart (negativeExtra k d (M.header b)) w + r + k ≤
        negativeLength (M.header b) := by
      change r + k ≤ windowLength k d at hrbound
      omega
    have htargetBound : j + r + k ≤ pathLength k d (M.header a) side := by
      change r + k ≤ windowLength k d at hrbound
      omega
    have hsourceMatch := readBits_sound (mem b) (negativePath (M.header b) (M.long b))
      (negativeLength (M.header b)) (windowStart (negativeExtra k d (M.header b)) w + r)
      k (hi.sound b) hsourceBound seed hseedread
    have htarget : Matches seed (pathLetters k d (M.header a) (M.long a) side) (j + r) := by
      intro u
      calc
        seed u = negativePath (M.header b) (M.long b)
            (windowStart (negativeExtra k d (M.header b)) w + r + u.val) := hsourceMatch u
        _ = pathLetters k d (M.header a) (M.long a) side (j + r + u.val) := by
          have hu : r + u.val < windowLength k d := by
            have := u.isLt
            change r + k ≤ windowLength k d at hrbound
            omega
          simpa only [Nat.add_assoc] using hagree (r + u.val) hu
    have hread : readPath k d (M.header b) (mem b) false
        (windowStart (negativeExtra k d (M.header b)) w + r) k = some seed := by
      simpa only [readPath, ite_eq_left hsourceBound] using hseedread
    obtain ⟨newSlot, extra, mem', hexecute, hinvariant⟩ := execute_start M s mem hi
      b false (windowStart (negativeExtra k d (M.header b)) w + r)
      a side (j + r) seed hread htargetBound htarget
    exact ⟨s.start a newSlot, mem',
      .start b false (windowStart (negativeExtra k d (M.header b)) w + r)
        a side (j + r) extra,
      Step.startSupplier s b a w newSlot hr hn hsrc ha, hexecute, hinvariant⟩
  | fillBase b w hr hn hsrc =>
    obtain ⟨r, seed, hrbound, hseedread⟩ := hi.realizes.ready_seedKnown s mem
      (fun b => negativeExtra k d (M.header b)) k b w
      (negativeExtra_le (M.valid b)) hr
    obtain ⟨t, ht, hsound, hext, hknown⟩ := fillFromBase_correct x
      (negativePath (M.header b) (M.long b)) n k (windowLength k d) (mem b)
      (negativeLength (M.header b)) (windowStart (negativeExtra k d (M.header b)) w)
      r seed hx (hi.sound b) (M.window_bound b w) hrbound hseedread
      (M.base_occurrence b w hsrc)
    have hstep := Step.fillBase s b w hr hn hsrc
    refine ⟨s.fill b w, Function.update mem b t, .fillBase b w r, hstep, ?_, ?_⟩
    · simp only [execute, ht, Option.map_some]
    · exact ⟨step_preserves M.schedule hstep hi.wellFormed,
        M.sound_update mem hi.sound b t hsound,
        SelectedWindows.Realizes.fill_update s mem (fun b => negativeExtra k d (M.header b))
          k hi.realizes b w t hext ⟨_, hknown⟩⟩
  | fillSupplier b a w hr hn hsrc ha =>
    obtain ⟨side, j, hjbound, hagree⟩ := M.supplier_occurrence b w a hsrc
    obtain ⟨bits, hread, hmatch⟩ := readPath_complete k d (M.header a) (M.long a) (mem a)
      side j (windowLength k d) (M.valid a) (M.header_matches a) (hi.sound a)
      (M.complete_known s mem hi.realizes a ha) hjbound
    have htarget : Matches bits (negativePath (M.header b) (M.long b))
        (windowStart (negativeExtra k d (M.header b)) w) := by
      intro u
      exact (hmatch u).trans (hagree u.val u.isLt).symm
    obtain ⟨t, ht, hsound, hext, hknown⟩ := writeBits_correct (mem b)
      (negativePath (M.header b) (M.long b)) (negativeLength (M.header b))
      (windowStart (negativeExtra k d (M.header b)) w) (windowLength k d)
      (hi.sound b) (M.window_bound b w) bits htarget
    have hstep := Step.fillSupplier s b a w hr hn hsrc ha
    refine ⟨s.fill b w, Function.update mem b t, .fillSupplier a side j b w, hstep, ?_, ?_⟩
    · simp only [execute, hread, Option.bind_some, ht, Option.map_some]
    · exact ⟨step_preserves M.schedule hstep hi.wellFormed,
        M.sound_update mem hi.sound b t hsound,
        SelectedWindows.Realizes.fill_update s mem (fun b => negativeExtra k d (M.header b))
          k hi.realizes b w t hext ⟨bits, hknown⟩⟩

#print axioms lift_step

end DeletionCode.Burst.ConcreteProgress
