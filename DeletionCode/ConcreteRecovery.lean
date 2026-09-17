import DeletionCode.ConcreteProgress
import DeletionCode.ConcreteInitialization

/-!
Bounded execution of the concrete decoder from sound realized root data.
The instruction record is constructed from proved executable local progress;
its successful execution is not an input hypothesis.
-/
namespace DeletionCode.ConcreteRecovery

open Windows PartialWords HeaderRecovery SelectedWindows ConcreteDecoder ConcreteModel

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {x : Letters} {n k : ℕ}

theorem bounded_run (M : Model B x n k) (hx : KUnique x n k)
    (s : Recovery.State B) (mem : Bank B) (hi : M.Invariant s mem) :
    ∃ instructions mem' q,
      run x n k M.header mem instructions = some mem' ∧
      M.Invariant q mem' ∧ (∀ b, q.Complete b) ∧
      instructions.length + s.score ≤ 4 * Fintype.card B := by
  classical
  let N := 4 * Fintype.card B
  have aux : ∀ d : ℕ, ∀ s : Recovery.State B, ∀ mem : Bank B,
      N - s.score = d → M.Invariant s mem →
      ∃ instructions mem' q,
        run x n k M.header mem instructions = some mem' ∧
        M.Invariant q mem' ∧ (∀ b, q.Complete b) ∧
        instructions.length + s.score ≤ N := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro s mem hd hi
      by_cases hdone : ∀ b, s.Complete b
      · refine ⟨[], mem, s, rfl, hi, hdone, ?_⟩
        simpa [N] using Recovery.State.score_le s
      · obtain ⟨q, hstep⟩ := Recovery.progress M.schedule s hi.wellFormed hdone
        obtain ⟨q', mem', instruction, hstep', hexec, hinv⟩ :=
          ConcreteProgress.lift_step M hx s mem hi hstep
        have hscore : q'.score = s.score + 1 := Recovery.step_score M.schedule hstep'
        have hbound : q'.score ≤ N := Recovery.State.score_le q'
        have hlt : N - q'.score < d := by omega
        obtain ⟨instructions, mem'', q'', hrun, hfinal, hcomplete, hcost⟩ :=
          ih (N - q'.score) hlt q' mem' rfl hinv
        refine ⟨instruction :: instructions, mem'', q'', ?_, hfinal, hcomplete, ?_⟩
        · simp only [run, hexec, Option.bind_some]
          exact hrun
        · simp only [List.length_cons]
          omega
  exact aux (N - s.score) s mem rfl hi

/-- Bounded concrete execution recovers all finite negative words exactly. -/
theorem bounded_run_finishes (M : Model B x n k) (hx : KUnique x n k)
    (s : Recovery.State B) (mem : Bank B) (hi : M.Invariant s mem) :
    ∃ instructions,
      instructions.length + s.score ≤ 4 * Fintype.card B ∧
      (run x n k M.header mem instructions).bind (finish k M.header) =
        some (fun b i => negativePath k (M.header b) (M.long b) i.val) := by
  obtain ⟨instructions, mem', q, hrun, hinv, hdone, hcost⟩ := bounded_run M hx s mem hi
  refine ⟨instructions, hcost, ?_⟩
  rw [hrun]
  simp only [Option.bind_some]
  apply finish_correct k M.header M.long mem' hinv.sound
  intro b
  exact M.complete_known q mem' hinv.realizes b (hdone b)

#print axioms bounded_run
#print axioms bounded_run_finishes

/-- Actual root positions and at most 4|B| instructions decode the modeled words. -/
theorem decode_exists (M : Model B x n k) (hx : KUnique x n k) :
    ∃ roots instructions,
      roots.length = ConcreteInitialization.rootCount M ∧
      instructions.length ≤ 4 * Fintype.card B ∧
      decode x n k M.header roots instructions =
        some (fun b i => negativePath k (M.header b) (M.long b) i.val) := by
  obtain ⟨roots, mem, hroots, hload, hi⟩ := ConcreteInitialization.initialization_exists M
  obtain ⟨instructions, hcost, hrun⟩ :=
    bounded_run_finishes M hx (Recovery.initial M.schedule) mem hi
  refine ⟨roots, instructions, hroots, by omega, ?_⟩
  simp only [decode, hload, Option.bind_some]
  exact hrun

#print axioms decode_exists

end DeletionCode.ConcreteRecovery
