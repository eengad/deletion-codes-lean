import DeletionCode.Burst.ConcreteDecoder
import DeletionCode.Qary.RootSelection

/-!
Local semantic obligations for interpreting the scheduler on word paths.
These are explicit occurrence/overlap facts, not decoder-success or trace
assumptions. GeneratingModel constructs this interface from generating edited
paths; GeneratingRecovery identifies the selected roots with support components.
-/
namespace DeletionCode.Burst.ConcreteModel

variable {α : Type*} [DecidableEq α] [Inhabited α]

open DeletionCode.Qary.Windows DeletionCode.Burst.HeaderRecovery DeletionCode.Burst.SelectedWindows DeletionCode.Qary.PartialWords DeletionCode.Burst.PathMemory DeletionCode.Burst.ConcreteDecoder

structure Model (B : Type*) (x : Letters α) (n k d : ℕ) where
  header : B → Header α
  long : B → Letters α
  schedule : Recovery.Data B
  valid : ∀ b, (header b).Valid k d
  header_matches : ∀ b, (header b).Matches (long b)
  base_occurrence : ∀ b w, schedule.source b w = none →
    ∃ a, a + windowLength k d ≤ n ∧
      Agree x a (negativePath (header b) (long b))
        (windowStart (negativeExtra k d (header b)) w) (windowLength k d)
  supplier_occurrence : ∀ b w a, schedule.source b w = some a →
    ∃ side j, j + windowLength k d ≤ pathLength k d (header a) side ∧
      Agree (negativePath (header b) (long b))
        (windowStart (negativeExtra k d (header b)) w)
        (pathLetters k d (header a) (long a) side) j (windowLength k d)
  adjacent_seed : ∀ a b, schedule.adjacent a b →
    ∃ sideA sideB i j, i + k ≤ pathLength k d (header a) sideA ∧
      j + k ≤ pathLength k d (header b) sideB ∧
      Agree (pathLetters k d (header a) (long a) sideA) i
        (pathLetters k d (header b) (long b) sideB) j k
  root_occurrence : ∀ b, schedule.root b →
    ∃ a, a + negativeLength (header b) ≤ n ∧
      Agree x a (negativePath (header b) (long b)) 0 (negativeLength (header b))

variable {B : Type*} {x : Letters α} {n k d : ℕ}

def Model.Sound (M : Model B x n k d) (mem : Bank α B) : Prop :=
  ∀ b, Qary.PartialWords.Sound (mem b) (negativePath (M.header b) (M.long b))
    (negativeLength (M.header b))

def Model.Realizes (M : Model B x n k d) (s : Recovery.State B) (mem : Bank α B) : Prop :=
  SelectedWindows.Realizes (d := d) s mem (fun b => negativeExtra k d (M.header b)) k

structure Model.Invariant [DecidableEq B] (M : Model B x n k d)
    (s : Recovery.State B) (mem : Bank α B) : Prop where
  wellFormed : s.WellFormed M.schedule
  sound : M.Sound mem
  realizes : M.Realizes s mem

theorem Model.window_bound (M : Model B x n k d) (b : B) (w : Recovery.Slot) :
    windowStart (negativeExtra k d (M.header b)) w + windowLength k d ≤
      negativeLength (M.header b) := by
  rw [negativeLength_eq (M.valid b)]
  have := windowStart_le (negativeExtra k d (M.header b)) w
  omega

theorem Model.complete_known (M : Model B x n k d) (s : Recovery.State B)
    (mem : Bank α B) (hreal : M.Realizes s mem) (b : B) (hc : s.Complete b) :
    WindowKnown (mem b) 0 (negativeLength (M.header b)) := by
  rw [negativeLength_eq (M.valid b)]
  exact hreal.complete_wordKnown s mem (fun b => negativeExtra k d (M.header b)) k
    b (negativeExtra_le (M.valid b)) hc

theorem Model.sound_update [DecidableEq B] (M : Model B x n k d)
    (mem : Bank α B) (hs : M.Sound mem) (b : B) (t : Memory α)
    (ht : Qary.PartialWords.Sound t (negativePath (M.header b) (M.long b))
      (negativeLength (M.header b))) : M.Sound (Function.update mem b t) := by
  intro a
  by_cases hab : a = b
  · subst a
    simpa using ht
  · have hba : b ≠ a := Ne.symm hab
    simpa [hab, hba] using hs a

#print axioms Model.window_bound
#print axioms Model.complete_known
#print axioms Model.sound_update

end DeletionCode.Burst.ConcreteModel
