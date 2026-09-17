import DeletionCode.ConcreteDecoder
import DeletionCode.RootSelection

/-!
Local semantic obligations for interpreting the scheduler on word paths.
These are explicit occurrence/overlap facts, not decoder-success or trace
assumptions. GeneratingModel constructs this interface from generating edited
paths; GeneratingRecovery identifies the selected roots with support components.
-/
namespace DeletionCode.ConcreteModel

open Windows HeaderRecovery SelectedWindows PartialWords PathMemory ConcreteDecoder

structure Model (B : Type*) (x : Letters) (n k : ℕ) where
  header : B → Header
  long : B → Letters
  schedule : Recovery.Data B
  rho_lower : ∀ b, 1 ≤ (header b).rho
  rho_upper : ∀ b, (header b).rho ≤ k + 1
  header_bit : ∀ b, long b (editOffset k) = (header b).bit
  base_occurrence : ∀ b w, schedule.source b w = none →
    ∃ a, a + windowLength k ≤ n ∧
      Agree x a (negativePath k (header b) (long b))
        (windowStart (negativeExtra k (header b)) w) (windowLength k)
  supplier_occurrence : ∀ b w a, schedule.source b w = some a →
    ∃ side j, j + windowLength k ≤ pathLength k (header a) side ∧
      Agree (negativePath k (header b) (long b))
        (windowStart (negativeExtra k (header b)) w)
        (pathLetters k (header a) (long a) side) j (windowLength k)
  adjacent_seed : ∀ a b, schedule.adjacent a b →
    ∃ sideA sideB i j, i + k ≤ pathLength k (header a) sideA ∧
      j + k ≤ pathLength k (header b) sideB ∧
      Agree (pathLetters k (header a) (long a) sideA) i
        (pathLetters k (header b) (long b) sideB) j k
  root_occurrence : ∀ b, schedule.root b →
    ∃ a, a + negativeLength k (header b) ≤ n ∧
      Agree x a (negativePath k (header b) (long b)) 0 (negativeLength k (header b))

variable {B : Type*} {x : Letters} {n k : ℕ}

def Model.Sound (M : Model B x n k) (mem : Bank B) : Prop :=
  ∀ b, PartialWords.Sound (mem b) (negativePath k (M.header b) (M.long b))
    (negativeLength k (M.header b))

def Model.Realizes (M : Model B x n k) (s : Recovery.State B) (mem : Bank B) : Prop :=
  SelectedWindows.Realizes s mem (fun b => negativeExtra k (M.header b)) k

structure Model.Invariant [DecidableEq B] (M : Model B x n k)
    (s : Recovery.State B) (mem : Bank B) : Prop where
  wellFormed : s.WellFormed M.schedule
  sound : M.Sound mem
  realizes : M.Realizes s mem

theorem Model.window_bound (M : Model B x n k) (b : B) (w : Recovery.Slot) :
    windowStart (negativeExtra k (M.header b)) w + windowLength k ≤
      negativeLength k (M.header b) := by
  rw [negativeLength_eq k (M.header b) (M.rho_lower b) (M.rho_upper b)]
  have := windowStart_le (negativeExtra k (M.header b)) w
  omega

theorem Model.complete_known (M : Model B x n k) (s : Recovery.State B)
    (mem : Bank B) (hreal : M.Realizes s mem) (b : B) (hc : s.Complete b) :
    WindowKnown (mem b) 0 (negativeLength k (M.header b)) := by
  rw [negativeLength_eq k (M.header b) (M.rho_lower b) (M.rho_upper b)]
  exact hreal.complete_wordKnown s mem (fun b => negativeExtra k (M.header b)) k
    b (Nat.le_of_lt (negativeExtra_lt k (M.header b) (M.rho_lower b) (M.rho_upper b))) hc

theorem Model.sound_update [DecidableEq B] (M : Model B x n k)
    (mem : Bank B) (hs : M.Sound mem) (b : B) (t : Memory)
    (ht : PartialWords.Sound t (negativePath k (M.header b) (M.long b))
      (negativeLength k (M.header b))) : M.Sound (Function.update mem b t) := by
  intro a
  by_cases hab : a = b
  · subst a
    simpa using ht
  · have hba : b ≠ a := Ne.symm hab
    simpa [hab, hba] using hs a

#print axioms Model.window_bound
#print axioms Model.complete_known
#print axioms Model.sound_update

end DeletionCode.ConcreteModel
