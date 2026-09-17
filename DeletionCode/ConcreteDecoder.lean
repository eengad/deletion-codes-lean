import DeletionCode.ConcreteFill
import DeletionCode.ConcreteStart
import DeletionCode.PathMemory

/-!
A deterministic decoder for explicit recovery records. Inputs are the fixed x,
finite bubble headers, root positions, and a list of start/fill instructions.
No unknown target paths, generating-set witnesses, or proof oracles are inputs.

RecordBounds and RecordSerialization encode these fields into finite Description.
GeneratingRecovery proves that every generating edited-word family has a
successful bounded record; ManuscriptCounting completes the signed-rule count.
-/
namespace DeletionCode.ConcreteDecoder

open Windows PartialWords HeaderRecovery SelectedWindows

abbrev Bank (B : Type*) := B → Memory

inductive Instruction (B : Type*) where
  | start (source : B) (sourceSide : Bool) (sourceOffset : ℕ)
      (dest : B) (destSide : Bool) (destOffset : ℕ) (extra : Bool)
  | fillBase (dest : B) (window : Recovery.Slot) (seedOffset : ℕ)
  | fillSupplier (source : B) (sourceSide : Bool) (sourceOffset : ℕ)
      (dest : B) (window : Recovery.Slot)

variable {B : Type*} [DecidableEq B]

def execute (x : Letters) (n k : ℕ) (header : B → Header)
    (mem : Bank B) : Instruction B → Option (Bank B)
  | .start source sourceSide sourceOffset dest destSide destOffset extra =>
    (PathMemory.readPath k (header source) (mem source) sourceSide sourceOffset k).bind
      fun bits =>
        let result := if destSide then
          ConcreteStart.startPositive k (header dest) destOffset bits extra (mem dest)
        else ConcreteStart.startNegative k (header dest) destOffset bits (mem dest)
        result.map (Function.update mem dest)
  | .fillBase dest window seedOffset =>
    (ConcreteFill.fillFromBase x n k (windowLength k) (mem dest)
      (negativeLength k (header dest))
      (windowStart (negativeExtra k (header dest)) window) seedOffset).map
      (Function.update mem dest)
  | .fillSupplier source sourceSide sourceOffset dest window =>
    (PathMemory.readPath k (header source) (mem source) sourceSide sourceOffset
      (windowLength k)).bind fun bits =>
        (writeBits (mem dest) (negativeLength k (header dest))
          (windowStart (negativeExtra k (header dest)) window) bits).map
          (Function.update mem dest)

def run (x : Letters) (n k : ℕ) (header : B → Header)
    (mem : Bank B) : List (Instruction B) → Option (Bank B)
  | [] => some mem
  | instruction :: rest =>
    (execute x n k header mem instruction).bind fun mem' => run x n k header mem' rest

/-- Roots record a bubble name and one position in x. -/
def loadRoots (x : Letters) (n k : ℕ) (header : B → Header)
    (mem : Bank B) : List (B × ℕ) → Option (Bank B)
  | [] => some mem
  | (b, a) :: rest =>
    (ConcreteFill.loadRoot x n a (negativeLength k (header b))
      (mem b) (negativeLength k (header b))).bind fun t =>
        loadRoots x n k header (Function.update mem b t) rest

abbrev Output (k : ℕ) (header : B → Header) := ∀ b, PartialWords.Bits (negativeLength k (header b))

/-- Output succeeds only when every bit of every finite negative path is readable. -/
def finish [Fintype B] (k : ℕ) (header : B → Header) (mem : Bank B) :
    Option (Output k header) :=
  if ∀ b, readBits (mem b) 0 (negativeLength k (header b)) =
      some ((readBits (mem b) 0 (negativeLength k (header b))).getD (fun _ => false))
  then some (fun b => (readBits (mem b) 0 (negativeLength k (header b))).getD (fun _ => false))
  else none

def decode [Fintype B] (x : Letters) (n k : ℕ) (header : B → Header)
    (roots : List (B × ℕ)) (instructions : List (Instruction B)) :
    Option (Output k header) :=
  (loadRoots x n k header (fun _ => empty) roots).bind fun initial =>
    (run x n k header initial instructions).bind (finish k header)

theorem finish_eq_some_iff [Fintype B] (k : ℕ) (header : B → Header)
    (mem : Bank B) (output : Output k header) :
    finish k header mem = some output ↔
      ∀ b, readBits (mem b) 0 (negativeLength k (header b)) = some (output b) := by
  unfold finish
  split
  · rename_i h
    constructor
    · intro heq
      have heq' := Option.some.inj heq
      intro b
      rw [← heq']
      exact h b
    · intro hout
      congr 1
      funext b
      simp [hout b]
  · rename_i h
    constructor
    · simp
    · intro hout
      apply False.elim
      apply h
      intro b
      simp [hout b]

/-- Sound completed memory produces exactly the finite target negative paths. -/
theorem finish_correct [Fintype B] (k : ℕ) (header : B → Header)
    (long : B → Letters) (mem : Bank B)
    (hs : ∀ b, Sound (mem b) (negativePath k (header b) (long b))
      (negativeLength k (header b)))
    (hknown : ∀ b, WindowKnown (mem b) 0 (negativeLength k (header b))) :
    finish k header mem = some (fun b i => negativePath k (header b) (long b) i.val) := by
  apply (finish_eq_some_iff k header mem _).mpr
  intro b
  obtain ⟨bits, hread⟩ := hknown b
  have hbits := readBits_sound (mem b) (negativePath k (header b) (long b))
    (negativeLength k (header b)) 0 (negativeLength k (header b))
    (hs b) (by omega) bits hread
  rw [hread]
  congr 1
  funext i
  simpa only [Nat.zero_add] using hbits i

/-- Running a concatenated record is ordinary sequential composition. -/
theorem run_append (x : Letters) (n k : ℕ) (header : B → Header)
    (first second : List (Instruction B)) (mem : Bank B) :
    run x n k header mem (first ++ second) =
      (run x n k header mem first).bind (fun t => run x n k header t second) := by
  induction first generalizing mem with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [List.cons_append, run]
    cases he : execute x n k header mem instruction with
    | none => rfl
    | some t => exact ih t

#print axioms finish_eq_some_iff
#print axioms finish_correct
#print axioms run_append

end DeletionCode.ConcreteDecoder
