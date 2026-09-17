import DeletionCode.Windows
import Mathlib.Data.Fintype.Basic

/-!
Executable lookup of a window in the fixed word from a finite seed.
The algorithm receives only the fixed word, bounds, and the seed bits.
The unknown target word occurs only in the correctness theorems.
-/
namespace DeletionCode.SeedLookup

open Windows

/-- A candidate is in bounds and has the supplied seed at the requested offset. -/
def Matches (x : Letters) (n k L r : ℕ) (seed : Fin k → Bool) (a : ℕ) : Prop :=
  r + k ≤ L ∧ a + L ≤ n ∧ ∀ i : Fin k, x (a + r + i.val) = seed i

instance (x : Letters) (n k L r : ℕ) (seed : Fin k → Bool) (a : ℕ) :
    Decidable (Matches x n k L r seed a) := by
  unfold Matches
  infer_instance

/-- Search the finitely many candidate window starts; no witness is an input. -/
def lookup (x : Letters) (n k L r : ℕ) (seed : Fin k → Bool) : Option ℕ :=
  (List.range (n + 1)).find? (fun a => decide (Matches x n k L r seed a))

theorem lookup_sound (x : Letters) (n k L r a : ℕ) (seed : Fin k → Bool)
    (h : lookup x n k L r seed = some a) : Matches x n k L r seed a := by
  have hp : decide (Matches x n k L r seed a) = true :=
    List.find?_some (p := fun b => decide (Matches x n k L r seed b)) h
  exact of_decide_eq_true hp

theorem lookup_exists (x : Letters) (n k L r : ℕ) (seed : Fin k → Bool)
    (h : ∃ a, Matches x n k L r seed a) :
    ∃ a, lookup x n k L r seed = some a := by
  rcases h with ⟨a, ha⟩
  cases heq : lookup x n k L r seed with
  | some b => exact ⟨b, rfl⟩
  | none =>
    have hnone := List.find?_eq_none.mp heq
    have hamem : a ∈ List.range (n + 1) := by
      simp only [List.mem_range]
      have := ha.2.1
      omega
    have hfalse := hnone a hamem
    exact False.elim (hfalse (decide_eq_true ha))

theorem matches_unique (x : Letters) (n k L r a b : ℕ) (seed : Fin k → Bool)
    (hx : KUnique x n k) (ha : Matches x n k L r seed a)
    (hb : Matches x n k L r seed b) : a = b := by
  apply unique_window_lookup x n k L a b r hx ha.2.1 hb.2.1 ha.1
  intro i hi
  exact (ha.2.2 ⟨i, hi⟩).trans (hb.2.2 ⟨i, hi⟩).symm

/-- Under k-uniqueness the bounded search returns exactly the matching start. -/
theorem lookup_eq_some_iff (x : Letters) (n k L r a : ℕ) (seed : Fin k → Bool)
    (hx : KUnique x n k) :
    lookup x n k L r seed = some a ↔ Matches x n k L r seed a := by
  constructor
  · exact lookup_sound x n k L r a seed
  · intro ha
    obtain ⟨b, hb⟩ := lookup_exists x n k L r seed ⟨a, ha⟩
    have hab := matches_unique x n k L r a b seed hx ha
      (lookup_sound x n k L r b seed hb)
    simpa [hab] using hb

/-- Copy the entire located window as finite data. -/
def recoverWindow (x : Letters) (n k L r : ℕ) (seed : Fin k → Bool) :
    Option (Fin L → Bool) :=
  (lookup x n k L r seed).map (fun a i => x (a + i.val))

/-- Any returned window really is an in-bounds window of the fixed word. -/
theorem recoverWindow_sound (x : Letters) (n k L r : ℕ) (seed : Fin k → Bool)
    (bits : Fin L → Bool) (h : recoverWindow x n k L r seed = some bits) :
    ∃ a, Matches x n k L r seed a ∧ bits = fun i => x (a + i.val) := by
  unfold recoverWindow at h
  cases heq : lookup x n k L r seed with
  | none => simp [heq] at h
  | some a =>
    simp only [heq, Option.map_some, Option.some.injEq] at h
    exact ⟨a, lookup_sound x n k L r a seed heq, h.symm⟩

/-- A target window occurring in x is recovered exactly from its seed. -/
theorem recoverWindow_of_occurrence
    (x target : Letters) (n k L r a w : ℕ) (seed : Fin k → Bool)
    (hx : KUnique x n k) (hr : r + k ≤ L) (ha : a + L ≤ n)
    (hocc : Agree x a target w L)
    (hseed : ∀ i : Fin k, seed i = target (w + r + i.val)) :
    recoverWindow x n k L r seed = some (fun i : Fin L => target (w + i.val)) := by
  have hmatch : Matches x n k L r seed a := by
    refine ⟨hr, ha, ?_⟩
    intro i
    have hi : r + i.val < L := by omega
    calc
      x (a + r + i.val) = target (w + r + i.val) := by
        simpa [Nat.add_assoc] using hocc (r + i.val) hi
      _ = seed i := (hseed i).symm
  have hlookup := (lookup_eq_some_iff x n k L r a seed hx).mpr hmatch
  unfold recoverWindow
  rw [hlookup]
  simp only [Option.map_some, Option.some.injEq]
  funext i
  exact hocc i.val i.isLt

#print axioms lookup_sound
#print axioms lookup_exists
#print axioms matches_unique
#print axioms lookup_eq_some_iff
#print axioms recoverWindow_sound
#print axioms recoverWindow_of_occurrence

end DeletionCode.SeedLookup
