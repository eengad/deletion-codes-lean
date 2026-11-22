import DeletionCode.Explicit.DeterministicEncodings
import DeletionCode.Explicit.EditBallCount
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Fixed-alphabet word enumeration when the number of words is polynomial in the input. -/
namespace DeletionCode.Explicit.Machine

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

theorem encoded_word_length_le {q : ℕ} (w : QWord q) :
    (wordEncoding q w).length ≤ (2 * q + 1) * w.length := by
  induction w with
  | nil => simp [wordEncoding]
  | cons a w ih =>
    have ha := a.isLt
    simp only [wordEncoding, encList_cons, List.length_append, length_frame,
      Function.Embedding.coeFn_mk, encUnary_apply, List.length_replicate, List.length_cons,
      Nat.mul_succ] at *
    omega

private def prependSymbols (q : ℕ) (xs : List (QWord q)) : List (QWord q) :=
  (List.finRange q).flatMap fun a => xs.map (a :: ·)

private theorem prependSymbols_polyTime (q : ℕ) :
    ComputableInPolyTime (prependSymbols q)
      (encList (wordEncoding q)) (encList (wordEncoding q)) := by
  unfold prependSymbols
  apply flatMapConst
  intro a _
  apply ComputableInPolyTime.map
  unfold wordEncoding
  exact (cons _).comp ((const a).prod id')

/-- The same lexicographic enumeration as `wordsOfLength`, with the iteration count
given by an efficient unary length and a polynomial bound on the number of words. -/
theorem wordsOfLength_polyTime {α : Type} {enc : α ↪ List Bool} {m : α → ℕ}
    {q : ℕ} (hq : 2 ≤ q)
    (hm : ComputableInPolyTime m enc encUnary)
    (hcount : PolyBounded (fun a => (enc a).length) (fun a => q ^ m a)) :
    ComputableInPolyTime (fun a => wordsOfLength q (m a)) enc (encList (wordEncoding q)) := by
  have hmSize : PolyBounded (fun a => (enc a).length) m := by
    simpa only [encUnary_apply, List.length_replicate] using hm.polyBounded_length
  have hsize : PolyBounded (fun a => (enc a).length)
      (fun a => (2 * ((2 * q + 1) * m a) + 1) * q ^ m a) :=
    (((PolyBounded.const 2).mul ((PolyBounded.const (2 * q + 1)).mul hmSize)).add
      (PolyBounded.const 1)).mul hcount
  obtain ⟨hmachine, hcorrect⟩ := iterate_spec hm (const ([[]] : List (QWord q)))
    (prependSymbols_polyTime q) (fun _ i xs => xs = wordsOfLength q i)
    (fun _ => rfl) (fun _ i xs _ h => by rw [h]; rfl) hsize (fun a i xs hi h => by
      rw [h]
      refine (length_encList_le (wordEncoding q) _ (b := (2 * q + 1) * m a) ?_).trans ?_
      · intro w hw
        exact (encoded_word_length_le w).trans (Nat.mul_le_mul_left _
          (le_of_eq (mem_wordsOfLength.mp hw) |>.trans hi))
      · rw [length_wordsOfLength]
        rw [Nat.mul_comm (q ^ i)]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hi))
  exact hmachine.of_enc_eq (fun a => congrArg _ (hcorrect a).symm)

end DeletionCode.Explicit.Machine
