import DeletionCode.Explicit.ConditionalChooser
import DeletionCode.Explicit.Machine.TernaryProbability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-! Turing-machine certificates for the executable ternary selector. -/
namespace DeletionCode.Explicit.Machine.ConditionalChoice

open FieldHash ConditionalChooser
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

abbrev prefixEncoding := encList Ternary.tritEncoding

variable {π : Type} {enc : π ↪ List Bool}

theorem score_polyTime (E : π → Evaluator) (μ : π → Fin 3 → ℚ)
    (hE : ∀ i, ComputableInPolyTime (fun x : π × Prefix => E x.1 i x.2)
      (encPair enc prefixEncoding) encRat)
    (hμ : ∀ i, ComputableInPolyTime (fun x => μ x i) enc encRat) :
    ComputableInPolyTime (fun x : π × Prefix => score (E x.1) (μ x.1) x.2)
      (encPair enc prefixEncoding) encRat := by
  have hterm (i : Fin 3) := rat_div' (hE i) ((hμ i).comp (fst enc prefixEncoding))
  exact rat_add' (rat_add' (hterm 0) (hterm 1)) (hterm 2)

private theorem step_polyTime {E : π × Prefix → ℚ}
    (hE : ComputableInPolyTime E (encPair enc prefixEncoding) encRat) :
    ComputableInPolyTime (fun x : π × Prefix => step (fun p => E (x.1, p)) x.2)
      (encPair enc prefixEncoding) prefixEncoding := by
  have hp := fst enc prefixEncoding
  have hw := snd enc prefixEncoding
  have hchild (a : F₃) : ComputableInPolyTime (fun x : π × Prefix => E (x.1, x.2 ++ [a]))
      (encPair enc prefixEncoding) encRat :=
    hE.comp (hp.prod (listAppend' hw (const [a])))
  have hnext : ComputableInPolyTime (fun x : π × Prefix => next (fun p => E (x.1,p)) x.2)
      (encPair enc prefixEncoding) Ternary.tritEncoding :=
    ite_decide (rat_le' (hchild 0) hE) (const 0)
      (ite_decide (rat_le' (hchild 1) hE) (const 1) (const 2))
  exact listAppend' hw (cons' hnext (const []))

private def tritBits : ℕ := ∑ a : F₃, (Ternary.tritEncoding a).length

private theorem prefix_length_bound (p : Prefix) :
    (prefixEncoding p).length ≤ (2 * tritBits + 1) * p.length := by
  rw [Nat.mul_comm]
  apply length_encList_le
  intro a _
  exact Finset.single_le_sum (f := fun b => (Ternary.tritEncoding b).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

/-- The public data contains all evaluator inputs other than the prefix.
The result contains the entries in the order they were fixed. -/
theorem choose_polyTime {E : π × Prefix → ℚ}
    (hE : ComputableInPolyTime E (encPair enc prefixEncoding) encRat) :
    ComputableInPolyTime (fun x : π × ℕ => choose (fun p => E (x.1, p)) x.2)
      (encPair enc encUnary) prefixEncoding := by
  have hfuel := snd enc encUnary
  let size (x : π × ℕ) := (2 * tritBits + 1) * x.2
  have hs : PolyBounded (fun x => (encPair enc encUnary x).length) size := by
    apply (PolyBounded.const (2 * tritBits + 1)).mul
    simpa only [encUnary_apply, List.length_replicate] using hfuel.polyBounded_length
  exact (iterateWith_spec (step := fun a => step (fun p => E (a, p))) (fst enc encUnary)
    hfuel (const []) (step_polyTime hE) (fun _ i p => p.length = i)
    (fun _ => rfl) (fun _ _ p _ hp => by rw [step_length, hp]) hs
    (fun x i p hi hp => (prefix_length_bound p).trans (Nat.mul_le_mul_left _ (hp ▸ hi)))).1

set_option maxHeartbeats 1000000 in
theorem choose_three_polyTime (E : π → Evaluator) (μ : π → Fin 3 → ℚ)
    (hE : ∀ i, ComputableInPolyTime (fun x : π × Prefix => E x.1 i x.2)
      (encPair enc prefixEncoding) encRat)
    (hμ : ∀ i, ComputableInPolyTime (fun x => μ x i) enc encRat) :
    ComputableInPolyTime (fun x : π × ℕ => choose (score (E x.1) (μ x.1)) x.2)
      (encPair enc encUnary) prefixEncoding :=
  choose_polyTime (E := fun x => score (E x.1) (μ x.1) x.2) (score_polyTime E μ hE hμ)

#print axioms score_polyTime
#print axioms choose_polyTime
#print axioms choose_three_polyTime

end DeletionCode.Explicit.Machine.ConditionalChoice
