import DeletionCode.Explicit.DeterministicEncodings
import DeletionCode.Explicit.Labels
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower

/-! Machine-level polynomial time for the construction's word rank. -/

namespace DeletionCode.Explicit.Machine

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

private abbrev symbolEncoding (q : ℕ) : Fin q ↪ List Bool :=
  ⟨fun a => encUnary a.val, fun _ _ h => Fin.ext (encUnary.injective h)⟩

private theorem rank_snoc {q : ℕ} (w : QWord q) (a : Fin q) :
    wordRank (w ++ [a]) = q * wordRank w + a.val := by
  simp [wordRank, List.reverse_append, Nat.ofDigits_cons, Nat.add_comm]

/-- The same word rank used by the short-word labels, with binary numeric output. -/
theorem wordRank_polyTime {q : ℕ} (hq : 2 ≤ q) :
    ComputableInPolyTime (wordRank (q := q)) (wordEncoding q) encNat := by
  let step (r : ℕ) (a : Fin q) : ℕ := q * r + a.val
  have hval : ComputableInPolyTime (fun a : Fin q => a.val) (symbolEncoding q) encNat :=
    of_finite _
  have hstep : ComputableInPolyTime (fun p : ℕ × Fin q => step p.1 p.2)
      (encPair encNat (symbolEncoding q)) encNat :=
    binary_add.comp
      ((binary_mul' (const q) (fst encNat (symbolEncoding q))).prod
        (hval.comp (snd encNat (symbolEncoding q))))
  have hword : ComputableInPolyTime (fun w : QWord q => w)
      (wordEncoding q) (encList (symbolEncoding q)) := id'
  have hsize : PolyBounded (fun w : QWord q => (wordEncoding q w).length)
      (fun w => q * (wordEncoding q w).length + 1) :=
    PolyBounded.of_forall_le (q + 1) 1 (fun w => by
      simp only [pow_one]
      nlinarith)
  obtain ⟨hmachine, hcorrect⟩ :=
    foldl_spec hword (const 0) hstep (fun _ consumed r => r = wordRank consumed)
      (fun _ => rfl) (fun _ consumed r a _ hr => by rw [hr, rank_snoc])
      hsize (fun w consumed r hprefix hr => by
        have hq2 : q ≤ 2 ^ q := q.lt_two_pow_self.le
        have hrank : r ≤ 2 ^ (q * consumed.length) := by
          rw [hr, pow_mul]
          exact (wordRank_lt hq consumed).le.trans (Nat.pow_le_pow_left hq2 _)
        have hlength : consumed.length ≤ (wordEncoding q w).length := by
          exact hprefix.length_le.trans
            (SizedListEncoding.length_le (encA := symbolEncoding q)
              (encL := encList (symbolEncoding q)) w)
        exact (length_encNat_le_of_le_two_pow hrank).trans
          (Nat.add_le_add_right (Nat.mul_le_mul_left q hlength) 1))
  exact hmachine.of_enc_eq (fun w => congrArg encNat (hcorrect w).symm)

/-- Rank the final theorem's encoded word and return its binary representation as public bits. -/
theorem wordRank_bits_polyTime {q : ℕ} (hq : 2 ≤ q) :
    ComputableInPolyTime (fun w : QWord q => encNat (wordRank w)) (wordEncoding q) encBits :=
  (wordRank_polyTime hq).of_enc_eq (fun _ => rfl)

#print axioms wordRank_polyTime
#print axioms wordRank_bits_polyTime

end DeletionCode.Explicit.Machine
