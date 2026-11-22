import DeletionCode.Explicit.DeterministicEncodings
import DeletionCode.Explicit.EditBall
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! Machine certificates for enumerating bounded substring edits. -/
namespace DeletionCode.Explicit.Machine

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Burst (Edit)

private abbrev editInput (q : ℕ) : ((QWord q × ℕ) × ℕ) ↪ List Bool :=
  encPair (encPair (wordEncoding q) encUnary) encUnary

private theorem apply_polyTime {q : ℕ} (v : QWord q) :
    ComputableInPolyTime
      (fun p : (QWord q × ℕ) × ℕ => (Edit.mk p.1.2 p.2 v).apply p.1.1)
      (editInput q) (wordEncoding q) := by
  change ComputableInPolyTime (fun p : (QWord q × ℕ) × ℕ =>
    p.1.1.take p.1.2 ++ v ++ p.1.1.drop (p.1.2 + p.2))
    (encPair (encPair (wordEncoding q) encUnary) encUnary) (wordEncoding q)
  unfold wordEncoding
  fun_prop

private theorem replacements_polyTime {q : ℕ} (b : ℕ) :
    ComputableInPolyTime
      (fun p : (QWord q × ℕ) × ℕ => (List.range (b + 1)).flatMap fun vlen =>
          (wordsOfLength q vlen).map fun v => (Edit.mk p.1.2 p.2 v).apply p.1.1)
      (editInput q) (encList (wordEncoding q)) := by
  apply flatMapConst
  intro vlen _
  exact mapConst _ (fun v _ => apply_polyTime v)

private theorem removals_polyTime {q : ℕ} (b : ℕ) :
    ComputableInPolyTime (fun p : QWord q × ℕ =>
        (List.range (min b (p.1.length - p.2) + 1)).flatMap fun m =>
          (List.range (b + 1)).flatMap fun vlen =>
            (wordsOfLength q vlen).map fun v => (Edit.mk p.2 m v).apply p.1)
      (encPair (wordEncoding q) encUnary) (encList (wordEncoding q)) := by
  apply flatMapWithInput
  · unfold wordEncoding
    fun_prop
  · exact replacements_polyTime b

/-- Enumerate one-edit outputs in the original order and with the original multiplicities. -/
theorem oneEdit_polyTime {q : ℕ} (b : ℕ) :
    ComputableInPolyTime (oneEdit b (q := q)) (wordEncoding q) (encList (wordEncoding q)) := by
  unfold oneEdit
  apply flatMapWithInput
  · unfold wordEncoding
    fun_prop
  · exact removals_polyTime b

/-- The edit radius is fixed in the machine, as in the tag construction. -/
theorem editBall_polyTime {q : ℕ} (b s : ℕ) :
    ComputableInPolyTime (editBall b (q := q) s) (wordEncoding q) (encList (wordEncoding q)) := by
  induction s with
  | zero =>
    change ComputableInPolyTime (fun x : QWord q => [x]) (wordEncoding q) (encList (wordEncoding q))
    exact (cons _).comp (id'.prod (const []))
  | succ s ih =>
    change ComputableInPolyTime (fun x : QWord q => (editBall b s x).flatMap (oneEdit b))
      (wordEncoding q) (encList (wordEncoding q))
    apply flatMapWithInput ih
    exact (oneEdit_polyTime b).comp (snd _ _)

#print axioms editBall_polyTime

end DeletionCode.Explicit.Machine
