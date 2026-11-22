import DeletionCode.Explicit.Machine.Repair
import DeletionCode.Explicit.Machine.WordRank
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-! The executable label budget and the joint public-data label evaluator. -/
namespace DeletionCode.Explicit.Machine

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

theorem publicLabelBound_polyTime (q b s C A l₀ : ℕ) :
    ComputableInPolyTime (publicLabelBound q b s C A l₀) encUnary encUnary := by
  unfold publicLabelBound gramLength
  fun_prop

theorem labelAt_polyTime {q : ℕ} (hq : 2 ≤ q) (F : SourceCallbacks q) (H : F.Certified) (l₀ : ℕ) :
    ComputableInPolyTime (fun p : SourceInput q => labelAt l₀ (fun x => F.label (p.1, x)) p.2)
      (inputEncoding q) encNat := by
  have hw := snd encBits (wordEncoding q)
  have hshort := unary_lt' ((wordLength_polyTime q).comp hw) (const l₀)
  exact ite_decide hshort ((wordRank_polyTime hq).comp hw) H.label

#print axioms publicLabelBound_polyTime
#print axioms labelAt_polyTime

end DeletionCode.Explicit.Machine
