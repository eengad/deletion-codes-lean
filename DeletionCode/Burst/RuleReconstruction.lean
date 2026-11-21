import DeletionCode.Qary.SignedSupport
import DeletionCode.Burst.RecordSerialization
import DeletionCode.Qary.RuleReconstruction

/-!
Finite recovered words determine the signed rule set. Bubble-to-rule grouping
is fixed by the index scheme, so it is not an extra field in the description.
-/
namespace DeletionCode.Burst.RuleReconstruction

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

open DeletionCode.Qary.Windows DeletionCode.Burst.HeaderRecovery DeletionCode.Qary.RootSelection DeletionCode.Qary.SignedSupport DeletionCode.Burst.RecordSerialization DeletionCode.Burst.GeneratingModel
open scoped BigOperators

def negativeLetters {ν : ℕ} (data : RecoveredData α ν) (b : Fin ν) : Letters α :=
  fun i => (data.words b).getD i default

def recoveredFamily {ν : ℕ} (k d : ℕ) (rank : Fin ν → ℕ)
    (data : RecoveredData α ν) : Family α (Fin ν) where
  rank := rank
  path b side := if side then rebuildPositive (data.header b) (negativeLetters data b)
    else negativeLetters data b
  extra b side := PathMemory.pathLength k d (data.header b) side - windowLength k d

theorem negativeLetters_agree {ν k d : ℕ} (E : EditedFamily α (Fin ν) k d) (b : Fin ν) :
    Agree (negativeLetters (dataOfFamily E) b) 0
      (negativePath (E.header b) (E.long b)) 0 (negativeLength (E.header b)) := by
  intro i hi
  simp [negativeLetters, dataOfFamily, dataOfOutput, List.getD, hi]

theorem recoveredFamily_agree {ν k d : ℕ} (E : EditedFamily α (Fin ν) k d)
    (rank : Fin ν → ℕ) (b : Fin ν) (side : Bool) :
    Agree ((recoveredFamily k d rank (dataOfFamily E)).path b side) 0
      (E.family.path b side) 0 (windowLength k d + E.family.extra b side) := by
  rw [← E.path_length_eq b side]
  cases side with
  | false => exact negativeLetters_agree E b
  | true =>
    exact rebuild_positive_preserves_agreement (E.header b)
      (negativeLetters (dataOfFamily E) b) (E.long b) (negativeLetters_agree E b)

theorem pathSpectrum_congr (p q : Letters α) (L D : ℕ)
    (h : Agree p 0 q 0 (L + D)) : pathSpectrum p L D = pathSpectrum q L D := by
  classical
  funext g
  unfold pathSpectrum
  apply Finset.sum_congr rfl
  intro i hi
  have hgram : gram p L i.val = gram q L i.val := by
    funext j
    have hbound : i.val + j.val < L + D := by have := i.isLt; have := j.isLt; omega
    simpa only [gram, Nat.zero_add] using h (i.val + j.val) hbound
  rw [hgram]

theorem recovered_bubble_spectrum {ν k d : ℕ} (E : EditedFamily α (Fin ν) k d)
    (rank : Fin ν → ℕ) (b : Fin ν) :
    bubbleSpectrum (recoveredFamily k d rank (dataOfFamily E)) (windowLength k d) b =
      bubbleSpectrum E.family (windowLength k d) b := by
  funext g
  unfold bubbleSpectrum
  have hn := congrFun (pathSpectrum_congr _ _ (windowLength k d) (E.family.extra b false)
    (recoveredFamily_agree E rank b false)) g
  have hp := congrFun (pathSpectrum_congr _ _ (windowLength k d) (E.family.extra b true)
    (recoveredFamily_agree E rank b true)) g
  exact congrArg₂ (fun a b : ℤ => a - b) hp hn

theorem recovered_rule_spectrum {ν k d : ℕ} (E : EditedFamily α (Fin ν) k d)
    (rank : Fin ν → ℕ) (bubbles : Finset (Fin ν)) :
    ruleSpectrum (recoveredFamily k d rank (dataOfFamily E)) (windowLength k d) bubbles =
      ruleSpectrum E.family (windowLength k d) bubbles := by
  funext g
  unfold ruleSpectrum
  apply Finset.sum_congr rfl
  intro b hb
  exact congrFun (recovered_bubble_spectrum E rank b) g

abbrev groupBubbles := @Qary.RuleReconstruction.groupBubbles

noncomputable def rulesOfFamily {ν R k d : ℕ} (E : EditedFamily α (Fin ν) k d)
    (group : Fin ν → Fin R) : Finset (Gram α (windowLength k d) → ℤ) := by
  classical
  exact Finset.univ.image (fun r => ruleSpectrum E.family (windowLength k d) (groupBubbles group r))

noncomputable def rulesOfData {ν R : ℕ} (k d : ℕ) (group : Fin ν → Fin R)
    (data : RecoveredData α ν) : Finset (Gram α (windowLength k d) → ℤ) := by
  classical
  exact Finset.univ.image (fun r => ruleSpectrum
    (recoveredFamily k d (fun b => (group b).val) data) (windowLength k d) (groupBubbles group r))

/-- Recovering finite word data suffices to determine the entire signed rule set. -/
theorem rules_roundtrip {ν R k d : ℕ} (E : EditedFamily α (Fin ν) k d)
    (group : Fin ν → Fin R) : rulesOfData k d group (dataOfFamily E) = rulesOfFamily E group := by
  classical
  unfold rulesOfData rulesOfFamily
  apply Finset.image_congr
  intro r hr
  exact recovered_rule_spectrum E (fun b => (group b).val) (groupBubbles group r)

#print axioms recoveredFamily_agree
#print axioms recovered_bubble_spectrum
#print axioms recovered_rule_spectrum
#print axioms rules_roundtrip

end DeletionCode.Burst.RuleReconstruction
