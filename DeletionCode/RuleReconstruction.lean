import DeletionCode.SignedSupport
import DeletionCode.RecordSerialization

/-!
Finite recovered words determine the signed rule set. Bubble-to-rule grouping
is fixed by the index scheme, so it is not an extra field in the description.
-/
namespace DeletionCode.RuleReconstruction

open Windows HeaderRecovery RootSelection SignedSupport RecordSerialization GeneratingModel
open scoped BigOperators

def negativeLetters {ν : ℕ} (data : RecoveredData ν) (b : Fin ν) : Letters :=
  fun i => (data.words b).getD i false

def recoveredFamily {ν : ℕ} (k : ℕ) (rank : Fin ν → ℕ)
    (data : RecoveredData ν) : Family (Fin ν) where
  rank := rank
  path b side := if side then rebuildPositive k (data.header b) (negativeLetters data b)
    else negativeLetters data b
  extra b side := PathMemory.pathLength k (data.header b) side - windowLength k

theorem negativeLetters_agree {ν k : ℕ} (E : EditedFamily (Fin ν) k) (b : Fin ν) :
    Agree (negativeLetters (dataOfFamily E) b) 0
      (negativePath k (E.header b) (E.long b)) 0 (negativeLength k (E.header b)) := by
  intro i hi
  simp [negativeLetters, dataOfFamily, dataOfOutput, List.getD, hi]

theorem recoveredFamily_agree {ν k : ℕ} (E : EditedFamily (Fin ν) k)
    (rank : Fin ν → ℕ) (b : Fin ν) (side : Bool) :
    Agree ((recoveredFamily k rank (dataOfFamily E)).path b side) 0
      (E.family.path b side) 0 (windowLength k + E.family.extra b side) := by
  rw [← E.path_length_eq b side]
  cases side with
  | false => exact negativeLetters_agree E b
  | true =>
    exact rebuild_positive_from_known_negative k (E.header b) (E.long b)
      (negativeLetters (dataOfFamily E) b) (E.rho_lower b) (E.rho_upper b)
      (E.header_bit b) (negativeLetters_agree E b)

theorem pathSpectrum_congr (p q : Letters) (L D : ℕ)
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

theorem recovered_bubble_spectrum {ν k : ℕ} (E : EditedFamily (Fin ν) k)
    (rank : Fin ν → ℕ) (b : Fin ν) :
    bubbleSpectrum (recoveredFamily k rank (dataOfFamily E)) (windowLength k) b =
      bubbleSpectrum E.family (windowLength k) b := by
  funext g
  unfold bubbleSpectrum
  have hn := congrFun (pathSpectrum_congr _ _ (windowLength k) (E.family.extra b false)
    (recoveredFamily_agree E rank b false)) g
  have hp := congrFun (pathSpectrum_congr _ _ (windowLength k) (E.family.extra b true)
    (recoveredFamily_agree E rank b true)) g
  exact congrArg₂ (fun a b : ℤ => a - b) hp hn

theorem recovered_rule_spectrum {ν k : ℕ} (E : EditedFamily (Fin ν) k)
    (rank : Fin ν → ℕ) (bubbles : Finset (Fin ν)) :
    ruleSpectrum (recoveredFamily k rank (dataOfFamily E)) (windowLength k) bubbles =
      ruleSpectrum E.family (windowLength k) bubbles := by
  funext g
  unfold ruleSpectrum
  apply Finset.sum_congr rfl
  intro b hb
  exact congrFun (recovered_bubble_spectrum E rank b) g

/-- Fixed labels identify the rule containing each bubble. -/
def groupBubbles {ν R : ℕ} (group : Fin ν → Fin R) (r : Fin R) : Finset (Fin ν) :=
  Finset.univ.filter (fun b => group b = r)

noncomputable def rulesOfFamily {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) : Finset (Gram (windowLength k) → ℤ) := by
  classical
  exact Finset.univ.image (fun r => ruleSpectrum E.family (windowLength k) (groupBubbles group r))

noncomputable def rulesOfData {ν R : ℕ} (k : ℕ) (group : Fin ν → Fin R)
    (data : RecoveredData ν) : Finset (Gram (windowLength k) → ℤ) := by
  classical
  exact Finset.univ.image (fun r => ruleSpectrum
    (recoveredFamily k (fun b => (group b).val) data) (windowLength k) (groupBubbles group r))

/-- Recovering finite word data suffices to determine the entire signed rule set. -/
theorem rules_roundtrip {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) : rulesOfData k group (dataOfFamily E) = rulesOfFamily E group := by
  classical
  unfold rulesOfData rulesOfFamily
  apply Finset.image_congr
  intro r hr
  exact recovered_rule_spectrum E (fun b => (group b).val) (groupBubbles group r)

#print axioms recoveredFamily_agree
#print axioms recovered_bubble_spectrum
#print axioms recovered_rule_spectrum
#print axioms rules_roundtrip

end DeletionCode.RuleReconstruction
