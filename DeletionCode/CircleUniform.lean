import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The concrete probability spaces for the manuscript's random hash weights.
Lebesgue measure restricted to [0,1) is a probability measure and reduces
modulo one to circle Haar measure; finite independent coordinate products
have the corresponding product Haar law. The actual strict circle-norm
test has measure 2/Q, including Q=2, where the omitted endpoint is null.
-/

namespace DeletionCode.CircleUniform

open MeasureTheory Set
open scoped ENNReal

/-- The exact strict test in the definition of surviving rules. -/
def smallArc (Q : ℕ) : Set UnitAddCircle := {z | ‖z‖ < 1 / (Q : ℝ)}

theorem smallArc_eq_ball (Q : ℕ) :
    smallArc Q = Metric.ball (0 : UnitAddCircle) (1 / (Q : ℝ)) := by
  ext z
  simp only [smallArc, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]

theorem measurableSet_smallArc (Q : ℕ) : MeasurableSet (smallArc Q) := by
  rw [smallArc_eq_ball]
  exact measurableSet_ball

/-- Open and closed circle balls have equal Haar measure, so the strict
inequality loses no mass even at radius one half. -/
theorem volume_smallArc (Q : ℕ) (hQ : 2 ≤ Q) :
    volume (smallArc Q) = ENNReal.ofReal (2 / (Q : ℝ)) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hQ)
  have htwo : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hsmall : 2 * (1 / (Q : ℝ)) ≤ 1 := by
    calc
      2 * (1 / (Q : ℝ)) = 2 / (Q : ℝ) := by ring
      _ ≤ 1 := (div_le_one hQr).mpr htwo
  have hae : Metric.closedBall (0 : UnitAddCircle) (1 / (Q : ℝ)) =ᵐ[volume]
      Metric.ball (0 : UnitAddCircle) (1 / (Q : ℝ)) :=
    AddCircle.closedBall_ae_eq_ball
  rw [smallArc_eq_ball, ← measure_congr hae, AddCircle.volume_closedBall, min_eq_right hsmall]
  congr 1
  ring

/-- For Q=2 the open test has full measure, although it excludes the
half-turn itself. No incorrect equality of the underlying sets is used. -/
theorem volume_smallArc_two : volume (smallArc 2) = 1 := by
  simpa using volume_smallArc 2 (by decide)

/-- Uniform real weights on the paper's actual half-open interval [0,1). -/
noncomputable def realUnit : Measure ℝ := volume.restrict (Set.Ico 0 1)

instance realUnit_probability : IsProbabilityMeasure realUnit where
  measure_univ := by simp [realUnit]

/-- The covering map has the correct law for [0,1), not only for the
(0,1] fundamental domain used by the standard library. -/
theorem measurePreserving_realUnit :
    MeasurePreserving (fun r : ℝ => (r : UnitAddCircle)) realUnit volume := by
  unfold realUnit
  rw [restrict_Ico_eq_restrict_Ioc]
  simpa only [zero_add] using UnitAddCircle.measurePreserving_mk 0

theorem map_realUnit :
    Measure.map (fun r : ℝ => (r : UnitAddCircle)) realUnit = volume :=
  measurePreserving_realUnit.map_eq

/-- The independent uniform real weights for any finite coordinate set. -/
noncomputable def realWeights (I : Type*) [Fintype I] : Measure (I → ℝ) :=
  Measure.pi (fun _ : I => realUnit)

instance realWeights_probability (I : Type*) [Fintype I] :
    IsProbabilityMeasure (realWeights I) := by
  unfold realWeights
  infer_instance

/-- Coordinatewise reduction modulo one. -/
def toCircle {I : Type*} (weights : I → ℝ) : I → UnitAddCircle :=
  fun i => (weights i : UnitAddCircle)

/-- Finite independent real weights reduce to product circle Haar measure.
The empty coordinate family is included. -/
theorem measurePreserving_toCircle (I : Type*) [Fintype I] :
    MeasurePreserving (@toCircle I) (realWeights I) volume := by
  exact measurePreserving_pi (fun _ : I => realUnit)
    (fun _ : I => (volume : Measure UnitAddCircle)) (fun _ => measurePreserving_realUnit)

theorem map_toCircle (I : Type*) [Fintype I] :
    Measure.map (@toCircle I) (realWeights I) = volume :=
  (measurePreserving_toCircle I).map_eq

#print axioms volume_smallArc
#print axioms volume_smallArc_two
#print axioms measurePreserving_realUnit
#print axioms measurePreserving_toCircle

end DeletionCode.CircleUniform
