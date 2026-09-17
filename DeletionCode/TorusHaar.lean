import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Probability.Independence.Basic

/-!
The normalized Haar law on a finite product of unit circles. A continuous
surjective additive homomorphism preserves this law, so its output coordinates
are independent and uniform. Surjectivity remains an explicit hypothesis here;
the integer-matrix argument establishes it for the actual joint hash.
-/

namespace DeletionCode.TorusHaar

open MeasureTheory ProbabilityTheory
open scoped BigOperators

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

variable {I J : Type*} [Fintype I] [Fintype J]

/-- A continuous surjection of finite tori preserves their probability Haar laws. -/
theorem measurePreserving
    (f : (I → UnitAddCircle) →+ (J → UnitAddCircle))
    (hcont : Continuous f) (hsurj : Function.Surjective f) :
    MeasurePreserving f volume volume :=
  AddMonoidHom.measurePreserving hcont hsurj (by simp)

/-- Any random vector with the product Haar law has a uniform law in each coordinate. -/
theorem coordinate_measurePreserving_of_measurePreserving
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → (J → UnitAddCircle)} (hf : MeasurePreserving f μ volume) (j : J) :
    MeasurePreserving (fun x => f x j) μ volume :=
  (measurePreserving_eval (fun _ : J => (volume : Measure UnitAddCircle)) j).comp hf

/-- A product Haar joint law implies joint independence, for any source measure. -/
theorem coordinates_independent_of_measurePreserving
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → (J → UnitAddCircle)} (hf : MeasurePreserving f μ volume) :
    iIndepFun (fun j x => f x j) μ := by
  have : IsProbabilityMeasure (μ.map f) := by
    rw [hf.map_eq]
    infer_instance
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_of_map hf.aemeasurable
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun j => (coordinate_measurePreserving_of_measurePreserving hf j).aemeasurable)).2
  have hcoords (j : J) : μ.map (fun x => f x j) = volume :=
    (coordinate_measurePreserving_of_measurePreserving hf j).map_eq
  simp_rw [hcoords]
  exact hf.map_eq

/-- Every output coordinate has the uniform unit-circle law. -/
theorem coordinate_measurePreserving
    (f : (I → UnitAddCircle) →+ (J → UnitAddCircle))
    (hcont : Continuous f) (hsurj : Function.Surjective f) (j : J) :
    MeasurePreserving (fun x => f x j) volume volume :=
  coordinate_measurePreserving_of_measurePreserving (measurePreserving f hcont hsurj) j

/-- The output coordinates are jointly independent, including an empty output family. -/
theorem coordinates_independent
    (f : (I → UnitAddCircle) →+ (J → UnitAddCircle))
    (hcont : Continuous f) (hsurj : Function.Surjective f) :
    iIndepFun (fun j x => f x j) volume :=
  coordinates_independent_of_measurePreserving (measurePreserving f hcont hsurj)

/-- The original product-coordinate variables are themselves independent. -/
theorem evaluations_independent :
    iIndepFun (fun i (x : I → UnitAddCircle) => x i) volume := by
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

/-- Measurable coordinate tests have exactly the product of their uniform probabilities. -/
theorem preimage_rectangle
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → (J → UnitAddCircle)} (hf : MeasurePreserving f μ volume)
    (A : J → Set UnitAddCircle) (hA : ∀ j, MeasurableSet (A j)) :
    μ (f ⁻¹' Set.univ.pi A) = ∏ j, volume (A j) := by
  calc
    μ (f ⁻¹' Set.univ.pi A) = volume (Set.univ.pi A) := by
      have h := congrArg (fun ν : Measure (J → UnitAddCircle) => ν (Set.univ.pi A)) hf.map_eq
      rw [Measure.map_apply hf.measurable (MeasurableSet.univ_pi hA)] at h
      exact h
    _ = ∏ j, volume (A j) := volume_pi_pi A

/-- A pointwise form of `preimage_rectangle` convenient for simultaneous survival events. -/
theorem forall_mem_measure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → (J → UnitAddCircle)} (hf : MeasurePreserving f μ volume)
    (A : J → Set UnitAddCircle) (hA : ∀ j, MeasurableSet (A j)) :
    μ {x | ∀ j, f x j ∈ A j} = ∏ j, volume (A j) := by
  have hset : {x | ∀ j, f x j ∈ A j} = f ⁻¹' Set.univ.pi A := by
    ext x
    simp
  rw [hset]
  exact preimage_rectangle hf A hA

end DeletionCode.TorusHaar

#print axioms DeletionCode.TorusHaar.measurePreserving
#print axioms DeletionCode.TorusHaar.coordinate_measurePreserving_of_measurePreserving
#print axioms DeletionCode.TorusHaar.coordinates_independent_of_measurePreserving
#print axioms DeletionCode.TorusHaar.coordinate_measurePreserving
#print axioms DeletionCode.TorusHaar.coordinates_independent
#print axioms DeletionCode.TorusHaar.evaluations_independent
#print axioms DeletionCode.TorusHaar.preimage_rectangle
#print axioms DeletionCode.TorusHaar.forall_mem_measure
