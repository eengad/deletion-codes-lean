import DeletionCode.CircleHash
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Group.ZPow

/-!
The simultaneous integer-weighted hash is a continuous surjective homomorphism
when its integer rows are linearly independent over the rationals. Surjectivity
is obtained by finding a rational right inverse, casting its identity to the
reals, and lifting the prescribed circle coordinates to real representatives.
-/
namespace DeletionCode.IntegerTorusMap

open scoped BigOperators Matrix
open CircleHash

variable {I J : Type*} [Fintype I]

/-- Evaluate all the integer-coordinate hashes at the same circle weights. -/
noncomputable def jointHash (w : J → I → ℤ) :
    (I → UnitAddCircle) →+ (J → UnitAddCircle) where
  toFun weights j := weightedHash weights (w j)
  map_zero' := by
    funext j
    simp [weightedHash]
  map_add' weights weights' := by
    funext j
    change (∑ i, w j i • (weights i + weights' i)) =
      (∑ i, w j i • weights i) + (∑ i, w j i • weights' i)
    simp only [smul_add, Finset.sum_add_distrib]

@[simp] theorem jointHash_apply (w : J → I → ℤ)
    (weights : I → UnitAddCircle) (j : J) :
    jointHash w weights j = weightedHash weights (w j) := rfl

theorem continuous_jointHash (w : J → I → ℤ) : Continuous (jointHash w) := by
  apply continuous_pi
  intro j
  change Continuous (fun weights : I → UnitAddCircle => ∑ i, w j i • weights i)
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).zsmul (w j i))

variable [Fintype J]

/-- Full rational row rank gives a rational right inverse. -/
theorem rational_right_inverse [DecidableEq J] (A : Matrix J I ℚ)
    (h : LinearIndependent ℚ A.row) :
    ∃ B : Matrix I J ℚ, A * B = 1 := by
  classical
  have hrank : A.rank = Fintype.card J := h.rank_matrix
  have hrange : LinearMap.range A.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change A.rank = Module.finrank ℚ (J → ℚ)
    simpa only [Module.finrank_fintype_fun_eq_card] using hrank
  have hsurj : Function.Surjective A.mulVec :=
    LinearMap.range_eq_top.mp hrange
  exact Matrix.mulVec_surjective_iff_exists_right_inverse.mp hsurj

/-- Cast an actual rational right-inverse identity to the reals. This avoids
assuming that arbitrary rationally independent real vectors are real-independent. -/
theorem real_right_inverse [DecidableEq J] (A : Matrix J I ℚ)
    (h : LinearIndependent ℚ A.row) :
    ∃ B : Matrix I J ℝ, A.map (Rat.castHom ℝ) * B = 1 := by
  classical
  obtain ⟨B, hB⟩ := rational_right_inverse A h
  refine ⟨B.map (Rat.castHom ℝ), ?_⟩
  have hmap := congrArg (fun M : Matrix J J ℚ => M.map (Rat.castHom ℝ)) hB
  rw [Matrix.map_mul] at hmap
  have hone : (1 : Matrix J J ℚ).map (Rat.castHom ℝ) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  exact hmap.trans hone

/-- Simultaneous real weighted sums attain every real vector. -/
theorem realWeightedSums_surjective (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j => fun i => (w j i : ℚ))) :
    Function.Surjective (fun weights : I → ℝ =>
      fun j => ∑ i, weights i * (w j i : ℝ)) := by
  classical
  let A : Matrix J I ℚ := fun j i => (w j i : ℚ)
  have hA : LinearIndependent ℚ A.row := h
  obtain ⟨B, hB⟩ := real_right_inverse A hA
  have hsurj : Function.Surjective (A.map (Rat.castHom ℝ)).mulVec :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨B, hB⟩
  intro target
  obtain ⟨weights, hweights⟩ := hsurj target
  refine ⟨weights, ?_⟩
  funext j
  have hj := congrFun hweights j
  change (∑ i, ((w j i : ℚ) : ℝ) * weights i) = target j at hj
  simpa only [Rat.cast_intCast, mul_comm] using hj

/-- Rationally independent integer rule vectors give a surjective joint torus
hash, with no additional rank or torus-surjectivity premise. -/
theorem jointHash_surjective (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j => fun i => (w j i : ℚ))) :
    Function.Surjective (jointHash w) := by
  intro target
  obtain ⟨weights, hweights⟩ :=
    realWeightedSums_surjective w h (fun j => representative (target j))
  refine ⟨fun i => (weights i : UnitAddCircle), ?_⟩
  funext j
  have hj : (∑ i, weights i * (w j i : ℝ)) = representative (target j) :=
    congrFun hweights j
  change realWeightedHash weights (w j) = target j
  rw [realWeightedHash_apply, hj, coe_representative]

#print axioms rational_right_inverse
#print axioms real_right_inverse
#print axioms continuous_jointHash
#print axioms jointHash_surjective

end DeletionCode.IntegerTorusMap
