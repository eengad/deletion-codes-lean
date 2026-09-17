import DeletionCode.IntegerTorusMap
import DeletionCode.TorusHaar
import DeletionCode.CircleUniform

/-!
The manuscript's independent-differences lemma for the actual finite weighted
integer-coordinate hash. Rational independence supplies torus surjectivity;
Haar measure preservation supplies joint uniformity and independence. The
strict norm test then has exactly the stated simultaneous survival probability.
-/
namespace DeletionCode.RandomHash

open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Rational independence of the actual integer rows gives a joint uniform
circle law, with no rank or measure-preservation premise supplied by callers. -/
theorem joint_uniform (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) :
    MeasurePreserving (jointHash w) volume volume :=
  TorusHaar.measurePreserving (jointHash w) (continuous_jointHash w) (jointHash_surjective w h)

theorem coordinate_uniform (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) (j : J) :
    MeasurePreserving (fun weights => weightedHash weights (w j)) volume volume :=
  TorusHaar.coordinate_measurePreserving (jointHash w)
    (continuous_jointHash w) (jointHash_surjective w h) j

theorem independent (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) :
    iIndepFun (fun j weights => weightedHash weights (w j)) volume :=
  TorusHaar.coordinates_independent (jointHash w)
    (continuous_jointHash w) (jointHash_surjective w h)

/-- Exact simultaneous survival probability, including Q = 2 and an empty
independent family. The test is strict, as in the manuscript. -/
theorem simultaneous_test_probability (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) (Q : ℕ) (hQ : 2 ≤ Q) :
    volume {weights : I → UnitAddCircle | ∀ j, ‖weightedHash weights (w j)‖ < 1 / (Q : ℝ)} =
      ENNReal.ofReal (2 / (Q : ℝ)) ^ Fintype.card J := by
  classical
  calc
    _ = ∏ j : J, volume (smallArc Q) := by
      simpa only [jointHash_apply, smallArc, Set.mem_ofPred_eq] using
        TorusHaar.forall_mem_measure (joint_uniform w h)
          (fun _ => smallArc Q) (fun _ => measurableSet_smallArc Q)
    _ = _ := by simp only [volume_smallArc Q hQ, Finset.prod_const, Finset.card_univ]

/-- For fixed catalogue members, the norm tests are exactly membership in
the actual surviving set. No catalogue premise is needed for the norm-only result. -/
theorem rules_survival_probability (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ)))
    (K₀ : Set (I → ℤ)) (hw : ∀ j, w j ∈ K₀) (Q : ℕ) (hQ : 2 ≤ Q) :
    volume {weights : I → UnitAddCircle | ∀ j, w j ∈ surviving (weightedHash weights) Q K₀} =
      ENNReal.ofReal (2 / (Q : ℝ)) ^ Fintype.card J := by
  simpa only [surviving, Set.mem_ofPred_eq, hw, true_and] using
    simultaneous_test_probability w h Q hQ

omit [Fintype I] in
theorem rational_ne_zero (w : I → ℤ) (hw : w ≠ 0) : (fun i => (w i : ℚ)) ≠ 0 := by
  intro h
  apply hw
  funext i
  have hi := congrFun h i
  change (w i : ℚ) = 0 at hi
  change w i = 0
  exact_mod_cast hi

/-- The manuscript's nonzero-vector assertion is the one-row case. -/
theorem nonzero_test_probability (w : I → ℤ) (hw : w ≠ 0) (Q : ℕ) (hQ : 2 ≤ Q) :
    volume {weights : I → UnitAddCircle | ‖weightedHash weights w‖ < 1 / (Q : ℝ)} =
      ENNReal.ofReal (2 / (Q : ℝ)) := by
  have hi : LinearIndependent ℚ (fun _ : Fin 1 => fun i => (w i : ℚ)) :=
    LinearIndependent.of_subsingleton 0 (rational_ne_zero w hw)
  simpa only [Fin.forall_fin_one, Fintype.card_fin, pow_one] using
    simultaneous_test_probability (fun _ : Fin 1 => w) hi Q hQ

/-- The manuscript uses independent real weights on [0,1). Their coordinate
reduction gives precisely the joint circle law established above. -/
theorem real_joint_uniform (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) :
    MeasurePreserving (fun weights j => realWeightedHash weights (w j)) (realWeights I) volume :=
  (joint_uniform w h).comp (measurePreserving_toCircle I)

theorem real_coordinate_uniform (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) (j : J) :
    MeasurePreserving (fun weights => realWeightedHash weights (w j)) (realWeights I) volume :=
  TorusHaar.coordinate_measurePreserving_of_measurePreserving (real_joint_uniform w h) j

theorem real_independent (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) :
    iIndepFun (fun j weights => realWeightedHash weights (w j)) (realWeights I) :=
  TorusHaar.coordinates_independent_of_measurePreserving (real_joint_uniform w h)

/-- The full joint-law assertion of `lem:hash-independent`, for the actual
real-weight probability space specified by the manuscript. -/
theorem independent_differences (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) :
    iIndepFun (fun j weights => realWeightedHash weights (w j)) (realWeights I) ∧
    (∀ j, MeasurePreserving (fun weights => realWeightedHash weights (w j)) (realWeights I) volume) ∧
    MeasurePreserving (fun weights j => realWeightedHash weights (w j)) (realWeights I) volume :=
  ⟨real_independent w h, real_coordinate_uniform w h, real_joint_uniform w h⟩

theorem real_simultaneous_test_probability (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) (Q : ℕ) (hQ : 2 ≤ Q) :
    realWeights I {weights | ∀ j, ‖realWeightedHash weights (w j)‖ < 1 / (Q : ℝ)} =
      ENNReal.ofReal (2 / (Q : ℝ)) ^ Fintype.card J := by
  classical
  calc
    _ = ∏ j : J, volume (smallArc Q) := by
      simpa only [smallArc, Set.mem_ofPred_eq] using
        TorusHaar.forall_mem_measure (real_joint_uniform w h)
          (fun _ => smallArc Q) (fun _ => measurableSet_smallArc Q)
    _ = _ := by simp only [volume_smallArc Q hQ, Finset.prod_const, Finset.card_univ]

/-- Exact probability that all fixed independent catalogue rules survive. -/
theorem real_rules_survival_probability (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ)))
    (K₀ : Set (I → ℤ)) (hw : ∀ j, w j ∈ K₀) (Q : ℕ) (hQ : 2 ≤ Q) :
    realWeights I {weights | ∀ j, w j ∈ surviving (realWeightedHash weights) Q K₀} =
      ENNReal.ofReal (2 / (Q : ℝ)) ^ Fintype.card J := by
  simpa only [surviving, Set.mem_ofPred_eq, hw, true_and] using
    real_simultaneous_test_probability w h Q hQ

theorem real_nonzero_test_probability (w : I → ℤ) (hw : w ≠ 0) (Q : ℕ) (hQ : 2 ≤ Q) :
    realWeights I {weights | ‖realWeightedHash weights w‖ < 1 / (Q : ℝ)} =
      ENNReal.ofReal (2 / (Q : ℝ)) := by
  have hi : LinearIndependent ℚ (fun _ : Fin 1 => fun i => (w i : ℚ)) :=
    LinearIndependent.of_subsingleton 0 (rational_ne_zero w hw)
  simpa only [Fin.forall_fin_one, Fintype.card_fin, pow_one] using
    real_simultaneous_test_probability (fun _ : Fin 1 => w) hi Q hQ

/-- The same simultaneous probability as an ordinary real number. -/
theorem real_rules_survival_probability_toReal (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ)))
    (K₀ : Set (I → ℤ)) (hw : ∀ j, w j ∈ K₀) (Q : ℕ) (hQ : 2 ≤ Q) :
    (realWeights I {weights | ∀ j, w j ∈ surviving (realWeightedHash weights) Q K₀}).toReal =
      (2 / (Q : ℝ)) ^ Fintype.card J := by
  rw [real_rules_survival_probability w h K₀ hw Q hQ, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (div_nonneg (by norm_num) (Nat.cast_nonneg Q))]

theorem real_nonzero_test_probability_toReal (w : I → ℤ) (hw : w ≠ 0) (Q : ℕ) (hQ : 2 ≤ Q) :
    (realWeights I {weights | ‖realWeightedHash weights w‖ < 1 / (Q : ℝ)}).toReal =
      2 / (Q : ℝ) := by
  rw [real_nonzero_test_probability w hw Q hQ,
    ENNReal.toReal_ofReal (div_nonneg (by norm_num) (Nat.cast_nonneg Q))]

/-- Finite rule sets are counted without adding an ordering or occurrence multiplicity. -/
theorem real_finset_survival_probability (S : Finset (I → ℤ))
    (h : LinearIndependent ℚ (fun w : S => fun i => (w.val i : ℚ)))
    (K₀ : Set (I → ℤ)) (hS : ∀ w ∈ S, w ∈ K₀) (Q : ℕ) (hQ : 2 ≤ Q) :
    realWeights I {weights | ∀ w ∈ S, w ∈ surviving (realWeightedHash weights) Q K₀} =
      ENNReal.ofReal (2 / (Q : ℝ)) ^ S.card := by
  have ht := real_rules_survival_probability (fun w : S => w.val) h K₀
    (fun w => hS w.val w.property) Q hQ
  simpa only [Subtype.forall, Fintype.card_coe] using ht

#print axioms joint_uniform
#print axioms independent
#print axioms simultaneous_test_probability
#print axioms rules_survival_probability
#print axioms nonzero_test_probability
#print axioms real_joint_uniform
#print axioms independent_differences
#print axioms real_simultaneous_test_probability
#print axioms real_rules_survival_probability
#print axioms real_nonzero_test_probability
#print axioms real_rules_survival_probability_toReal
#print axioms real_finset_survival_probability

end DeletionCode.RandomHash
