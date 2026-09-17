import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring

/-!
The deterministic circle-hash collision test. Labels use the canonical
representative in [0,1) and integer floor. Equal labels give a strict distance
less than 1/Q, and hence survival of a catalogue difference under any additive
hash. The finite weighted integer-coordinate hash is constructed explicitly.
-/

namespace DeletionCode.CircleHash

open scoped BigOperators

/-- The paper's canonical circle representative in [0,1). -/
noncomputable def representative (z : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 z).val

theorem representative_mem (z : UnitAddCircle) :
    representative z ∈ Set.Ico (0 : ℝ) 1 := by
  simpa only [representative, zero_add] using
    (AddCircle.equivIco (1 : ℝ) 0 z).property

@[simp] theorem coe_representative (z : UnitAddCircle) :
    (representative z : UnitAddCircle) = z :=
  AddCircle.coe_equivIco

/-- The label is an integer, with its precise finite range proved below. -/
noncomputable def label (Q : ℕ) (z : UnitAddCircle) : ℤ :=
  ⌊(Q : ℝ) * representative z⌋

theorem label_nonneg (Q : ℕ) (z : UnitAddCircle) : 0 ≤ label Q z := by
  apply Int.floor_nonneg.mpr
  exact mul_nonneg (Nat.cast_nonneg Q) (representative_mem z).1

theorem label_lt (Q : ℕ) (hQ : 0 < Q) (z : UnitAddCircle) : label Q z < (Q : ℤ) := by
  apply Int.floor_lt.mpr
  have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have h := mul_lt_mul_of_pos_left (representative_mem z).2 hQr
  simpa only [mul_one, Int.cast_natCast] using h

/-- Thus the labels are exactly of the paper's type: integers from 0 through Q-1. -/
theorem label_range (Q : ℕ) (hQ : 2 ≤ Q) (z : UnitAddCircle) :
    0 ≤ label Q z ∧ label Q z < (Q : ℤ) :=
  ⟨label_nonneg Q z, label_lt Q (lt_of_lt_of_le (by decide : 0 < 2) hQ) z⟩

/-- The strict upper endpoint of each half-open bin gives a strict difference bound. -/
theorem equal_scaled_floors_close (Q : ℕ) (hQ : 0 < Q) (a b : ℝ)
    (hlabel : ⌊(Q : ℝ) * a⌋ = ⌊(Q : ℝ) * b⌋) :
    |b - a| < 1 / (Q : ℝ) := by
  have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have h := Int.abs_sub_lt_one_of_floor_eq_floor hlabel.symm
  rw [← mul_sub, abs_mul, abs_of_pos hQr] at h
  apply (lt_div_iff₀ hQr).mpr
  simpa only [mul_comm] using h

theorem equal_labels_representatives_close (Q : ℕ) (hQ : 0 < Q)
    (a b : UnitAddCircle) (hlabel : label Q a = label Q b) :
    |representative b - representative a| < 1 / (Q : ℝ) :=
  equal_scaled_floors_close Q hQ (representative a) (representative b) hlabel

/-- The circle difference has a real representative in the required open interval.
This does not incorrectly require its [0,1) representative to be near zero. -/
theorem equal_labels_small_representative (Q : ℕ) (hQ : 0 < Q)
    (a b : UnitAddCircle) (hlabel : label Q a = label Q b) :
    ∃ r : ℝ, (r : UnitAddCircle) = b - a ∧
      -(1 / (Q : ℝ)) < r ∧ r < 1 / (Q : ℝ) := by
  refine ⟨representative b - representative a, ?_, ?_⟩
  · simp only [AddCircle.coe_sub, coe_representative]
  · exact abs_lt.mp (equal_labels_representatives_close Q hQ a b hlabel)

/-- The actual quotient norm is no larger than the short representative difference. -/
theorem equal_labels_close (Q : ℕ) (hQ : 0 < Q)
    (a b : UnitAddCircle) (hlabel : label Q a = label Q b) :
    ‖b - a‖ < 1 / (Q : ℝ) := by
  have hrep := equal_labels_representatives_close Q hQ a b hlabel
  have hquot : ‖((representative b - representative a : ℝ) : UnitAddCircle)‖ ≤
      |representative b - representative a| := by
    simpa only [Real.norm_eq_abs] using
      (QuotientAddGroup.norm_mk_le_norm
        (S := AddSubgroup.zmultiples (1 : ℝ)) (m := representative b - representative a))
  have hnorm := hquot.trans_lt hrep
  simpa only [AddCircle.coe_sub, coe_representative] using hnorm

/-- This is the paper's distance to the nearest integer, attained at round r. -/
theorem norm_coe_eq_nearest_integer (r : ℝ) :
    ‖(r : UnitAddCircle)‖ = |r - (round r : ℝ)| :=
  UnitAddCircle.norm_eq

theorem norm_coe_le_integer_distance (r : ℝ) (z : ℤ) :
    ‖(r : UnitAddCircle)‖ ≤ |r - (z : ℝ)| := by
  rw [norm_coe_eq_nearest_integer]
  exact round_le r z

/-- The finite weighted sum is an additive hash on actual integer-coordinate vectors. -/
noncomputable def weightedHash {I : Type*} [Fintype I]
    (weights : I → UnitAddCircle) : (I → ℤ) →+ UnitAddCircle where
  toFun p := ∑ g, p g • weights g
  map_zero' := by simp
  map_add' p q := by simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib]

/-- The real-weight formulation in the manuscript, with each weight reduced modulo one. -/
noncomputable def realWeightedHash {I : Type*} [Fintype I]
    (weights : I → ℝ) : (I → ℤ) →+ UnitAddCircle :=
  weightedHash (fun g => (weights g : UnitAddCircle))

theorem realWeightedHash_apply {I : Type*} [Fintype I]
    (weights : I → ℝ) (p : I → ℤ) :
    realWeightedHash weights p = ((∑ g, weights g * (p g : ℝ) : ℝ) : UnitAddCircle) := by
  change (∑ g, p g • (weights g : UnitAddCircle)) =
    ((∑ g, weights g * (p g : ℝ) : ℝ) : UnitAddCircle)
  calc
    (∑ g, p g • (weights g : UnitAddCircle)) =
        ∑ g, ((weights g * (p g : ℝ) : ℝ) : UnitAddCircle) := by
      apply Finset.sum_congr rfl
      intro g hg
      simpa only [zsmul_eq_mul, mul_comm] using
        (AddCircle.coe_zsmul (p := (1 : ℝ)) (n := p g) (x := weights g)).symm
    _ = ((∑ g, weights g * (p g : ℝ) : ℝ) : UnitAddCircle) :=
      (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
        (fun g => weights g * (p g : ℝ)) Finset.univ).symm

/-- Surviving rules are catalogue members passing the strict circle-norm test. -/
def surviving {V : Type*} [AddCommGroup V] (H : V →+ UnitAddCircle)
    (Q : ℕ) (K₀ : Set V) : Set V :=
  {w | w ∈ K₀ ∧ ‖H w‖ < 1 / (Q : ℝ)}

/-- Equal hash labels force the actual spectrum difference to pass the test. -/
theorem equal_hash_labels_norm_lt {V : Type*} [AddCommGroup V]
    (H : V →+ UnitAddCircle) (Q : ℕ) (hQ : 2 ≤ Q) (p p' : V)
    (hlabel : label Q (H p) = label Q (H p')) :
    ‖H (p' - p)‖ < 1 / (Q : ℝ) := by
  rw [map_sub]
  exact equal_labels_close Q (lt_of_lt_of_le (by decide : 0 < 2) hQ) (H p) (H p') hlabel

theorem equal_hash_labels_survive {V : Type*} [AddCommGroup V]
    (H : V →+ UnitAddCircle) (Q : ℕ) (hQ : 2 ≤ Q) (p p' : V)
    {K₀ : Set V} (hlabel : label Q (H p) = label Q (H p'))
    (hcat : p' - p ∈ K₀) : p' - p ∈ surviving H Q K₀ :=
  ⟨hcat, equal_hash_labels_norm_lt H Q hQ p p' hlabel⟩

#print axioms label_range
#print axioms equal_labels_small_representative
#print axioms equal_labels_close
#print axioms norm_coe_eq_nearest_integer
#print axioms realWeightedHash_apply
#print axioms equal_hash_labels_survive

end DeletionCode.CircleHash
