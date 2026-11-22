import DeletionCode.Explicit.FieldHash
import Mathlib.Analysis.Real.Sqrt

/-! Simultaneous bucket balance for ternary linear hashes (manuscript `d:balance`). -/

namespace DeletionCode.Explicit.BucketBalance

open FieldHash
variable {n θ J : ℕ}

abbrev Word (n : ℕ) := Fin n → F₃
abbrev Family (n : ℕ) := Finset (Word n)

def bucketCount (B : Family n) (H : TernaryMatrix θ n) (z : Word θ) : ℕ :=
  (B.filter fun v => H.mulVec v = z).card

/-- The manuscript's sum of squared bucket deviations, normalized by family size. -/
def potential (B : Fin J → Family n) (H : TernaryMatrix θ n) : ℚ :=
  ∑ j, (∑ z : Word θ, ((bucketCount (B j) H z : ℚ) - (B j).card / (3 : ℚ)^θ)^2) /
    (B j).card

/-- One kernel equation for an ordered pair of family members. -/
def differenceRow (v w : Word n) : TernaryMatrix 1 n := fun _ => v - w

theorem differenceRow_iff (H : TernaryMatrix θ n) (v w : Word n) :
    (∀ j, (differenceRow v w).mulVec (H j) = 0) ↔ H.mulVec v = H.mulVec w := by
  have entry (j : Fin θ) (i : Fin 1) :
      (differenceRow v w).mulVec (H j) i = H.mulVec v j - H.mulVec w j := by
    change dotProduct (v - w) (H j) = dotProduct (H j) v - dotProduct (H j) w
    rw [sub_dotProduct, dotProduct_comm v, dotProduct_comm w]
  constructor
  · intro h
    funext j
    exact sub_eq_zero.mp (by simpa only [entry, Pi.zero_apply] using congrFun (h j) 0)
  · intro h j
    funext i
    simp [entry, h]

/-- Sum any bucket-dependent weight over members of a family. -/
private theorem sum_bucket_weight (B : Family n) (H : TernaryMatrix θ n) (f : Word θ → ℚ) :
    ∑ z, (bucketCount B H z : ℚ) * f z = ∑ v ∈ B, f (H.mulVec v) := by
  classical
  calc
    _ = ∑ z, ∑ v ∈ B, if H.mulVec v = z then f z else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_ite]
      simp [bucketCount, nsmul_eq_mul]
    _ = _ := by rw [Finset.sum_comm]; simp

/-- The squared-deviation and ordered-pair expressions in `d:potential` agree. -/
theorem potential_eq_pairs (B : Fin J → Family n) (H : TernaryMatrix θ n) :
    potential B H = ∑ j, ((∑ v ∈ B j, ∑ w ∈ B j, if H.mulVec v = H.mulVec w then (1 : ℚ) else 0) /
      (B j).card - (B j).card / (3 : ℚ)^θ) := by
  classical
  unfold potential
  apply Finset.sum_congr rfl
  intro j _
  let b := B j
  let M : ℚ := b.card
  let P : ℚ := 3^θ
  let ν (z : Word θ) : ℚ := bucketCount b H z
  have hsum : ∑ z, ν z = M := by simpa [ν, M] using sum_bucket_weight b H (fun _ => 1)
  have hsq : ∑ z, (ν z)^2 =
      ∑ v ∈ b, ∑ w ∈ b, if H.mulVec v = H.mulVec w then (1 : ℚ) else 0 := by
    rw [show (∑ z, (ν z)^2) = ∑ z, ν z * ν z by simp [sq], sum_bucket_weight b H ν]
    apply Finset.sum_congr rfl
    intro v _
    simp only [Finset.sum_boole, ν, bucketCount]
    congr 2
    ext w
    simp [eq_comm]
  have hcard : (Fintype.card (Word θ) : ℚ) = P := by simp [Word, F₃, P]
  change (∑ z, (ν z - M / P)^2) / M = _ / M - M / P
  rw [← hsq]
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  have hP : P ≠ 0 := by dsimp [P]; positivity
  by_cases hM : M = 0
  · simp [hM]
  · field_simp [hM, hP]
    ring

/-- Exact rational returned by summing the partial-hash collision probabilities.
Only the supplied families and their ordered pairs are enumerated. -/
def conditionalPotential (B : Fin J → Family n) (p : PartialHash θ n) : ℚ :=
  ∑ j, ((∑ v ∈ B j, ∑ w ∈ B j, conditionalKernelProbability (differenceRow v w) p) /
    (B j).card - (B j).card / (3 : ℚ)^θ)

/-- Uniform average over all total hashes extending the fixed entries. -/
noncomputable def completionMean (p : PartialHash θ n) (f : TernaryMatrix θ n → ℚ) : ℚ := by
  classical
  exact (∑ h : {H : Fin θ → Fin n → F₃ // Extends p H}, f h.val) /
    (Nat.card {H : Fin θ → Fin n → F₃ // Extends p H} : ℚ)

theorem mean_sum {ι : Type*} (s : Finset ι) (p : PartialHash θ n)
    (f : ι → TernaryMatrix θ n → ℚ) :
    completionMean p (fun H => ∑ i ∈ s, f i H) = ∑ i ∈ s, completionMean p (f i) := by
  classical
  simp only [completionMean, div_eq_mul_inv, Finset.sum_comm (s := Finset.univ) (t := s),
    Finset.sum_mul]

private theorem mean_sub_const (p : PartialHash θ n) (f : TernaryMatrix θ n → ℚ) (a b : ℚ) :
    completionMean p (fun H => f H / a - b) = completionMean p f / a - b := by
  classical
  have hc : (Fintype.card {H : Fin θ → Fin n → F₃ // Extends p H} : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (by simpa only [Nat.card_eq_fintype_card] using extends_card_pos p)
  simp only [completionMean, Nat.card_eq_fintype_card, div_eq_mul_inv, Finset.sum_sub_distrib,
    ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hc]

theorem mean_div (p : PartialHash θ n) (f : TernaryMatrix θ n → ℚ) (a : ℚ) :
    completionMean p (fun H => f H / a) = completionMean p f / a := by
  simpa using mean_sub_const p f a 0

/-- The mean of the indicator of a joint kernel event, for any number of rows. -/
theorem mean_kernel {r : ℕ} (p : PartialHash θ n) (A : TernaryMatrix r n) :
    completionMean p (fun H => if ∀ j, A.mulVec (H j) = 0 then 1 else 0) =
      conditionalKernelProbability A p := by
  classical
  let e : {h : {H : Fin θ → Fin n → F₃ // Extends p H} // ∀ j, A.mulVec (h.val j) = 0} ≃
      {H : Fin θ → Fin n → F₃ // Extends p H ∧ ∀ j, A.mulVec (H j) = 0} :=
    { toFun := fun h => ⟨h.val.val, h.val.property, h.property⟩
      invFun := fun h => ⟨⟨h.val, h.property.1⟩, h.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [conditionalKernelProbability_eq_fraction, ← Nat.card_congr e]
  simp only [completionMean, Nat.card_eq_fintype_card, Finset.sum_boole, Fintype.card_subtype]

theorem mean_collision (p : PartialHash θ n) (v w : Word n) :
    completionMean p (fun H => if H.mulVec v = H.mulVec w then 1 else 0) =
      conditionalKernelProbability (differenceRow v w) p := by
  simpa only [differenceRow_iff] using mean_kernel p (differenceRow v w)

/-- The algorithm computes exactly the conditional expectation of the original
squared bucket potential for any pattern of fixed hash entries. -/
theorem conditionalPotential_eq_mean (B : Fin J → Family n) (p : PartialHash θ n) :
    conditionalPotential B p = completionMean p (potential B) := by
  classical
  rw [show potential B = _ from funext (potential_eq_pairs B)]
  simp only [conditionalPotential, mean_sum, mean_sub_const, mean_collision]

#print axioms conditionalPotential_eq_mean

/-- The initial partial hash, before setup chooses any entries. -/
def freeHash (θ n : ℕ) : PartialHash θ n := fun _ _ => none

private theorem extends_free (H : Fin θ → Fin n → F₃) : Extends (freeHash θ n) H := by
  simp [Extends, freeHash]

theorem free_kernel {m : ℕ} (A : TernaryMatrix m n) :
    conditionalKernelProbability A (freeHash θ n) = 1 / ((3 : ℚ)^θ)^A.rank := by
  let e : {H : Fin θ → Fin n → F₃ // Extends (freeHash θ n) H} ≃ (Fin θ → Fin n → F₃) :=
    { toFun := Subtype.val
      invFun := fun h => ⟨h, extends_free h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← uniform_kernel_probability A θ, conditionalKernelProbability_eq_fraction,
    independentProbability_eq_fraction, Nat.card_congr e]
  congr 2
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun H => and_iff_right (extends_free H)))

theorem uniform_collision (v w : Word n) :
    conditionalKernelProbability (differenceRow v w) (freeHash θ n) =
      if v = w then 1 else 1 / (3 : ℚ)^θ := by
  rw [free_kernel]
  by_cases h : v = w
  · subst w
    have hr : differenceRow v v = 0 := by ext; simp [differenceRow]
    simp [hr]
  · have hr : (differenceRow v w).rank = 1 := by
      rw [Matrix.rank_eq_finrank_span_row]
      change Module.finrank F₃ (Submodule.span F₃ (Set.range (fun _ : Fin 1 => v - w))) = 1
      rw [Set.range_const]
      exact finrank_span_singleton (sub_ne_zero.mpr h)
    simp [hr, h]

/-- With all entries free, each nonempty family contributes exactly `1 - 1/P`. -/
theorem uniform_mean (B : Fin J → Family n) (hne : ∀ j, (B j).Nonempty) :
    completionMean (freeHash θ n) (potential B) = (J : ℚ) * (1 - 1 / (3 : ℚ)^θ) := by
  classical
  rw [← conditionalPotential_eq_mean]
  unfold conditionalPotential
  let q : ℚ := 1 / (3 : ℚ)^θ
  have pair (v w : Word n) : conditionalKernelProbability (differenceRow v w) (freeHash θ n) =
      q + (if v = w then 1 - q else 0) := by
    rw [uniform_collision]
    split <;> simp_all [q]
  simp_rw [pair]
  calc
    _ = ∑ _j : Fin J, (1 - q) := by
      apply Finset.sum_congr rfl
      intro j _
      have hM : ((B j).card : ℚ) ≠ 0 := by exact_mod_cast (hne j).card_pos.ne'
      have row (v : Word n) (hv : v ∈ B j) :
          (∑ w ∈ B j, (q + if v = w then 1 - q else 0)) = (B j).card * q + (1 - q) := by
        simp [Finset.sum_add_distrib, hv, nsmul_eq_mul]
      rw [Finset.sum_congr rfl row]
      simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      dsimp [q]
      field_simp [hM]
      ring
    _ = _ := by simp [q, nsmul_eq_mul]; ring

theorem potential_nonneg (B : Fin J → Family n) (H : TernaryMatrix θ n) : 0 ≤ potential B H := by
  exact Finset.sum_nonneg fun j _ => div_nonneg
    (Finset.sum_nonneg fun z _ => sq_nonneg _) (Nat.cast_nonneg _)

/-- One squared bucket deviation is bounded by the full potential times its family size. -/
theorem bucket_deviation_sq (B : Fin J → Family n) (H : TernaryMatrix θ n)
    (j : Fin J) (z : Word θ) (hne : (B j).Nonempty) :
    ((bucketCount (B j) H z : ℚ) - (B j).card / (3 : ℚ)^θ)^2 ≤ potential B H * (B j).card := by
  let term (i : Fin J) (y : Word θ) := ((bucketCount (B i) H y : ℚ) - (B i).card / (3 : ℚ)^θ)^2
  have hsingle : term j z ≤ ∑ y, term j y :=
    Finset.single_le_sum (f := term j) (fun y _ => sq_nonneg _) (Finset.mem_univ z)
  have hfamily : (∑ y, term j y) / (B j).card ≤ potential B H :=
    Finset.single_le_sum (f := fun i => (∑ y, term i y) / (B i).card)
      (fun i _ => div_nonneg (Finset.sum_nonneg fun y _ => sq_nonneg _) (Nat.cast_nonneg _))
      (Finset.mem_univ j)
  exact hsingle.trans ((div_le_iff₀ (by exact_mod_cast hne.card_pos : (0 : ℚ) < (B j).card)).mp hfamily)

/-- All three inequalities of `d:bucket`, including the stated square-root bound. -/
theorem large_bucket_bounds (B : Fin J → Family n) (H : TernaryMatrix θ n)
    (hΦ : potential B H ≤ 3 * J) (j : Fin J) (z : Word θ)
    (hlarge : 12 * J * (3^θ)^2 ≤ (B j).card) :
    let M : ℝ := (B j).card
    let P : ℝ := 3^θ
    (bucketCount (B j) H z : ℝ) ≤ M/P + Real.sqrt (3*J*M) ∧
      M/P + Real.sqrt (3*J*M) ≤ 3*M/(2*P) ∧ 3*M/(2*P) ≤ 2*M/P := by
  dsimp only
  have hJ : 0 < J := j.pos
  have hM : 0 < (B j).card := lt_of_lt_of_le (by positivity) hlarge
  have hs := (bucket_deviation_sq B H j z (Finset.card_pos.mp hM)).trans
    (mul_le_mul_of_nonneg_right hΦ (Nat.cast_nonneg _))
  let P : ℝ := 3^θ
  let M : ℝ := (B j).card
  let ν : ℝ := bucketCount (B j) H z
  have hP : 0 < P := by dsimp [P]; positivity
  have hm : 0 ≤ M := by dsimp [M]; positivity
  have hl : 12 * (J : ℝ) * P^2 ≤ M := by dsimp [P, M]; exact_mod_cast hlarge
  have hd : (ν - M/P)^2 ≤ 3*(J : ℝ)*M := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr hs
    push_cast at hcast
    exact hcast
  change ν ≤ M/P + _ ∧ M/P + _ ≤ 3*M/(2*P) ∧ 3*M/(2*P) ≤ 2*M/P
  have hroot : Real.sqrt (3*(J : ℝ)*M) ≤ M/(2*P) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hl hm]
  refine ⟨?_, ?_, ?_⟩
  · linarith [Real.le_sqrt_of_sq_le hd]
  · linarith [show M/P + M/(2*P) = 3*M/(2*P) by field_simp; ring]
  · field_simp
    linarith

#print axioms uniform_mean
#print axioms large_bucket_bounds

end DeletionCode.Explicit.BucketBalance
