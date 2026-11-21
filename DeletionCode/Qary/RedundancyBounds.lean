import DeletionCode.PaperParameters

/-!
Finite-code and asymptotic redundancy estimates in an arbitrary base q >= 2.
The label exponents are explicit parameters, so the final coefficient does
not depend on the alphabet. Only the eventual threshold may depend on q.
-/
namespace DeletionCode.Qary.RedundancyBounds

open Filter

variable {β : Type*}

noncomputable def redundancy (q n : ℕ) (C : Finset β) : ℝ :=
  (n : ℝ) - Real.logb q (C.card : ℝ)

theorem card_positive (q n Q : ℕ) (C : Finset β) (hq : 1 ≤ q)
    (hcard : q ^ n ≤ 8 * Q * C.card) : 0 < C.card := by
  have hp : 0 < q ^ n := pow_pos (by omega) _
  by_contra h
  have hz : C.card = 0 := by omega
  rw [hz, mul_zero] at hcard
  omega

theorem code_nonempty (q n Q : ℕ) (C : Finset β) (hq : 1 ≤ q)
    (hcard : q ^ n ≤ 8 * Q * C.card) : C.Nonempty :=
  Finset.card_pos.mp (card_positive q n Q C hq hcard)

theorem logb_eight_le (q : ℕ) (hq : 2 ≤ q) : Real.logb q (8 : ℝ) ≤ 3 := by
  have hqreal : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hb : (1 : ℝ) < q := by linarith
  have hp : (8 : ℝ) ≤ (q : ℝ) ^ (3 : ℕ) := by
    nlinarith [sq_nonneg ((q : ℝ) - 2)]
  have h := Real.logb_le_logb_of_le hb (by norm_num : (0 : ℝ) < 8) hp
  simpa only [Real.logb_pow, Real.logb_self_eq_one hb, Nat.cast_ofNat, mul_one] using h

/-- A factor-eight finite loss costs at most three q-ary symbols. -/
theorem redundancy_le_log_labels (q n Q : ℕ) (C : Finset β)
    (hq : 2 ≤ q) (hQ : 1 ≤ Q) (hcard : q ^ n ≤ 8 * Q * C.card) :
    redundancy q n C ≤ Real.logb q (Q : ℝ) + 3 := by
  have hb : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hc : (0 : ℝ) < C.card := by
    exact_mod_cast card_positive q n Q C (by omega) hcard
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hreal : (q : ℝ) ^ n ≤ 8 * (Q : ℝ) * (C.card : ℝ) := by
    exact_mod_cast hcard
  have hlog := Real.logb_le_logb_of_le hb (pow_pos (by linarith : (0 : ℝ) < q) n) hreal
  rw [Real.logb_mul (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hQpos))
      (ne_of_gt hc), Real.logb_mul (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hQpos)] at hlog
  simp only [Real.logb_pow, Real.logb_self_eq_one hb, mul_one] at hlog
  have h8 := logb_eight_le q hq
  unfold redundancy
  linarith

/-- The old binary window length is still logarithmic in n for every fixed q. -/
theorem logb_L_le_logb_logb_add (q n : ℕ) (hq : 2 ≤ q) (hn : 2 ≤ n) :
    Real.logb q (PaperParameters.L n : ℝ) ≤
      Real.logb q (Real.logb q (n : ℝ)) + Real.logb q (21 * Real.logb 2 q) := by
  have hb : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlogn : 0 < Real.logb q (n : ℝ) := Real.logb_pos hb hnreal
  have hlogq : 0 < Real.logb 2 (q : ℝ) := Real.logb_pos (by norm_num) hb
  have hchange : Real.logb 2 (q : ℝ) * Real.logb q (n : ℝ) =
      Real.logb 2 (n : ℝ) :=
    Real.mul_logb (by linarith) (by linarith) (by linarith)
  have hwindow := PaperParameters.L_le_twenty_one_logb n hn
  rw [← hchange] at hwindow
  have hL : (0 : ℝ) < PaperParameters.L n := by
    exact_mod_cast (show 0 < PaperParameters.L n by have := PaperParameters.nine_le_L n; omega)
  have h := Real.logb_le_logb_of_le hb hL hwindow
  rw [← mul_assoc, Real.logb_mul (mul_ne_zero (by norm_num : (21 : ℝ) ≠ 0)
    (ne_of_gt hlogq)) (ne_of_gt hlogn)] at h
  linarith

theorem tendsto_logb_logb_atTop (q : ℕ) (hq : 2 ≤ q) :
    Tendsto (fun n : ℕ => Real.logb q (Real.logb q (n : ℝ))) atTop atTop := by
  have hb : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  exact (Real.tendsto_logb_atTop hb).comp
    ((Real.tendsto_logb_atTop hb).comp tendsto_natCast_atTop_atTop)

/-- The multiplicative constant two is independent of q. -/
theorem eventually_logb_L_le_twice_logb_logb (q : ℕ) (hq : 2 ≤ q) :
    ∀ᶠ n : ℕ in atTop, Real.logb q (PaperParameters.L n : ℝ) ≤
      2 * Real.logb q (Real.logb q (n : ℝ)) := by
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_logb_logb_atTop q hq).eventually_ge_atTop
      (Real.logb q (21 * Real.logb 2 q))] with n hn hlarge
  have h := logb_L_le_logb_logb_add q n hq hn
  linarith

/-- Integer label scale with separate alphabet, length and window exponents. -/
def labelCount (q d a b n : ℕ) : ℕ :=
  8 * q ^ a * n ^ d * PaperParameters.L n ^ b

theorem labelCount_positive (q d a b n : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n) :
    0 < labelCount q d a b n := by
  have hL : 0 < PaperParameters.L n := by have := PaperParameters.nine_le_L n; omega
  unfold labelCount
  positivity

theorem logb_labelCount (q d a b n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    Real.logb q (labelCount q d a b n : ℝ) =
      Real.logb q (8 : ℝ) + a + (d : ℝ) * Real.logb q (n : ℝ) +
        (b : ℝ) * Real.logb q (PaperParameters.L n : ℝ) := by
  have hb : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLpos : (0 : ℝ) < PaperParameters.L n := by
    exact_mod_cast (show 0 < PaperParameters.L n by have := PaperParameters.nine_le_L n; omega)
  simp only [labelCount, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  rw [Real.logb_mul (by positivity) (pow_ne_zero _ (ne_of_gt hLpos)),
    Real.logb_mul (by positivity) (pow_ne_zero _ (ne_of_gt hnpos)),
    Real.logb_mul (by norm_num : (8 : ℝ) ≠ 0) (by positivity),
    Real.logb_pow, Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hb, mul_one]

/-- The coefficient 2b+a+6 is independent of q; the threshold may depend on q.
The only hypothesis on the finite code is the cardinality estimate. -/
theorem eventually_paper_redundancy_bound (q d a b : ℕ) (hq : 2 ≤ q) :
    ∀ᶠ n : ℕ in atTop, ∀ {γ : Type*} (C : Finset γ),
      q ^ n ≤ 8 * labelCount q d a b n * C.card →
      redundancy q n C ≤ (d : ℝ) * Real.logb q (n : ℝ) +
        ((2 * b + a + 6 : ℕ) : ℝ) * Real.logb q (Real.logb q (n : ℝ)) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_logb_L_le_twice_logb_logb q hq,
    (tendsto_logb_logb_atTop q hq).eventually_ge_atTop 1] with n hn hwindow hll
  intro γ C hcard
  have hbase := redundancy_le_log_labels q n (labelCount q d a b n) C hq
    (labelCount_positive q d a b n (by omega) hn) hcard
  rw [logb_labelCount q d a b n hq hn] at hbase
  have h8 := logb_eight_le q hq
  have hmul := mul_le_mul_of_nonneg_left hwindow (Nat.cast_nonneg b : (0 : ℝ) ≤ b)
  have ha := mul_le_mul_of_nonneg_left hll (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

#print axioms redundancy_le_log_labels
#print axioms eventually_paper_redundancy_bound

end DeletionCode.Qary.RedundancyBounds
