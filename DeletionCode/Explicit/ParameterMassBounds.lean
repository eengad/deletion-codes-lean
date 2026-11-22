import DeletionCode.Explicit.ParameterEnumerationBounds

/-! Numerical consequences for the three normalized weights in
`d:parameters`. The weight estimates come from their own catalogue proofs. -/
namespace DeletionCode.Explicit.UniformParameters

variable {q b t ℓ : ℕ}
open scoped BigOperators

private theorem short_power {n ℓ : ℕ} (h : n^8 ≤ ℓ) : n^2 ≤ ℓ := by
  by_cases hn : n = 0
  · simp [hn]
  · exact (Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr hn) (by decide)).trans h

private theorem product_le {a b ℓ : ℕ} (ha : a^2 ≤ ℓ) (hb : b^2 ≤ ℓ) : a*b ≤ ℓ := by
  have hs : (a*b)^2 ≤ ℓ^2 := by
    rw [mul_pow, pow_two ℓ]
    exact Nat.mul_le_mul ha hb
  by_contra! h
  exact (Nat.pow_lt_pow_left h (by decide : 2 ≠ 0)).not_ge hs

private theorem eta_ge_cutoff (h : BasicBounds q b t ℓ) :
    cutoffExponent q b t ≤ eta q ℓ :=
  (cutoffExponent q b t).lt_two_pow_self.le.trans h.eta_ge

private theorem eight_power_le (hq : 2 ≤ q) (hstart : minLength q b t ≤ ℓ) : q^8 ≤ ℓ := by
  have hZ := (cutoff_lower q b t).1
  have hY : 8 ≤ 2^(cutoffExponent q b t) := by
    have h := (cutoffExponent q b t).lt_two_pow_self
    omega
  exact (Nat.pow_le_pow_right (by omega) hY).trans hstart

theorem matching_estimate_le (hq : 2 ≤ q) (hstart : minLength q b t ≤ ℓ)
    (hbinom : matchBound q b t ℓ ^ 8 ≤ ℓ) :
    (ℓ : ℚ)^2 * (matchBound q b t ℓ : ℚ) / (q : ℚ)^(windowLength q ℓ) ≤ 1 / (q : ℚ)^8 := by
  have hmul : matchBound q b t ℓ * q^4 ≤ ℓ := by
    apply product_le (short_power hbinom)
    rw [← pow_mul]
    exact eight_power_le hq hstart
  have hclog : ℓ ≤ q^(eta q ℓ) := Nat.le_pow_clog (by omega) _
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have he : ℓ^2 * matchBound q b t ℓ * q^8 ≤ q^(windowLength q ℓ) := by
    calc
      _ = ℓ^2 * (matchBound q b t ℓ * q^4) * q^4 := by ring
      _ ≤ ℓ^2 * ℓ * q^4 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hmul)
      _ = ℓ^3 * q^4 := by ring
      _ ≤ (q^(eta q ℓ))^3 * q^4 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hclog 3)
      _ = q^(windowLength q ℓ) := by
        rw [windowLength, pow_add, ← pow_mul, Nat.mul_comm (eta q ℓ) 3]
  exact_mod_cast (show ℓ^2 * matchBound q b t ℓ * q^8 ≤ 1 * q^(windowLength q ℓ) by simpa using he)

theorem exceptional_estimate_le (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : minLength q b t ≤ ℓ) :
    (3 : ℚ) * exceptionalConstant b t * (q : ℚ)^(b*edits t) * gram q b t ℓ *
      (ℓ : ℚ)^(edits t-1) / (hashCount q b t ℓ : ℚ) ≤ 1 / (q : ℚ)^8 := by
  have basic := basicBounds hq hb ht hstart
  have hℓ : 0 < ℓ := Nat.zero_lt_of_lt basic.record_length
  have hP := (hashCount_bounds (q := q) (b := b) (t := t) hℓ).1
  have hZ := (cutoff_lower q b t).2.2.2.2.2.1
  let X := exceptionalConstant b t * q^(b*edits t + 8)
  have hX : 3 * X ≤ gram q b t ℓ := by
    have hx : 64 * X ≤ cutoffExponent q b t := by
      simpa [X, Nat.mul_assoc] using hZ
    have hLg : eta q ℓ ≤ gram q b t ℓ := by
      change eta q ℓ ≤ gramMultiplier t * (eta q ℓ + b + 3)
      exact (by omega : eta q ℓ ≤ eta q ℓ + b + 3).trans
        (Nat.le_mul_of_pos_left _ ((by decide : 0 < 32).trans_le (multiplier_ge t)))
    exact (Nat.mul_le_mul_right X (by decide : 3 ≤ 64)).trans
      (hx.trans ((eta_ge_cutoff basic).trans hLg))
  have hA : 2 ≤ hashExponent q b t := by unfold hashExponent; omega
  have hN : 3 * exceptionalConstant b t * q^(b*edits t) * gram q b t ℓ *
      ℓ^(edits t-1) * q^8 ≤ hashCount q b t ℓ := by
    calc
      _ = ℓ^(edits t-1) * (3*X * gram q b t ℓ) := by unfold X; rw [pow_add]; ring
      _ ≤ ℓ^(edits t-1) * (gram q b t ℓ)^2 := Nat.mul_le_mul_left _ (by
        rw [pow_two]; exact Nat.mul_le_mul_right _ hX)
      _ ≤ hashThreshold q b t ℓ := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by have := basic.gram_large; omega) hA)
      _ ≤ _ := hP
  apply (div_le_div_iff₀ (by unfold hashCount; positivity) (by positivity)).mpr
  exact_mod_cast (show _ ≤ 1 * hashCount q b t ℓ by simpa using hN)

theorem core_estimate_le (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : minLength q b t ≤ ℓ) (hΓ : gamma q b t ℓ ^ 8 ≤ ℓ) :
    3 * (gamma q b t ℓ : ℚ) * (∑ r ∈ Finset.Icc 1 (coreLimit t),
        ((ℓ : ℚ)^t / (hashCount q b t ℓ : ℚ))^r) ≤ 1 / (q : ℚ)^8 := by
  have basic := basicBounds hq hb ht hstart
  have hℓ : 0 < ℓ := Nat.zero_lt_of_lt basic.record_length
  have hℓ' : 0 < (ℓ : ℚ) := by exact_mod_cast hℓ
  have hPow : ℓ^(t+1) ≤ hashCount q b t ℓ := by
    have ht' : t + 1 ≤ edits t - 1 := by unfold edits; omega
    refine (Nat.pow_le_pow_right hℓ ht').trans ?_
    refine (Nat.le_mul_of_pos_right _ ?_).trans (hashCount_bounds hℓ).1
    exact pow_pos (basic.gram_large.trans_lt' (by decide)) _
  let x : ℚ := (ℓ : ℚ)^t / (hashCount q b t ℓ : ℚ)
  have hx : x ≤ 1 / (ℓ : ℚ) := by
    unfold x
    apply (div_le_div_iff₀ (by unfold hashCount; positivity) hℓ').mpr
    simpa only [one_mul, ← pow_succ] using (show (ℓ : ℚ)^(t+1) ≤ (hashCount q b t ℓ : ℚ) by
      exact_mod_cast hPow)
  have hx₀ : 0 ≤ x := by unfold x; positivity
  have hx₁ : x ≤ 1 := hx.trans ((div_le_iff₀ hℓ').mpr (by simpa using (show (1 : ℚ) ≤ (ℓ : ℚ) by exact_mod_cast (show 1 ≤ ℓ from hℓ))))
  have hs : (∑ r ∈ Finset.Icc 1 (coreLimit t), x^r) ≤ (coreLimit t : ℚ) / ℓ := by
    calc
      _ ≤ ∑ _ ∈ Finset.Icc 1 (coreLimit t), (1 : ℚ) / ℓ := by
        apply Finset.sum_le_sum
        intro r hr
        have h1 := (Finset.mem_Icc.mp hr).1
        have he : x^r = x^(r-1) * x := by
          rw [← pow_succ, show r - 1 + 1 = r by omega]
        rw [he]
        exact (mul_le_of_le_one_left hx₀ (pow_le_one₀ hx₀ hx₁)).trans hx
      _ = _ := by simp [Nat.card_Icc, nsmul_eq_mul, div_eq_mul_inv]
  let a := 3 * coreLimit t * q^8
  have ha : a ≤ eta q ℓ := by
    have hh := (cutoff_lower q b t).2.2.2.2.2.2
    exact (Nat.mul_le_mul_right (q^8) (Nat.mul_le_mul_right (coreLimit t) (by decide : 3 ≤ 64))).trans
      (hh.trans (eta_ge_cutoff basic))
  have hmul : a * gamma q b t ℓ ≤ ℓ :=
    product_le ((Nat.pow_le_pow_left ha 2).trans basic.length_ge_eta_square) (short_power hΓ)
  change 3 * (gamma q b t ℓ : ℚ) * (∑ r ∈ Finset.Icc 1 (coreLimit t), x^r) ≤ _
  refine (mul_le_mul_of_nonneg_left hs (by positivity)).trans ?_
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hℓ' (by positivity)).mpr
  simp only [one_mul]
  have hh : (a : ℚ) * (gamma q b t ℓ : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hmul
  convert hh using 1
  simp only [a, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  ring

theorem mass_from_normalized {W : ℕ} (hq : 2 ≤ q) (hℓ : 8 ≤ ℓ)
    (h : (W : ℚ) / (q : ℚ)^ℓ ≤ 1 / (q : ℚ)^8) :
    W ≤ q^(ℓ-8) := by
  have h₁ := (div_le_div_iff₀ (by positivity : 0 < (q : ℚ)^ℓ)
    (by positivity : 0 < (q : ℚ)^8)).mp h
  have he : (q : ℚ)^ℓ = (q : ℚ)^(ℓ-8) * (q : ℚ)^8 := by
    rw [← pow_add, Nat.sub_add_cancel hℓ]
  rw [one_mul, he] at h₁
  exact_mod_cast le_of_mul_le_mul_right h₁ (by positivity)

/-- Apply the estimates to integer root masses. The exceptional and core
premises are the inequalities obtained by multiplying the two mean
bounds by the factors of three in `d:three-bounds`. -/
theorem root_masses_bound (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : minLength q b t ≤ ℓ) {matching exceptional core : ℕ}
    (hm : (matching : ℚ) / (q : ℚ)^ℓ ≤
      (ℓ : ℚ)^2 * (matchBound q b t ℓ : ℚ) / (q : ℚ)^(windowLength q ℓ))
    (he : (exceptional : ℚ) / (q : ℚ)^ℓ ≤
      3 * exceptionalConstant b t * (q : ℚ)^(b*edits t) * gram q b t ℓ *
        (ℓ : ℚ)^(edits t-1) / (hashCount q b t ℓ : ℚ))
    (hc : (core : ℚ) / (q : ℚ)^ℓ ≤ 3 * (gamma q b t ℓ : ℚ) *
      (∑ r ∈ Finset.Icc 1 (coreLimit t), ((ℓ : ℚ)^t / (hashCount q b t ℓ : ℚ))^r)) :
    matching ≤ q^(ℓ-8) ∧ exceptional ≤ q^(ℓ-8) ∧ core ≤ q^(ℓ-8) := by
  have h := basicBounds hq hb ht hstart
  have hℓ : 8 ≤ ℓ := (by decide : 8 ≤ 400).trans (h.gram_large.trans h.borrowed_length)
  obtain ⟨hΓ, _, hbinom⟩ := enumerationBounds hq hb ht hstart
  exact ⟨mass_from_normalized hq hℓ (hm.trans (matching_estimate_le hq hstart hbinom)),
    mass_from_normalized hq hℓ (he.trans (exceptional_estimate_le hq hb ht hstart)),
    mass_from_normalized hq hℓ (hc.trans (core_estimate_le hq hb ht hstart hΓ))⟩

#print axioms root_masses_bound
#print axioms matching_estimate_le
#print axioms exceptional_estimate_le
#print axioms core_estimate_le
#print axioms mass_from_normalized

end DeletionCode.Explicit.UniformParameters
