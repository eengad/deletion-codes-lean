import DeletionCode.Explicit.Labels
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Redundancy of the concrete length choices in `d:wrapper-redundancy`. -/

namespace DeletionCode.Explicit

private theorem clog_product {q : ℕ} (hq : 2 ≤ q) (a x : ℕ) :
    Nat.clog q (a * x) ≤ Nat.clog q a + Nat.clog q x := by
  apply Nat.clog_le_of_le_pow
  rw [Nat.pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog hq a) (Nat.le_pow_clog hq x)

private theorem clog_power {q : ℕ} (hq : 2 ≤ q) (a d : ℕ) :
    Nat.clog q (a ^ d) ≤ d * Nat.clog q a := by
  apply Nat.clog_le_of_le_pow
  rw [Nat.mul_comm d, Nat.pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog hq a) d

private theorem clog_succ_le {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    Nat.clog q (n + 1) ≤ Nat.clog q n + 1 := by
  apply Nat.clog_le_of_le_pow
  rw [Nat.pow_succ]
  have hn := Nat.le_pow_clog hq n
  have hp : 0 < q ^ Nat.clog q n := Nat.pow_pos (by omega)
  have hm := Nat.mul_le_mul_left (q ^ Nat.clog q n) hq
  omega

/-- The uniform label budget costs at most `s-1` copies of the message-length
logarithm. All gram and threshold factors are isolated in lower-order terms. -/
theorem publicLabel_clog_bound {q : ℕ} (hq : 2 ≤ q) (b s C A l₀ : ℕ) :
    ∃ K : ℕ, ∀ n,
      Nat.clog q (publicLabelBound q b s C A l₀ n) ≤
        (s - 1) * Nat.clog q n + A * Nat.clog q (Nat.clog q n + 1) + K := by
  let g := C * (b + 3)
  refine ⟨l₀ + Nat.clog q 9 + A * Nat.clog q g, ?_⟩
  intro n
  let x := Nat.clog q n
  let y := Nat.clog q (x + 1)
  have hgram : gramLength q b C n ≤ g * (x + 1) := by
    dsimp [gramLength, g, x]
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    nlinarith
  have hg : Nat.clog q (gramLength q b C n) ≤ Nat.clog q g + y :=
    Nat.le_trans (Nat.clog_mono_right q hgram) (clog_product hq g (x + 1))
  have h₁ := clog_product hq (9 * n ^ (s - 1)) (gramLength q b C n ^ A)
  have h₂ := clog_product hq 9 (n ^ (s - 1))
  have h₃ := clog_power hq n (s - 1)
  have h₄ := clog_power hq (gramLength q b C n) A
  have h₅ := Nat.mul_le_mul_left A hg
  rw [Nat.mul_add] at h₅
  unfold publicLabelBound
  rcases Nat.le_total (q ^ l₀) (9 * n ^ (s - 1) * gramLength q b C n ^ A) with h | h
  · rw [Nat.max_eq_right h]
    change _ ≤ (s - 1) * x + A * y + _
    change Nat.clog q (n ^ (s - 1)) ≤ (s - 1) * x at h₃
    omega
  · rw [Nat.max_eq_left h, Nat.clog_pow q l₀ hq]
    omega

/-- A ceiling-logarithmic leading term and one iterated logarithm suffice
for the sum of both tag lengths produced by the executable setup. -/
theorem tagLengths_clog_bound {q : ℕ} (hq : 2 ≤ q) (b t C A l₀ : ℕ) :
    ∃ K : ℕ, ∀ n,
      let T := prepareTags q b t n (publicLabelBound q b (2 * t) C A l₀ n)
      T.m₀ + T.mOut ≤ (2 * t - 1) * Nat.clog q n +
        K * (Nat.clog q (Nat.clog q n + 1) + 1) := by
  let s := 2 * t
  obtain ⟨D, hD⟩ := publicLabel_clog_bound hq b s C A l₀
  let F := (s - 1) + A + D + s * b + 5
  let E := A + s + 1 + s
  let overhead := D + 2 * (s * Nat.clog q F) + 1 + 2 * tagConstant b s
  refine ⟨E + overhead, ?_⟩
  intro n
  let x := Nat.clog q n
  let y := Nat.clog q (x + 1)
  let j := Nat.clog q (n + 1)
  let L := Nat.clog q (publicLabelBound q b s C A l₀ n)
  let O := Nat.clog q (j + 1)
  have hL : L ≤ (s - 1) * x + A * y + D := hD n
  have hj : j ≤ x + 1 := clog_succ_le hq n
  have hO : O ≤ y + 1 := calc
    _ ≤ Nat.clog q ((x + 1) + 1) := Nat.clog_mono_right q (Nat.succ_le_succ hj)
    _ ≤ _ := clog_succ_le hq (x + 1)
  have hy : y ≤ x + 1 := Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self hq))
  have hAy := Nat.mul_le_mul_left A hy
  have hc : (s - 1) * x ≤ (s - 1) * (x + 1) := Nat.mul_le_mul_left _ (by omega)
  have dominate (a : ℕ) : a ≤ a * (x + 1) := by rw [Nat.mul_succ]; omega
  have hInner : L + j + s * b + 2 ≤ F * (x + 1) := by
    dsimp [F]
    simp only [Nat.add_mul]
    have := dominate D
    have := dominate (s * b)
    omega
  have hOuter : O + 0 + s * b + 2 ≤ F * (x + 1) := by
    dsimp [F]
    simp only [Nat.add_mul]
    have := dominate (s * b)
    omega
  have log_bound (u : ℕ) (hu : u ≤ F * (x + 1)) : Nat.clog q u ≤ Nat.clog q F + y :=
    Nat.le_trans (Nat.clog_mono_right q hu) (clog_product hq F (x + 1))
  have hin := Nat.mul_le_mul_left s (log_bound _ hInner)
  have hout := Nat.mul_le_mul_left s (log_bound _ hOuter)
  rw [Nat.mul_add] at hin hout
  change (L + s * Nat.clog q (L + j + s * b + 2) + tagConstant b s) +
      (O + s * Nat.clog q (O + 0 + s * b + 2) + tagConstant b s) ≤
      (s - 1) * x + (E + overhead) * (y + 1)
  have hsum : (L + s * Nat.clog q (L + j + s * b + 2) + tagConstant b s) +
      (O + s * Nat.clog q (O + 0 + s * b + 2) + tagConstant b s) ≤
      (s - 1) * x + E * y + overhead := by
    dsimp [E, overhead]
    simp only [Nat.add_mul, Nat.one_mul, Nat.add_zero] at hout ⊢
    omega
  apply Nat.le_trans hsum
  rw [Nat.mul_succ]
  have hm := Nat.mul_le_mul_right y (show E ≤ E + overhead by omega)
  omega

private theorem eventual_fit {q c K : ℕ} (hq : 2 ≤ q) :
    ∃ N : ℕ, ∀ n ≥ N,
      c * Nat.clog q n + K * (Nat.clog q (Nat.clog q n + 1) + 1) + 1 ≤ n := by
  let E := c + K + 1
  refine ⟨q ^ (2 * E + 5) + 1, ?_⟩
  intro n hn
  let x := Nat.clog q n
  let r := x - 1
  have hx : 2 * E + 5 < x := (Nat.lt_clog_iff_pow_lt hq).mpr (by omega)
  have hxr : x = r + 1 := by dsimp [r]; omega
  have hy : Nat.clog q (x + 1) ≤ x + 1 := Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self hq))
  have hsq := square_le_two_pow r (by omega)
  have hn₂ : 1 < n := by
    have hp : 0 < q ^ (2 * E + 5) := Nat.pow_pos (by omega)
    omega
  have hexp : q ^ r < n := Nat.pow_pred_clog_lt_self hq hn₂
  have h₁ : c * x ≤ c * (r + 3) := Nat.mul_le_mul_left _ (by omega)
  have h₂ : K * (Nat.clog q (x + 1) + 1) ≤ K * (r + 3) := Nat.mul_le_mul_left _ (by omega)
  have h₃ : E * (r + 3) ≤ E * (2 * r) := Nat.mul_le_mul_left E (by omega)
  have h₄ : (2 * E) * r ≤ r * r := Nat.mul_le_mul_right r (by omega)
  rw [show E * (2 * r) = (2 * E) * r by ring] at h₃
  have hd : c * (r + 3) + K * (r + 3) + 1 ≤ E * (r + 3) := by
    dsimp [E]; simp only [Nat.add_mul, Nat.one_mul]; omega
  have hqpow := Nat.pow_le_pow_left hq r
  change c * x + K * (Nat.clog q (x + 1) + 1) + 1 ≤ n
  omega

private theorem real_clog_le {q n : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n) :
    (Nat.clog q n : ℝ) ≤ Real.logb q n + 1 := by
  rw [← Real.natCeil_logb_natCast]
  exact le_of_lt (Nat.ceil_lt_add_one (Real.logb_nonneg
    (by exact_mod_cast (show 1 < q by omega)) (by exact_mod_cast hn)))

private theorem real_iterated_clog_le {q n : ℕ} (hq : 2 ≤ q) (hn : q ^ q ≤ n) :
    1 ≤ Real.logb q (Real.logb q n) ∧
    ((Nat.clog q (Nat.clog q n + 1) : ℕ) : ℝ) + 1 ≤ 5 * Real.logb q (Real.logb q n) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hn₁ : 1 ≤ n := by have := Nat.pow_pos (n := q) (by omega : 0 < q); omega
  have hbig := Real.logb_le_logb_of_le hqR (show (0 : ℝ) < (q : ℝ) ^ q by positivity)
    (show (q : ℝ) ^ q ≤ n by exact_mod_cast hn)
  rw [Real.logb_pow, Real.logb_self_eq_one hqR, mul_one] at hbig
  have h₂ := Real.logb_le_logb_of_le hqR (by linarith : (0 : ℝ) < q) hbig
  rw [Real.logb_self_eq_one hqR] at h₂
  have h₃ : Real.logb (q : ℝ) 3 ≤ 2 := by
    have hq₂ : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have h := Real.logb_le_logb_of_le hqR (by norm_num : (0 : ℝ) < 3)
      (show (3 : ℝ) ≤ (q : ℝ)^2 by nlinarith)
    simpa [Real.logb_pow, Real.logb_self_eq_one hqR] using h
  have hx := real_clog_le hq hn₁
  have hy := real_clog_le (n := Nat.clog q n + 1) hq (by omega)
  push_cast at hy
  have hmono := Real.logb_le_logb_of_le hqR (by positivity : (0 : ℝ) < (Nat.clog q n : ℝ) + 1)
    (show (Nat.clog q n : ℝ) + 1 ≤ 3 * Real.logb q n by linarith)
  rw [Real.logb_mul (by norm_num) (by linarith : Real.logb q n ≠ 0)] at hmono
  exact ⟨h₂, by linarith⟩

/-- The two actual tags fit at all sufficiently large lengths, leaving at
least one message symbol. Their cost has the leading coefficient of
`d:wrapper-redundancy`, with a constant depending on the fixed parameters. -/
theorem wrapper_redundancy {q t : ℕ} (hq : 2 ≤ q) (ht : 2 ≤ t) (b C A l₀ : ℕ) :
    ∃ K N : ℕ, ∀ n ≥ N,
      let T := prepareTags q b t n (publicLabelBound q b (2 * t) C A l₀ n)
      T.m₀ + T.mOut < n ∧
      (n : ℝ) - (T.k : ℝ) ≤ (2 * (t : ℝ) - 1) * Real.logb q n +
        K * Real.logb q (Real.logb q n) := by
  let c := 2 * t - 1
  obtain ⟨D, hD⟩ := tagLengths_clog_bound hq b t C A l₀
  obtain ⟨N, hN⟩ := eventual_fit (c := c) (K := D) hq
  refine ⟨c + 5 * D, max N (q ^ q), ?_⟩
  intro n hn T
  obtain ⟨hnN, hlarge⟩ := Nat.max_le.mp hn
  have hsize := hD n
  have hfit := hN n hnN
  change T.m₀ + T.mOut ≤ c * Nat.clog q n + D * (Nat.clog q (Nat.clog q n + 1) + 1) at hsize
  have hT : T.m₀ + T.mOut < n := by omega
  refine ⟨hT, ?_⟩
  have hred : n - T.k = T.m₀ + T.mOut := prepareTags_redundancy (Nat.le_of_lt hT)
  have hk : T.k ≤ n := by change n - _ - _ ≤ n; omega
  rw [← Nat.cast_sub hk, hred]
  have hcast : ((T.m₀ + T.mOut : ℕ) : ℝ) ≤
      (c : ℝ) * Nat.clog q n + D * ((Nat.clog q (Nat.clog q n + 1) : ℝ) + 1) := by
    exact_mod_cast hsize
  have hn₁ : 1 ≤ n := by have := Nat.pow_pos (n := q) (by omega : 0 < q); omega
  have hx := real_clog_le hq hn₁
  obtain ⟨h₂, hy⟩ := real_iterated_clog_le hq hlarge
  have hc : (c : ℝ) = 2 * (t : ℝ) - 1 := by
    dsimp [c]; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hcx := mul_le_mul_of_nonneg_left hx (show 0 ≤ (c : ℝ) by positivity)
  have hDy := mul_le_mul_of_nonneg_left hy (show 0 ≤ (D : ℝ) by positivity)
  have hcover := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ (c : ℝ) by positivity)
  push_cast at hcast ⊢
  rw [← hc]
  linarith only [hcast, hcx, hDy, hcover]

/-- For the positive gram-length constant of `d:parameters`, the tag budget also
has the manuscript's matching leading lower bound once both tags fit. -/
theorem wrapper_redundancy_lower {q t n C : ℕ} (hq : 2 ≤ q) (ht : 2 ≤ t)
    (hn : 1 ≤ n) (hC : 1 ≤ C) (b A l₀ : ℕ) :
    let B := publicLabelBound q b (2 * t) C A l₀ n
    let T := prepareTags q b t n B
    T.m₀ + T.mOut ≤ n →
    (2 * (t : ℝ) - 1) * Real.logb q n ≤ (n : ℝ) - (T.k : ℝ) := by
  intro B T hfit
  let c := 2 * t - 1
  have hg : 0 < gramLength q b C n := by
    unfold gramLength
    exact Nat.mul_pos hC (by omega)
  have hp : 0 < gramLength q b C n ^ A := Nat.pow_pos hg
  have hB : n ^ c ≤ B := by
    have h₁ := Nat.mul_le_mul_left (9 * n ^ c) hp
    have h₂ : n ^ c ≤ 9 * n ^ c := by omega
    apply Nat.le_trans _ (Nat.le_max_right ..)
    simp only [Nat.mul_one] at h₁
    exact Nat.le_trans h₂ h₁
  have hqR : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hlog := Real.logb_le_logb_of_le hqR (show (0 : ℝ) < (n : ℝ) ^ c by positivity)
    (show (n : ℝ) ^ c ≤ (B : ℝ) by exact_mod_cast hB)
  rw [Real.logb_pow] at hlog
  have hbceil : Real.logb q B ≤ (Nat.clog q B : ℝ) := by
    rw [← Real.natCeil_logb_natCast]
    exact Nat.le_ceil _
  have htags : Nat.clog q B ≤ T.m₀ + T.mOut := by
    change Nat.clog q B ≤ (Nat.clog q B + _ + _) + _
    omega
  have hred : n - T.k = T.m₀ + T.mOut := prepareTags_redundancy hfit
  have hk : T.k ≤ n := by change n - _ - _ ≤ n; omega
  have hc : (c : ℝ) = 2 * (t : ℝ) - 1 := by
    dsimp [c]; rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [← hc, ← Nat.cast_sub hk, hred]
  exact le_trans hlog (le_trans hbceil (by exact_mod_cast htags))

/-- Stage 1 of `sec:d-encoding` from the earlier sections' source hypotheses.
The same explicit tag tables determine the encoder, decoder, message length
and redundancy. The threshold and remainder are uniform in the supplied data. -/
theorem wrapped_code_of_source_data {q t : ℕ} (hq : 2 ≤ q) (ht : 2 ≤ t) (b C A l₀ : ℕ) :
    ∃ K N : ℕ, ∀ n ≥ N,
      let B := publicLabelBound q b (2 * t) C A l₀ n
      let T := prepareTags q b t n B
      (n : ℝ) - (T.k : ℝ) ≤ (2 * (t : ℝ) - 1) * Real.logb q n +
        K * Real.logb q (Real.logb q n) ∧
      ∀ (zero : Fin q) (D : RepairData (Fin q)) (largeLabel : QWord q → ℕ) (P : ℕ → ℕ),
        (∀ l, l₀ ≤ l → l ≤ n → P l < 3 * l ^ (2 * t - 1) * gramLength q b C l ^ A) →
        (∀ x : QWord q, l₀ ≤ x.length → x.length ≤ n → D.accepted x = true →
          largeLabel x < 3 * P x.length) →
        (∀ x y : QWord q, l₀ ≤ x.length → x.length = y.length → x.length ≤ n →
          D.accepted x = true → D.accepted y = true → largeLabel x = largeLabel y →
          Burst.WithinBursts b (2 * t) x y → x = y) →
        let W := T.wrapper zero D (labelAt l₀ largeLabel)
        ∀ u : QWord q, u.length = T.k → (W.encode u).length = n ∧
          ∀ z, Burst.WithinBursts b t (W.encode u) z → W.decode b t z = some u := by
  obtain ⟨K, N, h⟩ := wrapper_redundancy hq ht b C A l₀
  refine ⟨K, N, ?_⟩
  intro n hn B T
  obtain ⟨hfit, hred⟩ := h n hn
  refine ⟨hred, ?_⟩
  intro zero D label P hP hbound hsep
  exact encoding_correct_of_source_data hq zero D label P hP hbound hsep (Nat.le_of_lt hfit)

#print axioms wrapped_code_of_source_data

#print axioms wrapper_redundancy_lower

#print axioms wrapper_redundancy

#print axioms publicLabel_clog_bound
#print axioms tagLengths_clog_bound

end DeletionCode.Explicit
