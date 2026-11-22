import DeletionCode.Explicit.Labels
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The integer formulas in `d:parameters`, `d:cutoff`, `d:Gamma`, and
`d:Jbound`. Ceiling logs use the least exponent passing an integer test. -/
namespace DeletionCode.Explicit.UniformParameters

def edits (t : ℕ) : ℕ := 2 * t
def alphabetBits (q : ℕ) : ℕ := Nat.clog 2 q
def gramMultiplier (t : ℕ) : ℕ := max 32 (4 * edits t + 16)
def reciprocal (q b t : ℕ) : ℕ := 2^20 * (edits t)^2 * (b + 1) * (alphabetBits q + 1)
def kappa (q b t : ℕ) : ℚ := 1 / (reciprocal q b t : ℚ)
def metadata (q b t : ℕ) : ℕ := 100 * edits t * (b + 1) * (alphabetBits q + 1)
def hashExponent (q b t : ℕ) : ℕ := metadata q b t + 16 * reciprocal q b t + 8

def eta (q ℓ : ℕ) : ℕ := Nat.clog q ℓ
def windowLength (q ℓ : ℕ) : ℕ := 3 * eta q ℓ + 4
def gram (q b t ℓ : ℕ) : ℕ := gramLength q b (gramMultiplier t) ℓ
def componentCutoff (q b t ℓ : ℕ) : ℕ :=
  Nat.log 2 ℓ / (reciprocal q b t * Nat.clog 2 (gram q b t ℓ))
def witnessLimit (q b t ℓ : ℕ) : ℕ := 8 * edits t * componentCutoff q b t ℓ + 1
def omittedLetters (q b t ℓ : ℕ) : ℕ :=
  16 * (edits t)^2 * b * (componentCutoff q b t ℓ + 1)
def localOmitted (q b t ℓ : ℕ) : ℕ := 14 * edits t * b * componentCutoff q b t ℓ
def hashThreshold (q b t ℓ : ℕ) : ℕ := ℓ^(edits t - 1) * (gram q b t ℓ)^(hashExponent q b t)
def hashWidth (q b t ℓ : ℕ) : ℕ := Nat.clog 3 (hashThreshold q b t ℓ)
def hashCount (q b t ℓ : ℕ) : ℕ := 3^(hashWidth q b t ℓ)

def replayBound (q b L E : ℕ) : ℕ :=
  (E + 1) * (100 * (E + 1) * (L + 1))^(20 * E) * q^(4 * b * E)
def gamma (q b t ℓ : ℕ) : ℕ :=
  replayBound q b (gram q b t ℓ) (edits t * witnessLimit q b t ℓ)
def familyBound (q b L Λ : ℕ) : ℕ :=
  12 * (L + b + 1)^3 * q^(2*b) * (Λ + 1) * (3 * q * (L + b + 1))^Λ
def families (q b t ℓ : ℕ) : ℕ :=
  familyBound q b (gram q b t ℓ) (omittedLetters q b t ℓ)
def matchBound (q b t ℓ : ℕ) : ℕ :=
  (windowLength q ℓ + 3 * omittedLetters q b t ℓ).choose (windowLength q ℓ) ^ 2

def cycleLimit (t : ℕ) : ℕ := 10 * edits t
def coreLimit (t : ℕ) : ℕ := (cycleLimit t - 1) / (t - 1)
def exceptionalConstant (b t : ℕ) : ℕ :=
  let s := edits t
  2^(s - 1) * (2 * (b + 1))^s *
    ((s - 1) + 8 * s * (s + 1) * (1 + t*b) + s * (s*b + 1))

def cutoffExponent (q b t : ℕ) : ℕ :=
  max 16 (max (2 * gramMultiplier t + 4 * b * alphabetBits q + alphabetBits q + 10)
    (max (2^16 * (edits t)^2 * (b + 1) * (alphabetBits q + 1))
      (max (64 * reciprocal q b t) (max (64 * (hashExponent q b t + 1))
        (max (64 * exceptionalConstant b t * q^(b * edits t + 8)) (64 * coreLimit t * q^8))))))

def minLength (q b t : ℕ) : ℕ := q^(2^(cutoffExponent q b t))

/-- Length-dependent parameters, in the order `η, K, L, R, D, Λ, Λ₀, θ, P,
Γ, J̄, choose(K+3Λ,K)^2`. The other parameters depend only on `q, b, t`. -/
def values (q b t ℓ : ℕ) : List ℕ :=
  [eta q ℓ, windowLength q ℓ, gram q b t ℓ, componentCutoff q b t ℓ,
    witnessLimit q b t ℓ, omittedLetters q b t ℓ, localOmitted q b t ℓ,
    hashWidth q b t ℓ, hashCount q b t ℓ, gamma q b t ℓ,
    families q b t ℓ, matchBound q b t ℓ]

variable {q b t ℓ : ℕ}

theorem cutoff_lower (q b t : ℕ) :
    let Z := cutoffExponent q b t
    16 ≤ Z ∧ 2 * gramMultiplier t + 4 * b * alphabetBits q + alphabetBits q + 10 ≤ Z ∧
    2^16 * (edits t)^2 * (b + 1) * (alphabetBits q + 1) ≤ Z ∧ 64 * reciprocal q b t ≤ Z ∧
    64 * (hashExponent q b t + 1) ≤ Z ∧ 64 * exceptionalConstant b t * q^(b * edits t + 8) ≤ Z ∧
    64 * coreLimit t * q^8 ≤ Z := by
  simp [cutoffExponent, le_max_iff]

theorem multiplier_ge (t : ℕ) : 32 ≤ gramMultiplier t := le_max_left _ _

theorem hashCount_bounds (hℓ : 0 < ℓ) :
    hashThreshold q b t ℓ ≤ hashCount q b t ℓ ∧
      hashCount q b t ℓ < 3 * hashThreshold q b t ℓ := by
  unfold hashCount hashWidth
  have hL : 1 < gram q b t ℓ := by
    have h := multiplier_ge t
    unfold gram gramLength
    nlinarith
  have hA : 1 ≤ hashExponent q b t := by unfold hashExponent; omega
  have hpow : gram q b t ℓ ≤ (gram q b t ℓ)^(hashExponent q b t) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hL.le hA
  have hone : 1 < hashThreshold q b t ℓ := by
    have hpos : 0 < ℓ^(edits t - 1) := pow_pos hℓ _
    unfold hashThreshold
    nlinarith
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 3) hone
  have hc := Nat.clog_pos (by decide : 1 < 3) hone
  refine ⟨Nat.le_pow_clog (by decide) _, ?_⟩
  rw [show Nat.clog 3 (hashThreshold q b t ℓ) = (Nat.clog 3 (hashThreshold q b t ℓ) - 1) + 1
    by omega, pow_succ, Nat.mul_comm]
  exact Nat.mul_lt_mul_of_pos_left hp (by decide)

private theorem square_succ_le_two_pow (v : ℕ) (h : 6 ≤ v) : (v + 1)^2 ≤ 2^v := by
  induction v with
  | zero => omega
  | succ v ih =>
    by_cases hv : v = 5
    · subst v
      decide
    have hh := ih (by omega)
    rw [Nat.pow_succ 2 v]
    nlinarith

/-- Basic bounds used by the local geometry and by the enumeration estimates.
The inequality on `log₂ L` is stated as the equivalent integer comparison
`L ≤ η²`. -/
structure BasicBounds (q b t ℓ : ℕ) : Prop where
  eta_ge : 2^(cutoffExponent q b t) ≤ eta q ℓ
  eta_mul_log_le : cutoffExponent q b t * Nat.log 2 (eta q ℓ) ≤ eta q ℓ
  log_lower : eta q ℓ ≤ Nat.log 2 ℓ + 1
  log_upper : Nat.log 2 ℓ ≤ alphabetBits q * eta q ℓ
  gram_le_square : gram q b t ℓ ≤ (eta q ℓ)^2
  gram_log_upper : Nat.clog 2 (gram q b t ℓ) ≤ 3 * Nat.log 2 (eta q ℓ)
  gram_log_lower : 2^(4 * b * alphabetBits q) ≤ gram q b t ℓ
  gram_large : 400 ≤ gram q b t ℓ
  R_ge : 2 ≤ componentCutoff q b t ℓ
  E_le : edits t * witnessLimit q b t ℓ ≤ gram q b t ℓ
  omitted_le : 8 * omittedLetters q b t ℓ ≤ eta q ℓ
  record_length : edits t * b + 1 ≤ ℓ
  borrowed_unique : 2 * eta q ℓ + 2 ≤ windowLength q ℓ
  borrowed_gram : 3 * (windowLength q ℓ + b + 1) ≤ gram q b t ℓ
  borrowed_window : b < windowLength q ℓ
  borrowed_length : gram q b t ℓ ≤ ℓ
  length_ge_eta_square : (eta q ℓ)^2 ≤ ℓ
  local_gram : b + 2 ≤ gram q b t ℓ
  local_removed : 4 * (edits t * b * componentCutoff q b t ℓ) ≤ gram q b t ℓ
  local_omit : 2 * localOmitted q b t ℓ ≤ gram q b t ℓ
  local_flank : localOmitted q b t ℓ + b ≤ omittedLetters q b t ℓ
  local_gap : localOmitted q b t ℓ + windowLength q ℓ + b < gram q b t ℓ - 1
  overlap_window : windowLength q ℓ + 2 * omittedLetters q b t ℓ ≤ gram q b t ℓ - 1
  overlap_ceil : windowLength q ℓ + 2 * omittedLetters q b t ℓ ≤
    gram q b t ℓ - (gram q b t ℓ + b - 2 + 1) / 2

set_option maxHeartbeats 700000 in
theorem basicBounds (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) (hstart : minLength q b t ≤ ℓ) :
    BasicBounds q b t ℓ := by
  let s := edits t
  let w := alphabetBits q
  let C := gramMultiplier t
  let B := reciprocal q b t
  let Z := cutoffExponent q b t
  let y := eta q ℓ
  let L := gram q b t ℓ
  let R := componentCutoff q b t ℓ
  let Λ := omittedLetters q b t ℓ
  let Λ₀ := localOmitted q b t ℓ
  let K := windowLength q ℓ
  let v := Nat.log 2 y
  let c := Nat.clog 2 L
  let N := Nat.log 2 ℓ
  have hs : 4 ≤ s := by unfold s edits; omega
  have hw : 1 ≤ w := Nat.clog_pos (by decide) hq
  have hC : 32 ≤ C := multiplier_ge t
  have hB : B = 2^20 * s^2 * (b + 1) * (w + 1) := rfl
  have hz : 16 ≤ Z ∧ 2*C + 4*b*w + w + 10 ≤ Z ∧
      2^16 * s^2 * (b+1) * (w+1) ≤ Z ∧ 64 * B ≤ Z :=
    let ⟨h1, h2, h3, h4, _⟩ := cutoff_lower q b t
    ⟨h1, h2, h3, h4⟩
  obtain ⟨hZ, hZC, hZs, hZB⟩ := hz
  have hy : 2^Z ≤ y := by
    change q^(2^Z) ≤ ℓ at hstart
    change 2^Z ≤ Nat.clog q ℓ
    simpa only [Nat.clog_pow _ _ (by omega : 1 < q)] using Nat.clog_mono_right q hstart
  have hv : Z ≤ v := Nat.le_log_of_pow_le (by decide) hy
  have hzy : Z ≤ y := Z.lt_two_pow_self.le.trans hy
  have hyv : Z * v ≤ y := by
    have hp := Nat.pow_log_le_self 2 (x := y) (by omega)
    exact (Nat.mul_le_mul_right v hv).trans
      ((show v * v ≤ (v + 1)^2 by nlinarith).trans
        ((square_succ_le_two_pow v (by omega)).trans hp))
  have hymin : 16 ≤ y := by omega
  have hyb : b + 3 ≤ y := by nlinarith
  have hys : 256 * s^2 * b ≤ y := by
    have hh : 256 * s^2 * b ≤ 2^16 * s^2 * (b + 1) * (w + 1) :=
      (Nat.mul_le_mul (Nat.mul_le_mul_right (s^2) (by decide : 256 ≤ 2^16))
        (Nat.le_succ b)).trans (Nat.le_mul_of_pos_right _ (by omega))
    exact hh.trans (hZs.trans hzy)
  have hs2 : s ≤ s^2 := by nlinarith only [hs]
  have hs_y : s * b + 1 ≤ y := by
    have hh := Nat.mul_le_mul_right b hs2
    have hp : 1 ≤ s^2*b := Nat.mul_pos (by positivity) hb
    nlinarith only [hh, hp, hys]
  have hL : L = C * (y + b + 3) := rfl
  have hLy : 32 * y ≤ L := by nlinarith
  have hLa : 400 ≤ L := by omega
  have hLs : L ≤ y^2 := by
    calc
      L ≤ C * (2*y) := hL ▸ Nat.mul_le_mul_left C (by omega)
      _ = (2*C) * y := by ring
      _ ≤ y^2 := by rw [pow_two]; exact Nat.mul_le_mul_right y (by omega)
  have hc : c ≤ 3*v := by
    apply (Nat.clog_le_iff_le_pow (by decide)).2
    have hy2 := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) y).le
    calc
      L ≤ y^2 := hLs
      _ ≤ (2^(v+1))^2 := Nat.pow_le_pow_left hy2 _
      _ = 2^((v+1)*2) := by rw [pow_mul]
      _ ≤ 2^(3*v) := Nat.pow_le_pow_right (by decide) (by omega)
  have hcl : 1 ≤ c := Nat.clog_pos (by decide) (by omega)
  have hCL : 2^(4*b*w) ≤ L :=
    (Nat.pow_le_pow_right (by decide) (by omega : 4*b*w ≤ Z)).trans (hy.trans (by omega))
  have hNhi : N ≤ w*y := by
    have h1 : ℓ ≤ q^y := Nat.le_pow_clog (by omega : 1 < q) ℓ
    have h2 : q ≤ 2^w := Nat.le_pow_clog (by decide : 1 < 2) q
    have h3 : ℓ ≤ 2^(w*y) := h1.trans (by rw [pow_mul]; exact Nat.pow_le_pow_left h2 _)
    simpa only [Nat.log_pow (by decide : 1 < 2)] using Nat.log_mono_right (b := 2) h3
  have hNlo : y ≤ N + 1 := by
    apply Nat.clog_le_of_le_pow
    exact (Nat.lt_pow_succ_log_self (by decide : 1 < 2) ℓ).le.trans (Nat.pow_le_pow_left hq _)
  have hR : R = N / (B*c) := rfl
  have hRmul : R * (B*c) ≤ N := by rw [hR]; exact Nat.div_mul_le_self _ _
  have hRlow : 2 ≤ R := by
    rw [hR]
    have hBp : 0 < B := by rw [hB]; positivity
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos hBp hcl)).2
    have hsmall : 8 * B * v ≤ y := (Nat.mul_le_mul_right v (by omega : 8 * B ≤ Z)).trans hyv
    have hstep : 2 * (B*c) ≤ 6 * B * v := by
      calc
        _ = (2*B)*c := by ring
        _ ≤ (2*B)*(3*v) := Nat.mul_le_mul_left _ hc
        _ = _ := by ring
    have hgap : 6 * B * v < 8 * B * v := by
      apply Nat.mul_lt_mul_of_pos_right _ (by omega)
      omega
    omega
  have hcoeff : (256*s^2*b)*w ≤ B := by
    rw [hB]
    calc
      _ ≤ (2^20*s^2*(b+1))*w := Nat.mul_le_mul_right w (Nat.mul_le_mul
        (Nat.mul_le_mul_right (s^2) (by decide : 256 ≤ 2^20)) (Nat.le_succ b))
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hRsize : 256*s^2*b*R ≤ y := by
    apply Nat.le_of_mul_le_mul_right _ (by omega : 0 < w)
    calc
      _ = R * ((256*s^2*b)*w) := by ring
      _ ≤ R * B := Nat.mul_le_mul_left _ hcoeff
      _ ≤ R * (B*c) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hcl)
      _ ≤ N := hRmul
      _ ≤ _ := by simpa only [Nat.mul_comm] using hNhi
  have hΛ : Λ = 16*s^2*b*(R+1) := rfl
  have hΛb : 8 * Λ ≤ y := by nlinarith
  have hΛ₀ : Λ₀ = 14*s*b*R := rfl
  have hΛlocal : Λ₀ + b ≤ Λ := by
    have hss : s ≤ s^2 := by nlinarith
    calc
      Λ₀ + b = 14*(s*b*R) + b := by rw [hΛ₀]; ring
      _ ≤ 16*s^2*b*(R+1) := by
        have ha := Nat.mul_le_mul_right (b*R) hss
        have hb' : b ≤ s^2*b := Nat.le_mul_of_pos_left _ (by positivity)
        nlinarith only [ha, hb']
      _ = Λ := hΛ.symm
  have hE : s * witnessLimit q b t ℓ ≤ L := by
    change s*(8*s*R+1) ≤ L
    nlinarith [Nat.mul_le_mul_left (256*s^2*R) hb]
  have hℓexp : 2^(y-1) < ℓ := by
    have hq1 : 1 < q := by omega
    have hℓ1 : 1 < ℓ := by
      have hh : q ≤ q^(2^Z) := by
        simpa only [pow_one] using Nat.pow_le_pow_right hq1.le (by have := Z.lt_two_pow_self; omega : 1 ≤ 2^Z)
      exact (lt_of_lt_of_le hq1 hh).trans_le hstart
    exact (Nat.pow_le_pow_left hq _).trans_lt (Nat.pow_pred_clog_lt_self hq1 hℓ1)
  have hℓy : y^2 ≤ ℓ := by
    have hp := square_succ_le_two_pow (y - 1) (by omega)
    rw [show y - 1 + 1 = y by omega] at hp
    exact hp.trans hℓexp.le
  have hK : K = 3*y+4 := rfl
  have hfl : s*b*R ≤ Λ₀ := by rw [hΛ₀]; nlinarith
  refine ⟨hy, hyv, hNlo, hNhi, hLs, hc, hCL, hLa, hRlow, hE, hΛb, ?_, ?_,
    ?_, ?_, hLs.trans hℓy, hℓy, ?_, ?_, ?_, hΛlocal, ?_, ?_, ?_⟩
  · change s*b+1 ≤ ℓ
    exact hs_y.trans ((by nlinarith only [hymin] : y ≤ y^2).trans hℓy)
  · change 2*y+2 ≤ K
    omega
  · change 3*(K+b+1) ≤ L
    omega
  · change b < K
    omega
  · change b+2 ≤ L
    omega
  · change 4*(s*b*R) ≤ L
    omega
  · change 2*Λ₀ ≤ L
    omega
  · change Λ₀ + K + b < L - 1
    omega
  · change K + 2*Λ ≤ L - 1
    omega
  · change K + 2*Λ ≤ L - (L+b-2+1)/2
    omega

#print axioms cutoff_lower
#print axioms hashCount_bounds
#print axioms basicBounds

end DeletionCode.Explicit.UniformParameters
