import DeletionCode.Explicit.UniformParameters
import Mathlib.Data.Nat.Choose.Bounds

/-! The three enumeration bounds in `d:parameter-bounds`. We use the
equivalent integer comparisons obtained by raising both sides to eight. -/
namespace DeletionCode.Explicit.UniformParameters

theorem replay_le {q b L E : ℕ} (hL : 400 ≤ L) (hE : E ≤ L)
    (hq : q^(4*b) ≤ L) : replayBound q b L E ≤ L^(61*E+2) := by
  have hQ : 100*(E+1)*(L+1) ≤ L^3 := by
    calc
      _ ≤ 100*(2*L)*(2*L) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 400*L^2 := by ring
      _ ≤ L^3 := by rw [show L^3 = L*L^2 by ring]; exact Nat.mul_le_mul_right _ hL
  have hlast : q^(4*b*E) ≤ L^E := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hq _
  have hhead : E + 1 ≤ L^2 := by nlinarith only [hL, hE]
  unfold replayBound
  calc
    _ ≤ L^2 * (L^3)^(20*E) * L^E :=
      Nat.mul_le_mul (Nat.mul_le_mul hhead (Nat.pow_le_pow_left hQ _)) hlast
    _ = L^(61*E+2) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega

private theorem families_le {q b L Λ : ℕ} (hq : 2 ≤ q) (hb : 1 ≤ b)
    (hL : 400 ≤ L) (hbL : b+1 ≤ L) (hΛ : Λ+1 ≤ L) (h4 : q^(4*b) ≤ L) :
    familyBound q b L Λ ≤ L^(2*Λ+6) := by
  have hq2 : q^(2*b) ≤ L :=
    (Nat.pow_le_pow_right (by omega : 1 ≤ q) (by omega)).trans h4
  have hq4 : q^4 ≤ L :=
    (Nat.pow_le_pow_right (by omega : 1 ≤ q) (by omega)).trans h4
  have hqL : 6*q ≤ L := by
    have hq3 : 6 ≤ q^3 := (by decide : 6 ≤ 2^3).trans (Nat.pow_le_pow_left hq _)
    exact (Nat.mul_le_mul_right q hq3).trans hq4
  have hbase : 3*q*(L+b+1) ≤ L^2 := by
    calc
      _ ≤ 3*q*(2*L) := Nat.mul_le_mul_left _ (by omega)
      _ = (6*q)*L := by ring
      _ ≤ L^2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ hqL
  have hcoef : 12*(L+b+1)^3*q^(2*b)*(Λ+1) ≤ L^6 := by
    calc
      _ ≤ 12*(2*L)^3*L*L :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
          hq2) hΛ
      _ = 96*L^5 := by ring
      _ ≤ L^6 := by rw [show L^6 = L*L^5 by ring]; exact Nat.mul_le_mul_right _ (by omega)
  unfold familyBound
  calc
    _ ≤ L^6 * (L^2)^Λ := Nat.mul_le_mul hcoef (Nat.pow_le_pow_left hbase _)
    _ = L^(2*Λ+6) := by rw [← pow_mul, ← pow_add, Nat.add_comm]

/-- Combine the cutoff's budget for the terms proportional to `R` with
the separate budget for the constant overheads. -/
private theorem exponent_budget {Z B N w η R c v p a : ℕ}
    (hw : 0 < w) (hη : 2 ≤ η) (hN : η ≤ N+1) (hW : N ≤ w*η)
    (hR : R*(B*c) ≤ N) (hv : Z*v ≤ η) (hc : c ≤ 3*v)
    (hp : 4*p*w ≤ B) (ha : 12*a ≤ Z) :
    (p*R+a)*c ≤ N := by
  have h₁ : 4*(p*R*c) ≤ η := by
    refine Nat.le_of_mul_le_mul_right ?_ hw
    calc
      _ = (R*c)*(4*p*w) := by ring
      _ ≤ (R*c)*B := Nat.mul_le_mul_left _ hp
      _ = R*(B*c) := by ring
      _ ≤ N := hR
      _ ≤ η*w := hW.trans (by rw [Nat.mul_comm])
  have h₂ : 4*(a*c) ≤ η := by
    calc
      _ = (4*a)*c := by ring
      _ ≤ (4*a)*(3*v) := Nat.mul_le_mul_left _ hc
      _ = (12*a)*v := by ring
      _ ≤ Z*v := Nat.mul_le_mul_right _ ha
      _ ≤ η := hv
  nlinarith only [h₁, h₂, hη, hN]

private theorem pow_le_from_budget {L ℓ d : ℕ} (hℓ : ℓ ≠ 0)
    (hd : d * Nat.clog 2 L ≤ Nat.log 2 ℓ) : L^d ≤ ℓ := by
  calc
    _ ≤ (2^Nat.clog 2 L)^d := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
    _ = 2^(d * Nat.clog 2 L) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ 2^Nat.log 2 ℓ := Nat.pow_le_pow_right (by decide) hd
    _ ≤ ℓ := Nat.pow_log_le_self _ hℓ

variable {q b t ℓ : ℕ}

set_option maxHeartbeats 1200000 in
theorem enumerationBounds (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : minLength q b t ≤ ℓ) :
    gamma q b t ℓ ^ 8 ≤ ℓ ∧ families q b t ℓ ^ 8 ≤ ℓ ∧ matchBound q b t ℓ ^ 8 ≤ ℓ := by
  let s := edits t
  let w := alphabetBits q
  let Z := cutoffExponent q b t
  let B := reciprocal q b t
  let L := gram q b t ℓ
  let η := eta q ℓ
  let R := componentCutoff q b t ℓ
  let Λ := omittedLetters q b t ℓ
  let E := s * witnessLimit q b t ℓ
  let K := windowLength q ℓ
  let c := Nat.clog 2 L
  let v := Nat.log 2 η
  let N := Nat.log 2 ℓ
  have basic := basicBounds hq hb ht hstart
  have hn : ℓ ≠ 0 := (Nat.zero_lt_of_lt basic.record_length).ne'
  have hη : 2 ≤ η := (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    ((by decide : 1 ≤ 16).trans (cutoff_lower q b t).1)).trans basic.eta_ge
  have hw : 0 < w := Nat.clog_pos (by decide) hq
  have hs : 4 ≤ s := by unfold s edits; omega
  have hZ : 2^16 * s^2 * (b+1) * (w+1) ≤ Z := (cutoff_lower q b t).2.2.1
  have hL : 400 ≤ L := basic.gram_large
  have hLy : 32*η ≤ L := by
    have he : L = gramMultiplier t * (η+b+3) := rfl
    exact he ▸ Nat.mul_le_mul (multiplier_ge t) (by omega)
  have hLBig : b + 1 ≤ L := by
    have he : L = gramMultiplier t * (η+b+3) := rfl
    exact (by omega : b+1 ≤ η+b+3).trans
      (he ▸ Nat.le_mul_of_pos_left _ ((by decide : 0 < 32).trans_le (multiplier_ge t)))
  have hΛ : Λ = 16*s^2*b*(R+1) := rfl
  have hK : K = 3*η+4 := rfl
  have hE : E = s*(8*s*R+1) := rfl
  have hΛ₁ : 8*Λ ≤ η := basic.omitted_le
  have hq4 : q^(4*b) ≤ L := by
    have h := Nat.le_pow_clog (by decide : 1 < 2) q
    calc
      _ ≤ (2^w)^(4*b) := Nat.pow_le_pow_left h _
      _ = 2^(4*b*w) := by rw [← pow_mul, Nat.mul_comm w]
      _ ≤ L := basic.gram_log_lower
  have coeff (x : ℕ) (hx : x ≤ 2^20) :
      x * s^2 * (b+1) * w ≤ B := by
    change _ ≤ 2^20 * s^2 * (b+1) * (w+1)
    gcongr
    omega
  have overhead (x : ℕ) (hx : x ≤ 2^16) : x * s^2 * (b+1) ≤ Z := by
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hx)).trans
      ((Nat.le_mul_of_pos_right _ (by omega : 0 < w + 1)).trans hZ)
  have trade {p a : ℕ} (hp : 4*p*w ≤ B) (ha : 12*a ≤ Z) :
      (p*R+a)*c ≤ N :=
    exponent_budget hw hη basic.log_lower basic.log_upper (Nat.div_mul_le_self _ _)
      basic.eta_mul_log_le basic.gram_log_upper hp ha
  have hgamma : 8*(61*E+2)*c ≤ N := by
    have hp : 4*(3904*s^2)*w ≤ B := by
      calc
        _ ≤ 15616*s^2*(b+1)*w := by
          rw [show 4*(3904*s^2)*w = 15616*s^2*w by ring]
          exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
        _ ≤ _ := coeff _ (by decide)
    have ha : 12*(488*s+16) ≤ Z := by
      calc
        _ ≤ 6000*s^2 := by nlinarith only [hs]
        _ ≤ 6000*s^2*(b+1) := Nat.le_mul_of_pos_right _ (by omega)
        _ ≤ _ := overhead _ (by decide)
    have hh : 8 * (61 * E + 2) = (3904*s^2)*R + (488*s+16) := by rw [hE]; ring
    rw [hh]
    exact trade hp ha
  have hj : 8*(2*Λ+6)*c ≤ N := by
    have hp : 4*(256*s^2*b)*w ≤ B := by
      calc
        _ ≤ 1024*s^2*(b+1)*w := by
          rw [show 4*(256*s^2*b)*w = 1024*s^2*b*w by ring]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
        _ ≤ _ := coeff _ (by decide)
    have ha : 12*(256*s^2*b+48) ≤ Z := by
      exact (by nlinarith only [hs, Nat.zero_le (s^2*b)] :
        12*(256*s^2*b+48) ≤ 4096*s^2*(b+1)).trans (overhead _ (by decide))
    rw [show 8*(2*Λ+6) = (256*s^2*b)*R+(256*s^2*b+48) by rw [hΛ]; ring]
    exact trade hp ha
  have hm : 48*Λ*c ≤ N := by
    have hp : 4*(768*s^2*b)*w ≤ B := by
      calc
        _ ≤ 3072*s^2*(b+1)*w := by
          rw [show 4*(768*s^2*b)*w = 3072*s^2*b*w by ring]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
        _ ≤ _ := coeff _ (by decide)
    have ha : 12*(768*s^2*b) ≤ Z := by
      exact (by rw [show 12*(768*s^2*b) = 9216*s^2*b by ring]
                exact Nat.mul_le_mul_left _ (Nat.le_succ b) :
        12*(768*s^2*b) ≤ 9216*s^2*(b+1)).trans (overhead _ (by decide))
    rw [show 48*Λ = (768*s^2*b)*R+(768*s^2*b) by rw [hΛ]; ring]
    exact trade hp ha
  refine ⟨?_, ?_, ?_⟩
  · change replayBound q b L E ^ 8 ≤ ℓ
    refine (Nat.pow_le_pow_left (replay_le hL basic.E_le hq4) 8).trans ?_
    rw [← pow_mul, Nat.mul_comm (61*E+2)]
    exact pow_le_from_budget hn hgamma
  · change familyBound q b L Λ ^ 8 ≤ ℓ
    refine (Nat.pow_le_pow_left (families_le hq hb hL hLBig (by omega) hq4) 8).trans ?_
    rw [← pow_mul, Nat.mul_comm (2*Λ+6)]
    exact pow_le_from_budget hn hj
  · change ((K+3*Λ).choose K ^ 2) ^ 8 ≤ ℓ
    have hchoose := Nat.choose_symm (n := K+3*Λ) (k := K) (by omega)
    have hsym : (K + 3*Λ).choose K = (K + 3*Λ).choose (3*Λ) := by
      simpa only [Nat.add_sub_cancel_left] using hchoose.symm
    have hM : (K + 3*Λ).choose K ≤ L^(3*Λ) := hsym ▸
      (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
    calc
      _ ≤ ((L^(3*Λ))^2)^8 := Nat.pow_le_pow_left (Nat.pow_le_pow_left hM 2) 8
      _ = L^(48*Λ) := by rw [← pow_mul, ← pow_mul]; congr 1; omega
      _ ≤ ℓ := pow_le_from_budget hn hm

#print axioms enumerationBounds

end DeletionCode.Explicit.UniformParameters
