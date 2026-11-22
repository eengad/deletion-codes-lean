import DeletionCode.Explicit.ParameterEnumerationBounds

/-! Numerical bounds on the widths of the fields in `d:small-saving`,
`d:peel-saving`, and `d:explicit-peel`. -/
namespace DeletionCode.Explicit.UniformParameters

variable {q b t ℓ : ℕ}

private theorem power_clog_le {q x : ℕ} (hq : 1 < q) (hx : 1 < x) :
    q^Nat.clog q x ≤ q*x := by
  have hp := Nat.pow_pred_clog_lt_self hq hx
  have hc := Nat.clog_pos hq hx
  have he : q^Nat.clog q x = q * q^(Nat.clog q x - 1) := by
    conv_lhs => rw [show Nat.clog q x = Nat.clog q x - 1 + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  rw [he]
  exact Nat.mul_le_mul_left _ hp.le

private theorem gram_eta {q b t ℓ : ℕ} :
    eta q ℓ ≤ gram q b t ℓ := by
  change eta q ℓ ≤ gramMultiplier t * (eta q ℓ + b + 3)
  exact (by omega : eta q ℓ ≤ eta q ℓ + b + 3).trans
    (Nat.le_mul_of_pos_left _ ((by decide : 0 < 32).trans_le (multiplier_ge t)))

private theorem cutoff_le_eta (basic : BasicBounds q b t ℓ) :
    cutoffExponent q b t ≤ eta q ℓ :=
  (cutoffExponent q b t).lt_two_pow_self.le.trans basic.eta_ge

private theorem pow_gram_of_q (basic : BasicBounds q b t ℓ) :
    q^(4*b) ≤ gram q b t ℓ := by
  calc
    _ ≤ (2^alphabetBits q)^(4*b) := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
    _ = 2^(4*b*alphabetBits q) := by rw [← pow_mul, Nat.mul_comm (alphabetBits q)]
    _ ≤ _ := basic.gram_log_lower

private theorem le_of_eighth {x n : ℕ} (h : x^8 ≤ n) : x ≤ n := by
  by_cases hx : x = 0
  · simp [hx]
  · have he : x ≤ x^8 := by
      simpa only [pow_one] using
        Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr hx) (by decide : 1 ≤ 8)
    exact he.trans h

/-- The replay index and one anchor each fit into `η` symbols.
The remaining description fields are budgeted separately. -/
theorem small_description_bound (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : minLength q b t ≤ ℓ) :
    Nat.clog q (gamma q b t ℓ) + eta q ℓ + (3*Nat.clog q (gram q b t ℓ) + 5) ≤
      2*eta q ℓ + 3*Nat.clog q (gram q b t ℓ) + 5 := by
  have h := Nat.clog_mono_right q (le_of_eighth (enumerationBounds hq hb ht hstart).1)
  change Nat.clog q (gamma q b t ℓ) ≤ eta q ℓ at h
  omega

/-- The one-anchor description may use the manuscript's upper bound,
rounded upwards to `2η + 3⌈log_q L⌉ + 5`. The width of the family
index is counted by its exact ceiling logarithm. -/
theorem smallFamily_saves_eight (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : minLength q b t ≤ ℓ) {J M active description : ℕ}
    (hJ : J ≤ families q b t ℓ) (hM : M < 12*J*(hashCount q b t ℓ)^2)
    (ha : gram q b t ℓ - omittedLetters q b t ℓ ≤ active) (ha' : active ≤ ℓ)
    (hd : description ≤ 2*eta q ℓ + 3*Nat.clog q (gram q b t ℓ) + 5) :
    (ℓ-active) + Nat.clog q M + description + 8 ≤ ℓ := by
  let η := eta q ℓ
  let L := gram q b t ℓ
  let Λ := omittedLetters q b t ℓ
  let c := Nat.clog q L
  let A := hashExponent q b t
  let s := edits t
  let v := Nat.log 2 η
  let Z := cutoffExponent q b t
  let cost := (s-1)*η + A*c
  have basic := basicBounds hq hb ht hstart
  have hℓ : 0 < ℓ := Nat.zero_lt_of_lt basic.record_length
  have hq' : 1 < q := hq
  have hη : ℓ ≤ q^η := Nat.le_pow_clog hq' _
  have hLc : L ≤ q^c := Nat.le_pow_clog hq' _
  have hPc : hashCount q b t ℓ ≤ 3 * q^cost := by
    apply (hashCount_bounds hℓ).2.le.trans
    apply Nat.mul_le_mul_left
    unfold hashThreshold
    calc
      _ ≤ (q^η)^(s-1) * (q^c)^A :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hη _) (Nat.pow_le_pow_left hLc _)
      _ = q^cost := by rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; unfold cost; ring
  have hJη : J ≤ q^η :=
    hJ.trans ((le_of_eighth (enumerationBounds hq hb ht hstart).2.1).trans hη)
  have hI : Nat.clog q M ≤ η + 2*cost + 7 := by
    apply (Nat.clog_le_iff_le_pow hq').mpr
    calc
      M ≤ 12*q^η*(3*q^cost)^2 := hM.le.trans (Nat.mul_le_mul
        (Nat.mul_le_mul_left _ hJη) (Nat.pow_le_pow_left hPc _))
      _ = 108*q^(η+2*cost) := by rw [mul_pow, ← pow_mul, pow_add, Nat.mul_comm 2]; ring
      _ ≤ q^7 * q^(η+2*cost) :=
        Nat.mul_le_mul_right _ ((by decide : 108 ≤ 2^7).trans (Nat.pow_le_pow_left hq _))
      _ = _ := by rw [←pow_add]; congr 1; omega
  have hlog : c ≤ 3*v :=
    (Nat.clog_anti_left (by decide) hq).trans basic.gram_log_upper
  have hAc : (2*A+3)*c ≤ η := by
    have hZ : 64*(A+1) ≤ Z := (cutoff_lower q b t).2.2.2.2.1
    calc
      _ ≤ (2*A+3)*(3*v) := Nat.mul_le_mul_left _ hlog
      _ = (6*A+9)*v := by ring
      _ ≤ Z*v := Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := basic.eta_mul_log_le
  have hL : (4*s+16)*η ≤ L := by
    change _ ≤ gramMultiplier t * (η+b+3)
    exact Nat.mul_le_mul (le_max_right _ _) (by omega)
  have hΛ : 8*Λ ≤ η := basic.omitted_le
  have hη16 : 16 ≤ η := (cutoff_lower q b t).1.trans (cutoff_le_eta basic)
  have hs : 4 ≤ s := by unfold s edits; omega
  have hAct : L ≤ active+Λ := Nat.sub_le_iff_le_add.mp ha
  change description ≤ 2*η+3*c+5 at hd
  have hcost' : cost ≤ s*η+A*c := Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _
  have hsum : Nat.clog q M + description + 8 ≤ active := by
    nlinarith only [hI, hd, hcost', hAc, hL, hΛ, hη16, hs, hAct]
  omega

set_option maxHeartbeats 1400000 in
/-- Given the joint range of the literal letters and the pivot digits,
the exact integer field widths of the peeled representation save eight
symbols. The tree case takes the first-event inequality `R < d`. -/
theorem peeled_saves_eight (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : minLength q b t ≤ ℓ) {d c₀ g data : ℕ}
    (hd : 0 < d) (hD : d ≤ witnessLimit q b t ℓ)
    (hc : c₀ + g = (edits t - 1)*d + 1)
    (hTree : g = 0 → componentCutoff q b t ℓ < d)
    (hp : 0 < data) (hdata : data * (hashCount q b t ℓ)^d ≤ q^ℓ * 3^d) :
    Nat.clog q (witnessLimit q b t ℓ + 1) +
      Nat.clog q (replayBound q b (gram q b t ℓ) (edits t*d)) +
      c₀ * eta q ℓ + Nat.clog q data + 8 ≤ ℓ := by
  let s := edits t
  let L := gram q b t ℓ
  let D := witnessLimit q b t ℓ
  let η := eta q ℓ
  let w := alphabetBits q
  let A := hashExponent q b t
  let M := metadata q b t
  let B := reciprocal q b t
  let u := Nat.clog q L
  let v := Nat.log 2 η
  let a := Nat.clog 2 L
  let N := Nat.log 2 ℓ
  let R := componentCutoff q b t ℓ
  let Gd := replayBound q b L (s*d)
  let header := Nat.clog q (D+1) + Nat.clog q Gd + c₀*η
  let base := (s-1)*(η-1)*d
  let extra := (A-M)*d
  let tree := if g = 0 then η else 0
  change c₀ + g = (s-1)*d + 1 at hc
  have hq' : 1 < q := hq
  have hs : 4 ≤ s := by unfold s edits; omega
  have basic := basicBounds hq hb ht hstart
  have hL : 400 ≤ L := basic.gram_large
  have hℓ : 1 < ℓ := by
    have h : s*b+1 ≤ ℓ := basic.record_length
    nlinarith only [h, hb, hs]
  have hη : 16 ≤ η := (cutoff_lower q b t).1.trans (cutoff_le_eta basic)
  have hD₁ : D + 1 ≤ L := by
    have hDpos : 0 < D := hd.trans_le hD
    have hE : s*D ≤ L := basic.E_le
    nlinarith only [hDpos, hE, hs]
  have hqL : q ≤ L := by
    have h := pow_gram_of_q basic
    have hq4 : q ≤ q^(4*b) := by
      simpa only [pow_one] using Nat.pow_le_pow_right hq'.le (show 1 ≤ 4*b by omega)
    exact hq4.trans h
  have hGu : Nat.clog q Gd ≤ (61*s*d+2)*u := by
    apply (Nat.clog_le_iff_le_pow hq').mpr
    have hE : s*d ≤ L := (Nat.mul_le_mul_left s hD).trans basic.E_le
    have hG := replay_le hL hE (pow_gram_of_q basic)
    have hu : L ≤ q^u := Nat.le_pow_clog hq' _
    calc
      Gd ≤ L^(61*s*d+2) := by simpa only [Nat.mul_assoc] using hG
      _ ≤ (q^u)^(61*s*d+2) := Nat.pow_le_pow_left hu _
      _ = _ := by rw [← pow_mul, Nat.mul_comm u]
  have hDwidth : Nat.clog q (D+1) ≤ u := Nat.clog_mono_right _ hD₁
  have hAnchor : c₀*η ≤ base+(s-1)*d+tree := by
    have hbase : (s-1)*d*η = base+(s-1)*d := by
      unfold base
      have he : η - 1 + 1 = η := by omega
      conv_lhs => rw [← he]
      ring
    rcases Nat.eq_zero_or_pos g with hg | hg
    · simp only [tree, hg, ite_true]
      have hc' : c₀ = (s-1)*d + 1 := by omega
      rw [hc', Nat.add_mul, one_mul, hbase]
    · simp only [tree, hg.ne', ite_false, add_zero]
      rw [← hbase]
      exact Nat.mul_le_mul_right _ (by omega)
  have hheader : header+8 ≤ (61*s*d+3)*u + (base+tree) + ((s-1)*d+8) := by
    unfold header
    nlinarith only [hDwidth, hGu, hAnchor]
  have huPow : q^u ≤ L^2 :=
    (power_clog_le hq' (by omega : 1 < L)).trans (by
      rw [pow_two]; exact Nat.mul_le_mul_right _ hqL)
  have hM : 400*s ≤ M := by
    unfold M metadata
    have hW : 1 ≤ w := Nat.clog_pos (by decide) hq
    have h1 : 100*s*2*2 ≤ 100*s*(b+1)*(w+1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    convert h1 using 1 <;> ring
  have hmeta : (q^u)^(61*s*d+3) * q^((s-1)*d+8) * 3^d ≤ L^(M*d) := by
    calc
      _ ≤ (L^2)^(61*s*d+3) * L^((s-1)*d+8) * L^d :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left huPow _) (Nat.pow_le_pow_left hqL _))
          (Nat.pow_le_pow_left (by omega) _)
      _ ≤ L^(M*d) := by
        rw [←pow_mul, ←pow_add, ←pow_add]
        apply Nat.pow_le_pow_right (by omega)
        have hsmall : 14 ≤ 14*d := Nat.le_mul_of_pos_right 14 hd
        have hlarge := Nat.mul_le_mul_right d hM
        have hsd : (s-1)*d ≤ s*d := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        have hsd' : d ≤ s*d := Nat.le_mul_of_pos_left _ (by omega)
        nlinarith only [hsmall, hlarge, hsd, hsd']
  have htree : q^tree ≤ L^extra := by
    by_cases hg : g = 0
    · simp only [tree, hg, ite_true]
      have hR : R = N/(B*a) := rfl
      have hB : 0 < B := by unfold B reciprocal; positivity
      have ha : 0 < a := Nat.clog_pos (by decide) (by omega)
      have hnext : N < d*(B*a) := by
        have ht := hTree hg
        change R < d at ht
        rw [hR] at ht
        exact (Nat.div_lt_iff_lt_mul (Nat.mul_pos hB ha)).mp ht
      have hupper : d*(B*a) ≤ 3*B*d*v := by
        have hh : a ≤ 3*v := basic.gram_log_upper
        calc
          _ = (d*B)*a := by ring
          _ ≤ (d*B)*(3*v) := Nat.mul_le_mul_left _ hh
          _ = _ := by ring
      have hwη : w ≤ η := by
        have hz := (cutoff_lower q b t).2.1
        exact (by omega : w ≤ _).trans (hz.trans (cutoff_le_eta basic))
      have hNlo : η ≤ N+1 := basic.log_lower
      have hA : 16*B ≤ A-M := by unfold A hashExponent B M; omega
      have hexp : w+(N+1) ≤ v*extra := by
        calc
          _ ≤ 2*(N+1) := by omega
          _ ≤ 6*B*d*v := by nlinarith only [hupper, hnext]
          _ ≤ 16*B*d*v := by gcongr <;> omega
          _ ≤ v*extra := by
            unfold extra
            rw [Nat.mul_comm v]
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hA)
      calc
        q^η ≤ q*ℓ := power_clog_le hq' hℓ
        _ ≤ 2^w * 2^(N+1) := Nat.mul_le_mul (Nat.le_pow_clog (by decide) _)
          (Nat.lt_pow_succ_log_self (by decide : 1 < 2) ℓ).le
        _ ≤ (2^v)^extra := by rw [←pow_add, ←pow_mul]; exact Nat.pow_le_pow_right (by decide) hexp
        _ ≤ L^extra :=
          Nat.pow_le_pow_left ((Nat.pow_log_le_self _ (show η ≠ 0 by omega)).trans gram_eta) _
    · simp only [tree, hg, ite_false, pow_zero]
      exact pow_pos (by omega : 0 < L) _
  have hP : q^base * L^(A*d) ≤ (hashCount q b t ℓ)^d := by
    have hmin : q^(η-1) ≤ ℓ := (Nat.pow_pred_clog_lt_self hq' hℓ).le
    have hP₀ := (hashCount_bounds (q := q) (b := b) (t := t) (by omega : 0 < ℓ)).1
    calc
      _ = (((q^(η-1))^(s-1))*L^A)^d := by
        rw [mul_pow, ←pow_mul, ←pow_mul, ←pow_mul]
        congr 2
        unfold base
        ring
      _ ≤ _ := Nat.pow_le_pow_left
        ((Nat.mul_le_mul_right (L^A) (Nat.pow_le_pow_left hmin _)).trans hP₀) _
  have hExp : M*d+extra = A*d := by
    have hA : M ≤ A := by unfold A M hashExponent; omega
    unfold extra
    rw [← Nat.add_mul, Nat.add_sub_of_le hA]
  have hpack : q^(header+8)*3^d ≤ (hashCount q b t ℓ)^d := by
    calc
      _ ≤ q^((61*s*d+3)*u+(base+tree)+((s-1)*d+8))*3^d :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq'.le hheader)
      _ = (q^base*q^tree) * ((q^u)^(61*s*d+3)*q^((s-1)*d+8)*3^d) := by
        rw [pow_add, pow_add, pow_add, Nat.mul_comm (61*s*d+3) u, pow_mul]
        ring
      _ ≤ (q^base*L^extra)*L^(M*d) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ htree) hmeta
      _ = q^base*L^(A*d) := by rw [mul_assoc, ←pow_add, Nat.add_comm extra, hExp]
      _ ≤ _ := hP
  have hPpos : 0 < (hashCount q b t ℓ)^d := by unfold hashCount; positivity
  have hproduct : data * q^(header+8) ≤ q^ℓ := by
    refine Nat.le_of_mul_le_mul_right ?_ hPpos
    calc
      _ = (data*(hashCount q b t ℓ)^d)*q^(header+8) := by ring
      _ ≤ (q^ℓ*3^d)*q^(header+8) := Nat.mul_le_mul_right _ hdata
      _ = q^ℓ*(q^(header+8)*3^d) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hpack
  have hheadLen : header+8 ≤ ℓ := by
    have h := (Nat.le_mul_of_pos_left (q^(header+8)) hp).trans hproduct
    by_contra! hn
    exact (Nat.pow_lt_pow_right hq' hn).not_ge h
  have hdataBound : data ≤ q^(ℓ-(header+8)) := by
    refine Nat.le_of_mul_le_mul_right ?_ (pow_pos (by omega : 0 < q) (header+8))
    rwa [←pow_add, Nat.sub_add_cancel hheadLen]
  have hwidth := (Nat.clog_le_iff_le_pow hq').mpr hdataBound
  change header + Nat.clog q data + 8 ≤ ℓ
  omega

/-- The recognition loop's `2^R ≤ ℓ^κ` bound in integer form,
with `B = 1/κ`. -/
theorem boolean_budget (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : minLength q b t ≤ ℓ) :
    (2^(componentCutoff q b t ℓ))^(reciprocal q b t) ≤ ℓ := by
  have h := basicBounds hq hb ht hstart
  have hℓ : ℓ ≠ 0 := (Nat.zero_lt_of_lt h.record_length).ne'
  have hc : 0 < Nat.clog 2 (gram q b t ℓ) :=
    Nat.clog_pos (by decide) (by have := h.gram_large; omega)
  have hR : componentCutoff q b t ℓ * (reciprocal q b t * Nat.clog 2 (gram q b t ℓ))
      ≤ Nat.log 2 ℓ := Nat.div_mul_le_self _ _
  rw [← pow_mul]
  refine (Nat.pow_le_pow_right (by decide : 1 ≤ 2) ?_).trans (Nat.pow_log_le_self _ hℓ)
  exact (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hc)).trans hR

theorem gram_dictionary_bound (hq : 2 ≤ q) (hℓ : 1 < ℓ) :
    q^(gram q b t ℓ) ≤ q^(gramMultiplier t * (b+4)) * ℓ^(gramMultiplier t) := by
  have hη := power_clog_le (show 1 < q from hq) hℓ
  let C := gramMultiplier t
  let y := eta q ℓ
  have hG : gram q b t ℓ = (y+b+3)*C := by
    change C*(y+b+3) = _
    rw [Nat.mul_comm]
  rw [hG, pow_mul]
  have hspan : q^(y+b+3) ≤ q^(b+4)*ℓ := by
    calc
      _ = q^y * q^(b+3) := by rw [← pow_add, Nat.add_assoc]
      _ ≤ q*ℓ*q^(b+3) := Nat.mul_le_mul_right _ hη
      _ = _ := by rw [Nat.pow_succ q (b+3)]; ring
  exact (Nat.pow_le_pow_left hspan C).trans_eq (by
    rw [mul_pow, ← pow_mul, Nat.mul_comm (b+4)])

#print axioms boolean_budget
#print axioms gram_dictionary_bound
#print axioms small_description_bound
#print axioms smallFamily_saves_eight
#print axioms peeled_saves_eight

end DeletionCode.Explicit.UniformParameters
