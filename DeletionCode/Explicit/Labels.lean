import DeletionCode.Explicit.TagTables
import Mathlib.Data.Nat.Digits.Defs

/-! `sec:d-labels` and `d:public-label-bound`: the same public bound covers
every length, including the short lengths at which the word is its own label. -/

namespace DeletionCode.Explicit

open Burst

/-- Digits are read with the first symbol most significant. At fixed length
leading zeroes pose no ambiguity. This applies to both q-ary and ternary labels. -/
def wordRank {q : ℕ} (w : QWord q) := Nat.ofDigits q (w.map Fin.val).reverse

private theorem rank_digit_lt {q : ℕ} (w : QWord q) (a : ℕ) (h : a ∈ (w.map Fin.val).reverse) :
    a < q := by
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp h)
  exact d.isLt

theorem wordRank_lt {q : ℕ} (hq : 2 ≤ q) (w : QWord q) : wordRank w < q ^ w.length := by
  simpa only [wordRank, List.length_reverse, List.length_map] using
    Nat.ofDigits_lt_base_pow_length hq (rank_digit_lt w)

theorem wordRank_injective_at_length {q : ℕ} (hq : 2 ≤ q) {x y : QWord q}
    (hl : x.length = y.length) (he : wordRank x = wordRank y) : x = y := by
  have h := Nat.ofDigits_inj_of_len_eq hq (by simpa only [List.length_reverse, List.length_map] using hl)
    (rank_digit_lt x) (rank_digit_lt y) he
  have hm := congrArg List.reverse h
  simp only [List.reverse_reverse] at hm
  exact List.map_injective_iff.mpr Fin.val_injective hm

def gramLength (q b C l : ℕ) := C * (Nat.clog q l + b + 3)

def publicLabelBound (q b s C A l₀ n : ℕ) :=
  max (q ^ l₀) (9 * n ^ (s - 1) * gramLength q b C n ^ A)

def labelAt {q : ℕ} (l₀ : ℕ) (largeLabel : QWord q → ℕ) (x : QWord q) :=
  if x.length < l₀ then wordRank x else largeLabel x

theorem labelAt_lt {q b s C A l₀ n : ℕ} (hq : 2 ≤ q) (largeLabel : QWord q → ℕ)
    (P : ℕ → ℕ) (hP : ∀ l, l₀ ≤ l → l ≤ n → P l < 3 * l ^ (s - 1) * gramLength q b C l ^ A)
    {x : QWord q} (hn : x.length ≤ n)
    (hx : l₀ ≤ x.length → largeLabel x < 3 * P x.length) :
    labelAt l₀ largeLabel x < publicLabelBound q b s C A l₀ n := by
  unfold labelAt publicLabelBound
  split
  · rename_i h
    exact Nat.lt_of_lt_of_le (wordRank_lt hq _) (Nat.le_trans
      (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt h)) (Nat.le_max_left ..))
  · rename_i h
    have hcut : l₀ ≤ x.length := by omega
    have hg : gramLength q b C x.length ≤ gramLength q b C n := by
      unfold gramLength
      apply Nat.mul_le_mul_left
      have := Nat.clog_mono_right q hn
      omega
    have hp := Nat.mul_le_mul_left 3 (Nat.le_of_lt (hP _ hcut hn))
    apply Nat.lt_of_lt_of_le (hx hcut)
    apply Nat.le_trans hp (Nat.le_trans _ (Nat.le_max_right ..))
    calc
      3 * (3 * x.length ^ (s - 1) * gramLength q b C x.length ^ A)
          = 9 * x.length ^ (s - 1) * gramLength q b C x.length ^ A := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn _))
        (Nat.pow_le_pow_left hg _)

theorem labelAt_separates {q b s l₀ : ℕ} (hq : 2 ≤ q) {largeLabel : QWord q → ℕ}
    {x y : QWord q} (hl : x.length = y.length)
    (hp : l₀ ≤ x.length → largeLabel x = largeLabel y → WithinBursts b s x y → x = y)
    (he : labelAt l₀ largeLabel x = labelAt l₀ largeLabel y) (hxy : WithinBursts b s x y) : x = y := by
  by_cases h : x.length < l₀
  · exact wordRank_injective_at_length hq hl (by simpa [labelAt, ← hl, h] using he)
  · exact hp (by omega) (by simpa [labelAt, ← hl, h] using he) hxy

/-- Stage 1 correctness of `sec:d-encoding` from the prior sections' data.
Only the large-length label is supplied. The short-length numbering, public
bound, bin tables, image test and decoder are computed by this development. -/
theorem encoding_correct_of_source_data {q b t n C A l₀ : ℕ} (hq : 2 ≤ q)
    (zero : Fin q) (D : RepairData (Fin q)) (largeLabel : QWord q → ℕ) (P : ℕ → ℕ)
    (hP : ∀ l, l₀ ≤ l → l ≤ n → P l < 3 * l ^ (2 * t - 1) * gramLength q b C l ^ A)
    (hbound : ∀ x : QWord q, l₀ ≤ x.length → x.length ≤ n → D.accepted x = true →
      largeLabel x < 3 * P x.length)
    (hsep : ∀ x y : QWord q, l₀ ≤ x.length → x.length = y.length → x.length ≤ n →
      D.accepted x = true → D.accepted y = true → largeLabel x = largeLabel y →
      WithinBursts b (2 * t) x y → x = y) :
    let B := publicLabelBound q b (2 * t) C A l₀ n
    let T := prepareTags q b t n B
    let W := T.wrapper zero D (labelAt l₀ largeLabel)
    T.m₀ + T.mOut ≤ n →
    ∀ u : QWord q, u.length = T.k → (W.encode u).length = n ∧
      ∀ z, WithinBursts b t (W.encode u) z → W.decode b t z = some u := by
  intro B T W hfit
  have hk : T.k ≤ n := by change n - _ - _ ≤ n; omega
  apply prepared_decode hq zero D (labelAt l₀ largeLabel) _ _ hfit
  · intro x hx ha
    have hn := Nat.le_trans hx hk
    exact labelAt_lt hq largeLabel P hP hn (fun hl => hbound x hl hn ha)
  · intro x y hl hx ax ay he hxy
    exact labelAt_separates hq hl (fun hc => hsep x y hc hl (Nat.le_trans hx hk) ax ay) he hxy

#print axioms encoding_correct_of_source_data

#print axioms labelAt_lt
#print axioms labelAt_separates

end DeletionCode.Explicit
