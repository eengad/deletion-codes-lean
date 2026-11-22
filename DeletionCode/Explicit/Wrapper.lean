import DeletionCode.Explicit.Repair
import DeletionCode.Explicit.Truncation
import DeletionCode.Burst.ChronologicalRecords
import Mathlib.Data.Nat.Log

/-! The transmitted word `d:wrapped-word` and the separation argument
`d:wrapper`. The hypotheses below are the interface supplied by the
accepted-word label and the assigned finite greedy tag tables. -/

namespace DeletionCode.Explicit

open Burst

structure Wrapper (q : ℕ) where
  k : ℕ
  m₀ : ℕ
  mOut : ℕ
  labelCount : ℕ
  zero : Fin q
  repairData : RepairData (Fin q)
  label : List (Fin q) → ℕ
  inner : ℕ → ℕ → ℕ → List (Fin q)
  outer : ℕ → List (Fin q)

namespace Wrapper

variable {q : ℕ} (W : Wrapper q)

def bin (l : ℕ) := Nat.clog q (W.k - l + 1)

def padded (x : List (Fin q)) :=
  List.replicate (W.k - x.length - W.bin x.length) W.zero ++ x

def innerPart (x : List (Fin q)) := W.inner (W.bin x.length) x.length (W.label x)

def headPart (x : List (Fin q)) := W.padded x ++ W.innerPart x

def wrap (x : List (Fin q)) := W.headPart x ++ W.outer (W.bin x.length)

def encode (u : List (Fin q)) := W.wrap (W.repairData.repair u)

/-- Domains are restricted to assigned lengths, bins and labels. Distinct
inner tags in different bins need no separation property. -/
structure Laws (b t : ℕ) : Prop where
  alphabet : 2 ≤ q
  label_lt : ∀ x, x.length ≤ W.k → W.repairData.accepted x = true → W.label x < W.labelCount
  label_separates : ∀ x y, x.length = y.length → x.length ≤ W.k →
    W.repairData.accepted x = true → W.repairData.accepted y = true →
    W.label x = W.label y → WithinBursts b (2 * t) x y → x = y
  outer_length : ∀ j ≤ Nat.clog q (W.k + 1), (W.outer j).length = W.mOut
  outer_separates : ∀ i j, i ≤ Nat.clog q (W.k + 1) → j ≤ Nat.clog q (W.k + 1) →
    WithinBursts b (2 * t) (W.outer i) (W.outer j) → i = j
  inner_length : ∀ l z, l ≤ W.k → z < W.labelCount →
    (W.inner (W.bin l) l z).length = W.m₀ + W.bin l
  inner_separates : ∀ l l' z z', l ≤ W.k → l' ≤ W.k → z < W.labelCount → z' < W.labelCount →
    W.bin l = W.bin l' → WithinBursts b (2 * t) (W.inner (W.bin l) l z) (W.inner (W.bin l') l' z') →
    l = l' ∧ z = z'

variable {W} {b t : ℕ}

theorem bin_le_loss (hq : 2 ≤ q) (l : ℕ) : W.bin l ≤ W.k - l :=
  Nat.clog_le_of_le_pow (Nat.lt_pow_self hq)

theorem bin_le_max (l : ℕ) : W.bin l ≤ Nat.clog q (W.k + 1) :=
  Nat.clog_mono_right q (by omega)

private theorem prefix_length (H : W.Laws b t) {x : List (Fin q)} (hx : x.length ≤ W.k) :
    (W.padded x).length = W.k - W.bin x.length := by
  have := W.bin_le_loss H.alphabet x.length
  simp only [padded, List.length_append, List.length_replicate]
  omega

private theorem head_length (H : W.Laws b t) {x : List (Fin q)}
    (hx : x.length ≤ W.k) (ha : W.repairData.accepted x = true) :
    (W.headPart x).length = W.k + W.m₀ := by
  have := W.bin_le_loss H.alphabet x.length
  rw [headPart, List.length_append, prefix_length H hx, innerPart,
    H.inner_length _ _ hx (H.label_lt _ hx ha)]
  omega

theorem encode_length (H : W.Laws b t) {u : List (Fin q)} (hu : u.length = W.k) :
    (W.encode u).length = W.k + W.m₀ + W.mOut := by
  have hx := W.repairData.repair_length_le u
  rw [hu] at hx
  rw [encode, wrap, List.length_append, head_length H hx (W.repairData.repair_accepted u),
    H.outer_length _ (W.bin_le_max _)]

private theorem cut_prefix {α : Type*} {a a' x y : List α} {s : ℕ}
    (h : WithinBursts b s (a ++ x) (a' ++ y)) (hl : a.length = a'.length) :
    WithinBursts b s x y := by
  have hc := withinBursts_drop a.length h
  simpa [List.drop_append, hl] using hc

private theorem cut_suffix {α : Type*} {a a' x y : List α} {s : ℕ}
    (h : WithinBursts b s (x ++ a) (y ++ a')) (hl : a.length = a'.length) :
    WithinBursts b s x y := by
  have hc := withinBursts_dropRight a.length h
  simpa [List.take_append, hl] using hc

private theorem wrap_separates (H : W.Laws b t) {x y : List (Fin q)}
    (hx : x.length ≤ W.k) (hy : y.length ≤ W.k)
    (ax : W.repairData.accepted x = true) (ay : W.repairData.accepted y = true)
    (h : WithinBursts b (2 * t) (W.wrap x) (W.wrap y)) : x = y := by
  have tx := W.bin_le_max x.length
  have ty := W.bin_le_max y.length
  have hout := cut_prefix h ((head_length H hx ax).trans (head_length H hy ay).symm)
  have hj := H.outer_separates _ _ tx ty hout
  have hh := cut_suffix h ((H.outer_length _ tx).trans (H.outer_length _ ty).symm)
  have hpx := prefix_length H hx
  have hpy := prefix_length H hy
  have hi := cut_prefix hh (by rw [hpx, hpy, hj])
  have ltx := H.label_lt _ hx ax
  have lty := H.label_lt _ hy ay
  obtain ⟨hl, hz⟩ := H.inner_separates _ _ _ _ hx hy ltx lty hj hi
  have hn : (W.innerPart x).length = (W.innerPart y).length := by
    rw [innerPart, innerPart, H.inner_length _ _ hx ltx, H.inner_length _ _ hy lty, hj]
  have hp := cut_suffix hh hn
  have hxy := cut_prefix hp (by simp [hl])
  exact H.label_separates x y hl hx ax ay hz hxy

/-- `d:wrapper`: even a path of `2*t` edits between encodings forces
message equality. This includes the zero-edit path. -/
theorem encode_separates (H : W.Laws b t) {u v : List (Fin q)}
    (hu : u.length = W.k) (hv : v.length = W.k)
    (h : WithinBursts b (2 * t) (W.encode u) (W.encode v)) : u = v := by
  apply W.repairData.repair_injective_of_length_eq (hu.trans hv.symm)
  apply wrap_separates H _ _ (W.repairData.repair_accepted u) (W.repairData.repair_accepted v) h
  · simpa only [← hu] using W.repairData.repair_length_le u
  · simpa only [← hv] using W.repairData.repair_length_le v

theorem encode_injective (H : W.Laws b t) {u v : List (Fin q)}
    (hu : u.length = W.k) (hv : v.length = W.k) (he : W.encode u = W.encode v) : u = v := by
  apply encode_separates H hu hv
  rw [he]
  exact ⟨0, Nat.zero_le _, .refl _⟩

theorem eq_of_common_output (H : W.Laws b t) {u v z : List (Fin q)}
    (hu : u.length = W.k) (hv : v.length = W.k)
    (hz : WithinBursts b t (W.encode u) z) (hz' : WithinBursts b t (W.encode v) z) : u = v :=
  encode_separates H hu hv (Confusable.script ⟨z, hz, hz'⟩)

#print axioms encode_length
#print axioms encode_injective
#print axioms eq_of_common_output

end Wrapper
end DeletionCode.Explicit
