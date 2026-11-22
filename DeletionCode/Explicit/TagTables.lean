import DeletionCode.Explicit.GreedyTags
import DeletionCode.Explicit.TagLength
import DeletionCode.Explicit.WrapperDecoding

/-! The length bins and assignment of greedy tags from `sec:d-bins`. -/

namespace DeletionCode.Explicit

open Burst

/-- Public parameters and tag tables for one block length. The inner table
at index `j` stores words of length `m₀+j`. -/
structure TagTables (q : ℕ) where
  k : ℕ
  m₀ : ℕ
  mOut : ℕ
  labelCount : ℕ
  innerCodes : List (List (QWord q))
  outerCode : List (QWord q)

def prepareTags (q b t n B : ℕ) : TagTables q :=
  let s := 2 * t
  let jMax := Nat.clog q (n + 1)
  let m₀ := tagLength q b s B jMax
  let mOut := tagLength q b s (jMax + 1) 0
  { k := n - m₀ - mOut
    m₀, mOut, labelCount := B
    innerCodes := (List.range (jMax + 1)).map (fun j => greedyTags q b s (m₀ + j))
    outerCode := greedyTags q b s mOut }

/-- Assign row `(l,z)` its tag at offset `(k - l) * B + z` inside its bin.
Every assigned offset is in range. Gaps between offsets are harmless. -/
def TagTables.wrapper {q : ℕ} (T : TagTables q) (zero : Fin q)
    (D : RepairData (Fin q)) (label : QWord q → ℕ) : Wrapper q :=
  { k := T.k, m₀ := T.m₀, mOut := T.mOut, labelCount := T.labelCount
    zero, repairData := D, label
    inner := fun j l z => (T.innerCodes.getD j []).getD ((T.k - l) * T.labelCount + z) []
    outer := fun j => T.outerCode.getD j [] }

private theorem offset_lt {q k B l z : ℕ} (hq : 2 ≤ q) (hz : z < B) :
    (k - l) * B + z < q ^ Nat.clog q (k - l + 1) * B := by
  have hh := Nat.mul_le_mul_right B (Nat.le_pow_clog hq (k - l + 1))
  rw [Nat.succ_mul] at hh
  omega

private theorem offset_injective {k B l l' z z' : ℕ} (hl : l ≤ k) (hl' : l' ≤ k)
    (hz : z < B) (hz' : z' < B) (he : (k - l) * B + z = (k - l') * B + z') :
    l = l' ∧ z = z' := by
  have hm := congrArg (· % B) he
  simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hz, Nat.mod_eq_of_lt hz'] at hm
  subst z'
  have hp : 0 < B := by omega
  have hmul := Nat.add_right_cancel he
  have hbase := Nat.eq_of_mul_eq_mul_right hp hmul
  exact ⟨by omega, rfl⟩

private theorem tagBallBound_mono (q b s : ℕ) {m m' : ℕ} (h : m ≤ m') :
    tagBallBound q b s m ≤ tagBallBound q b s m' :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) s)

private theorem inner_count {q b t n B j : ℕ} (hq : 2 ≤ q) (hj : j ≤ Nat.clog q (n + 1)) :
    q ^ j * B ≤ (greedyTags q b (2 * t) ((prepareTags q b t n B).m₀ + j)).length := by
  let m := (prepareTags q b t n B).m₀
  let s := 2 * t
  let J := Nat.clog q (n + 1)
  have hbase : B * tagBallBound q b s (m + J) ≤ q ^ m := tagLength_sufficient hq b s B J
  apply greedyTags_count (by omega)
  change q ^ j * B * tagBallBound q b s (m + j) ≤ q ^ (m + j)
  rw [Nat.pow_add, Nat.mul_comm (q ^ m), Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  exact Nat.le_trans (Nat.mul_le_mul_left B (tagBallBound_mono _ _ _ (by omega))) hbase

private theorem outer_count {q b t n B : ℕ} (hq : 2 ≤ q) :
    Nat.clog q (n + 1) + 1 ≤ (prepareTags q b t n B).outerCode.length := by
  apply greedyTags_count (by omega)
  simpa using tagLength_sufficient hq b (2 * t) (Nat.clog q (n+1) + 1) 0

private theorem indexed_tag {q b s m i : ℕ} (hi : i < (greedyTags q b s m).length) :
    ((greedyTags q b s m).getD i []).length = m := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact (greedyTags_spec q b s m).1 _ (List.getElem_mem ..)

private theorem tag_index_eq {q b s m i j : ℕ}
    (hi : i < (greedyTags q b s m).length) (hj : j < (greedyTags q b s m).length)
    (h : WithinBursts b s ((greedyTags q b s m).getD i []) ((greedyTags q b s m).getD j [])) :
    i = j := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Option.getD_some] at h
  have hp := List.pairwise_iff_getElem.mp (greedyTags_spec q b s m).2.1
  rcases Nat.lt_trichotomy i j with hij | he | hji
  · exact (hp i j hi hj hij h).elim
  · exact he
  · obtain ⟨r, hr, path⟩ := h
    exact (hp j i hj hi hji ⟨r, hr, path.reverse⟩).elim

private theorem innerCodes_get {q b t n B j : ℕ} (hj : j ≤ Nat.clog q (n + 1)) :
    (prepareTags q b t n B).innerCodes.getD j [] =
      greedyTags q b (2 * t) ((prepareTags q b t n B).m₀ + j) := by
  simp [prepareTags, List.getD_eq_getElem?_getD, Nat.lt_succ_of_le hj]

/-- The earlier construction supplies only the repair data and the bounded,
separating label on accepted words. The two tag tables are computed here. -/
theorem prepared_laws {q b t n B : ℕ} (hq : 2 ≤ q) (zero : Fin q)
    (D : RepairData (Fin q)) (label : QWord q → ℕ)
    (hbound : ∀ x : QWord q, x.length ≤ (prepareTags q b t n B).k → D.accepted x = true → label x < B)
    (hlabel : ∀ x y : QWord q, x.length = y.length → x.length ≤ (prepareTags q b t n B).k →
      D.accepted x = true → D.accepted y = true → label x = label y → WithinBursts b (2 * t) x y → x = y) :
    ((prepareTags q b t n B).wrapper zero D label).Laws b t := by
  let T := prepareTags q b t n B
  let W := T.wrapper zero D label
  have hmax : Nat.clog q (W.k + 1) ≤ Nat.clog q (n + 1) := by
    apply Nat.clog_mono_right
    change n - _ - _ + 1 ≤ n + 1
    omega
  have hbin (l : ℕ) := Nat.le_trans (W.bin_le_max l) hmax
  have hindex (l z : ℕ) (hz : z < B) :
      (W.k - l) * B + z < (greedyTags q b (2 * t) (W.m₀ + W.bin l)).length :=
    Nat.lt_of_lt_of_le (offset_lt hq hz) (inner_count hq (hbin l))
  have hinner (l z : ℕ) : W.inner (W.bin l) l z =
      (greedyTags q b (2 * t) (W.m₀ + W.bin l)).getD ((W.k - l) * B + z) [] := by
    exact congrArg (fun xs : List (QWord q) => xs.getD ((W.k - l) * B + z) []) (innerCodes_get (hbin l))
  refine ⟨hq, hbound, hlabel, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact indexed_tag (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_trans hj hmax)) (outer_count (B := B) hq))
  · intro i j hi hj h
    apply tag_index_eq _ _ h
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_trans hi hmax)) (outer_count (B := B) hq)
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_trans hj hmax)) (outer_count (B := B) hq)
  · intro l z _ hz
    change (W.inner (W.bin l) l z).length = _
    rw [hinner]
    exact indexed_tag (hindex l z hz)
  · intro l l' z z' hl hl' hz hz' hj h
    change WithinBursts b (2 * t) (W.inner (W.bin l) l z) (W.inner (W.bin l') l' z') at h
    rw [hinner, hinner, hj] at h
    have hi := hindex l z hz
    rw [hj] at hi
    exact offset_injective hl hl' hz hz' (tag_index_eq hi (hindex l' z' hz') h)

/-- Exact redundancy before estimating the two tag lengths
(`d:wrapper-redundancy`). -/
theorem prepareTags_redundancy {q b t n B : ℕ}
    (h : (prepareTags q b t n B).m₀ + (prepareTags q b t n B).mOut ≤ n) :
    n - (prepareTags q b t n B).k =
      (prepareTags q b t n B).m₀ + (prepareTags q b t n B).mOut := by
  dsimp only [prepareTags] at *
  omega

/-- Correctness of the concrete tag setup and wrapper at block length `n`,
given the earlier accepted-word test, label and repair data. -/
theorem prepared_decode {q b t n B : ℕ} (hq : 2 ≤ q) (zero : Fin q)
    (D : RepairData (Fin q)) (label : QWord q → ℕ)
    (hbound : ∀ x : QWord q, x.length ≤ (prepareTags q b t n B).k → D.accepted x = true → label x < B)
    (hlabel : ∀ x y : QWord q, x.length = y.length → x.length ≤ (prepareTags q b t n B).k →
      D.accepted x = true → D.accepted y = true → label x = label y → WithinBursts b (2 * t) x y → x = y)
    (hfit : (prepareTags q b t n B).m₀ + (prepareTags q b t n B).mOut ≤ n) :
    let T := prepareTags q b t n B
    let W := T.wrapper zero D label
    ∀ u : QWord q, u.length = T.k → (W.encode u).length = n ∧
      ∀ z, WithinBursts b t (W.encode u) z → W.decode b t z = some u := by
  intro T W u hu
  have H := prepared_laws hq zero D label hbound hlabel
  refine ⟨?_, fun z hz => W.decode_correct H hu hz⟩
  rw [Wrapper.encode_length H hu]
  change n - T.m₀ - T.mOut + T.m₀ + T.mOut = n
  change T.m₀ + T.mOut ≤ n at hfit
  omega

#print axioms prepared_laws
#print axioms prepareTags_redundancy
#print axioms prepared_decode

end DeletionCode.Explicit
