import DeletionCode.Explicit.Machine.TernaryProbability
import DeletionCode.Explicit.BucketBalance

/-! Exact conditional bucket potential on explicitly listed families. -/
namespace DeletionCode.Explicit.Machine.Ternary

open FieldHash Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open scoped BigOperators

set_option maxHeartbeats 600000

-- A balanced numerator/denominator bit bound grows additively under addition.
-- Bounding the entire framed pair with the coarse one-step lemma would
-- multiply the running bound at each term.
private def ratBits (x : ℚ) := max x.num.natAbs.size x.den.size

private theorem ratBits_le_encoding (x : ℚ) : ratBits x ≤ (encRat x).length := by
  rw [length_encRat, ratBits]
  exact max_le (by omega) (by omega)

private theorem encoding_le_ratBits (x : ℚ) : (encRat x).length ≤ 3 * ratBits x + 3 := by
  rw [length_encRat, ratBits]
  have hn := Nat.le_max_left x.num.natAbs.size x.den.size
  have hd := Nat.le_max_right x.num.natAbs.size x.den.size
  omega

private theorem ratBits_add (a b : ℚ) : ratBits (a + b) ≤ ratBits a + ratBits b + 1 := by
  have hd : (a + b).den.size ≤ a.den.size + b.den.size :=
    (Nat.size_le_size (Rat.den_add_le a b)).trans (Nat.size_mul_le _ _)
  -- The numerator is the sum of two products; the max bound is paid only
  -- once for each operand, using the maximum of the two product sizes.
  have hadd : ∀ x y : ℕ, (x + y).size ≤ max x.size y.size + 1 := by
    intro x y
    have hx := Nat.lt_size_self x
    have hy := Nat.lt_size_self y
    have hl := hx.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_max_left x.size y.size))
    have hr := hy.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_max_right x.size y.size))
    exact Nat.size_le.mpr (by rw [pow_succ]; omega)
  rw [ratBits]
  apply max_le
  · refine (Nat.size_le_size (Rat.natAbs_num_add_le a b)).trans ((hadd _ _).trans ?_)
    apply Nat.add_le_add_right
    apply max_le
    · exact (Nat.size_mul_le _ _).trans (Nat.add_le_add (Nat.le_max_left ..) (Nat.le_max_right ..))
    · have hb := Nat.add_le_add (Nat.le_max_left b.num.natAbs.size b.den.size)
          (Nat.le_max_right a.num.natAbs.size a.den.size)
      exact (Nat.size_mul_le _ _).trans (by simpa [ratBits, Nat.add_comm] using hb)
  · exact hd.trans ((Nat.add_le_add (Nat.le_max_right ..) (Nat.le_max_right ..)).trans (Nat.le_succ _))

private theorem foldSum_eq (l : List ℚ) (x : ℚ) :
    l.foldl (· + ·) x = x + l.sum := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp [ih, add_assoc]

theorem ratSum_polyTime : ComputableInPolyTime (List.sum (α := ℚ)) (encList encRat) encRat := by
  let size (xs : List ℚ) := (encList encRat xs).length
  have hs : PolyBounded size
      (fun xs => 3 * (ratBits 0 + size xs * (size xs + 1)) + 3) :=
    ((PolyBounded.const 3).mul ((PolyBounded.const (ratBits 0)).add
      (PolyBounded.self.mul (PolyBounded.self.add (PolyBounded.const 1))))).add (PolyBounded.const 3)
  have h := (foldl_spec (id' (encIn := encList encRat)) (const 0) rat_add
    (fun xs pref a => ratBits a ≤ ratBits 0 + pref.length * (size xs + 1))
    (fun _ => by simp) (fun xs pref a b hp ha => by
      have hb : ratBits b ≤ size xs := (ratBits_le_encoding b).trans
        (SizedListEncoding.length_elem_le xs b (hp.subset (by simp)))
      have hab := ratBits_add a b
      simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
      omega)
    hs (fun xs pref a hp ha => by
      have hlen := hp.length_le.trans (SizedListEncoding.length_le (encA := encRat) (encL := encList encRat) xs)
      change pref.length ≤ size xs at hlen
      have ha' := ha.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (size xs + 1) hlen) _)
      exact (encoding_le_ratBits a).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left 3 ha') 3))).1
  exact h.of_enc_eq fun xs => by simp only [foldSum_eq, zero_add]

abbrev PotentialInput := (ℕ × PartialRows) × List Rows
abbrev partialHashEncoding := encPair encUnary partialRowsEncoding
abbrev potentialEncoding := encPair partialHashEncoding (encList rowsEncoding)

def rowOf (n : ℕ) (r : Row) : BucketBalance.Word n :=
  fun i => r.getD i.val 0

def familyOf (n : ℕ) (rs : Rows) : BucketBalance.Family n :=
  (rs.map (rowOf n)).toFinset

private def difference (n : ℕ) (v w : Row) : MatrixInput :=
  (n, [(List.range n).map fun j => v.getD j 0 - w.getD j 0])

private theorem difference_polyTime :
    ComputableInPolyTime (fun p : (ℕ × Row) × Row => difference p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary rowEncoding) rowEncoding) matrixEncoding := by
  let e := encPair (encPair encUnary rowEncoding) rowEncoding
  have hp := fst (encPair encUnary rowEncoding) rowEncoding
  have hn := hp.fst'
  have hv := hp.snd'
  have hw := snd (encPair encUnary rowEncoding) rowEncoding
  have hstep : ComputableInPolyTime (fun p : F₃ × F₃ => p.1 - p.2)
      (encPair tritEncoding tritEncoding) tritEncoding := of_finite _
  have hrow := mapWithInput
    (f := fun p j => p.1.2.getD j 0 - p.2.getD j 0) (unary_range' hn)
    (hstep.comp ((listGetDWithInput (hv.comp (fst e encUnary)) (snd e encUnary) 0).prod
      (listGetDWithInput (hw.comp (fst e encUnary)) (snd e encUnary) 0)))
  exact hn.prod (cons' hrow (const []))

private theorem difference_eq (n : ℕ) (v w : Row) :
    matrixOf (difference n v w) = BucketBalance.differenceRow (rowOf n v) (rowOf n w) := by
  funext i j
  have hiL : i.val < 1 := i.isLt
  have hi : i.val = 0 := by omega
  have hj : j.val < n := j.isLt
  change cell (difference n v w).2 i.val j.val = v.getD j.val 0 - w.getD j.val 0
  rw [hi]
  change ((List.range n).map (fun k => v.getD k 0 - w.getD k 0)).getD j.val 0 = _
  simp [List.getD_eq_getElem?_getD, hj]

private def pairProbability (p : (ℕ × PartialRows) × Row × Row) : ℚ :=
  conditional (difference p.1.1 p.2.1 p.2.2, p.1.2)

private theorem pairProbability_polyTime :
    ComputableInPolyTime pairProbability
      (encPair partialHashEncoding (encPair rowEncoding rowEncoding)) encRat := by
  have hp := fst partialHashEncoding (encPair rowEncoding rowEncoding)
  have hv := snd partialHashEncoding (encPair rowEncoding rowEncoding)
  have hdiff := difference_polyTime.comp ((hp.fst'.prod hv.fst').prod hv.snd')
  exact conditional_polyTime.comp (hdiff.prod hp.snd')

private def familyPotential (p : (ℕ × PartialRows) × Rows) : ℚ :=
  ((p.2.map fun v => (p.2.map fun w => pairProbability (p.1, v, w)).sum).sum) / p.2.length -
    p.2.length / (3 : ℚ) ^ p.1.2.length

private theorem familyPotential_polyTime :
    ComputableInPolyTime familyPotential (encPair partialHashEncoding rowsEncoding) encRat := by
  let e := encPair partialHashEncoding rowsEncoding
  let eRow := encPair e rowEncoding
  have hrows := snd partialHashEncoding rowsEncoding
  have hc := fst partialHashEncoding rowsEncoding
  have hvr := fst e rowEncoding
  have hwr := fst eRow rowEncoding
  have hp := (hc.comp hvr).comp hwr
  have hv := (snd e rowEncoding).comp hwr
  have hw := snd eRow rowEncoding
  have hcall := pairProbability_polyTime.comp (hp.prod (hv.prod hw))
  have hinner := mapWithInput (f := fun (p : ((ℕ × PartialRows) × Rows) × Row) w =>
      pairProbability (p.1.1, p.2, w)) (hrows.comp hvr)
    (by simpa only [Function.comp_def] using hcall)
  have houter := mapWithInput (f := fun (p : (ℕ × PartialRows) × Rows) v =>
      (p.2.map fun w => pairProbability (p.1, v, w)).sum) hrows
    (by simpa only [Function.comp_def] using ratSum_polyTime.comp hinner)
  have hcard := ratOfNat_polyTime.comp (unary_to_binary.comp ((length_list rowEncoding).comp hrows))
  have hθ := (length_list partialRowEncoding).comp hc.snd'
  exact rat_sub'
    (rat_div' (ratSum_polyTime.comp houter) hcard)
    (rat_div' hcard (threePow_polyTime.comp hθ))

/-- Each inner list enumerates its family once. Its order is immaterial. -/
def potential (p : PotentialInput) : ℚ :=
  (p.2.map fun family => familyPotential (p.1, family)).sum

theorem potential_polyTime : ComputableInPolyTime potential potentialEncoding encRat := by
  have hcall := familyPotential_polyTime.comp
    ((fst potentialEncoding rowsEncoding).fst'.prod (snd potentialEncoding rowsEncoding))
  have h := mapWithInput (f := fun (p : PotentialInput) family => familyPotential (p.1, family))
    (snd partialHashEncoding (encList rowsEncoding)) (by simpa only [Function.comp_def] using hcall)
  exact ratSum_polyTime.comp h

private theorem familySum_eq {n : ℕ} {rs : Rows} (hN : (rs.map (rowOf n)).Nodup)
    (f : BucketBalance.Word n → ℚ) :
    (rs.map fun r => f (rowOf n r)).sum = ∑ v ∈ familyOf n rs, f v := by
  simpa only [familyOf, List.map_map, Function.comp_def] using (List.sum_toFinset f hN).symm

private theorem familyPotential_eq (p : ℕ × PartialRows) (rs : Rows)
    (hN : (rs.map (rowOf p.1)).Nodup) :
    familyPotential (p, rs) =
      (∑ v ∈ familyOf p.1 rs, ∑ w ∈ familyOf p.1 rs,
        conditionalKernelProbability (BucketBalance.differenceRow v w) (hashOf p.1 p.2)) /
        (familyOf p.1 rs).card - (familyOf p.1 rs).card / (3 : ℚ) ^ p.2.length := by
  have hc : (familyOf p.1 rs).card = rs.length := by
    simpa only [familyOf, List.length_map] using List.toFinset_card_of_nodup hN
  have hpair (v w : Row) : pairProbability (p, v, w) =
      conditionalKernelProbability (BucketBalance.differenceRow (rowOf p.1 v) (rowOf p.1 w))
        (hashOf p.1 p.2) := by
    unfold pairProbability
    rw [conditional_eq]
    change conditionalKernelProbability (matrixOf (difference p.1 v w)) (hashOf p.1 p.2) = _
    exact congrArg (fun A => conditionalKernelProbability A (hashOf p.1 p.2))
      (difference_eq p.1 v w)
  let f := fun v w : BucketBalance.Word p.1 =>
    conditionalKernelProbability (BucketBalance.differenceRow v w) (hashOf p.1 p.2)
  have hinner (v : Row) :
      (rs.map (fun w => pairProbability (p, v, w))).sum =
        ∑ w ∈ familyOf p.1 rs, f (rowOf p.1 v) w := by
    rw [show (rs.map (fun w => pairProbability (p, v, w))) =
        rs.map (fun w => f (rowOf p.1 v) (rowOf p.1 w)) from
      List.map_congr_left (fun w _ => hpair v w)]
    exact familySum_eq hN (f (rowOf p.1 v))
  have hsum :
      (rs.map (fun v => (rs.map (fun w => pairProbability (p, v, w))).sum)).sum =
        ∑ v ∈ familyOf p.1 rs, ∑ w ∈ familyOf p.1 rs, f v w := by
    rw [show (rs.map (fun v => (rs.map (fun w => pairProbability (p, v, w))).sum)) =
        rs.map (fun v => ∑ w ∈ familyOf p.1 rs, f (rowOf p.1 v) w) from
      List.map_congr_left (fun v _ => hinner v)]
    exact familySum_eq hN (fun v => ∑ w ∈ familyOf p.1 rs, f v w)
  change (rs.map (fun v => (rs.map (fun w => pairProbability (p, v, w))).sum)).sum / rs.length -
    rs.length / (3 : ℚ) ^ p.2.length = _
  rw [hsum, hc]

/-- With duplicate-free family enumerations, the encoded computation is
exactly the manuscript's existing `conditionalPotential`. -/
theorem potential_eq (p : PotentialInput)
    (hN : ∀ rs ∈ p.2, (rs.map (rowOf p.1.1)).Nodup) :
    potential p = BucketBalance.conditionalPotential
      (fun j : Fin p.2.length => familyOf p.1.1 (p.2.getD j.val [])) (hashOf p.1.1 p.1.2) := by
  unfold potential BucketBalance.conditionalPotential
  rw [← List.sum_ofFn]
  apply congrArg List.sum
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hi₀ : i < p.2.length := by simpa using hi
  simp only [List.getElem_map, List.getElem_ofFn]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₀, Option.getD_some]
  exact familyPotential_eq p.1 p.2[i] (hN _ (List.getElem_mem hi₀))

#print axioms potential_polyTime
#print axioms potential_eq

end DeletionCode.Explicit.Machine.Ternary
