import DeletionCode.Explicit.Machine.TernaryRank
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPower

/-! Exact affine and conditional probabilities on row-major inputs. -/
namespace DeletionCode.Explicit.Machine.Ternary

open FieldHash
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

set_option maxHeartbeats 500000

theorem rank_represents {x : MatrixInput} {m n : ℕ} {A : TernaryMatrix m n}
    (hm : x.2.length = m) (hn : x.1 = n) (hA : asMatrix x.2 m n = A) :
    rank x = ternaryRank A := by
  subst m n A
  exact rank_eq x

abbrev AffineInput := MatrixInput × Row
abbrev affineEncoding := encPair matrixEncoding rowEncoding

def augmented (p : AffineInput) : MatrixInput :=
  (p.1.1 + 1, tabRows p.1.2.length (p.1.1 + 1) fun i j =>
    if j = 0 then p.2.getD i 0 else cell p.1.2 i (j - 1))

theorem augmented_polyTime : ComputableInPolyTime augmented affineEncoding matrixEncoding := by
  have hA := fst matrixEncoding rowEncoding
  have hn := unary_add' hA.fst' (const 1)
  refine hn.prod (tabRows_polyTime ((length_list rowEncoding).comp hA.snd') hn ?_)
  let e := encPair affineEncoding encUnary
  have hp := (fst affineEncoding encUnary).comp (fst e encUnary)
  have hi := (snd affineEncoding encUnary).comp (fst e encUnary)
  have hj := snd e encUnary
  have hzero := listGetDWithInput ((snd matrixEncoding rowEncoding).comp hp) hi 0
  have hnonzero := cell_polyTime (hA.snd'.comp hp) hi (unary_sub' hj (const 1))
  exact ite_decide (hj.decide_eq' (const 0)) hzero hnonzero

theorem augmented_eq (p : AffineInput) :
    rank (augmented p) = ternaryRank (augment (matrixOf p.1) fun i => p.2.getD i.val 0) := by
  apply rank_represents (m := p.1.2.length) (n := p.1.1 + 1) (tabRows_length ..) rfl
  funext i j
  change cell (augmented p).2 i.val j.val = _
  unfold augmented
  dsimp only
  rw [tabRows_cell _ _ _ i.isLt j.isLt]
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [augment]
  · simp [augment, matrixOf, asMatrix]

theorem ratOfNat_polyTime : ComputableInPolyTime (fun n : ℕ => (n : ℚ)) encNat encRat := by
  have h := rat_intCast.comp intBin_natCast
  simpa only [Function.comp_def, Int.cast_natCast] using h

theorem threePow_polyTime :
    ComputableInPolyTime (fun n : ℕ => (3 : ℚ) ^ n) encUnary encRat := by
  have h := ratOfNat_polyTime.comp (binary_pow.comp ((const (encOut := encNat) 3).prod id'))
  simpa only [Function.comp_def, id_eq, Nat.cast_pow, Nat.cast_ofNat] using h

private def inverseThreePow (n : ℕ) : ℚ := 1 / (3 : ℚ) ^ n

private theorem inverseThreePow_polyTime :
    ComputableInPolyTime inverseThreePow encUnary encRat :=
  rat_div' (const 1) threePow_polyTime

/-- Exact affine probability, with a binary numerator-denominator output. -/
def affine (p : AffineInput) : ℚ :=
  let r := rank p.1
  if rank (augmented p) = r then inverseThreePow r else 0

theorem affine_polyTime : ComputableInPolyTime affine affineEncoding encRat := by
  have hr := rank_polyTime.comp (fst matrixEncoding rowEncoding)
  have haug := rank_polyTime.comp augmented_polyTime
  exact ite_decide (haug.decide_eq' hr) (inverseThreePow_polyTime.comp hr) (const 0)

theorem affine_eq (p : AffineInput) :
    affine p = affineProbability (matrixOf p.1) (fun i => p.2.getD i.val 0) := by
  unfold affine affineProbability
  dsimp only
  rw [augmented_eq, rank_eq]
  rfl

theorem affine_represents {p : AffineInput} {m n : ℕ} {A : TernaryMatrix m n} {y : Fin m → F₃}
    (hm : p.1.2.length = m) (hn : p.1.1 = n) (hA : asMatrix p.1.2 m n = A)
    (hy : (fun i : Fin m => p.2.getD i.val 0) = y) :
    affine p = affineProbability A y := by
  subst m n A y
  exact affine_eq p

abbrev PartialRow := List (Option F₃)
abbrev PartialRows := List PartialRow
abbrev partialRowEncoding := encList (encOption tritEncoding)
abbrev partialRowsEncoding := encList partialRowEncoding
abbrev conditionalEncoding := encPair matrixEncoding partialRowsEncoding

def partialValue (p : PartialRow) (i : ℕ) : Option F₃ := p.getD i none

def hashOf (n : ℕ) (x : PartialRows) : PartialHash x.length n :=
  fun j i => partialValue (x.getD j.val []) i.val

theorem partialValue_polyTime {α : Type} {enc : α ↪ List Bool} {p : α → PartialRow} {i : α → ℕ}
    (hp : ComputableInPolyTime p enc partialRowEncoding) (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun a => partialValue (p a) (i a)) enc (encOption tritEncoding) :=
  listGetDWithInput hp hi none

private def fixedCell (p : PartialRow) (i j : ℕ) : F₃ :=
  if i = j ∧ (partialValue p i).isSome then 1 else 0

private theorem fixedCell_polyTime {α : Type} {enc : α ↪ List Bool}
    {p : α → PartialRow} {i j : α → ℕ}
    (hp : ComputableInPolyTime p enc partialRowEncoding)
    (hi : ComputableInPolyTime i enc encUnary) (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun a => fixedCell (p a) (i a) (j a)) enc tritEncoding :=
  ite_decide (decide_and (hi.decide_eq' hj) (optionIsSome (partialValue_polyTime hp hi)))
    (const 1) (const 0)

def fixed (n : ℕ) (p : PartialRow) : AffineInput :=
  ((n, tabRows n n (fixedCell p)), (List.range n).map fun i => (partialValue p i).getD 0)

private theorem fixed_polyTime :
    ComputableInPolyTime (fun p : ℕ × PartialRow => fixed p.1 p.2)
      (encPair encUnary partialRowEncoding) affineEncoding := by
  let e := encPair encUnary partialRowEncoding
  have hn := fst encUnary partialRowEncoding
  have hp := snd encUnary partialRowEncoding
  have hpair := fst (encPair e encUnary) encUnary
  have hmat := tabRows_polyTime (f := fun p i j => fixedCell p.2 i j) hn hn
    (fixedCell_polyTime (hp.comp ((fst e encUnary).comp hpair)) ((snd e encUnary).comp hpair) (snd _ _))
  have hvec := mapWithInput (f := fun p i => (partialValue p.2 i).getD 0) (unary_range' hn)
    (optionGetDWithInput (partialValue_polyTime (hp.comp (fst e encUnary)) (snd e encUnary)) (const 0))
  exact (hn.prod hmat).prod hvec

def joint (p : MatrixInput × PartialRow) : AffineInput :=
  let m := p.1.2.length
  let n := p.1.1
  ((n, tabRows (m + n) n fun i j =>
    if i < m then cell p.1.2 i j else fixedCell p.2 (i - m) j),
    List.replicate m 0 ++ (fixed n p.2).2)

theorem joint_polyTime :
    ComputableInPolyTime joint (encPair matrixEncoding partialRowEncoding) affineEncoding := by
  let e := encPair matrixEncoding partialRowEncoding
  have hA := fst matrixEncoding partialRowEncoding
  have hn := hA.fst'
  have hrows := hA.snd'
  have hp := snd matrixEncoding partialRowEncoding
  have hm := (length_list rowEncoding).comp hrows
  have hmat : ComputableInPolyTime (fun p : MatrixInput × PartialRow =>
      tabRows (p.1.2.length + p.1.1) p.1.1 (fun i j =>
        if i < p.1.2.length then cell p.1.2 i j else fixedCell p.2 (i - p.1.2.length) j))
      e rowsEncoding := by
    apply tabRows_polyTime (unary_add' hm hn) hn
    let ei := encPair e encUnary
    have hx := (fst e encUnary).comp (fst ei encUnary)
    have hi := (snd e encUnary).comp (fst ei encUnary)
    have hj := snd ei encUnary
    have hml := hm.comp hx
    exact ite_decide (unary_lt' hi hml) (cell_polyTime (hrows.comp hx) hi hj)
      (fixedCell_polyTime (hp.comp hx) (unary_sub' hi hml) hj)
  have hvec := listAppend' (replicate hm (const (0 : F₃)))
    (fixed_polyTime.comp (hn.prod hp)).snd'
  exact (hn.prod hmat).prod hvec

private theorem foldProd_eq (l : List ℚ) (x : ℚ) :
    l.foldl (· * ·) x = x * l.prod := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp [ih, mul_assoc]

theorem ratProduct_polyTime :
    ComputableInPolyTime (List.prod (α := ℚ)) (encList encRat) encRat := by
  have h := foldlWith_of_bounded_growth (step := fun (_ : Bool) (a b : ℚ) => a * b)
    (const false) (id' (encIn := encList encRat)) (const 1)
    (rat_mul.comp ((fst (encPair encBool encRat) encRat).snd'.prod (snd _ _)))
    (growth := fun xs => (encList encRat xs).length) PolyBounded.self
    (fun xs a b hb => (length_encRat_mul_le a b).trans
      (Nat.add_le_add_left (SizedListEncoding.length_elem_le (encA := encRat) xs b hb) _))
  exact h.of_enc_eq fun xs => by simp only [foldProd_eq, one_mul]

/-- Conditional kernel probability by the same joint and fixed affine systems as Stage 1. -/
def conditional (p : MatrixInput × PartialRows) : ℚ :=
  (p.2.map fun r => affine (joint (p.1, r))).prod /
    (p.2.map fun r => affine (fixed p.1.1 r)).prod

theorem conditional_polyTime :
    ComputableInPolyTime conditional conditionalEncoding encRat := by
  have hrs := snd matrixEncoding partialRowsEncoding
  have hinput := fst conditionalEncoding partialRowEncoding
  have hrow := snd conditionalEncoding partialRowEncoding
  have hmat := hinput.fst'
  have hJ := (affine_polyTime.comp joint_polyTime).comp (hmat.prod hrow)
  have hF := (affine_polyTime.comp fixed_polyTime).comp (hmat.fst'.prod hrow)
  have hj := mapWithInput (f := fun (p : MatrixInput × PartialRows) r => affine (joint (p.1, r))) hrs
    (by simpa only [Function.comp_def] using hJ)
  have hf := mapWithInput (f := fun (p : MatrixInput × PartialRows) r => affine (fixed p.1.1 r)) hrs
    (by simpa only [Function.comp_def] using hF)
  exact rat_div' (ratProduct_polyTime.comp hj) (ratProduct_polyTime.comp hf)

private theorem fixed_eq (n : ℕ) (p : PartialRow) :
    affine (fixed n p) = affineProbability
      (FieldHash.fixedMatrix (fun i : Fin n => partialValue p i.val))
      (FieldHash.fixedTarget (fun i : Fin n => partialValue p i.val)) := by
  apply affine_represents (m := n) (n := n) (tabRows_length ..) rfl
  · funext i j
    change cell (tabRows n n (fixedCell p)) i.val j.val =
      Matrix.diagonal (fun k : Fin n => if (partialValue p k.val).isSome then 1 else 0) i j
    rw [tabRows_cell _ _ _ i.isLt j.isLt]
    by_cases h : i = j
    · subst j
      simp [fixedCell]
    · have hv : i.val ≠ j.val := fun e => h (Fin.ext e)
      simp [fixedCell, hv, Matrix.diagonal_apply_ne _ h]
  · funext i
    change ((List.range n).map fun k => (partialValue p k).getD 0).getD i.val 0 =
      (partialValue p i.val).getD 0
    simp [List.getD_eq_getElem?_getD, i.isLt]

theorem joint_matrix (p : MatrixInput) (r : PartialRow) :
    asMatrix (joint (p,r)).1.2 (p.2.length+p.1) p.1 =
      FieldHash.jointMatrix (matrixOf p) (fun i : Fin p.1 => partialValue r i.val) := by
  funext i j
  change cell (tabRows (p.2.length + p.1) p.1
    (fun i j => if i < p.2.length then cell p.2 i j else fixedCell r (i - p.2.length) j))
    i.val j.val = Fin.append (matrixOf p)
      (FieldHash.fixedMatrix (fun k : Fin p.1 => partialValue r k.val)) i j
  rw [tabRows_cell _ _ _ i.isLt j.isLt]
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · have he := Fin.append_left (matrixOf p)
      (FieldHash.fixedMatrix (fun k : Fin p.1 => partialValue r k.val)) a
    rw [congrFun he j]
    simp [a.isLt, matrixOf, asMatrix]
  · have he := Fin.append_right (matrixOf p)
      (FieldHash.fixedMatrix (fun k : Fin p.1 => partialValue r k.val)) a
    rw [congrFun he j]
    simp only [Fin.val_natAdd, Nat.not_lt.mpr (Nat.le_add_right _ _), ite_false,
      Nat.add_sub_cancel_left]
    change fixedCell r a.val j.val = Matrix.diagonal
      (fun k : Fin p.1 => if (partialValue r k.val).isSome then 1 else 0) a j
    by_cases h : a = j
    · subst j
      simp [fixedCell]
    · have hv : a.val ≠ j.val := fun e => h (Fin.ext e)
      simp [fixedCell, hv, Matrix.diagonal_apply_ne _ h]

private theorem joint_eq (p : MatrixInput) (r : PartialRow) :
    affine (joint (p, r)) = affineProbability
      (FieldHash.jointMatrix (matrixOf p) (fun i : Fin p.1 => partialValue r i.val))
      (FieldHash.jointTarget (fun i : Fin p.1 => partialValue r i.val)) := by
  apply affine_represents (m := p.2.length + p.1) (n := p.1) (tabRows_length ..) rfl
  · exact joint_matrix p r
  · funext i
    change (List.replicate p.2.length (0 : F₃) ++ (fixed p.1 r).2).getD i.val 0 =
      Fin.append (fun _ : Fin p.2.length => (0 : F₃))
        (fun a : Fin p.1 => (partialValue r a.val).getD 0) i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append, a.isLt]
    · simp [fixed, List.getD_eq_getElem?_getD, a.isLt]

private theorem prod_map_fin {α : Type} (xs : List α) (f : α → ℚ) (d : α) :
    (xs.map f).prod = ∏ i : Fin xs.length, f (xs.getD i.val d) := by
  rw [← List.prod_ofFn]
  apply congrArg List.prod
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [List.getD_eq_getElem?_getD]

theorem conditional_eq (p : MatrixInput × PartialRows) :
    conditional p = conditionalKernelProbability (matrixOf p.1) (hashOf p.1.1 p.2) := by
  unfold conditional conditionalKernelProbability independentProbability
  rw [prod_map_fin _ _ [], prod_map_fin _ _ []]
  simp only [joint_eq, fixed_eq]
  rfl

#print axioms affine_polyTime
#print axioms affine_eq
#print axioms conditional_polyTime
#print axioms conditional_eq

end DeletionCode.Explicit.Machine.Ternary
