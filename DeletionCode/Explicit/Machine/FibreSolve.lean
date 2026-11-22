import DeletionCode.Explicit.FibreListing
import DeletionCode.Explicit.FibreExposure
import DeletionCode.Explicit.Machine.WordEnumeration

/-! Uniform machines for pivot selection and reconstruction. -/
namespace DeletionCode.Explicit.Machine.BooleanFibres

open FieldHash Ternary Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

abbrev bitEncoding : Fin 2 ↪ List Bool :=
  ⟨fun a => encUnary a.val, fun _ _ h => Fin.ext (encUnary.injective h)⟩

abbrev bitWordEncoding := wordEncoding 2
abbrev coefficientEncoding := encPair encUnary tritEncoding
abbrev coefficientsEncoding := encList coefficientEncoding

abbrev PivotSearch := MatrixInput × ℕ
abbrev pivotSearchEncoding := encPair matrixEncoding encUnary

private theorem ownsPivot_polyTime :
    ComputableInPolyTime (fun x : PivotSearch × ℕ => ownsPivot x.1.1 x.1.2 x.2)
      (encPair pivotSearchEncoding encUnary) encBool := by
  let e := encPair pivotSearchEncoding encUnary
  have hx := fst pivotSearchEncoding encUnary
  have hj := snd pivotSearchEncoding encUnary
  have hi := hx.snd'
  have hrows := hx.fst'.snd'
  have hread := cell_polyTime hrows hi hj
  have hp := fst e encUnary
  have hk := snd e encUnary
  have hcheck := bool_or' (hk.decide_eq' (hi.comp hp))
    ((cell_polyTime (hrows.comp hp) hk (hj.comp hp)).decide_eq' (const 0))
  have hall := allWithInput (encIn := e) (encA := encUnary)
    (test := fun x k => decide (k = x.1.2) || decide (cell x.1.1.2 k x.2 = 0))
    (unary_range' ((length_list rowEncoding).comp hrows)) hcheck
  exact bool_and' (bool_not.comp (hread.decide_eq' (const 0))) hall

theorem pivotColumn_polyTime :
    ComputableInPolyTime (fun x : PivotSearch => pivotColumn x.1 x.2)
      pivotSearchEncoding (encOption encUnary) := by
  unfold pivotColumn
  exact findWithInput (encIn := pivotSearchEncoding) (encA := encUnary)
    (test := fun x j => ownsPivot x.1 x.2 j) (unary_range' (fst matrixEncoding encUnary).fst')
    ownsPivot_polyTime

theorem pivotRows_polyTime : ComputableInPolyTime pivotRows matrixEncoding (encList encUnary) := by
  unfold pivotRows
  exact filterWithInput (encIn := matrixEncoding) (encA := encUnary)
    (test := fun x i => (pivotColumn x i).isSome)
    (unary_range' ((length_list rowEncoding).comp (snd encUnary rowsEncoding)))
    (optionIsSome pivotColumn_polyTime)

theorem prepare_polyTime : ComputableInPolyTime prepare matrixEncoding matrixEncoding :=
  (fst encUnary rowsEncoding).prod reducedRows_polyTime

abbrev SolveInput := (MatrixInput × Row) × QWord 2
abbrev matrixBaseEncoding := encPair matrixEncoding rowEncoding
abbrev solveEncoding := encPair matrixBaseEncoding bitWordEncoding

private theorem coefficient_polyTime :
    ComputableInPolyTime (fun x : SolveInput × ℕ => coefficient x.1.1.1 x.1.1.2 x.1.2 x.2)
      (encPair solveEncoding encUnary) coefficientEncoding := by
  let e := encPair solveEncoding encUnary
  have hp := fst solveEncoding encUnary
  have hk := snd solveEncoding encUnary
  have hx := hp.fst'.fst'
  have hv := hp.fst'.snd'
  have ha := hp.snd'
  have hs := pivotRows_polyTime.comp hx
  have hi := listGetDWithInput hs hk 0
  have hsearch : ComputableInPolyTime (fun x : SolveInput × ℕ =>
      (x.1.1.1, (pivotRows x.1.1.1).getD x.2 0)) e pivotSearchEncoding := hx.prod hi
  have hj := optionGetDWithInput
    (pivotColumn_polyTime.comp (encIn := e) (encMid := pivotSearchEncoding) hsearch) (const 0)
  have hb := (of_finite (encIn := bitEncoding) (encOut := tritEncoding) bitTrit).comp
    (listGetDWithInput ha hk (0 : Fin 2))
  have hval := listGetDWithInput hv hj 0
  have hz := cell_polyTime hx.snd' hi hj
  have hcoef : ComputableInPolyTime (fun z : (F₃ × F₃) × F₃ => (z.1.1-z.1.2)/z.2)
      (encPair (encPair tritEncoding tritEncoding) tritEncoding) tritEncoding := of_finite _
  let trits := encPair (encPair tritEncoding tritEncoding) tritEncoding
  have hpack : ComputableInPolyTime (fun x : SolveInput × ℕ =>
      let i := (pivotRows x.1.1.1).getD x.2 0
      let j := (pivotColumn x.1.1.1 i).getD 0
      ((bitTrit (x.1.2.getD x.2 0),x.1.1.2.getD j 0),cell x.1.1.1.2 i j)) e trits :=
    (hb.prod hval).prod hz
  have hquot := hcoef.comp (encIn := e) (encMid := trits) hpack
  exact (hi.prod hquot).of_enc_eq (fun _ => rfl)

private theorem coefficients_polyTime :
    ComputableInPolyTime (fun x : SolveInput => coefficients x.1.1 x.1.2 x.2)
      solveEncoding coefficientsEncoding := by
  have hx := (fst matrixBaseEncoding bitWordEncoding).fst'
  have hr := (length_list encUnary).comp (pivotRows_polyTime.comp hx)
  unfold coefficients
  exact mapWithInput (encIn := solveEncoding) (encA := encUnary)
    (f := fun x k => coefficient x.1.1 x.1.2 x.2 k) (unary_range' hr) coefficient_polyTime

private theorem addTrit_polyTime : ComputableInPolyTime (fun x : F₃ × F₃ => x.1 + x.2)
    (encPair tritEncoding tritEncoding) tritEncoding := of_finite _

private theorem tritSum_polyTime : ComputableInPolyTime (List.sum (α := F₃)) rowEncoding tritEncoding := by
  have hb : ∀ a : F₃, (tritEncoding a).length ≤ 10 := by decide
  have hf := foldlWith_of_bounded_growth (step := fun (_ : Bool) (a b : F₃) => a + b)
    (const false) (id' (encIn := rowEncoding)) (const 0)
    (addTrit_polyTime.comp ((fst (encPair encBool tritEncoding) tritEncoding).snd'.prod (snd _ _)))
    (growth := fun _ => 10) (PolyBounded.const 10)
    (fun _ _ _ _ => (hb _).trans (Nat.le_add_left _ _))
  exact hf.of_enc_eq (fun xs => congrArg tritEncoding (by
    have h (a : F₃) (ys : List F₃) : ys.foldl (· + ·) a = a + ys.sum := by
      induction ys generalizing a with
      | nil => simp
      | cons x ys ih => simp [ih, add_assoc]
    simp [h]))

abbrev ReconstructInput := (MatrixInput × Row) × Coefficients
abbrev reconstructEncoding := encPair matrixBaseEncoding coefficientsEncoding

private theorem reconstructAt_polyTime :
    ComputableInPolyTime (fun x : ReconstructInput × ℕ => x.1.1.2.getD x.2 0 +
      (x.1.2.map (fun c => c.2 * cell x.1.1.1.2 c.1 x.2)).sum)
      (encPair reconstructEncoding encUnary) tritEncoding := by
  let src := encPair reconstructEncoding encUnary
  have hp := fst reconstructEncoding encUnary
  have hj := snd reconstructEncoding encUnary
  have hl := hp.fst'.fst'.snd'
  have hv := listGetDWithInput hp.fst'.snd' hj 0
  have hi := fst src coefficientEncoding
  have hc := snd src coefficientEncoding
  have hmul : ComputableInPolyTime (fun x : F₃ × F₃ => x.1 * x.2)
      (encPair tritEncoding tritEncoding) tritEncoding := of_finite _
  have hrow := cell_polyTime (hl.comp hi) hc.fst' (hj.comp hi)
  let trits := encPair tritEncoding tritEncoding
  let arg := encPair src coefficientEncoding
  have hpair : ComputableInPolyTime (fun p : (ReconstructInput × ℕ) × (ℕ × F₃) =>
      (p.2.2,cell p.1.1.1.1.2 p.2.1 p.1.2)) arg trits := hc.snd'.prod hrow
  have hprod := hmul.comp (encIn := arg) (encMid := trits) hpair
  have hm := mapWithInput (encIn := src) (encA := coefficientEncoding)
    (f := fun x c => c.2 * cell x.1.1.1.2 c.1 x.2) hp.snd' hprod
  have hs := tritSum_polyTime.comp (encIn := src) (encMid := rowEncoding) hm
  exact (addTrit_polyTime.comp (encIn := src) (encMid := trits) (hv.prod hs)).of_enc_eq (fun _ => rfl)

private theorem reconstruct_polyTime :
    ComputableInPolyTime (fun x : ReconstructInput => reconstruct x.1.1 x.1.2 x.2)
      reconstructEncoding rowEncoding := by
  have hi := fst matrixBaseEncoding coefficientsEncoding
  unfold reconstruct
  exact mapWithInput (encIn := reconstructEncoding) (encA := encUnary)
    (unary_range' hi.fst'.fst') reconstructAt_polyTime

theorem solve_polyTime :
    ComputableInPolyTime (fun x : SolveInput => solve x.1.1 x.1.2 x.2) solveEncoding rowEncoding := by
  have hp := fst matrixBaseEncoding bitWordEncoding
  have ha := snd matrixBaseEncoding bitWordEncoding
  have hbase := (prepare_polyTime.comp hp.fst').prod hp.snd'
  let src := solveEncoding
  have hc := coefficients_polyTime.comp (encIn := src) (encMid := solveEncoding) (hbase.prod ha)
  have hpack : ComputableInPolyTime (fun x : SolveInput =>
      ((prepare x.1.1,x.1.2),coefficients (prepare x.1.1) x.1.2 x.2)) src reconstructEncoding :=
    hbase.prod hc
  exact (reconstruct_polyTime.comp (encIn := src) (encMid := reconstructEncoding) hpack).of_enc_eq
    (fun _ => rfl)

private theorem binaryTrit_polyTime :
    ComputableInPolyTime (fun x : F₃ => decide (x = 0) || decide (x = 1)) tritEncoding encBool := of_finite _

theorem booleanRow_polyTime :
    ComputableInPolyTime (fun x : ℕ × Row => booleanRow x.1 x.2)
      (encPair encUnary rowEncoding) encBool := by
  let e := encPair encUnary rowEncoding
  have hw := (snd encUnary rowEncoding).comp (fst e encUnary)
  have hj := snd e encUnary
  unfold booleanRow
  exact allWithInput (encIn := e) (encA := encUnary)
    (unary_range' (fst encUnary rowEncoding)) (binaryTrit_polyTime.comp (listGetDWithInput hw hj 0))

abbrev AddCheck := ℕ × (Row × Row)
abbrev addCheckEncoding := encPair encUnary (encPair rowEncoding rowEncoding)

theorem booleanAfter_polyTime :
    ComputableInPolyTime (fun x : AddCheck => booleanAfter x.1 x.2.1 x.2.2) addCheckEncoding encBool := by
  have hs := (snd encUnary (encPair rowEncoding rowEncoding)).comp (fst addCheckEncoding encUnary)
  have hj := snd addCheckEncoding encUnary
  have hp := listGetDWithInput hs.fst' hj 0
  have hr := listGetDWithInput hs.snd' hj 0
  let src := encPair addCheckEncoding encUnary
  let trits := encPair tritEncoding tritEncoding
  have hsum := addTrit_polyTime.comp (encIn := src) (encMid := trits) (hp.prod hr)
  have hcheck := binaryTrit_polyTime.comp (encIn := src) (encMid := tritEncoding) hsum
  unfold booleanAfter
  dsimp only
  exact allWithInput (encIn := addCheckEncoding) (encA := encUnary)
    (unary_range' (fst encUnary (encPair rowEncoding rowEncoding))) hcheck

#print axioms pivotColumn_polyTime
#print axioms solve_polyTime
#print axioms booleanAfter_polyTime

end DeletionCode.Explicit.Machine.BooleanFibres
