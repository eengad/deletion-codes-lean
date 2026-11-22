import DeletionCode.Explicit.Machine.FibreSolve
import DeletionCode.Explicit.ParameterSavings
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPower

/-! One machine for listing, exposure and closure with a unary Boolean budget. -/
namespace DeletionCode.Explicit.Machine.BooleanFibres

open FieldHash Ternary Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

abbrev BudgetedFibre := ℕ × (MatrixInput × Row)
abbrev budgetedFibreEncoding := encPair encUnary matrixBaseEncoding

private theorem fits_polyTime :
    ComputableInPolyTime (fun x : ℕ × MatrixInput => fits x.1 x.2)
      (encPair encUnary matrixEncoding) encBool := by
  have hn := fst encUnary matrixEncoding
  have hx := snd encUnary matrixEncoding
  have hr := Ternary.rank_polyTime.comp hx
  exact binary_le' (binary_pow.comp ((const (encOut := encNat) 2).prod hr))
    (unary_to_binary.comp hn)

theorem boundedFibre_polyTime :
    ComputableInPolyTime (fun x : BudgetedFibre => boundedFibre x.1 x.2.1 x.2.2)
      budgetedFibreEncoding rowsEncoding := by
  let e := budgetedFibreEncoding
  let k (x : BudgetedFibre) := if fits x.1 x.2.1 then Ternary.rank x.2.1 else 0
  have hn := fst encUnary matrixBaseEncoding
  have hd := snd encUnary matrixBaseEncoding
  have hfit := fits_polyTime.comp (hn.prod hd.fst')
  have hk : ComputableInPolyTime k e encUnary :=
    ite hfit (Ternary.rank_polyTime.comp hd.fst') (const 0)
  have hsize : PolyBounded (fun x : BudgetedFibre => (e x).length) (fun x => x.1) := by
    simpa only [encUnary_apply, List.length_replicate] using hn.polyBounded_length
  have hbudget : PolyBounded (fun x : BudgetedFibre => (e x).length) (fun x => 2^k x) := by
    apply (hsize.add (PolyBounded.const 1)).mono
    intro x
    unfold k
    by_cases h : fits x.1 x.2.1 = true
    · simp only [h, ↓reduceIte]
      exact (show 2^Ternary.rank x.2.1 ≤ x.1 by simpa [fits] using h).trans (Nat.le_succ _)
    · simp [h]
  have hwords := wordsOfLength_polyTime (q := 2) (by decide) hk hbudget
  let ab := encPair e bitWordEncoding
  have hpack : ComputableInPolyTime (fun x : BudgetedFibre × QWord 2 => (x.1.2,x.2)) ab solveEncoding :=
    (hd.comp (fst e bitWordEncoding)).prod (snd e bitWordEncoding)
  have hsolve := solve_polyTime.comp (encIn := ab) (encMid := solveEncoding) hpack
  have hs := mapWithInput (encIn := e) (encA := bitWordEncoding)
    (f := fun x a => solve x.2.1 x.2.2 a) hwords hsolve
  have hkeep := booleanRow_polyTime.comp
    ((hd.fst'.fst'.comp (fst e rowEncoding)).prod (snd e rowEncoding))
  have hrows := filterWithInput (encIn := e) (encA := rowEncoding)
    (test := fun x v => booleanRow x.2.1.1 v) hs hkeep
  have h := ite hfit hrows (const [])
  exact h.of_enc_eq (fun x => by
    apply congrArg rowsEncoding
    by_cases hf : fits x.1 x.2.1 = true <;> simp [boundedFibre,fibreRows,k,hf,pivotRows_length])

abbrev ExposureInput := BudgetedFibre × Row
abbrev exposureEncoding := encPair budgetedFibreEncoding rowEncoding

theorem boundedExposed_polyTime :
    ComputableInPolyTime (fun x : ExposureInput => boundedExposed x.1.1 x.1.2.1 x.1.2.2 x.2)
      exposureEncoding encBool := by
  have hp := fst budgetedFibreEncoding rowEncoding
  have hr := snd budgetedFibreEncoding rowEncoding
  let arg := encPair exposureEncoding rowEncoding
  have hpack : ComputableInPolyTime (fun x : ExposureInput × Row => (x.1.1.2.1.1,(x.2,x.1.2)))
      arg addCheckEncoding :=
    (hp.snd'.fst'.fst'.comp (fst exposureEncoding rowEncoding)).prod
      ((snd exposureEncoding rowEncoding).prod (hr.comp (fst exposureEncoding rowEncoding)))
  have hcheck := booleanAfter_polyTime.comp (encIn := arg) (encMid := addCheckEncoding) hpack
  unfold boundedExposed
  exact anyWithInput (encIn := exposureEncoding) (encA := rowEncoding)
    (test := fun x u => booleanAfter x.1.2.1.1 u x.2) (boundedFibre_polyTime.comp hp) hcheck

abbrev ClosureInput := (ℕ × ℕ) × (Row × Rows)
abbrev closureEncoding := encPair (encPair encUnary encUnary) (encPair rowEncoding rowsEncoding)

private abbrev searchEncoding := encPair closureEncoding rowsEncoding

private theorem boundedChoose_polyTime :
    ComputableInPolyTime (fun x : ClosureInput × Rows => boundedChoose x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2 x.2)
      searchEncoding (encOption rowEncoding) := by
  let arg := encPair searchEncoding rowEncoding
  have hx := (fst closureEncoding rowsEncoding).comp (fst searchEncoding rowEncoding)
  have hac := (snd closureEncoding rowsEncoding).comp (fst searchEncoding rowEncoding)
  have hr := snd searchEncoding rowEncoding
  have hm := hx.fst'.snd'.prod hac
  have hi := independentAdjunction_polyTime.comp (hm.prod hr)
  have he := boundedExposed_polyTime.comp (encIn := arg) (encMid := exposureEncoding)
    ((hx.fst'.fst'.prod (hm.prod hx.snd'.fst')).prod hr)
  unfold boundedChoose
  exact findWithInput (encIn := searchEncoding) (encA := rowEncoding)
    ((fst closureEncoding rowsEncoding).snd'.snd') (bool_and' hi he)

/-- One iteration retains its state when the finite scan finds no rule. -/
def closureStep (x : ClosureInput) (acc : Rows) : Rows :=
  (boundedChoose x.1.1 x.1.2 x.2.1 x.2.2 acc).elim acc (fun r => r :: acc)

private theorem closureStep_polyTime :
    ComputableInPolyTime (fun x : ClosureInput × Rows => closureStep x.1 x.2)
      searchEncoding rowsEncoding := by
  have ha := snd closureEncoding rowsEncoding
  have hp := fst searchEncoding rowEncoding
  exact optionElimWithInput (body := fun x r => r :: x.2) boundedChoose_polyTime ha
    (cons' (snd searchEncoding rowEncoding) (ha.comp hp))

private theorem closureStep_some_mem {x : ClosureInput} {acc : Rows} {r : Row}
    (he : boundedChoose x.1.1 x.1.2 x.2.1 x.2.2 acc = some r) : r ∈ x.2.2 := by
  obtain ⟨_,j,hj,hget,_⟩ := List.find?_eq_some_iff_getElem.mp he
  exact hget ▸ List.getElem_mem hj

private theorem closureStep_iterate (x : ClosureInput) (acc : Rows) (fuel : ℕ) :
    (closureStep x)^[fuel] acc = greedyRows (boundedChoose x.1.1 x.1.2 x.2.1 x.2.2) fuel acc := by
  induction fuel generalizing acc with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, greedyRows]
    cases he : boundedChoose x.1.1 x.1.2 x.2.1 x.2.2 acc with
    | none =>
      have hs : closureStep x acc = acc := by simp [closureStep,he]
      rw [hs, Function.iterate_fixed hs]
    | some r =>
      have hs : closureStep x acc = r :: acc := by simp [closureStep,he]
      rw [hs,ih]

theorem closureRows_polyTime :
    ComputableInPolyTime (fun x : ClosureInput => closureRows x.1.1 x.1.2 x.2.1 x.2.2)
      closureEncoding rowsEncoding := by
  let e := closureEncoding
  have hd := fst (encPair encUnary encUnary) (encPair rowEncoding rowsEncoding)
  have hr := (snd (encPair encUnary encUnary) (encPair rowEncoding rowsEncoding)).snd'
  have hn := unary_add' hd.snd' (const 1)
  have hn' : PolyBounded (fun x : ClosureInput => (e x).length) (fun x => x.1.2 + 1) := by
    simpa only [encUnary_apply, List.length_replicate] using hn.polyBounded_length
  have hsize := hn'.mul (((PolyBounded.const 2).mul hr.polyBounded_length).add (PolyBounded.const 1))
  let inv (x : ClosureInput) (i : ℕ) (acc : Rows) := acc.length ≤ i ∧ ∀ r ∈ acc, r ∈ x.2.2
  have hpres : ∀ x i acc, i < x.1.2+1 → inv x i acc → inv x (i+1) (closureStep x acc) := by
    intro x i acc _ h
    unfold closureStep
    cases he : boundedChoose x.1.1 x.1.2 x.2.1 x.2.2 acc with
    | none => exact ⟨h.1.trans (Nat.le_succ _),h.2⟩
    | some r =>
      have hm := closureStep_some_mem he
      refine ⟨Nat.succ_le_succ h.1, ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hm
      · exact h.2 _ ha
  have h := (iterateWith_spec (step := closureStep) id' hn (const []) closureStep_polyTime inv
    (fun _ => by simp [inv]) hpres hsize (fun x i acc hi h => by
      apply (length_encList_le rowEncoding acc (b := (rowsEncoding x.2.2).length) ?_).trans
        (Nat.mul_le_mul_right _ (h.1.trans hi))
      intro r hr'
      exact SizedListEncoding.length_elem_le x.2.2 r (h.2 _ hr'))).1
  exact h.of_enc_eq (fun x => congrArg rowsEncoding (closureStep_iterate x [] (x.1.2+1)).symm)

open _root_.DeletionCode.Explicit.UniformParameters in
theorem closureRows_uniform_eq (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : minLength q b t ≤ ℓ) (cols : Fin n ≃ Qary.SignedSupport.Gram (Fin q) L)
    (v : Row) (rules : Rows)
    (hr : Module.finrank F₃ (BooleanClosure.closure (rulesSet cols rules) (onGrams cols v)) ≤
      componentCutoff q b t ℓ) :
    gramSpan cols (closureRows ℓ n v rules) = BooleanClosure.closure (rulesSet cols rules) (onGrams cols v) := by
  have hB : 0 < reciprocal q b t := by
    unfold reciprocal edits
    have hpos : 0 < t := by omega
    positivity
  apply closureRows_eq
  refine (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hr).trans ?_
  have hp : 2 ^ componentCutoff q b t ℓ ≤ (2 ^ componentCutoff q b t ℓ) ^ reciprocal q b t := by
    conv_lhs => rw [← pow_one (2 ^ componentCutoff q b t ℓ)]
    exact Nat.pow_le_pow_right (by positivity) hB
  exact hp.trans (boolean_budget hq hb ht hstart)

#print axioms boundedFibre_polyTime
#print axioms boundedExposed_polyTime
#print axioms closureRows_polyTime
#print axioms closureRows_uniform_eq

end DeletionCode.Explicit.Machine.BooleanFibres
