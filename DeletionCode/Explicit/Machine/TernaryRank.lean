import DeletionCode.Explicit.FieldHash
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.ZMod

/-! Row-major ternary matrices and a uniform Gauss–Jordan machine certificate. -/
set_option maxHeartbeats 500000

namespace DeletionCode.Explicit.Machine.Ternary

open FieldHash Matrix.GaussJordan
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

abbrev Row := List F₃
abbrev Rows := List Row

/-- The width is explicit, also for matrices with no rows. Missing cells
read as zero, and columns beyond the declared width are ignored. -/
abbrev MatrixInput := ℕ × Rows

abbrev tritEncoding : F₃ ↪ List Bool := encZMod 3
abbrev rowEncoding := encList tritEncoding
abbrev rowsEncoding := encList rowEncoding
abbrev matrixEncoding := encPair encUnary rowsEncoding

def cell (xs : Rows) (i j : ℕ) : F₃ := (xs.getD i []).getD j 0

def asMatrix (xs : Rows) (m n : ℕ) : TernaryMatrix m n :=
  fun i j => cell xs i.val j.val

def matrixOf (x : MatrixInput) : TernaryMatrix x.2.length x.1 :=
  asMatrix x.2 x.2.length x.1

theorem cell_polyTime {α : Type} {enc : α ↪ List Bool} {xs : α → Rows} {i j : α → ℕ}
    (hxs : ComputableInPolyTime xs enc rowsEncoding)
    (hi : ComputableInPolyTime i enc encUnary) (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun a => cell (xs a) (i a) (j a)) enc tritEncoding :=
  listGetDWithInput (listGetDWithInput hxs hi []) hj 0

def tabRows (m n : ℕ) (f : ℕ → ℕ → F₃) : Rows :=
  (List.range m).map fun i => (List.range n).map fun j => f i j

theorem tabRows_polyTime {α : Type} {enc : α ↪ List Bool} {m n : α → ℕ}
    {f : α → ℕ → ℕ → F₃}
    (hm : ComputableInPolyTime m enc encUnary) (hn : ComputableInPolyTime n enc encUnary)
    (hf : ComputableInPolyTime (fun p : (α × ℕ) × ℕ => f p.1.1 p.1.2 p.2)
      (encPair (encPair enc encUnary) encUnary) tritEncoding) :
    ComputableInPolyTime (fun a => tabRows (m a) (n a) (f a)) enc rowsEncoding :=
  mapWithInput (f := fun a i => (List.range (n a)).map (f a i)) (unary_range' hm)
    (mapWithInput (f := fun p j => f p.1 p.2 j)
      (unary_range' (hn.comp (fst enc encUnary))) hf)

@[simp] theorem tabRows_length (m n : ℕ) (f : ℕ → ℕ → F₃) :
    (tabRows m n f).length = m := by simp [tabRows]

theorem tabRows_row_length {m n : ℕ} {f : ℕ → ℕ → F₃} {v : Row}
    (hv : v ∈ tabRows m n f) : v.length = n := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
  simp

private theorem getD_map_range {α : Type} (f : ℕ → α) (d : α) {i k : ℕ} (hi : i < k) :
    ((List.range k).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem tabRows_cell (m n : ℕ) (f : ℕ → ℕ → F₃) {i j : ℕ}
    (hi : i < m) (hj : j < n) : cell (tabRows m n f) i j = f i j := by
  unfold cell tabRows
  rw [getD_map_range _ _ hi, getD_map_range _ _ hj]

private def zeroBefore (xs : Rows) (j i : ℕ) : Bool :=
  (List.range j).all fun k => decide (cell xs i k = 0)

private def eligible (xs : Rows) (j i : ℕ) : Bool :=
  zeroBefore xs j i && decide (cell xs i j ≠ 0)

private theorem eligible_polyTime :
    ComputableInPolyTime (fun p : (ℕ × Rows) × ℕ => eligible p.1.2 p.1.1 p.2)
      (encPair (encPair encUnary rowsEncoding) encUnary) encBool := by
  let e := encPair (encPair encUnary rowsEncoding) encUnary
  have hp := fst (encPair encUnary rowsEncoding) encUnary
  have hj := hp.fst'
  have hxs := hp.snd'
  have hi := snd (encPair encUnary rowsEncoding) encUnary
  have hz : ComputableInPolyTime (fun p : (ℕ × Rows) × ℕ => zeroBefore p.1.2 p.1.1 p.2)
      e encBool := by
    unfold zeroBefore
    exact allWith (par := id) (test := fun p => decide (cell p.1.1.2 p.1.2 p.2 = 0))
      ((cell_polyTime (hxs.comp (fst e encUnary)) (hi.comp (fst e encUnary))
        (snd e encUnary)).decide_eq' (const 0)) id' (unary_range' hj)
  have hne := (cell_polyTime hxs hi hj).decide_ne (const 0)
  exact (of_finite (encIn := encPair encBool encBool) (encOut := encBool)
    (fun p : Bool × Bool => p.1 && p.2)).comp (hz.prod hne)

private def pivot (p : ℕ × Rows) : Option ℕ :=
  (List.range p.2.length).find? (eligible p.2 p.1)

private theorem pivot_polyTime :
    ComputableInPolyTime pivot (encPair encUnary rowsEncoding) (encOption encUnary) :=
  findWithInput (test := fun (p : ℕ × Rows) i => eligible p.2 p.1 i)
    (unary_range' ((length_list rowEncoding).comp (snd encUnary rowsEncoding))) eligible_polyTime

private theorem zeroBefore_iff {xs : Rows} {m n : ℕ} (i : Fin m) (j : Fin n) :
    zeroBefore xs j.val i.val = true ↔ IsFreeBefore (asMatrix xs m n) j.val i := by
  simp only [zeroBefore, List.all_eq_true, List.mem_range, decide_eq_true_eq, IsFreeBefore, asMatrix]
  constructor
  · intro h k hk
    exact h k.val hk
  · intro h k hk
    exact h ⟨k, hk.trans j.isLt⟩ hk

private theorem eligible_iff {xs : Rows} {m n : ℕ} (i : Fin m) (j : Fin n) :
    eligible xs j.val i.val = true ↔
      IsFreeBefore (asMatrix xs m n) j.val i ∧ asMatrix xs m n i j ≠ 0 := by
  simp only [eligible, Bool.and_eq_true, zeroBefore_iff i j, decide_eq_true_eq, asMatrix]

private theorem pivot_none {xs : Rows} {n : ℕ} (j : Fin n) (h : pivot (j.val, xs) = none) :
    pivotRow (asMatrix xs xs.length n) j = none := by
  apply pivotRow_eq_none_iff.mpr
  intro i hfree
  by_contra hne
  have hel := (eligible_iff i j).mpr ⟨hfree, hne⟩
  exact List.find?_eq_none.mp h i.val (List.mem_range.mpr i.isLt) hel

private theorem pivot_some {xs : Rows} {n k : ℕ} (j : Fin n) (h : pivot (j.val, xs) = some k)
    (hk : k < xs.length) : pivotRow (asMatrix xs xs.length n) j = some ⟨k, hk⟩ := by
  obtain ⟨hel, i, hi, hik, hfirst⟩ := List.find?_eq_some_iff_getElem.mp h
  have hki : i = k := by simpa using hik
  have hgood := (eligible_iff (⟨k, hk⟩ : Fin xs.length) j).mp hel
  apply pivotRow_eq_some_iff.mpr
  refine ⟨hgood.1, hgood.2, fun l hl hfree => ?_⟩
  by_contra hne
  change l.val < k at hl
  have hbad := hfirst l.val (by omega : l.val < i)
  have hyes := (eligible_iff l j).mpr ⟨hfree, hne⟩
  simp [hyes] at hbad

private def eliminateRows (n j : ℕ) (xs : Rows) (p : ℕ) : Rows :=
  tabRows xs.length n fun i l =>
    if i = p then cell xs i l else cell xs i l - cell xs i j / cell xs p j * cell xs p l

private abbrev stepEncoding := encPair (encPair encUnary rowsEncoding) encUnary

private theorem eliminateRows_polyTime :
    ComputableInPolyTime (fun a : ((ℕ × Rows) × ℕ) × ℕ => eliminateRows a.1.2 a.1.1.1 a.1.1.2 a.2)
      (encPair stepEncoding encUnary) rowsEncoding := by
  let e := encPair stepEncoding encUnary
  have hp := fst stepEncoding encUnary
  unfold eliminateRows
  refine tabRows_polyTime
    (f := fun a i l => if i = a.2 then cell a.1.1.2 i l
      else cell a.1.1.2 i l - cell a.1.1.2 i a.1.1.1 / cell a.1.1.2 a.2 a.1.1.1 * cell a.1.1.2 a.2 l)
    ((length_list rowEncoding).comp hp.fst'.snd') hp.snd' ?_
  have h := (fst e encUnary).comp (fst (encPair e encUnary) encUnary)
  have hi := (snd e encUnary).comp (fst (encPair e encUnary) encUnary)
  have hl := snd (encPair e encUnary) encUnary
  have hxs := h.fst'.fst'.snd'
  have hj := h.fst'.fst'.fst'
  have hpivot := h.snd'
  have hcell := cell_polyTime hxs hi hl
  have hop : ComputableInPolyTime (fun x : F₃ × F₃ × F₃ × F₃ => x.1 - x.2.1 / x.2.2.1 * x.2.2.2)
      (encPair tritEncoding (encPair tritEncoding (encPair tritEncoding tritEncoding))) tritEncoding :=
    of_finite _
  have hc := hcell.prod ((cell_polyTime hxs hi hj).prod
    ((cell_polyTime hxs hpivot hj).prod (cell_polyTime hxs hpivot hl)))
  have hout := ite_decide (hi.decide_eq' hpivot) hcell (hop.comp hc)
  simpa only [Function.comp_def] using hout

private def stageRows (n j : ℕ) (xs : Rows) : Rows :=
  (pivot (j, xs)).elim xs (eliminateRows n j xs)

private theorem stageRows_polyTime :
    ComputableInPolyTime (fun p : (ℕ × Rows) × ℕ => stageRows p.2 p.1.1 p.1.2)
      stepEncoding rowsEncoding := by
  have hpair := fst (encPair encUnary rowsEncoding) encUnary
  exact optionElimWithInput (pivot_polyTime.comp hpair) hpair.snd'
    (body := fun (p : (ℕ × Rows) × ℕ) i => eliminateRows p.2 p.1.1 p.1.2 i)
    eliminateRows_polyTime

private theorem stageRows_shape (n j : ℕ) (xs : Rows)
    (hrows : ∀ v ∈ xs, v.length = n) :
    (stageRows n j xs).length = xs.length ∧ ∀ v ∈ stageRows n j xs, v.length = n := by
  unfold stageRows
  cases pivot (j, xs) with
  | none => exact ⟨rfl, hrows⟩
  | some i => exact ⟨tabRows_length .., fun _ h => tabRows_row_length h⟩

private theorem stageRows_eq (xs : Rows) (m n : ℕ) (hm : xs.length = m) (j : Fin n) :
    asMatrix (stageRows n j.val xs) m n = stage (asMatrix xs m n) j := by
  subst m
  unfold stageRows
  cases hp : pivot (j.val, xs) with
  | none => rw [stage_of_pivotRow_eq_none (pivot_none j hp)]; rfl
  | some p =>
    have hmem := List.mem_of_find?_eq_some hp
    have hp' : p < xs.length := List.mem_range.mp hmem
    rw [stage_of_pivotRow_eq_some (pivot_some j hp hp')]
    funext i l
    change cell (eliminateRows n j.val xs p) i.val l.val = _
    rw [eliminateRows, tabRows_cell _ _ _ i.isLt l.isLt]
    by_cases h : i.val = p
    · have hi : i = ⟨p, hp'⟩ := Fin.ext h
      simp only [h, ite_true]
      rw [hi, eliminate_apply_self]
      rfl
    · have hi : i ≠ ⟨p, hp'⟩ := fun e => h (congrArg Fin.val e)
      simp only [h, ite_false]
      rw [eliminate_apply_of_ne hi]
      rfl

private def normalized (x : MatrixInput) := tabRows x.2.length x.1 (cell x.2)

private theorem normalized_polyTime : ComputableInPolyTime normalized matrixEncoding rowsEncoding := by
  have hxs := snd encUnary rowsEncoding
  have hp := fst (encPair matrixEncoding encUnary) encUnary
  exact tabRows_polyTime ((length_list rowEncoding).comp hxs) (fst encUnary rowsEncoding)
    (cell_polyTime (hxs.comp ((fst matrixEncoding encUnary).comp hp))
      ((snd matrixEncoding encUnary).comp hp) (snd (encPair matrixEncoding encUnary) encUnary))

private def reductionStep (n : ℕ) (p : ℕ × Rows) : ℕ × Rows :=
  (p.1 + 1, stageRows n p.1 p.2)

def reducedRows (x : MatrixInput) : Rows :=
  ((reductionStep x.1)^[x.1] (0, normalized x)).2

private def tritMaxBits : ℕ := ∑ a : F₃, (tritEncoding a).length

private theorem tritBits_le (a : F₃) : (tritEncoding a).length ≤ tritMaxBits :=
  Finset.single_le_sum (f := fun a : F₃ => (tritEncoding a).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

private def inv (x : MatrixInput) (i : ℕ) (p : ℕ × Rows) : Prop :=
  p.1 = i ∧ p.2.length = x.2.length ∧ (∀ v ∈ p.2, v.length = x.1) ∧
    asMatrix p.2 x.2.length x.1 = reduceUpTo (matrixOf x) i

private theorem reductionMachine :
    ComputableInPolyTime reducedRows matrixEncoding rowsEncoding ∧
    ∀ x, inv x x.1 ((reductionStep x.1)^[x.1] (0, normalized x)) := by
  let encState := encPair encUnary rowsEncoding
  have hn := fst encUnary rowsEncoding
  have hrows := snd encUnary rowsEncoding
  have hm := (length_list rowEncoding).comp hrows
  have hsizeMachine := unary_add' (unary_add' (unary_mul' (const 2) hn) (const 1))
    (unary_mul' hm (unary_add' (unary_mul' (const 2)
      (unary_mul' hn (const (2 * tritMaxBits + 1)))) (const 1)))
  have hsize : PolyBounded (fun x : MatrixInput => (matrixEncoding x).length)
      (fun x => 2 * x.1 + 1 + x.2.length * (2 * (x.1 * (2 * tritMaxBits + 1)) + 1)) := by
    simpa only [Function.comp_def, encUnary_apply, List.length_replicate] using hsizeMachine.polyBounded_length
  have hstep : ComputableInPolyTime (fun p : ℕ × (ℕ × Rows) => reductionStep p.1 p.2)
      (encPair encUnary encState) encState := by
    have hp := snd encUnary encState
    have hs := stageRows_polyTime.comp (hp.prod (fst encUnary encState))
    have ht := (unary_add' hp.fst' (const 1)).prod hs
    change ComputableInPolyTime
      (fun p : ℕ × (ℕ × Rows) => (p.2.1 + 1, stageRows p.1 p.2.1 p.2.2))
      (encPair encUnary encState) encState
    simpa only [Function.comp_def] using ht
  have hbase (x : MatrixInput) : inv x 0 (0, normalized x) := by
    refine ⟨rfl, tabRows_length .., fun _ h => tabRows_row_length h, ?_⟩
    funext i j
    exact tabRows_cell _ _ _ i.isLt j.isLt
  have hpres (x : MatrixInput) (i : ℕ) (p : ℕ × Rows) (hi : i < x.1) (h : inv x i p) :
      inv x (i + 1) (reductionStep x.1 p) := by
    obtain ⟨hidx, hcount, hrows, hmat⟩ := h
    have shape := stageRows_shape x.1 p.1 p.2 hrows
    refine ⟨by simp [reductionStep, hidx], shape.1.trans hcount, shape.2, ?_⟩
    change asMatrix (stageRows x.1 p.1 p.2) x.2.length x.1 = _
    rw [hidx, stageRows_eq p.2 x.2.length x.1 hcount ⟨i, hi⟩, hmat, reduceUpTo_succ_of_lt _ hi]
  have hbound (x : MatrixInput) (i : ℕ) (p : ℕ × Rows) (hi : i ≤ x.1) (h : inv x i p) :
      (encState p).length ≤ 2 * x.1 + 1 + x.2.length * (2 * (x.1 * (2 * tritMaxBits + 1)) + 1) := by
    obtain ⟨hidx, hcount, hrows, _⟩ := h
    have hlen : (rowsEncoding p.2).length ≤
        x.2.length * (2 * (x.1 * (2 * tritMaxBits + 1)) + 1) := by
      rw [← hcount]
      apply length_encList_le
      intro w hw
      rw [← hrows w hw]
      exact length_encList_le _ _ (fun a _ => tritBits_le a)
    rw [length_encPair, encUnary_apply, List.length_replicate, hidx]
    omega
  obtain ⟨hM, hcorrect⟩ := iterateWith_spec hn hn ((const 0).prod normalized_polyTime)
    hstep inv hbase hpres hsize hbound
  exact ⟨hM.snd', hcorrect⟩

theorem reducedRows_polyTime : ComputableInPolyTime reducedRows matrixEncoding rowsEncoding :=
  reductionMachine.1

theorem reducedRows_length (x : MatrixInput) : (reducedRows x).length = x.2.length :=
  (reductionMachine.2 x).2.1

theorem reducedRows_eq (x : MatrixInput) :
    asMatrix (reducedRows x) x.2.length x.1 = reduce (matrixOf x) :=
  (reductionMachine.2 x).2.2.2

private def nonzeroRow (n : ℕ) (xs : Rows) (i : ℕ) : Bool :=
  (List.range n).any fun j => decide (cell xs i j ≠ 0)

private theorem nonzeroRow_iff {xs : Rows} {m n : ℕ} (i : Fin m) :
    nonzeroRow n xs i.val = true ↔ (asMatrix xs m n).row i ≠ 0 := by
  classical
  simp only [nonzeroRow, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, hne⟩ heq
    exact hne (congrFun heq ⟨j, hj⟩)
  · intro hne
    by_contra! h
    exact hne (funext fun j => h j.val j.isLt)

def rank (x : MatrixInput) : ℕ :=
  (List.range x.2.length).countP (nonzeroRow x.1 (reducedRows x))

private theorem countRows_polyTime :
    ComputableInPolyTime (fun p : MatrixInput => (List.range p.2.length).countP (nonzeroRow p.1 p.2))
      matrixEncoding encUnary := by
  have hm := (length_list rowEncoding).comp (snd encUnary rowsEncoding)
  apply countPWithInput (test := fun (p : MatrixInput) i => nonzeroRow p.1 p.2 i) (unary_range' hm)
  let e := encPair matrixEncoding encUnary
  have hp := fst matrixEncoding encUnary
  have hn := (fst encUnary rowsEncoding).comp hp
  unfold nonzeroRow
  have h0 := (cell_polyTime ((snd encUnary rowsEncoding).comp (hp.comp (fst e encUnary)))
    ((snd matrixEncoding encUnary).comp (fst e encUnary)) (snd e encUnary)).decide_ne (const 0)
  exact anyWithInput (test := fun (p : MatrixInput × ℕ) j => decide (cell p.1.2 p.2 j ≠ 0))
    (unary_range' hn) h0

theorem rank_polyTime : ComputableInPolyTime rank matrixEncoding encUnary :=
  (countRows_polyTime.comp ((fst encUnary rowsEncoding).prod reducedRows_polyTime)).of_enc_eq
    (fun x => by simp only [Function.comp_def, rank, reducedRows_length])

theorem rank_eq (x : MatrixInput) : rank x = ternaryRank (matrixOf x) := by
  classical
  let B := asMatrix (reducedRows x) x.2.length x.1
  let f : ℕ → Bool := nonzeroRow x.1 (reducedRows x)
  have hset : ((List.range x.2.length).filter f).toFinset =
      (Finset.univ.filter fun i : Fin x.2.length => B.row i ≠ 0).map Fin.valEmbedding := by
    ext i
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_map,
      Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨hi, hf⟩
      exact ⟨⟨i, hi⟩, (nonzeroRow_iff _).mp hf, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.isLt, (nonzeroRow_iff i).mpr hi⟩
  change (List.range x.2.length).countP f = _
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (List.nodup_range.filter _), hset, Finset.card_map,
    ternaryRank_eq]
  have hb : B = reduce (matrixOf x) := reducedRows_eq x
  exact (congrArg (fun M : TernaryMatrix x.2.length x.1 =>
    (Finset.univ.filter fun i => M.row i ≠ 0).card) hb).trans
    (rank_eq_card_reduce_ne_zero (matrixOf x)).symm

#print axioms rank_polyTime
#print axioms rank_eq

end DeletionCode.Explicit.Machine.Ternary
