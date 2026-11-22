import DeletionCode.Explicit.Machine.ClosureRank

/-! Pivot coordinates and the row span of the certified ternary reduction. -/
namespace DeletionCode.Explicit.Machine.BooleanFibres

open FieldHash Ternary Matrix.GaussJordan
open scoped BigOperators

def rowSpan (x : MatrixInput) : Submodule F₃ (Fin x.1 → F₃) :=
  Submodule.span F₃ (Set.range (matrixOf x).row)

@[reducible] def prepare (x : MatrixInput) : MatrixInput := (x.1,reducedRows x)

def ownsPivot (x : MatrixInput) (i j : ℕ) : Bool :=
  decide (cell x.2 i j ≠ 0) &&
    (List.range x.2.length).all (fun k => decide (k = i) || decide (cell x.2 k j = 0))

def pivotColumn (x : MatrixInput) (i : ℕ) : Option ℕ :=
  (List.range x.1).find? (ownsPivot x i)

def pivotRows (x : MatrixInput) : List ℕ :=
  (List.range x.2.length).filter fun i => (pivotColumn x i).isSome

private theorem span_eliminate_le (A : TernaryMatrix m n) (j : Fin n) (p : Fin m) :
    Submodule.span F₃ (Set.range (eliminate A j p).row) ≤ Submodule.span F₃ (Set.range A.row) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  let W := Submodule.span F₃ (Set.range A.row)
  have hrow (k : Fin m) : A.row k ∈ W := Submodule.subset_span (Set.mem_range_self k)
  by_cases h : i = p
  · subst i
    have he : (eliminate A j p).row p = A.row p := funext (eliminate_apply_self A j p)
    rw [he]
    exact hrow p
  · have he : (eliminate A j p).row i = A.row i - (A i j / A p j) • A.row p :=
      funext (eliminate_apply_of_ne h)
    rw [he]
    exact W.sub_mem (hrow i) (W.smul_mem _ (hrow p))

private theorem span_reduce_le (A : TernaryMatrix m n) (k : ℕ) :
    Submodule.span F₃ (Set.range (reduceUpTo A k).row) ≤ Submodule.span F₃ (Set.range A.row) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases h : k < n
    · rw [reduceUpTo_succ_of_lt A h, stage]
      cases pivotRow (reduceUpTo A k) ⟨k,h⟩ with
      | none => exact ih
      | some p => exact (span_eliminate_le _ _ p).trans ih
    · rw [reduceUpTo_succ_of_le A (Nat.not_lt.mp h)]
      exact ih

private theorem span_reduce (A : TernaryMatrix m n) :
    Submodule.span F₃ (Set.range (reduce A).row) = Submodule.span F₃ (Set.range A.row) := by
  apply Submodule.eq_of_le_of_finrank_le (span_reduce_le A n)
  rw [← Matrix.rank_eq_finrank_span_row, ← Matrix.rank_eq_finrank_span_row, rank_reduceUpTo]

theorem span_prepare (x : MatrixInput) : rowSpan (prepare x) = rowSpan x := by
  have hlen := reducedRows_length x
  have he : Set.range (matrixOf (prepare x)).row = Set.range (reduce (matrixOf x)).row := by
    rw [← reducedRows_eq]
    ext u
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨Fin.cast hlen i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨Fin.cast hlen.symm i,rfl⟩
  unfold rowSpan
  rw [he, span_reduce]

private theorem ownsPivot_iff (x : MatrixInput) (i : Fin x.2.length) (j : Fin x.1) :
    ownsPivot x i.val j.val = true ↔ matrixOf x i j ≠ 0 ∧ ∀ k, k ≠ i → matrixOf x k j = 0 := by
  simp only [ownsPivot, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true]
  apply and_congr_right
  intro _
  constructor
  · intro h k hk
    exact (h k.val k.isLt).resolve_left (fun e => hk (Fin.ext e))
  · intro h k hk
    by_cases e : k = i.val
    · exact Or.inl e
    · exact Or.inr (h ⟨k,hk⟩ (fun h' => e (congrArg Fin.val h')))

private theorem pivotColumn_found (x : MatrixInput) (i : ℕ) (h : (pivotColumn x i).isSome = true) :
    (pivotColumn x i).getD 0 < x.1 ∧ ownsPivot x i ((pivotColumn x i).getD 0) = true := by
  cases he : pivotColumn x i with
  | none => simp [he] at h
  | some j =>
    obtain ⟨hp,k,hk,hj,_⟩ := List.find?_eq_some_iff_getElem.mp he
    have hlt : j < x.1 := by
      have hr : k < x.1 := by simpa using hk
      have hj' : k = j := by simpa using hj
      exact hj' ▸ hr
    exact ⟨by simpa [he] using hlt, by simpa [he] using hp⟩

private theorem pivotColumn_isSome_iff (x : MatrixInput) (i : Fin (prepare x).2.length) :
    (pivotColumn (prepare x) i.val).isSome = true ↔ (matrixOf (prepare x)).row i ≠ 0 := by
  constructor
  · intro h hn
    obtain ⟨hlt,howns⟩ := pivotColumn_found _ _ h
    exact ((ownsPivot_iff _ i ⟨_,hlt⟩).mp howns).1 (congrFun hn ⟨_,hlt⟩)
  · intro hn
    let ii := Fin.cast (reducedRows_length x) i
    have hne : (reduce (matrixOf x)).row ii ≠ 0 := by
      rw [← reducedRows_eq]
      exact hn
    obtain ⟨j,hj,hd⟩ := exists_pivot_of_reduce_ne_zero _ hne
    rw [← reducedRows_eq] at hj hd
    have hp : ownsPivot (prepare x) i.val j.val = true := (ownsPivot_iff _ _ _).mpr
      ⟨hj, fun k hk => hd (Fin.cast (reducedRows_length x) k) (fun h => hk (Fin.cast_injective _ h))⟩
    cases he : pivotColumn (prepare x) i.val with
    | none => exact False.elim (List.find?_eq_none.mp he j.val (List.mem_range.mpr j.isLt) hp)
    | some v => rfl

theorem pivotRows_length (x : MatrixInput) : (pivotRows (prepare x)).length = Ternary.rank x := by
  classical
  let B := reduce (matrixOf x)
  let f (i : ℕ) := (pivotColumn (prepare x) i).isSome
  have hlen := reducedRows_length x
  have hs (i : Fin x.2.length) : f i.val = true ↔ B.row i ≠ 0 := by
    let ii := Fin.cast hlen.symm i
    have h := pivotColumn_isSome_iff x ii
    have hb : B.row i = (matrixOf (prepare x)).row ii := by
      unfold B
      rw [← reducedRows_eq]
      rfl
    exact hb ▸ h
  have hset : ((List.range x.2.length).filter f).toFinset =
      (Finset.univ.filter fun i : Fin x.2.length => B.row i ≠ 0).map Fin.valEmbedding := by
    ext j
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.valEmbedding_apply]
    exact ⟨fun ⟨hj,hf⟩ => ⟨⟨j,hj⟩,(hs ⟨j,hj⟩).mp hf,rfl⟩,
      fun ⟨i,hi,h⟩ => h ▸ ⟨i.isLt,(hs i).mpr hi⟩⟩
  have hr : pivotRows (prepare x) = (List.range x.2.length).filter f := by
    unfold pivotRows
    change (List.range (reducedRows x).length).filter f = _
    rw [hlen]
  rw [hr, ← List.toFinset_card_of_nodup (List.nodup_range.filter _), hset, Finset.card_map,
    rank_eq, ternaryRank_eq]
  exact (rank_eq_card_reduce_ne_zero (matrixOf x)).symm

abbrev PivotIndex (x : MatrixInput) := Fin (pivotRows (prepare x)).length

def rowAt (x : MatrixInput) (k : PivotIndex x) : Fin (prepare x).2.length :=
  ⟨(pivotRows (prepare x))[k.val],
    List.mem_range.mp (List.mem_filter.mp (List.getElem_mem k.isLt)).1⟩

private theorem rowAt_isSome (x : MatrixInput) (k : PivotIndex x) :
    (pivotColumn (prepare x) (rowAt x k).val).isSome = true :=
  (List.mem_filter.mp (List.getElem_mem k.isLt)).2

def colAt (x : MatrixInput) (k : PivotIndex x) : Fin x.1 :=
  ⟨(pivotColumn (prepare x) (rowAt x k).val).getD 0, (pivotColumn_found _ _ (rowAt_isSome x k)).1⟩

theorem rowAt_injective (x : MatrixInput) : Function.Injective (rowAt x) := by
  intro i j h
  have hn : (pivotRows (prepare x)).Nodup := List.nodup_range.filter _
  exact hn.get_inj_iff.mp (congrArg Fin.val h)

theorem pivot_diagonal (x : MatrixInput) (k : PivotIndex x) :
    matrixOf (prepare x) (rowAt x k) (colAt x k) ≠ 0 ∧
      ∀ j : PivotIndex x, j ≠ k → matrixOf (prepare x) (rowAt x j) (colAt x k) = 0 := by
  obtain ⟨ha,hb⟩ := (ownsPivot_iff _ (rowAt x k) (colAt x k)).mp
    (pivotColumn_found _ _ (rowAt_isSome x k)).2
  exact ⟨ha, fun j hj => hb (rowAt x j) (fun he => hj (rowAt_injective x he))⟩

def basisRow (x : MatrixInput) (k : PivotIndex x) : Fin x.1 → F₃ :=
  (matrixOf (prepare x)).row (rowAt x k)

theorem span_basisRow (x : MatrixInput) : Submodule.span F₃ (Set.range (basisRow x)) = rowSpan x := by
  rw [← span_prepare x]
  apply le_antisymm
  · apply Submodule.span_mono
    rintro r ⟨k,rfl⟩
    exact Set.mem_range_self (rowAt x k)
  · apply Submodule.span_le.mpr
    rintro r ⟨i,rfl⟩
    by_cases hi : (matrixOf (prepare x)).row i = 0
    · rw [hi]
      exact Submodule.zero_mem _
    · have hm : i.val ∈ pivotRows (prepare x) :=
        List.mem_filter.mpr ⟨List.mem_range.mpr i.isLt, (pivotColumn_isSome_iff x i).mpr hi⟩
      obtain ⟨k,hk,hval⟩ := List.getElem_of_mem hm
      have he : rowAt x ⟨k,hk⟩ = i := Fin.ext hval
      exact Submodule.subset_span (s := Set.range (basisRow x)) ⟨⟨k,hk⟩, congrArg (matrixOf (prepare x)).row he⟩

#print axioms span_prepare
#print axioms pivotRows_length
#print axioms pivot_diagonal
#print axioms span_basisRow

end DeletionCode.Explicit.Machine.BooleanFibres
