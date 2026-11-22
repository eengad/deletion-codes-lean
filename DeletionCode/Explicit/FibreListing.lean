import DeletionCode.Explicit.FibrePivots
import DeletionCode.Explicit.BooleanClosure

/-! Reconstruct Boolean fibres from the pivot values of a ternary affine space. -/
namespace DeletionCode.Explicit.Machine.BooleanFibres

open FieldHash Ternary LiftDictionary Qary.SignedSupport
open scoped BigOperators

abbrev Coefficients := List (ℕ × F₃)

def bitTrit (a : Fin 2) : F₃ := if a = 0 then 0 else 1

def coefficient (reduced : MatrixInput) (v : Row) (a : QWord 2) (k : ℕ) : ℕ × F₃ :=
  let i := (pivotRows reduced).getD k 0
  let j := (pivotColumn reduced i).getD 0
  (i, (bitTrit (a.getD k 0) - v.getD j 0) / cell reduced.2 i j)

def coefficients (reduced : MatrixInput) (v : Row) (a : QWord 2) : Coefficients :=
  (List.range (pivotRows reduced).length).map (coefficient reduced v a)

def reconstruct (reduced : MatrixInput) (v : Row) (cs : Coefficients) : Row :=
  (List.range reduced.1).map fun j => v.getD j 0 + (cs.map (fun c => c.2 * cell reduced.2 c.1 j)).sum

/-- The pivot equations are diagonal in the reduced basis. Subtract the base
value at each pivot and scale its row by the quotient by the pivot entry. -/
def solve (x : MatrixInput) (v : Row) (a : QWord 2) : Row :=
  let B := prepare x
  reconstruct B v (coefficients B v a)

def booleanRow (n : ℕ) (v : Row) : Bool :=
  (List.range n).all fun j => decide (v.getD j 0 = 0) || decide (v.getD j 0 = 1)

def fibreRows (x : MatrixInput) (v : Row) : Rows :=
  ((wordsOfLength 2 (pivotRows (prepare x)).length).map (solve x v)).filter (booleanRow x.1)

def coordEquiv (cols : Fin n ≃ Gram α L) : (Fin n → F₃) ≃ₗ[F₃] BooleanClosure.Vector α L where
  toFun f g := f (cols.symm g)
  invFun f j := f (cols j)
  left_inv f := funext fun j => congrArg f (cols.symm_apply_apply j)
  right_inv f := funext fun j => congrArg f (cols.apply_symm_apply j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def onGrams (cols : Fin n ≃ Gram α L) (r : Row) : BooleanClosure.Vector α L :=
  coordEquiv cols (vector n r)

def vectorData (cols : Fin n ≃ Gram α L) (w : BooleanClosure.Vector α L) : Row :=
  List.ofFn ((coordEquiv cols).symm w)

def gramSpan (cols : Fin n ≃ Gram α L) (rs : Rows) : BooleanClosure.Space α L :=
  (rowSpan (n,rs)).map (coordEquiv cols).toLinearMap

theorem ofFn_getD {A : Type*} (f : Fin n → A) (i : Fin n) (d : A) :
    (List.ofFn f).getD i.val d = f i := by
  have hi : i.val < (List.ofFn f).length := by rw [List.length_ofFn]; exact i.isLt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem_ofFn,
    Option.getD_some]

@[simp] theorem vector_vectorData (cols : Fin n ≃ Gram α L) (w : BooleanClosure.Vector α L) :
    vector n (vectorData cols w) = (coordEquiv cols).symm w := by
  funext i
  exact ofFn_getD _ i 0

@[simp] theorem onGrams_vectorData (cols : Fin n ≃ Gram α L) (w : BooleanClosure.Vector α L) :
    onGrams cols (vectorData cols w) = w := by rw [onGrams, vector_vectorData, LinearEquiv.apply_symm_apply]

private theorem getD_in_bounds {A : Type*} {xs : List A} (i : Fin xs.length) (d : A) :
    xs.getD i.val d = xs[i.val] := List.getD_eq_getElem _ _ i.isLt

private theorem coefficient_eq (x : MatrixInput) (v : Row) (a : QWord 2) (k : PivotIndex x) :
    coefficient (prepare x) v a k.val = ( (rowAt x k).val,
      (bitTrit (a.getD k.val 0) - vector x.1 v (colAt x k)) / basisRow x k (colAt x k)) := by
  unfold coefficient
  rw [getD_in_bounds k]
  rfl

private theorem coefficients_eq (x : MatrixInput) (v : Row) (a : QWord 2) :
    coefficients (prepare x) v a = List.ofFn (fun k : PivotIndex x => ((rowAt x k).val,
      (bitTrit (a.getD k.val 0) - vector x.1 v (colAt x k)) / basisRow x k (colAt x k))) := by
  unfold coefficients
  apply List.ext_getElem (by simp)
  intro j hj hi
  have h : j < (pivotRows (prepare x)).length := by simpa using hi
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  exact coefficient_eq x v a ⟨j,h⟩

theorem solve_apply (x : MatrixInput) (v : Row) (a : QWord 2) (j : Fin x.1) :
    vector x.1 (solve x v a) j = vector x.1 v j +
      ∑ k : PivotIndex x, ((bitTrit (a.getD k.val 0) - vector x.1 v (colAt x k)) /
        basisRow x k (colAt x k)) * basisRow x k j := by
  unfold solve reconstruct vector
  dsimp only
  have ht (f : ℕ → F₃) (d : F₃) : ((List.range x.1).map f).getD j.val d = f j.val := by
    have hj : j.val < ((List.range x.1).map f).length := by simp
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, List.getElem_map,
      List.getElem_range, Option.getD_some]
  rw [ht, coefficients_eq, List.map_ofFn, List.sum_ofFn]
  rfl

theorem solve_sub_mem (x : MatrixInput) (v : Row) (a : QWord 2) :
    vector x.1 (solve x v a) - vector x.1 v ∈ rowSpan x := by
  rw [← span_basisRow]
  refine (Submodule.mem_span_range_iff_exists_fun _).mpr ⟨fun k =>
    (bitTrit (a.getD k.val 0) - vector x.1 v (colAt x k)) / basisRow x k (colAt x k), ?_⟩
  funext j
  rw [Pi.sub_apply, solve_apply, add_sub_cancel_left, Finset.sum_apply]
  rfl

private theorem pivot_sum (x : MatrixInput) (c : PivotIndex x → F₃) (k : PivotIndex x) :
    (∑ i : PivotIndex x, c i • basisRow x i) (colAt x k) = c k * basisRow x k (colAt x k) := by
  rw [Finset.sum_apply]
  refine Finset.sum_eq_single k (fun i _ hi => ?_) (by simp)
  change c i * matrixOf (prepare x) (rowAt x i) (colAt x k) = 0
  rw [(pivot_diagonal x k).2 i hi,mul_zero]

theorem solve_cover (x : MatrixInput) (v : Row) (u : Fin x.1 → F₃)
    (hw : u - vector x.1 v ∈ rowSpan x) (hu : ∀ j, u j = 0 ∨ u j = 1) :
    ∃ a : QWord 2, a.length = Ternary.rank x ∧ vector x.1 (solve x v a) = u := by
  rw [← span_basisRow] at hw
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hw
  let a : PivotIndex x → Fin 2 := fun k => if u (colAt x k) = 0 then 0 else 1
  have ha (k : PivotIndex x) : bitTrit ((List.ofFn a).getD k.val 0) = u (colAt x k) := by
    rw [ofFn_getD a k]
    rcases hu (colAt x k) with he | he <;> simp [a,bitTrit,he]
  have hcoeff (k : PivotIndex x) :
      (bitTrit ((List.ofFn a).getD k.val 0) - vector x.1 v (colAt x k)) /
        basisRow x k (colAt x k) = c k := by
    rw [ha]
    apply (div_eq_iff (pivot_diagonal x k).1).mpr
    exact (congrFun hc (colAt x k)).symm.trans (pivot_sum x c k)
  refine ⟨List.ofFn a, List.length_ofFn.trans (pivotRows_length x), ?_⟩
  funext j
  rw [solve_apply]
  simp_rw [hcoeff]
  have hsum := congrFun hc j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hsum
  rw [hsum]
  abel

theorem booleanRow_eq (cols : Fin n ≃ Gram α L) (v : Row) :
    booleanRow n v = true ↔ IsZeroOne (onGrams cols v) := by
  simp only [booleanRow, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨fun h g => h (cols.symm g).val (cols.symm g).isLt, fun h j hj => ?_⟩
  obtain he := h (cols ⟨j,hj⟩)
  change v.getD (cols.symm (cols ⟨j,hj⟩)).val 0 = 0 ∨ v.getD (cols.symm (cols ⟨j,hj⟩)).val 0 = 1 at he
  simpa only [Equiv.symm_apply_apply] using he

theorem solve_mem_gramSpan (cols : Fin n ≃ Gram α L) (rs : Rows) (v : Row) (a : QWord 2) :
    onGrams cols (solve (n,rs) v a) - onGrams cols v ∈ gramSpan cols rs := by
  change _ ∈ (rowSpan (n,rs)).map (coordEquiv cols).toLinearMap
  exact Submodule.mem_map.mpr ⟨_,solve_sub_mem (n,rs) v a, (map_sub (coordEquiv cols) _ _)⟩

theorem solve_covers_fibre (cols : Fin n ≃ Gram α L) (rs : Rows) (v : Row)
    (u : BooleanClosure.Vector α L) (hu : u ∈ BooleanClosure.fibre (onGrams cols v) (gramSpan cols rs)) :
    ∃ a : QWord 2, a.length = Ternary.rank (n,rs) ∧ onGrams cols (solve (n,rs) v a) = u := by
  let w := (coordEquiv cols).symm u
  have hm : w - vector n v ∈ rowSpan (n,rs) := by
    obtain ⟨a,ha,he⟩ := Submodule.mem_map.mp hu.1
    have he' : (coordEquiv cols) a = u - onGrams cols v := he
    have h := (coordEquiv cols).injective (he'.trans (show _ = (coordEquiv cols) (w - vector n v) from by
      rw [map_sub, LinearEquiv.apply_symm_apply]; rfl))
    exact h ▸ ha
  have hb (j : Fin n) : w j = 0 ∨ w j = 1 := hu.2 (cols j)
  obtain ⟨a,ha,he⟩ := solve_cover (n,rs) v w hm hb
  refine ⟨a,ha,?_⟩
  change (coordEquiv cols) (vector n (solve (n,rs) v a)) = u
  rw [he, LinearEquiv.apply_symm_apply]

theorem mem_fibreRows (cols : Fin n ≃ Gram α L) (rs : Rows) (v : Row) (u : BooleanClosure.Vector α L) :
    u ∈ (fibreRows (n,rs) v).map (onGrams cols) ↔
      u ∈ BooleanClosure.fibre (onGrams cols v) (gramSpan cols rs) := by
  rw [← BooleanClosure.mem_listFibre (r := Ternary.rank (n,rs))
    (fun a => onGrams cols (solve (n,rs) v a)) (fun w => booleanRow n (vectorData cols w))
    (fun a _ => solve_mem_gramSpan cols rs v a) (solve_covers_fibre cols rs v)
    (fun w => (booleanRow_eq cols _).trans (by rw [onGrams_vectorData])) u]
  simp only [fibreRows, pivotRows_length, BooleanClosure.listFibre, List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨r,⟨⟨a,ha,rfl⟩,hb⟩,rfl⟩
    exact ⟨⟨a,ha,rfl⟩,(booleanRow_eq cols _).mpr (by simpa using (booleanRow_eq cols _).mp hb)⟩
  · rintro ⟨⟨a,ha,rfl⟩,hb⟩
    exact ⟨_,⟨⟨a,ha,rfl⟩,(booleanRow_eq cols _).mpr (by simpa using (booleanRow_eq cols _).mp hb)⟩,rfl⟩

#print axioms solve_mem_gramSpan
#print axioms solve_covers_fibre
#print axioms mem_fibreRows

end DeletionCode.Explicit.Machine.BooleanFibres
