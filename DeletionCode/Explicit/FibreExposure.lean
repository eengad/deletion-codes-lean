import DeletionCode.Explicit.FibreListing

/-! Exposure and finite-rule greedy closure using the executable fibre listing. -/
namespace DeletionCode.Explicit.Machine.BooleanFibres

open FieldHash Ternary LiftDictionary Qary.SignedSupport

/-- Test the translated vector in the same declared width as the affine space. -/
def booleanAfter (n : ℕ) (u r : Row) : Bool :=
  (List.range n).all fun j =>
    let z := u.getD j 0 + r.getD j 0
    decide (z = 0) || decide (z = 1)

def exposedRows (x : MatrixInput) (v r : Row) : Bool :=
  (fibreRows x v).any (fun u => booleanAfter x.1 u r)

theorem booleanAfter_eq (cols : Fin n ≃ Gram α L) (u r : Row) :
    booleanAfter n u r = true ↔ IsZeroOne (onGrams cols u + onGrams cols r) := by
  unfold booleanAfter IsZeroOne
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, Pi.add_apply]
  refine ⟨fun h g => h (cols.symm g).val (cols.symm g).isLt, fun h j hj => ?_⟩
  have he := h (cols ⟨j,hj⟩)
  change u.getD (cols.symm (cols ⟨j,hj⟩)).val 0 + r.getD (cols.symm (cols ⟨j,hj⟩)).val 0 = 0 ∨
    u.getD (cols.symm (cols ⟨j,hj⟩)).val 0 + r.getD (cols.symm (cols ⟨j,hj⟩)).val 0 = 1 at he
  simpa only [Equiv.symm_apply_apply] using he

theorem exposedRows_iff (cols : Fin n ≃ Gram α L) (rs : Rows) (v r : Row) :
    exposedRows (n,rs) v r = true ↔ Exposed (onGrams cols v) (gramSpan cols rs) (onGrams cols r) := by
  rw [BooleanClosure.exposed_iff_exists_fibre]
  simp only [exposedRows, List.any_eq_true]
  constructor
  · rintro ⟨u,hu,hb⟩
    have hv := (mem_fibreRows cols rs v _).mp (List.mem_map.mpr ⟨u,hu,rfl⟩)
    exact ⟨onGrams cols u,hv,hv.2,(booleanAfter_eq cols _ _).mp hb⟩
  · rintro ⟨u,hu,_,hb⟩
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ((mem_fibreRows cols rs v _).mpr hu)
    exact ⟨z,hz,(booleanAfter_eq cols _ _).mpr hb⟩

theorem gramSpan_eq_ruleSpan (cols : Fin n ≃ Gram α L) (rs : Rows) :
    gramSpan cols rs = BooleanClosure.ruleSpan (rs.map (onGrams cols)) := by
  unfold gramSpan rowSpan
  rw [Submodule.map_span]
  congr 1
  ext u
  simp only [Set.mem_image, Set.mem_range, Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    refine ⟨rs[i.val],List.getElem_mem i.isLt,?_⟩
    have hi : rs.getD i.val [] = rs[i.val] := List.getD_eq_getElem _ _ i.isLt
    simp only [onGrams, LinearEquiv.coe_coe]
    apply congrArg (coordEquiv cols)
    funext j
    change rs[i.val].getD j.val 0 = (rs.getD i.val []).getD j.val 0
    rw [hi]
  · rintro ⟨r,hr,rfl⟩
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hr
    refine ⟨(matrixOf (n,rs)).row ⟨i,hi⟩,⟨_,rfl⟩,?_⟩
    simp only [onGrams, LinearEquiv.coe_coe]
    apply congrArg (coordEquiv cols)
    funext j
    change (rs.getD i []).getD j.val 0 = rs[i].getD j.val 0
    rw [List.getD_eq_getElem _ _ hi]

private theorem row_not_mem_iff (cols : Fin n ≃ Gram α L) (rs : Rows) (r : Row) :
    vector n r ∉ rowSpan (n,rs) ↔ onGrams cols r ∉ gramSpan cols rs := by
  apply not_congr
  constructor
  · intro h
    exact Submodule.mem_map.mpr ⟨_,h,rfl⟩
  · intro h
    obtain ⟨a,ha,he⟩ := Submodule.mem_map.mp h
    have hev : (coordEquiv cols) a = (coordEquiv cols) (vector n r) := he
    exact (coordEquiv cols).injective hev ▸ ha

def rulesSet (cols : Fin n ≃ Gram α L) (rs : Rows) : Set (BooleanClosure.Vector α L) :=
  {r | r ∈ rs.map (onGrams cols)}

def canAdjoin (x : MatrixInput) (v r : Row) : Bool :=
  independentAdjunction (x,r) && exposedRows x v r

def chooseRows (n : ℕ) (v : Row) (rules acc : Rows) : Option Row :=
  rules.find? (canAdjoin (n,acc) v)

private theorem canAdjoin_iff (cols : Fin n ≃ Gram α L) (acc : Rows) (v r : Row) :
    canAdjoin (n,acc) v r = true ↔
      onGrams cols r ∉ gramSpan cols acc ∧ Exposed (onGrams cols v) (gramSpan cols acc) (onGrams cols r) := by
  rw [canAdjoin, Bool.and_eq_true, exposedRows_iff cols, independentAdjunction_eq_true]
  exact and_congr_left (fun _ => row_not_mem_iff cols acc r)

theorem chooseRows_some (cols : Fin n ≃ Gram α L) (v r : Row) (rules acc : Rows)
    (h : chooseRows n v rules acc = some r) :
    onGrams cols r ∈ rulesSet cols rules ∧ Exposed (onGrams cols v) (gramSpan cols acc) (onGrams cols r) ∧
      onGrams cols r ∉ gramSpan cols acc := by
  obtain ⟨hp,k,hk,hr,_⟩ := List.find?_eq_some_iff_getElem.mp h
  obtain ⟨hn,he⟩ := (canAdjoin_iff cols acc v r).mp hp
  exact ⟨List.mem_map.mpr ⟨r,hr ▸ List.getElem_mem hk,rfl⟩,he,hn⟩

theorem chooseRows_none (cols : Fin n ≃ Gram α L) (v : Row) (rules acc : Rows)
    (h : chooseRows n v rules acc = none) :
    BooleanClosure.ClosedAt (rulesSet cols rules) (onGrams cols v) (gramSpan cols acc) := by
  intro r hr he
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
  by_contra hn
  exact List.find?_eq_none.mp h s hs ((canAdjoin_iff cols acc v s).mpr ⟨hn,he⟩)

/-- The same finite search in the vector interface of `BooleanClosure.greedyRules`. -/
def choose (cols : Fin n ≃ Gram α L) (v : Row) (rules : Rows)
    (acc : List (BooleanClosure.Vector α L)) : Option (BooleanClosure.Vector α L) :=
  (chooseRows n v rules (acc.map (vectorData cols))).map (onGrams cols)

private theorem gramSpan_vectorData (cols : Fin n ≃ Gram α L) (acc : List (BooleanClosure.Vector α L)) :
    gramSpan cols (acc.map (vectorData cols)) = BooleanClosure.ruleSpan acc := by
  rw [gramSpan_eq_ruleSpan, List.map_map]
  have he : onGrams cols ∘ vectorData cols = id := funext (onGrams_vectorData cols)
  rw [he, List.map_id]

theorem choose_some (cols : Fin n ≃ Gram α L) (v : Row) (rules : Rows)
    (acc : List (BooleanClosure.Vector α L)) (r : BooleanClosure.Vector α L)
    (h : choose cols v rules acc = some r) :
    r ∈ rulesSet cols rules ∧ Exposed (onGrams cols v) (BooleanClosure.ruleSpan acc) r ∧
      r ∉ BooleanClosure.ruleSpan acc := by
  obtain ⟨s,hs,rfl⟩ := Option.map_eq_some_iff.mp h
  simpa only [gramSpan_vectorData] using chooseRows_some cols v s rules (acc.map (vectorData cols)) hs

theorem choose_none (cols : Fin n ≃ Gram α L) (v : Row) (rules : Rows)
    (acc : List (BooleanClosure.Vector α L)) (h : choose cols v rules acc = none) :
    BooleanClosure.ClosedAt (rulesSet cols rules) (onGrams cols v) (BooleanClosure.ruleSpan acc) := by
  have hs : chooseRows n v rules (acc.map (vectorData cols)) = none := Option.map_eq_none_iff.mp h
  simpa only [gramSpan_vectorData] using chooseRows_none cols v rules (acc.map (vectorData cols)) hs

theorem greedyRules_eq [Fintype α] (cols : Fin n ≃ Gram α L) (v : Row) (rules : Rows) :
    BooleanClosure.ruleSpan
      (BooleanClosure.greedyRules (choose cols v rules) (Fintype.card α ^ L + 1) []) =
      BooleanClosure.closure (rulesSet cols rules) (onGrams cols v) :=
  BooleanClosure.greedyRules_eq_closure _ _ _ (choose_some cols v rules) (choose_none cols v rules)

/-- The budget is supplied in unary to the machine. Rejection at the guard
bounds the enumerator even for inputs with an insufficient budget. -/
def fits (N : ℕ) (x : MatrixInput) : Bool := decide (2 ^ Ternary.rank x ≤ N)

def boundedFibre (N : ℕ) (x : MatrixInput) (v : Row) : Rows :=
  if fits N x then fibreRows x v else []

def boundedExposed (N : ℕ) (x : MatrixInput) (v r : Row) : Bool :=
  (boundedFibre N x v).any (fun u => booleanAfter x.1 u r)

def boundedChoose (N n : ℕ) (v : Row) (rules acc : Rows) : Option Row :=
  rules.find? (fun r => independentAdjunction ((n,acc),r) && boundedExposed N (n,acc) v r)

def greedyRows (pick : Rows → Option Row) : ℕ → Rows → Rows
  | 0, acc => acc
  | fuel+1, acc => match pick acc with
    | none => acc
    | some r => greedyRows pick fuel (r :: acc)

def closureRows (N n : ℕ) (v : Row) (rules : Rows) : Rows :=
  greedyRows (boundedChoose N n v rules) (n+1) []

theorem boundedFibre_eq (N : ℕ) (x : MatrixInput) (v : Row) (h : 2 ^ Ternary.rank x ≤ N) :
    boundedFibre N x v = fibreRows x v := by simp [boundedFibre, fits, h]

theorem mem_boundedFibre (cols : Fin n ≃ Gram α L) (N : ℕ) (rs : Rows) (v : Row)
    (h : 2 ^ Ternary.rank (n,rs) ≤ N) (u : BooleanClosure.Vector α L) :
    u ∈ (boundedFibre N (n,rs) v).map (onGrams cols) ↔
      u ∈ BooleanClosure.fibre (onGrams cols v) (gramSpan cols rs) := by
  rw [boundedFibre_eq _ _ _ h, mem_fibreRows]

theorem boundedExposed_iff (cols : Fin n ≃ Gram α L) (N : ℕ) (rs : Rows) (v r : Row)
    (h : 2 ^ Ternary.rank (n,rs) ≤ N) :
    boundedExposed N (n,rs) v r = true ↔ Exposed (onGrams cols v) (gramSpan cols rs) (onGrams cols r) := by
  rw [boundedExposed, boundedFibre_eq _ _ _ h]
  exact exposedRows_iff cols rs v r

private theorem boundedChoose_eq (N n : ℕ) (v : Row) (rules acc : Rows)
    (h : 2 ^ Ternary.rank (n,acc) ≤ N) : boundedChoose N n v rules acc = chooseRows n v rules acc := by
  simp only [boundedChoose, boundedExposed, boundedFibre_eq _ _ _ h, chooseRows, canAdjoin, exposedRows]
  rfl

theorem gramSpan_rank (cols : Fin n ≃ Gram α L) (rs : Rows) :
    Module.finrank F₃ (gramSpan cols rs) = Ternary.rank (n,rs) := by
  rw [gramSpan, LinearEquiv.finrank_map_eq, rowSpan, ← Matrix.rank_eq_finrank_span_row, Ternary.rank_eq,
    ternaryRank_eq]

theorem closureRows_eq [Fintype α] (cols : Fin n ≃ Gram α L) (N : ℕ) (v : Row) (rules : Rows)
    (hN : 2 ^ Module.finrank F₃ (BooleanClosure.closure (rulesSet cols rules) (onGrams cols v)) ≤ N) :
    gramSpan cols (closureRows N n v rules) = BooleanClosure.closure (rulesSet cols rules) (onGrams cols v) := by
  let U := BooleanClosure.closure (rulesSet cols rules) (onGrams cols v)
  have hn : Fintype.card α ^ L = n := by simpa [Gram] using (Fintype.card_congr cols).symm
  have hcons (r : Row) (rs : Rows) : gramSpan cols (r :: rs) =
      BooleanClosure.adjoining (gramSpan cols rs) (onGrams cols r) := by
    simp only [gramSpan_eq_ruleSpan, List.map_cons, BooleanClosure.ruleSpan_cons]
  suffices ∀ fuel k acc, n < k + fuel →
      BooleanClosure.Greedy (rulesSet cols rules) (onGrams cols v) k (gramSpan cols acc) →
      gramSpan cols (greedyRows (boundedChoose N n v rules) fuel acc) = U by
    apply this _ 0 [] (by simp)
    simpa [gramSpan_eq_ruleSpan, BooleanClosure.ruleSpan] using (BooleanClosure.Greedy.start
      (rules := rulesSet cols rules) (v := onGrams cols v))
  intro fuel
  induction fuel with
  | zero =>
    intro k acc hbound hg
    have hk := hg.steps_le_ambient
    omega
  | succ fuel ih =>
    intro k acc hbound hg
    have hdim := Submodule.finrank_mono hg.le_closure
    have hr : 2 ^ Ternary.rank (n,acc) ≤ N := by
      rw [← gramSpan_rank cols]
      exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hdim).trans hN
    rw [greedyRows, boundedChoose_eq _ _ _ _ _ hr]
    cases hx : chooseRows n v rules acc with
    | none => exact hg.eq_closure (chooseRows_none cols v rules acc hx)
    | some r =>
      obtain ⟨hm,he,hn⟩ := chooseRows_some cols v r rules acc hx
      apply ih (k+1) (r :: acc) (by omega)
      rw [hcons]
      exact .add hg hm he hn

#print axioms exposedRows_iff
#print axioms choose_some
#print axioms choose_none
#print axioms greedyRules_eq
#print axioms mem_boundedFibre
#print axioms boundedExposed_iff
#print axioms closureRows_eq

end DeletionCode.Explicit.Machine.BooleanFibres
