import DeletionCode.Explicit.RulePatchCore

/-! Executable connected components of the rule–patch multigraph.
Parallel edges affect the edge count but do not affect reachability. -/

namespace DeletionCode.Explicit.RulePatch

variable {d s c : ℕ}

private def incident (a : Incidence d s c) (i : Fin d) (p : Fin c) : Bool :=
  (List.finRange s).any (fun j => decide (a (i,j) = p))

/-- Adjacency in the underlying simple graph, computed from the bubble edges. -/
def adjacent (a : Incidence d s c) : Fin d ⊕ Fin c → Fin d ⊕ Fin c → Bool
  | .inl i, .inr p => incident a i p
  | .inr p, .inl i => incident a i p
  | _, _ => false

theorem adjacent_iff (a : Incidence d s c) (x y : Fin d ⊕ Fin c) :
    adjacent a x y = true ↔ (graph a).Adj x y := by
  change _ ↔ (SimpleGraph.fromRel (fun x y : Fin d ⊕ Fin c =>
    ∃ e : Fin d × Fin s, Sum.inl e.1 = x ∧ Sum.inr (a e) = y)).Adj x y
  cases x <;> cases y <;>
    simp [adjacent,incident,SimpleGraph.fromRel_adj,Prod.exists]

private def neighbors (a : Incidence d s c) (x : Fin d ⊕ Fin c) : Finset (Fin d ⊕ Fin c) :=
  Finset.univ.filter (fun y => adjacent a x y = true)

private theorem mem_neighbors (a : Incidence d s c) (x y : Fin d ⊕ Fin c) :
    y ∈ neighbors a x ↔ (graph a).Adj x y := by
  simp [neighbors,adjacent_iff]

private def expand (a : Incidence d s c) (V : Finset (Fin d ⊕ Fin c)) : Finset (Fin d ⊕ Fin c) :=
  V ∪ V.biUnion (neighbors a)

private theorem subset_expand (a : Incidence d s c) (V : Finset (Fin d ⊕ Fin c)) :
    V ⊆ expand a V := Finset.subset_union_left

private def expandFrom (a : Incidence d s c) (x : Fin d ⊕ Fin c) : ℕ → Finset (Fin d ⊕ Fin c)
  | 0 => {x}
  | n+1 => expand a (expandFrom a x n)

private theorem root_mem (a : Incidence d s c) (x : Fin d ⊕ Fin c) (n : ℕ) :
    x ∈ expandFrom a x n := by
  induction n with
  | zero => exact Finset.mem_singleton_self _
  | succ n ih => exact subset_expand a _ ih

private theorem expandFrom_reachable (a : Incidence d s c) (x : Fin d ⊕ Fin c) (n : ℕ)
    {y : Fin d ⊕ Fin c} (hy : y ∈ expandFrom a x n) : (graph a).Reachable x y := by
  induction n generalizing y with
  | zero =>
    have e : y = x := Finset.mem_singleton.mp hy
    subst y
    exact SimpleGraph.Reachable.rfl
  | succ n ih =>
    rcases Finset.mem_union.mp hy with hy | hy
    · exact ih hy
    · obtain ⟨z,hz,hy⟩ := Finset.mem_biUnion.mp hy
      exact (ih hz).trans ((mem_neighbors a z y).mp hy).reachable

private theorem expands_or_fixed (a : Incidence d s c) (x : Fin d ⊕ Fin c) (n : ℕ) :
    n+1 ≤ (expandFrom a x n).card ∨ expand a (expandFrom a x n) = expandFrom a x n := by
  induction n with
  | zero => exact Or.inl (by simp [expandFrom])
  | succ n ih =>
    by_cases h : expand a (expandFrom a x n) = expandFrom a x n
    · apply Or.inr
      change expand a (expand a (expandFrom a x n)) = expand a (expandFrom a x n)
      exact congrArg (expand a) h
    · have hcard := ih.resolve_right h
      have hlt := Finset.card_lt_card
        (lt_of_le_of_ne (subset_expand a (expandFrom a x n)) (Ne.symm h))
      exact Or.inl (by change n+1+1 ≤ (expand a (expandFrom a x n)).card; omega)

/-- At most the number of vertices many rounds suffice. -/
def component (a : Incidence d s c) (x : Fin d ⊕ Fin c) : Finset (Fin d ⊕ Fin c) :=
  expandFrom a x (d+c)

private theorem component_fixed (a : Incidence d s c) (x : Fin d ⊕ Fin c) :
    expand a (component a x) = component a x := by
  have hmax : (component a x).card ≤ d+c := by
    simpa only [Fintype.card_sum,Fintype.card_fin] using (component a x).card_le_univ
  exact (expands_or_fixed a x (d+c)).resolve_left (by
    change ¬ d+c+1 ≤ (component a x).card
    omega)

theorem mem_component (a : Incidence d s c) (x y : Fin d ⊕ Fin c) :
    y ∈ component a x ↔ (graph a).Reachable x y := by
  refine ⟨expandFrom_reachable a x (d+c),?_⟩
  rw [SimpleGraph.reachable_iff_reflTransGen]
  intro h
  induction h with
  | refl => exact root_mem a x _
  | tail _ hadj ih =>
    rw [← component_fixed a x]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨_,ih,(mem_neighbors a _ _).mpr hadj⟩)

theorem component_eq_of_reachable (a : Incidence d s c) {x y : Fin d ⊕ Fin c}
    (h : (graph a).Reachable x y) : component a x = component a y := by
  ext z
  rw [mem_component,mem_component]
  exact ⟨fun hw => h.symm.trans hw,fun hw => h.trans hw⟩

def componentRules (a : Incidence d s c) (x : Fin d ⊕ Fin c) : Finset (Fin d) :=
  Finset.univ.filter (fun i => Sum.inl i ∈ component a x)

def componentPatches (a : Incidence d s c) (x : Fin d ⊕ Fin c) : Finset (Fin c) :=
  Finset.univ.filter (fun p => Sum.inr p ∈ component a x)

@[simp] theorem mem_componentRules (a : Incidence d s c) (x : Fin d ⊕ Fin c) (i : Fin d) :
    i ∈ componentRules a x ↔ (graph a).Reachable x (.inl i) := by
  simp [componentRules,mem_component]

@[simp] theorem mem_componentPatches (a : Incidence d s c) (x : Fin d ⊕ Fin c) (p : Fin c) :
    p ∈ componentPatches a x ↔ (graph a).Reachable x (.inr p) := by
  simp [componentPatches,mem_component]

theorem component_rule_sets_of_cutoff (a : Incidence d s c) (R : ℕ)
    (h : ∀ p : Fin c, (componentRules a (.inr p)).card ≤ R) :
    ∀ p, ∃ rules : Finset (Fin d), rules.card ≤ R ∧
      ∀ i, (graph a).Reachable (.inl i) (.inr p) → i ∈ rules := by
  intro p
  exact ⟨componentRules a (.inr p),h p,fun i hi => (mem_componentRules a _ i).mpr hi.symm⟩

/-- The old rule–patch graph maps to the enlarged graph when every old
bubble's endpoint is updated to its enclosing patch. -/
def mergeHom {c' : ℕ} (old : Incidence d s c) (next : Incidence (d+1) s c')
    (merge : Fin c → Fin c') (h : ∀ i j, next (i.castSucc,j) = merge (old (i,j))) :
    graph old →g graph next where
  toFun := Sum.map Fin.castSucc merge
  map_rel' := by
    intro x y hxy
    have hadj := (adjacent_iff old x y).mpr hxy
    apply (adjacent_iff next _ _).mp
    cases x with
    | inl i =>
      cases y with
      | inl k => simp [adjacent] at hadj
      | inr p =>
        have hj : ∃ j, old (i,j) = p := by simpa [adjacent,incident] using hadj
        obtain ⟨j,hj⟩ := hj
        have he : next (i.castSucc,j) = merge p := (h i j).trans (congrArg merge hj)
        simpa [adjacent,incident] using (show ∃ j, next (i.castSucc,j) = merge p from ⟨j,he⟩)
    | inr p =>
      cases y with
      | inr q => simp [adjacent] at hadj
      | inl i =>
        have hj : ∃ j, old (i,j) = p := by simpa [adjacent,incident] using hadj
        obtain ⟨j,hj⟩ := hj
        have he : next (i.castSucc,j) = merge p := (h i j).trans (congrArg merge hj)
        simpa [adjacent,incident] using (show ∃ j, next (i.castSucc,j) = merge p from ⟨j,he⟩)

theorem adj_rule_patch_iff (a : Incidence d s c) (i : Fin d) (p : Fin c) :
    (graph a).Adj (.inl i) (.inr p) ↔ ∃ j, a (i,j) = p := by
  rw [← adjacent_iff]
  simp [adjacent,incident]

/-- Reachability stays in any collection of vertices closed under adjacency. -/
theorem reachable_closed (a : Incidence d s c) (P : Fin d ⊕ Fin c → Prop)
    (hc : ∀ {x y}, (graph a).Adj x y → P x → P y)
    {x y : Fin d ⊕ Fin c} (h : (graph a).Reachable x y) (hx : P x) : P y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hx
  | tail _ he ih => exact hc he ih

theorem bubble_reaches (a : Incidence d s c) (i : Fin d) (j : Fin s) :
    (graph a).Reachable (.inl i) (.inr (a (i,j))) := by
  apply SimpleGraph.Adj.reachable
  apply (adjacent_iff a _ _).mp
  simp [adjacent,incident,show ∃ k, a (i,k) = a (i,j) from ⟨j,rfl⟩]

theorem componentPatches_eq_incidence (a : Incidence d s c) (i : Fin d) :
    componentPatches a (.inl i) = patches a (componentRules a (.inl i)) := by
  ext p
  rw [mem_componentPatches]
  constructor
  · intro hreach
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_tail with he | ⟨x,hprior,hstep⟩
    · cases he
    · cases x with
      | inr q =>
        have h := (adjacent_iff a (.inr q) (.inr p)).mpr hstep
        simp [adjacent] at h
      | inl k =>
        obtain ⟨j,hj⟩ := (adj_rule_patch_iff a k p).mp hstep
        exact Finset.mem_image.mpr ⟨(k,j),Finset.mem_product.mpr
          ⟨(mem_componentRules _ _ _).mpr ((SimpleGraph.reachable_iff_reflTransGen _ _).mpr hprior),
            Finset.mem_univ _⟩,hj⟩
  · intro hp
    obtain ⟨⟨k,j⟩,he,hlabel⟩ := Finset.mem_image.mp hp
    have hk := (mem_componentRules a (.inl i) k).mp (Finset.mem_product.mp he).1
    exact hlabel ▸ hk.trans (bubble_reaches a k j)

#print axioms componentPatches_eq_incidence

section ComponentIncidence

variable (a : Incidence d s c) (root : Fin d ⊕ Fin c)

private abbrev rules := componentRules a root
private abbrev part := componentPatches a root

/-- Give the retained rule its original index, in chronological order. -/
def originalRule (i : Fin (rules a root).card) : ↥(rules a root) :=
  (rules a root).orderIsoOfFin rfl i

/-- Give the retained patch its original index, in patch order. -/
def originalPatch (p : Fin (part a root).card) : ↥(part a root) :=
  (part a root).orderIsoOfFin rfl p

private theorem incident_patch_in_component (i : ↥(rules a root)) (j : Fin s) :
    a (i.val,j) ∈ part a root :=
  (mem_componentPatches a root _).mpr
    (((mem_componentRules a root i.val).mp i.property).trans (bubble_reaches a i.val j))

/-- Reindex one component as a standalone incidence table, retaining all
bubble edges of each of its rules. -/
def componentIncidence : Incidence (rules a root).card s (part a root).card :=
  fun (i,j) => (part a root).orderIsoOfFin rfl |>.symm
    ⟨a ((originalRule a root i).val,j), incident_patch_in_component a root (originalRule a root i) j⟩

@[simp] theorem componentIncidence_original (i : Fin (rules a root).card) (j : Fin s) :
    (originalPatch a root (componentIncidence a root (i,j))).val =
      a ((originalRule a root i).val,j) := by
  simp [componentIncidence,originalPatch]

private def originalVertex : Fin (rules a root).card ⊕ Fin (part a root).card → Fin d ⊕ Fin c :=
  Sum.map (fun i => (originalRule a root i).val) (fun p => (originalPatch a root p).val)

private theorem original_in_component (x : Fin (rules a root).card ⊕ Fin (part a root).card) :
    (graph a).Reachable root (originalVertex a root x) := by
  cases x with
  | inl i => exact (mem_componentRules a root _).mp (originalRule a root i).property
  | inr p => exact (mem_componentPatches a root _).mp (originalPatch a root p).property

private theorem exists_original (x : Fin d ⊕ Fin c) (h : (graph a).Reachable root x) :
    ∃ y, originalVertex a root y = x := by
  cases x with
  | inl i =>
    let r : ↥(rules a root) := ⟨i,(mem_componentRules a root i).mpr h⟩
    refine ⟨.inl (((rules a root).orderIsoOfFin rfl).symm r),?_⟩
    exact congrArg (fun k : ↥(rules a root) => Sum.inl k.val)
      (((rules a root).orderIsoOfFin rfl).apply_symm_apply r)
  | inr p =>
    let q : ↥(part a root) := ⟨p,(mem_componentPatches a root p).mpr h⟩
    refine ⟨.inr (((part a root).orderIsoOfFin rfl).symm q),?_⟩
    exact congrArg (fun k : ↥(part a root) => Sum.inr k.val)
      (((part a root).orderIsoOfFin rfl).apply_symm_apply q)

private theorem originalVertex_injective : Function.Injective (originalVertex a root) := by
  have hr : Function.Injective (fun i => (originalRule a root i).val) :=
    Subtype.val_injective.comp ((rules a root).orderIsoOfFin rfl).injective
  have hp : Function.Injective (fun p => (originalPatch a root p).val) :=
    Subtype.val_injective.comp ((part a root).orderIsoOfFin rfl).injective
  intro x y h
  cases x <;> cases y <;> simp only [originalVertex,Sum.map_inl,Sum.map_inr,Sum.inl.injEq,Sum.inr.injEq] at h ⊢
  · exact hr h
  · contradiction
  · contradiction
  · exact hp h

private theorem adj_of_original_adj
    {x y : Fin (rules a root).card ⊕ Fin (part a root).card}
    (h : (graph a).Adj (originalVertex a root x) (originalVertex a root y)) :
    (graph (componentIncidence a root)).Adj x y := by
  have lift {i : Fin (rules a root).card} {p : Fin (part a root).card}
      (h : (graph a).Adj (.inl (originalRule a root i).val) (.inr (originalPatch a root p).val)) :
      (graph (componentIncidence a root)).Adj (.inl i) (.inr p) := by
    obtain ⟨j,hj⟩ := (adj_rule_patch_iff a _ _).mp h
    refine (adj_rule_patch_iff _ _ _).mpr ⟨j,?_⟩
    apply ((part a root).orderIsoOfFin rfl).injective
    apply Subtype.ext
    exact (componentIncidence_original a root i j).trans hj
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      have he := (adjacent_iff a (.inl (originalRule a root i).val)
        (.inl (originalRule a root j).val)).mpr h
      simp [adjacent] at he
    | inr p => exact lift h
  | inr p =>
    cases y with
    | inl i => exact (lift h.symm).symm
    | inr q =>
      have he := (adjacent_iff a (.inr (originalPatch a root p).val)
        (.inr (originalPatch a root q).val)).mpr h
      simp [adjacent] at he

theorem componentIncidence_connected : (graph (componentIncidence a root)).Connected := by
  obtain ⟨base,hbase⟩ := exists_original a root root SimpleGraph.Reachable.rfl
  have lift {x : Fin d ⊕ Fin c} (h : Relation.ReflTransGen (graph a).Adj root x) :
      ∃ y, originalVertex a root y = x ∧ (graph (componentIncidence a root)).Reachable base y := by
    induction h with
    | refl => exact ⟨base,hbase,SimpleGraph.Reachable.rfl⟩
    | @tail u v h₁ h₂ ih =>
      obtain ⟨prev,hprev,hpath⟩ := ih
      have hr : (graph a).Reachable root v :=
        (SimpleGraph.reachable_iff_reflTransGen _ _).mpr (h₁.tail h₂)
      obtain ⟨next,hnext⟩ := exists_original a root v hr
      have hn : (graph a).Adj (originalVertex a root prev) (originalVertex a root next) := by
        rw [hprev,hnext]
        exact h₂
      exact ⟨next,hnext,hpath.trans (adj_of_original_adj a root hn).reachable⟩
  have paths (x : Fin (rules a root).card ⊕ Fin (part a root).card) :
      (graph (componentIncidence a root)).Reachable base x := by
    obtain ⟨y,hy,hr⟩ := lift ((SimpleGraph.reachable_iff_reflTransGen _ _).mp (original_in_component a root x))
    have e : y = x := originalVertex_injective a root hy
    exact e ▸ hr
  exact @SimpleGraph.Connected.mk _ _ (fun x y => (paths x).symm.trans (paths y)) ⟨base⟩

theorem component_vertices_le :
    (rules a root).card + (part a root).card ≤ (rules a root).card*s+1 := by
  obtain ⟨v,_⟩ := exists_original a root root SimpleGraph.Reachable.rfl
  exact connected_vertices_le (componentIncidence a root) (componentIncidence_connected a root) v

#print axioms componentIncidence_connected

end ComponentIncidence

#print axioms mem_component

end DeletionCode.Explicit.RulePatch
