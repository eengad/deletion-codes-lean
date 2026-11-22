import DeletionCode.Explicit.MatchingPatterns

/-! Connected components and exact completion counts for a fixed matching. -/
namespace DeletionCode.Explicit.MatchingEnumeration

open MatchingWeight
open scoped BigOperators

variable {ℓ K q k : ℕ}

abbrev Labels := List ℕ

def labelAt (labels : Labels) (i : ℕ) : ℕ := labels.getD i 0

/-- Joining an edge replaces the second endpoint's label throughout its component. -/
def mergeLabels (labels : Labels) (edge : ℕ × ℕ) : Labels :=
  if edge.1 < labels.length then
    let a := labelAt labels edge.1
    let b := labelAt labels edge.2
    labels.map fun i => if i = b then a else i
  else labels

def components (ℓ : ℕ) (es : Edges) : Labels := es.foldl mergeLabels (List.range ℓ)

def consistent (pad : Fin q) (p : QWord q) (labels : Labels) : Bool :=
  (List.range p.length).all fun i => (List.range p.length).all fun j =>
    decide (labelAt labels i ≠ labelAt labels j) || decide (p.getD i pad = p.getD j pad)

def freeCount (ℓ k : ℕ) (labels : Labels) : ℕ :=
  (List.range ℓ).countP fun i =>
    decide (labelAt labels i = i) && !(List.range k).any (fun j => decide (labelAt labels j = i))

def completions (pad : Fin q) (ℓ : ℕ) (p : QWord q) (es : Edges) : ℕ :=
  let labels := components ℓ es
  if consistent pad p labels then q ^ freeCount ℓ p.length labels else 0

private abbrev Leaders (ℓ : ℕ) := Fin ℓ → Fin ℓ

private def merge (r : Leaders ℓ) (e : Fin ℓ × Fin ℓ) : Leaders ℓ :=
  fun i => if r i = r e.2 then r e.1 else r i

private def labelsOf (r : Leaders ℓ) : Labels := List.ofFn fun i => (r i).val

private theorem labelAt_labelsOf (r : Leaders ℓ) (i : Fin ℓ) : labelAt (labelsOf r) i.val = (r i).val := by
  exact prefix_getD (fun j => (r j).val) i 0

private theorem mergeLabels_eq (r : Leaders ℓ) (e : Fin ℓ × Fin ℓ) :
    mergeLabels (labelsOf r) (e.1.val,e.2.val) = labelsOf (merge r e) := by
  unfold mergeLabels
  rw [ite_eq_left (show e.1.val < (labelsOf r).length from
    by rw [labelsOf,List.length_ofFn]; exact e.1.isLt)]
  rw [labelAt_labelsOf r e.1, labelAt_labelsOf r e.2]
  simp only [labelsOf, List.map_ofFn, Function.comp_def]
  congr 1
  funext i
  have he : (r i).val = (r e.2).val ↔ r i = r e.2 := ⟨Fin.ext, congrArg Fin.val⟩
  by_cases h : r i = r e.2 <;> simp [merge,he,h]

private theorem components_eq (es : List (Fin ℓ × Fin ℓ)) :
    components ℓ (es.map fun e => (e.1.val,e.2.val)) = labelsOf (es.foldl merge id) := by
  have hrange : List.range ℓ = labelsOf (id : Leaders ℓ) := by
    apply List.ext_getElem (by simp [labelsOf])
    intro i hi hj
    simp only [List.getElem_range, labelsOf, List.getElem_ofFn, id_eq]
  unfold components
  rw [hrange]
  suffices ∀ r : Leaders ℓ, (es.map fun e => (e.1.val,e.2.val)).foldl mergeLabels (labelsOf r) =
      labelsOf (es.foldl merge r) by exact this id
  induction es with
  | nil => intro r; rfl
  | cons e es ih =>
    intro r
    simp only [List.map_cons, List.foldl_cons, mergeLabels_eq, ih]

private abbrev Respects (r : Leaders ℓ) (x : Fin ℓ → Fin q) : Prop :=
  ∀ i j, r i = r j → x i = x j

private theorem respects_merge (r : Leaders ℓ) (e : Fin ℓ × Fin ℓ) (x : Fin ℓ → Fin q) :
    Respects (merge r e) x ↔ Respects r x ∧ x e.1 = x e.2 := by
  constructor
  · intro h
    refine ⟨fun i j hij => h i j (by simp [merge,hij]), h e.1 e.2 ?_⟩
    simp [merge]
  · rintro ⟨h,he⟩ i j hij
    by_cases hi : r i = r e.2 <;> by_cases hj : r j = r e.2 <;>
      simp only [merge,hi,hj,↓reduceIte] at hij
    · exact h i j (hi.trans hj.symm)
    · exact (h i e.2 hi).trans (he.symm.trans (h e.1 j hij))
    · exact (h i e.1 hij).trans (he.trans (h e.2 j hj.symm))
    · exact h i j hij

private theorem merge_idempotent (r : Leaders ℓ) (h : ∀ i, r (r i) = r i)
    (e : Fin ℓ × Fin ℓ) : ∀ i, merge r e (merge r e i) = merge r e i := by
  intro i
  by_cases hi : r i = r e.2
  · by_cases he : r e.1 = r e.2 <;> simp [merge,hi,h,he]
  · simp [merge,hi,h]

private theorem fold_idempotent (es : List (Fin ℓ × Fin ℓ)) (r : Leaders ℓ)
    (h : ∀ i, r (r i) = r i) : ∀ i, es.foldl merge r (es.foldl merge r i) = es.foldl merge r i := by
  induction es generalizing r with
  | nil => exact h
  | cons e es ih => exact ih _ (merge_idempotent r h e)

private theorem fold_respects (es : List (Fin ℓ × Fin ℓ)) (r : Leaders ℓ) (x : Fin ℓ → Fin q) :
    Respects (es.foldl merge r) x ↔ Respects r x ∧ ∀ e ∈ es, x e.1 = x e.2 := by
  induction es generalizing r with
  | nil => simp
  | cons e es ih =>
    rw [List.foldl_cons, ih, respects_merge]
    simp only [List.forall_mem_cons, and_assoc]

private abbrev Supplied (hk : k ≤ ℓ) (r : Leaders ℓ) (i : Fin ℓ) : Prop :=
  ∃ j : Fin k, r (Fin.castLE hk j) = i

private abbrev PrefixAgrees (hk : k ≤ ℓ) (r : Leaders ℓ) (u : Fin k → Fin q) : Prop :=
  ∀ i j, r (Fin.castLE hk i) = r (Fin.castLE hk j) → u i = u j

abbrev PrefixExtends (hk : k ≤ ℓ) (u : Fin k → Fin q) (x : Fin ℓ → Fin q) : Prop :=
  ∀ j : Fin k, x (Fin.castLE hk j) = u j

private theorem consistent_iff (pad : Fin q) (hk : k ≤ ℓ) (r : Leaders ℓ) (u : Fin k → Fin q) :
    consistent pad (List.ofFn u) (labelsOf r) = true ↔ PrefixAgrees hk r u := by
  simp only [consistent, List.length_ofFn, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq]
  have hr (i : Fin k) : labelAt (labelsOf r) i.val = (r (Fin.castLE hk i)).val :=
    labelAt_labelsOf r (Fin.castLE hk i)
  constructor
  · intro h i j hij
    obtain ho | he := h i i.isLt j j.isLt
    · exact False.elim (ho (by rw [hr i,hr j,hij]))
    · rw [prefix_getD u i, prefix_getD u j] at he
      exact he
  · intro h i hi j hj
    let a : Fin k := ⟨i,hi⟩
    let b : Fin k := ⟨j,hj⟩
    by_cases he : labelAt (labelsOf r) i = labelAt (labelsOf r) j
    · right
      have hval := (hr a).symm.trans (he.trans (hr b))
      exact (prefix_getD u a pad).trans ((h a b (Fin.ext hval)).trans (prefix_getD u b pad).symm)
    · exact Or.inl he

private theorem freeCount_eq (hk : k ≤ ℓ) (r : Leaders ℓ) :
    freeCount ℓ k (labelsOf r) =
      (Finset.univ.filter fun i : Fin ℓ => r i = i ∧ ¬ Supplied hk r i).card := by
  let test (i : ℕ) := decide (labelAt (labelsOf r) i = i) &&
    !(List.range k).any (fun j => decide (labelAt (labelsOf r) j = i))
  have htest (i : Fin ℓ) : test i.val = true ↔ r i = i ∧ ¬ Supplied hk r i := by
    simp only [test, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, labelAt_labelsOf]
    apply and_congr
    · exact ⟨Fin.ext, congrArg Fin.val⟩
    · have hs : (List.range k).any (fun j => decide (labelAt (labelsOf r) j = i.val)) = true ↔
          Supplied hk r i := by
        simp only [Supplied, List.any_eq_true, List.mem_range, decide_eq_true_eq]
        refine ⟨fun ⟨j,hj,he⟩ => ⟨⟨j,hj⟩,Fin.ext ((labelAt_labelsOf r (Fin.castLE hk ⟨j,hj⟩)).symm.trans he)⟩,
          fun ⟨j,hj⟩ => ⟨j.val,j.isLt,(labelAt_labelsOf r (Fin.castLE hk j)).trans (congrArg Fin.val hj)⟩⟩
      exact Bool.eq_false_iff.trans (not_congr hs)
  have hset : ((List.range ℓ).filter test).toFinset =
      (Finset.univ.filter fun i : Fin ℓ => r i = i ∧ ¬ Supplied hk r i).map Fin.valEmbedding := by
    ext j
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_map,
      Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply]
    exact ⟨fun ⟨hj, ht⟩ => ⟨⟨j,hj⟩,(htest _).mp ht,rfl⟩,
      fun ⟨i,hi,he⟩ => he ▸ ⟨i.isLt,(htest i).mpr hi⟩⟩
  change (List.range ℓ).countP test = _
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (List.nodup_range.filter _),
    hset, Finset.card_map]

private theorem respecting_count (hk : k ≤ ℓ) (r : Leaders ℓ) (u : Fin k → Fin q)
    (hidem : ∀ i, r (r i) = r i) (hpre : PrefixAgrees hk r u) :
    Nat.card {x : Fin ℓ → Fin q // Respects r x ∧ PrefixExtends hk u x} = q ^ freeCount ℓ k (labelsOf r) := by
  classical
  let Free := {i : Fin ℓ // r i = i ∧ ¬ Supplied hk r i}
  let pick (f : Free → Fin q) (i : Fin ℓ) (hi : r i = i) : Fin q :=
    if h : Supplied hk r i then u (Classical.choose h) else f ⟨i,hi,h⟩
  have hforce (f : Free → Fin q) (j : Fin k) : pick f (r (Fin.castLE hk j)) (hidem _) = u j := by
    let hi : Supplied hk r (r (Fin.castLE hk j)) := ⟨j,rfl⟩
    simp only [pick,dite_eq_left hi]
    exact hpre _ _ (Classical.choose_spec hi)
  have hvalue (f : Free → Fin q) (a b : Fin ℓ) (ha : r a = a) (hb : r b = b) (he : a = b) :
      pick f a ha = pick f b hb := by subst b; rfl
  let equiv : {x : Fin ℓ → Fin q // Respects r x ∧ PrefixExtends hk u x} ≃ (Free → Fin q) :=
    { toFun := fun x i => x.val i.val
      invFun := fun f => ⟨fun i => pick f (r i) (hidem i),
        ⟨fun i j he => hvalue f (r i) (r j) (hidem i) (hidem j) he, hforce f⟩⟩
      left_inv := by
        intro x
        apply Subtype.ext
        funext i
        change pick (fun j => x.val j.val) (r i) (hidem i) = x.val i
        by_cases h : Supplied hk r (r i)
        · rw [show pick (fun j => x.val j.val) (r i) (hidem i) = u (Classical.choose h) by
            simp only [pick,dite_eq_left h]]
          exact (x.2.2 (Classical.choose h)).symm.trans (x.2.1 _ _ (Classical.choose_spec h))
        · simp only [pick,dite_eq_right h]
          exact x.2.1 _ _ (hidem i)
      right_inv := by
        intro f
        funext i
        have hi := i.2.1
        have hn := i.2.2
        change pick f (r i.val) (hidem i.val) = f i
        rw [hvalue f _ i.val (hidem i.val) hi hi]
        simp [pick,hn] }
  rw [Nat.card_congr equiv, Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, freeCount_eq hk]
  congr 1
  rw [Fintype.card_subtype]

theorem completions_eq (pad : Fin q) (hk : k ≤ ℓ) (u : Fin k → Fin q)
    (es : List (Fin ℓ × Fin ℓ)) :
    completions pad ℓ (List.ofFn u) (es.map fun e => (e.1.val,e.2.val)) =
      ∑ x : Fin ℓ → Fin q, if (∀ e ∈ es, x e.1 = x e.2) ∧ PrefixExtends hk u x then 1 else 0 := by
  classical
  let r := es.foldl merge (id : Leaders ℓ)
  have hidem := fold_idempotent es (id : Leaders ℓ) (fun _ => rfl)
  have hrs (x : Fin ℓ → Fin q) : Respects r x ↔ ∀ e ∈ es, x e.1 = x e.2 := by
    rw [fold_respects]
    exact and_iff_right (fun _ _ he => congrArg x he)
  simp only [completions, components_eq, List.length_ofFn, consistent_iff pad hk]
  change (if PrefixAgrees hk r u then q^freeCount ℓ k (labelsOf r) else 0) = _
  simp_rw [← hrs]
  by_cases h : PrefixAgrees hk r u
  · rw [ite_eq_left h, ← respecting_count hk r u hidem h, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Finset.sum_boole]
    rfl
  · have hh (x : Fin ℓ → Fin q) : ¬ (Respects r x ∧ PrefixExtends hk u x) := by
      rintro ⟨hx,hu⟩
      exact h (fun i j he => (hu i).symm.trans ((hx _ _ he).trans (hu j)))
    simp [h,hh]

theorem pattern_completions_eq (pad : Fin q) (hk : k ≤ ℓ) (u : Fin k → Fin q)
    (p : Pattern ℓ K) :
    completions pad ℓ (List.ofFn u) (edges (encodePattern p)) =
      ∑ x : Fin ℓ → Fin q, if Satisfies x p ∧ PrefixExtends hk u x then 1 else 0 := by
  rw [edges_encode]
  change completions pad ℓ (List.ofFn u)
    (List.ofFn ((fun e : Fin ℓ × Fin ℓ => (e.1.val,e.2.val)) ∘ fun i => (p.1 i,p.2 i))) = _
  rw [← List.map_ofFn, completions_eq pad hk (es := List.ofFn (fun i => (p.1 i,p.2 i)))]
  apply Finset.sum_congr rfl
  intro x _
  have he : (∀ e ∈ List.ofFn (fun i => (p.1 i,p.2 i)), x e.1 = x e.2) ↔ Satisfies x p := by
    refine ⟨fun h i => h _ (List.mem_ofFn.mpr ⟨i,rfl⟩), ?_⟩
    intro h e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact h i
  simp only [he]

#print axioms pattern_completions_eq

end DeletionCode.Explicit.MatchingEnumeration
