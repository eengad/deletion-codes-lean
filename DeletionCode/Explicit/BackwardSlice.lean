import DeletionCode.Explicit.RulePatchCore

/-! Backward slices and replay of the retained entries (`d:backward-slice`,
the dependency argument of `d:supplier-retention` and `d:grammar`). -/

namespace DeletionCode.Explicit.BackwardSlice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A retained bubble keeps each immediate supplier used by its references. -/
def Closed (suppliers : ι → Finset ι) (S : Finset ι) : Prop :=
  ∀ i ∈ S, suppliers i ⊆ S

private def expand (suppliers : ι → Finset ι) (S : Finset ι) : Finset ι :=
  S ∪ S.biUnion suppliers

omit [Fintype ι] in
private theorem expand_card_lt (f : ι → Finset ι) (S : Finset ι) (h : expand f S ≠ S) :
    S.card < (expand f S).card :=
  Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left,Ne.symm h⟩)

/-- Start with just the final bubbles and repeatedly add their suppliers. -/
def slice {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Finset ι) (S : Finset ι) : Finset ι :=
  if _h : expand f S = S then S else slice f (expand f S)
termination_by Fintype.card ι - S.card
decreasing_by
  have := expand_card_lt f S _h
  have := (expand f S).card_le_univ
  omega

/-- The computed set is the least supplier-closed set containing the finals. -/
theorem slice_spec (f : ι → Finset ι) (S : Finset ι) :
    S ⊆ slice f S ∧ Closed f (slice f S) ∧
      ∀ T, S ⊆ T → Closed f T → slice f S ⊆ T := by
  rw [slice]
  split
  next h =>
    refine ⟨Finset.Subset.rfl,?_,fun _ hsub _ => hsub⟩
    intro i hi j hj
    rw [← h]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,hi,hj⟩)
  next h =>
    obtain ⟨h₁,h₂,h₃⟩ := slice_spec f (expand f S)
    refine ⟨Finset.subset_union_left.trans h₁,h₂,?_⟩
    intro T hST hc
    apply h₃ _ _ hc
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact hST hj
    · obtain ⟨i,hi,hij⟩ := Finset.mem_biUnion.mp hj
      exact hc i (hST hi) hij
termination_by Fintype.card ι - S.card
decreasing_by
  have := expand_card_lt f S ‹expand f S ≠ S›
  have := (expand f S).card_le_univ
  omega

/-- If each supplier lies in its consumer's patch, recursive slicing uses
exactly the patches of the final bubbles. This is the anchor count in replay. -/
theorem patches_eq {κ : Type*} [DecidableEq κ] (f : ι → Finset ι) (patch : ι → κ)
    (hloc : ∀ i, ∀ j ∈ f i, patch j = patch i) (S : Finset ι) :
    (slice f S).image patch = S.image patch := by
  obtain ⟨hfinal,_,hmin⟩ := slice_spec f S
  apply Finset.Subset.antisymm _ (Finset.image_mono patch hfinal)
  let T := Finset.univ.filter fun i => patch i ∈ S.image patch
  have hT : S ⊆ T := fun i hi =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image_of_mem patch hi⟩
  have hc : Closed f T := by
    intro i hi j hj
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hloc i j hj ▸ (Finset.mem_filter.mp hi).2⟩
  intro k hk
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
  exact (Finset.mem_filter.mp (hmin T hT hc hi)).2

section Replay

variable {α : Type*}

/-- An entry can use its own data and the stored results of its named suppliers.
Original bubble identifiers remain stable when entries are filtered. -/
abbrev Eval (f : ι → Finset ι) (α : Type*) := (i : ι) → (↥(f i) → Option α) → Option α

private def update (f : ι → Finset ι) (eval : Eval f α) (m : ι → Option α) (i : ι) :=
  Function.update m i (eval i (fun j => m j.val))

def replay (f : ι → Finset ι) (eval : Eval f α) (order : List ι) (m : ι → Option α) :
    ι → Option α :=
  order.foldl (update f eval) m

omit [Fintype ι] in
private theorem replay_closed (f : ι → Finset ι) (eval : Eval f α) (T : Finset ι) (hc : Closed f T)
    (order : List ι) (m m' : ι → Option α) (heq : ∀ i ∈ T, m i = m' i) :
    ∀ j ∈ T, replay f eval order m j = replay f eval (order.filter (· ∈ T)) m' j := by
  induction order generalizing m m' with
  | nil => exact heq
  | cons i rest ih =>
    by_cases hi : i ∈ T
    · simp [hi, replay]
      apply ih
      intro j hj
      by_cases hji : j = i
      · subst j
        have hv : (fun v : ↥(f i) => m v.val) = (fun v : ↥(f i) => m' v.val) :=
          funext (fun v => heq _ (hc i hi v.property))
        simp [update,hv]
      · simpa [update,hji] using heq j hj
    · simp [hi, replay]
      apply ih
      intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      simpa [update,hji] using heq j hj

/-- Filtering to the computed backward slice reproduces each retained result,
using the original chronological order. In particular it reproduces the final
lifts whenever the full history evaluates them successfully. -/
theorem replay_slice (f : ι → Finset ι) (eval : Eval f α) (S : Finset ι)
    (order : List ι) (m : ι → Option α) :
    ∀ j ∈ slice f S, replay f eval order m j =
      replay f eval (order.filter (· ∈ slice f S)) m j :=
  replay_closed f eval _ (slice_spec f S).2.1 order m m (fun _ _ => rfl)

end Replay

section Renumber

variable {N : ℕ} {α : Type*}

/-- Original identifier of a bubble at a given index in the shortened history. -/
def original (T : Finset (Fin N)) := T.orderEmbOfFin rfl

/-- The compact index of a retained bubble is its rank in chronological order. -/
def number (T : Finset (Fin N)) (j : ↥T) : Fin T.card := (T.orderIsoOfFin rfl).symm j

@[simp] theorem original_number (T : Finset (Fin N)) (j : ↥T) :
    original T (number T j) = j.val :=
  congrArg Subtype.val ((T.orderIsoOfFin rfl).apply_symm_apply j)

/-- Translate all supplier references to indices in the shortened history. -/
def references (f : Fin N → Finset (Fin N)) (T : Finset (Fin N)) (i : Fin T.card) :
    Finset (Fin T.card) := Finset.univ.filter fun j => original T j ∈ f (original T i)

theorem references_earlier (f : Fin N → Finset (Fin N)) (T : Finset (Fin N))
    (hearlier : ∀ i, ∀ j ∈ f i, j < i) {i j : Fin T.card} (hm : j ∈ references f T i) : j < i :=
  (original T).lt_iff_lt.mp (hearlier _ _ (Finset.mem_filter.mp hm).2)

private def supplierIndex (f : Fin N → Finset (Fin N)) (T : Finset (Fin N)) (hc : Closed f T)
    (i : Fin T.card) (v : ↥(f (original T i))) : ↥(references f T i) :=
  let hv := hc (original T i) (T.orderEmbOfFin_mem rfl i) v.property
  ⟨number T ⟨v.val,hv⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp⟩⟩

/-- The same local evaluator, with each supplier read at its translated index. -/
def translatedEval (f : Fin N → Finset (Fin N)) (eval : Eval f α) (T : Finset (Fin N))
    (hc : Closed f T) : Eval (references f T) α :=
  fun i read => eval (original T i) (fun v => read (supplierIndex f T hc i v))

def translatedOrder (T : Finset (Fin N)) (order : List (Fin N)) : List (Fin T.card) :=
  order.filterMap (fun i => if h : i ∈ T then some (number T ⟨i,h⟩) else none)

private theorem lift_order (T : Finset (Fin N)) (order : List (Fin N)) :
    (translatedOrder T order).map (original T) = order.filter (· ∈ T) := by
  induction order with
  | nil => rfl
  | cons i xs ih =>
    by_cases h : i ∈ T <;> simp_all [translatedOrder]

private theorem replay_renumber (f : Fin N → Finset (Fin N)) (eval : Eval f α) (T : Finset (Fin N))
    (hc : Closed f T) (order : List (Fin T.card)) (m : Fin N → Option α) (m' : Fin T.card → Option α)
    (heq : ∀ i, m (original T i) = m' i) :
    ∀ j, replay f eval (order.map (original T)) m (original T j) =
      replay (references f T) (translatedEval f eval T hc) order m' j := by
  induction order generalizing m m' with
  | nil => exact heq
  | cons i rest ih =>
    simp only [List.map_cons,replay,List.foldl_cons]
    apply ih
    intro j
    by_cases hj : j = i
    · subst j
      simp only [update,Function.update_self,translatedEval]
      apply congrArg (eval (original T i))
      funext v
      simpa only [supplierIndex,original_number] using heq (supplierIndex f T hc i v).val
    · simpa [update,hj,(original T).injective.ne hj] using heq j

/-- The slice with translated references gives the full-history result for
every retained bubble, including failures. Earlier references remain earlier. -/
theorem replay_numbered_slice (f : Fin N → Finset (Fin N)) (eval : Eval f α)
    (S : Finset (Fin N)) (order : List (Fin N)) (m : Fin N → Option α) :
    let T := slice f S
    ∀ j : Fin T.card, replay f eval order m (original T j) =
      replay (references f T) (translatedEval f eval T (slice_spec f S).2.1)
        (translatedOrder T order) (m ∘ original T) j := by
  intro T j
  have keep := replay_slice f eval S order m (original T j) (T.orderEmbOfFin_mem rfl j)
  refine keep.trans ?_
  rw [← lift_order T order]
  exact replay_renumber f eval T (slice_spec f S).2.1 (translatedOrder T order) m _ (fun _ => rfl) j

end Renumber

#print axioms replay_numbered_slice

open RulePatch

/-- For a peeled core the slice needs at most `t*r` patches even if the full
supplier closure contains many additional bubbles. -/
theorem core_patch_bound {d c t : ℕ} (a : Incidence d (2*t) c)
    (f : Fin d × Fin (2*t) → Finset (Fin d × Fin (2*t)))
    (hloc : ∀ i, ∀ j ∈ f i, a j = a i) :
    ((slice f (edges (core a))).image a).card ≤ t*(core a).card := by
  rw [patches_eq f a hloc]
  exact patch_bound a _ (peel_terminal a Finset.univ).1

/-- Only original positions of the final bubbles contribute to the active set.
Each of their `s*r` occurrences can contribute at most `2L+b` positions. -/
theorem active_positions_bound {d s ℓ L b : ℕ} (rules : Finset (Fin d))
    (positions : Fin d × Fin s → Finset (Fin ℓ))
    (h : ∀ e ∈ edges rules, (positions e).card ≤ 2*L+b) :
    ((edges rules).biUnion positions).card ≤ s*rules.card*(2*L+b) := by
  calc
    _ ≤ ∑ e ∈ edges rules, (positions e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ edges rules, (2*L+b) := Finset.sum_le_sum h
    _ = _ := by simp [edges, Nat.mul_comm]

#print axioms slice_spec
#print axioms replay_slice
#print axioms core_patch_bound
#print axioms active_positions_bound

end DeletionCode.Explicit.BackwardSlice
