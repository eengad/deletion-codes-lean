import DeletionCode.Explicit.PatchInventory

/-! Coalesce intersecting closed creation intervals in source order (`d:patches`). -/

namespace DeletionCode.Explicit.LetterGraphCuts

open LocalBudget

/-- Closed interval between two source positions. -/
structure CreationInterval (ℓ : ℕ) where
  first : Fin ℓ
  last : Fin ℓ
  first_le_last : first ≤ last

namespace CreationInterval

variable {ℓ : ℕ}

def Contains (outer inner : CreationInterval ℓ) : Prop :=
  outer.first ≤ inner.first ∧ inner.last ≤ outer.last

instance (outer inner : CreationInterval ℓ) : Decidable (outer.Contains inner) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Contains.refl (i : CreationInterval ℓ) : i.Contains i := ⟨le_rfl,le_rfl⟩

theorem Contains.trans {i j k : CreationInterval ℓ} (hi : i.Contains j) (hj : j.Contains k) :
    i.Contains k := ⟨hi.1.trans hj.1,hj.2.trans hi.2⟩

def hull (i j : CreationInterval ℓ) : CreationInterval ℓ where
  first := min i.first j.first
  last := max i.last j.last
  first_le_last := (min_le_left _ _).trans (i.first_le_last.trans (le_max_left _ _))

theorem hull_contains_left (i j : CreationInterval ℓ) : (i.hull j).Contains i :=
  ⟨min_le_left _ _,le_max_left _ _⟩

theorem hull_contains_right (i j : CreationInterval ℓ) : (i.hull j).Contains j :=
  ⟨min_le_right _ _,le_max_right _ _⟩

theorem contains_hull {p i j : CreationInterval ℓ} (hi : p.Contains i) (hj : p.Contains j) :
    p.Contains (i.hull j) :=
  ⟨le_min hi.1 hj.1,max_le hi.2 hj.2⟩

/-- Each input interval lies inside a member of the covering list. -/
def Covers (cover input : List (CreationInterval ℓ)) : Prop :=
  ∀ i ∈ input, ∃ p ∈ cover, p.Contains i

theorem Covers.trans {a b c : List (CreationInterval ℓ)} (h : Covers a b) (h' : Covers b c) :
    Covers a c := by
  intro i hi
  obtain ⟨p,hp,hpi⟩ := h' i hi
  obtain ⟨q,hq,hqp⟩ := h p hp
  exact ⟨q,hq,hqp.trans hpi⟩

/-- The pairwise orientation also records that adjacent patches do not intersect. -/
def Separated (patches : List (CreationInterval ℓ)) : Prop :=
  patches.Pairwise (fun a b => a.last < b.first)

structure Partition (input output : List (CreationInterval ℓ)) : Prop where
  separated : Separated output
  covers : Covers output input
  finest : ∀ above, Separated above → Covers above input → Covers above output

private theorem same_container {xs : List (CreationInterval ℓ)} (hs : Separated xs)
    {i j : CreationInterval ℓ} (hi : i ∈ xs) (hj : j ∈ xs)
    (hl : i.first ≤ j.last) (hr : j.first ≤ i.last) : i = j := by
  obtain ⟨a,ha,he⟩ := List.mem_iff_getElem.mp hi
  obtain ⟨b,hb,hf⟩ := List.mem_iff_getElem.mp hj
  rcases lt_trichotomy a b with hab | hab | hab
  · have sep := List.pairwise_iff_getElem.mp hs a b ha hb hab
    exact (not_lt_of_ge hr (by simpa [he,hf] using sep)).elim
  · subst b
    exact he.symm.trans hf
  · have sep := List.pairwise_iff_getElem.mp hs b a hb ha hab
    exact (not_lt_of_ge hl (by simpa [he,hf] using sep)).elim

/-- Insert the leftmost interval, absorbing each overlapping patch at the front.
Equality at a boundary is an intersection of closed intervals. -/
private def mergeLeft (i : CreationInterval ℓ) : List (CreationInterval ℓ) → List (CreationInterval ℓ)
  | [] => [i]
  | j :: js => if j.first ≤ i.last then mergeLeft (i.hull j) js else i :: j :: js

private theorem mergeLeft_lower {p : Fin ℓ} {i : CreationInterval ℓ}
    {xs : List (CreationInterval ℓ)} (hi : p ≤ i.first) (hx : ∀ j ∈ xs, p ≤ j.first) :
    ∀ j ∈ mergeLeft i xs, p ≤ j.first := by
  induction xs generalizing i with
  | nil =>
    intro j hj
    have e : j = i := List.mem_singleton.mp hj
    simpa [e] using hi
  | cons k ks ih =>
    rw [mergeLeft]
    split
    · exact ih (le_min hi (hx k (List.mem_cons_self ..)))
        (fun j hj => hx j (List.mem_cons_of_mem _ hj))
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hx j hj

private theorem mergeLeft_partition {i : CreationInterval ℓ} {xs : List (CreationInterval ℓ)}
    (hfirst : ∀ j ∈ xs, i.first ≤ j.first) (hsep : Separated xs) :
    Partition (i :: xs) (mergeLeft i xs) := by
  induction xs generalizing i with
  | nil =>
    refine ⟨List.pairwise_singleton _ _,?_,fun _ _ h => h⟩
    intro j hj
    exact ⟨j,hj,Contains.refl j⟩
  | cons j js ih =>
    have hij := hfirst j (List.mem_cons_self ..)
    have hrest := fun k (hk : k ∈ js) => hfirst k (List.mem_cons_of_mem _ hk)
    obtain ⟨hsepj,hsepjs⟩ := List.pairwise_cons.mp hsep
    rw [mergeLeft]
    split
    next ht =>
      have hp := ih (i := i.hull j) (fun k hk => (min_le_left _ _).trans (hrest k hk)) hsepjs
      refine ⟨hp.separated,hp.covers.trans ?_,?_⟩
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact ⟨_,List.mem_cons_self ..,hull_contains_left _ _⟩
        · rcases List.mem_cons.mp hk with rfl | hk
          · exact ⟨_,List.mem_cons_self ..,hull_contains_right _ _⟩
          · exact ⟨k,List.mem_cons_of_mem _ hk,Contains.refl k⟩
      · intro Q hQ hcover
        apply hp.finest Q hQ
        intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · obtain ⟨p,hp,hpi⟩ := hcover i (List.mem_cons_self ..)
          obtain ⟨q,hq,hqj⟩ := hcover j (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          have e := same_container hQ hp hq
            ((hpi.1.trans hij).trans (j.first_le_last.trans hqj.2))
            ((hqj.1.trans ht).trans hpi.2)
          subst q
          exact ⟨p,hp,contains_hull hpi hqj⟩
        · exact hcover k (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hk))
    next ht =>
      refine ⟨List.pairwise_cons.mpr ⟨?_,hsep⟩,?_,fun _ _ h => h⟩
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact lt_of_not_ge ht
        · exact (lt_of_not_ge ht).trans ((j.first_le_last).trans_lt (hsepj k hk))
      · intro k hk
        exact ⟨k,hk,Contains.refl k⟩

private def mergeSorted (xs : List (CreationInterval ℓ)) : List (CreationInterval ℓ) :=
  xs.foldr mergeLeft []

private theorem mergeSorted_lower {p : Fin ℓ} {xs : List (CreationInterval ℓ)}
    (h : ∀ j ∈ xs, p ≤ j.first) : ∀ j ∈ mergeSorted xs, p ≤ j.first := by
  induction xs with
  | nil => simp [mergeSorted]
  | cons i xs ih =>
    exact mergeLeft_lower (h i (List.mem_cons_self ..))
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

private theorem mergeSorted_partition {xs : List (CreationInterval ℓ)}
    (h : xs.Pairwise (fun i j => i.first ≤ j.first)) : Partition xs (mergeSorted xs) := by
  induction xs with
  | nil =>
    refine ⟨List.Pairwise.nil,?_,?_⟩
    · intro _ hi
      simp at hi
    · intro _ _ _ _ hi
      simp [mergeSorted] at hi
  | cons i xs ih =>
    obtain ⟨hix,hxs⟩ := List.pairwise_cons.mp h
    have hx := ih hxs
    have hp := mergeLeft_partition (i := i) (mergeSorted_lower hix) hx.separated
    refine ⟨hp.separated,hp.covers.trans ?_,?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨j,List.mem_cons_self ..,Contains.refl j⟩
      · obtain ⟨p,hp,hpj⟩ := hx.covers j hj
        exact ⟨p,List.mem_cons_of_mem _ hp,hpj⟩
    · intro Q hQ hcover
      apply hp.finest Q hQ
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hcover j (List.mem_cons_self ..)
      · exact hx.finest Q hQ (fun j hj => hcover j (List.mem_cons_of_mem _ hj)) j hj

def coalesce (xs : List (CreationInterval ℓ)) : List (CreationInterval ℓ) :=
  mergeSorted (xs.mergeSort (fun i j => decide (i.first ≤ j.first)))

/-- The executable merge gives the finest ordered, disjoint cover of the
creation intervals. Thus it merges intersecting intervals transitively,
and retains a boundary whenever the two sides are disjoint. -/
theorem coalesce_partition (xs : List (CreationInterval ℓ)) : Partition xs (coalesce xs) := by
  let sorted := xs.mergeSort (fun i j => decide (i.first ≤ j.first))
  have hs : sorted.Pairwise (fun i j => i.first ≤ j.first) := by
    have hp := List.pairwise_mergeSort (le := fun (i j : CreationInterval ℓ) => decide (i.first ≤ j.first))
      (fun a b c hab hbc => decide_eq_true ((of_decide_eq_true hab).trans (of_decide_eq_true hbc)))
      (fun a b => by simpa using le_total a.first b.first) xs
    simpa [sorted] using hp
  have hm (i : CreationInterval ℓ) : i ∈ sorted ↔ i ∈ xs :=
    (List.mergeSort_perm xs _).mem_iff
  have hp := mergeSorted_partition hs
  exact ⟨hp.separated,fun i hi => hp.covers i ((hm i).mpr hi),
    fun q hq hc => hp.finest q hq (fun i hi => hc i ((hm i).mp hi))⟩

private theorem mergeLeft_has_input {i : CreationInterval ℓ} {xs : List (CreationInterval ℓ)}
    {p : CreationInterval ℓ} (hp : p ∈ mergeLeft i xs) :
    ∃ t ∈ i :: xs, p.Contains t := by
  induction xs generalizing i with
  | nil =>
    have e : p = i := List.mem_singleton.mp hp
    exact ⟨p,e ▸ List.mem_cons_self ..,Contains.refl p⟩
  | cons j js ih =>
    rw [mergeLeft] at hp
    split at hp
    · obtain ⟨t,ht,hpt⟩ := ih hp
      rcases List.mem_cons.mp ht with ht | ht
      · subst t
        exact ⟨i,List.mem_cons_self ..,hpt.trans (hull_contains_left i j)⟩
      · exact ⟨t,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht),hpt⟩
    · exact ⟨p,hp,Contains.refl p⟩

private theorem mergeSorted_has_input {xs : List (CreationInterval ℓ)}
    {p : CreationInterval ℓ} (hp : p ∈ mergeSorted xs) : ∃ i ∈ xs, p.Contains i := by
  induction xs generalizing p with
  | nil => simp [mergeSorted] at hp
  | cons i xs ih =>
    obtain ⟨t,ht,hpt⟩ := mergeLeft_has_input hp
    rcases List.mem_cons.mp ht with ht | ht
    · subst t
      exact ⟨i,List.mem_cons_self ..,hpt⟩
    · obtain ⟨j,hj,htj⟩ := ih ht
      exact ⟨j,List.mem_cons_of_mem _ hj,hpt.trans htj⟩

theorem coalesce_has_input {xs : List (CreationInterval ℓ)}
    {p : CreationInterval ℓ} (hp : p ∈ coalesce xs) : ∃ i ∈ xs, p.Contains i := by
  obtain ⟨i,hi,hpi⟩ := mergeSorted_has_input hp
  exact ⟨i,(List.mergeSort_perm xs _).mem_iff.mp hi,hpi⟩

/-- Locate the index of the patch containing a specified interval. -/
def locate (patches : List (CreationInterval ℓ)) (i : CreationInterval ℓ) :
    Option (Fin patches.length) :=
  (List.finRange patches.length).find? (fun p => decide ((patches.get p).Contains i))

theorem contains_of_locate {patches : List (CreationInterval ℓ)} {i : CreationInterval ℓ}
    {p : Fin patches.length} (h : locate patches i = some p) : (patches.get p).Contains i :=
  of_decide_eq_true (List.find?_some (p := fun q => decide ((patches.get q).Contains i)) h)

theorem locate_isSome {patches : List (CreationInterval ℓ)} {i : CreationInterval ℓ}
    (h : ∃ p ∈ patches, p.Contains i) : (locate patches i).isSome := by
  obtain ⟨p,hp,hpi⟩ := h
  obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hp
  cases hfind : locate patches i with
  | some => trivial
  | none =>
    have hn := List.find?_eq_none.mp hfind ⟨j,hj⟩ (List.mem_finRange ⟨j,hj⟩)
    exact (hn (by simpa [he] using hpi)).elim

theorem containing_index_unique {patches : List (CreationInterval ℓ)} (h : Separated patches)
    {i : CreationInterval ℓ} {p q : Fin patches.length}
    (hp : (patches.get p).Contains i) (hq : (patches.get q).Contains i) : p = q := by
  rcases lt_trichotomy p q with hpq | hpq | hqp
  · have hl := (List.pairwise_iff_get.mp h) p q hpq
    exact (not_lt_of_ge (hq.1.trans (i.first_le_last.trans hp.2)) hl).elim
  · exact hpq
  · have hl := (List.pairwise_iff_get.mp h) q p hqp
    exact (not_lt_of_ge (hp.1.trans (i.first_le_last.trans hq.2)) hl).elim

/-- The executable patch label of an input interval. -/
def label (xs : List (CreationInterval ℓ)) (i : CreationInterval ℓ) (hi : i ∈ xs) :
    Fin (coalesce xs).length :=
  (locate (coalesce xs) i).get (locate_isSome ((coalesce_partition xs).covers i hi))

theorem label_contains (xs : List (CreationInterval ℓ)) (i : CreationInterval ℓ) (hi : i ∈ xs) :
    ((coalesce xs).get (label xs i hi)).Contains i :=
  contains_of_locate ((Option.some_get _).symm)

theorem label_eq_iff (xs : List (CreationInterval ℓ)) (i : CreationInterval ℓ) (hi : i ∈ xs)
    (p : Fin (coalesce xs).length) : label xs i hi = p ↔ ((coalesce xs).get p).Contains i := by
  constructor
  · rintro rfl
    exact label_contains xs i hi
  · exact containing_index_unique (coalesce_partition xs).separated (label_contains xs i hi)

/-- The enclosing positions of a patch before any gate inventory is attached. -/
def toPatches (xs : List (CreationInterval ℓ)) (h : Separated xs) : Patches ℓ xs.length where
  first p := (xs.get p).first.val
  last p := (xs.get p).last.val
  inside p := (xs.get p).last.isLt
  ordered hpq := (List.pairwise_iff_get.mp h) _ _ hpq
  marks _ := ∅
  marks_inside _ := Finset.empty_subset _

def patches (xs : List (CreationInterval ℓ)) : Patches ℓ (coalesce xs).length :=
  toPatches (coalesce xs) (coalesce_partition xs).separated

theorem patches_contains (xs : List (CreationInterval ℓ)) (i : CreationInterval ℓ) (hi : i ∈ xs) :
    (patches xs).first (label xs i hi) ≤ i.first.val ∧
      i.last.val ≤ (patches xs).last (label xs i hi) :=
  label_contains xs i hi

theorem width_mono {p i : CreationInterval ℓ} (h : p.Contains i) :
    i.last.val + 1 - i.first.val ≤ p.last.val + 1 - p.first.val := by
  have hl : p.first.val ≤ i.first.val := h.1
  have hr : i.last.val ≤ p.last.val := h.2
  omega

/-- Inclusive width of the interval in original positions. -/
def width (i : CreationInterval ℓ) : ℕ := i.last.val+1-i.first.val

theorem width_le_sum_of_overlap {i j : CreationInterval ℓ}
    (hl : i.first ≤ j.last) (hr : j.first ≤ i.last) :
    (i.hull j).width ≤ i.width+j.width := by
  have hil : i.first.val ≤ i.last.val := i.first_le_last
  have hjl : j.first.val ≤ j.last.val := j.first_le_last
  have hln : i.first.val ≤ j.last.val := hl
  have hrn : j.first.val ≤ i.last.val := hr
  simp only [width,hull,Fin.val_min,Fin.val_max]
  omega

private theorem mergeLeft_width {i : CreationInterval ℓ} {xs : List (CreationInterval ℓ)}
    (hfirst : ∀ j ∈ xs, i.first ≤ j.first) :
    ((mergeLeft i xs).map width).sum ≤ i.width+(xs.map width).sum := by
  induction xs generalizing i with
  | nil => simp [mergeLeft]
  | cons j rest ih =>
    have hij := hfirst j List.mem_cons_self
    have hr := fun k hk => hfirst k (List.mem_cons_of_mem j hk)
    rw [mergeLeft]
    split
    next he =>
      have hbound := width_le_sum_of_overlap (hij.trans j.first_le_last) he
      have hh : ∀ k ∈ rest, (i.hull j).first ≤ k.first :=
        fun k hk => (min_le_left _ _).trans (hr k hk)
      have hw := ih hh
      simp only [List.map_cons,List.sum_cons]
      omega
    next => simp

private theorem mergeSorted_width {xs : List (CreationInterval ℓ)}
    (hsorted : xs.Pairwise (fun i j => i.first ≤ j.first)) :
    ((mergeSorted xs).map width).sum ≤ (xs.map width).sum := by
  induction xs with
  | nil => rfl
  | cons i rest ih =>
    obtain ⟨hi,ht⟩ := List.pairwise_cons.mp hsorted
    have hh := mergeLeft_width (i := i) (mergeSorted_lower hi)
    exact hh.trans (Nat.add_le_add_left (ih ht) _)

/-- All of a patch's width is charged to creation intervals. -/
theorem coalesce_width_sum (xs : List (CreationInterval ℓ)) :
    ((coalesce xs).map width).sum ≤ (xs.map width).sum := by
  let sorted := xs.mergeSort (fun i j => decide (i.first ≤ j.first))
  have hsorted : sorted.Pairwise (fun i j => i.first ≤ j.first) := by
    have h := List.pairwise_mergeSort (le := fun (i j : CreationInterval ℓ) => decide (i.first ≤ j.first))
      (fun a b c hab hbc => decide_eq_true ((of_decide_eq_true hab).trans (of_decide_eq_true hbc)))
      (fun a b => by simpa using le_total a.first b.first) xs
    simpa [sorted] using h
  have hper := (List.mergeSort_perm xs (fun i j => decide (i.first ≤ j.first))).map width
  exact (mergeSorted_width hsorted).trans_eq hper.sum_eq

theorem patch_width_upper (xs : List (CreationInterval ℓ)) {L E : ℕ}
    (hE : xs.length ≤ E) (h : ∀ i ∈ xs, i.width ≤ 3*L)
    (p : Fin (coalesce xs).length) :
    ((patches xs).positions p).card ≤ 3*E*L := by
  have hm : ((coalesce xs).get p).width ∈ (coalesce xs).map width :=
    List.mem_map.mpr ⟨_,List.get_mem ..,rfl⟩
  have htotal : (xs.map width).sum ≤ xs.length*(3*L) := by
    clear hm p hE
    induction xs with
    | nil => simp
    | cons i rest ih =>
      have hi := h i List.mem_cons_self
      have hrest := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
      simpa [Nat.add_mul,Nat.add_comm,Nat.add_left_comm] using Nat.add_le_add hi hrest
  rw [Patches.positions,Nat.card_Icc]
  change ((coalesce xs).get p).width ≤ _
  calc
    _ ≤ ((coalesce xs).map width).sum := List.le_sum_of_mem hm
    _ ≤ (xs.map width).sum := coalesce_width_sum xs
    _ ≤ xs.length*(3*L) := htotal
    _ ≤ E*(3*L) := Nat.mul_le_mul_right _ hE
    _ = 3*E*L := by ring

#print axioms patch_width_upper

theorem patch_width_lower (xs : List (CreationInterval ℓ)) {L : ℕ}
    (h : ∀ i ∈ xs, L ≤ 2 * (i.last.val + 1 - i.first.val)) (p : Fin (coalesce xs).length) :
    L ≤ 2 * ((patches xs).positions p).card := by
  have hm : (coalesce xs).get p ∈ coalesce xs := List.get_mem ..
  obtain ⟨i,hi,hc⟩ := coalesce_has_input hm
  rw [Patches.positions,Nat.card_Icc]
  exact (h i hi).trans (Nat.mul_le_mul_left 2 (width_mono hc))

/-- Two overlapping input intervals have the same patch label. -/
theorem label_eq_of_intersects (xs : List (CreationInterval ℓ))
    {i j : CreationInterval ℓ} (hi : i ∈ xs) (hj : j ∈ xs)
    (hij : i.first ≤ j.last) (hji : j.first ≤ i.last) :
    label xs i hi = label xs j hj := by
  have hI := label_contains xs i hi
  have hJ := label_contains xs j hj
  have hs := (coalesce_partition xs).separated
  rcases lt_trichotomy (label xs i hi) (label xs j hj) with h | h | h
  · have sep := List.Pairwise.rel_get_of_lt hs h
    exact (not_lt_of_ge (hJ.1.trans (hji.trans hI.2)) sep).elim
  · exact h
  · have sep := List.Pairwise.rel_get_of_lt hs h
    exact (not_lt_of_ge (hI.1.trans (hij.trans hJ.2)) sep).elim

/-- An old patch maps to the enclosing patch when the partition is enlarged. -/
def appendMerge (old new : List (CreationInterval ℓ)) :
    PatchMerge (patches old) (patches (coalesce old ++ new)) where
  label p := label (coalesce old ++ new) ((coalesce old).get p)
    (List.mem_append_left _ (List.get_mem ..))
  first_le p := (patches_contains _ ((coalesce old).get p) _).1
  last_le p := (patches_contains _ ((coalesce old).get p) _).2

private theorem contains_antisymm {i j : CreationInterval ℓ} (h : i.Contains j)
    (h' : j.Contains i) : i = j := by
  obtain ⟨a,b,hab⟩ := i
  obtain ⟨c,d,hcd⟩ := j
  have hf : a = c := le_antisymm h.1 h'.1
  have hl : b = d := le_antisymm h'.2 h.2
  subst c d
  rfl

private theorem mergeLeft_upper {p : Fin ℓ} {i : CreationInterval ℓ}
    {xs : List (CreationInterval ℓ)} (hi : i.last ≤ p) (hx : ∀ j ∈ xs, j.last ≤ p) :
    ∀ j ∈ mergeLeft i xs, j.last ≤ p := by
  induction xs generalizing i with
  | nil =>
    intro j hj
    simpa [List.mem_singleton.mp hj] using hi
  | cons j js ih =>
    rw [mergeLeft]
    split
    · exact ih (max_le hi (hx j List.mem_cons_self))
        (fun k hk => hx k (List.mem_cons_of_mem _ hk))
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hi
      · exact hx k hk

private theorem mergeSorted_upper {p : Fin ℓ} {xs : List (CreationInterval ℓ)}
    (h : ∀ j ∈ xs, j.last ≤ p) : ∀ j ∈ mergeSorted xs, j.last ≤ p := by
  induction xs with
  | nil => simp [mergeSorted]
  | cons i xs ih =>
    exact mergeLeft_upper (h i List.mem_cons_self)
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

private theorem coalesce_lower {p : Fin ℓ} {xs : List (CreationInterval ℓ)}
    (h : ∀ j ∈ xs, p ≤ j.first) : ∀ j ∈ coalesce xs, p ≤ j.first :=
  mergeSorted_lower (fun j hj => h j ((List.mergeSort_perm xs _).mem_iff.mp hj))

private theorem coalesce_upper {p : Fin ℓ} {xs : List (CreationInterval ℓ)}
    (h : ∀ j ∈ xs, j.last ≤ p) : ∀ j ∈ coalesce xs, j.last ≤ p :=
  mergeSorted_upper (fun j hj => h j ((List.mergeSort_perm xs _).mem_iff.mp hj))

/-- An interval disjoint from all the other inputs survives as a patch. -/
theorem isolated_label (xs : List (CreationInterval ℓ)) (i : CreationInterval ℓ) (hi : i ∈ xs)
    (hiso : ∀ j ∈ xs, j = i ∨ j.last < i.first ∨ i.last < j.first) :
    (coalesce xs).get (label xs i hi) = i := by
  let left := xs.filter (fun j => decide (j.last < i.first))
  let right := xs.filter (fun j => decide (i.last < j.first))
  let candidate := coalesce left ++ i :: coalesce right
  have hleft (p : CreationInterval ℓ) (hp : p ∈ coalesce left) : p.last < i.first := by
    have hnon : 0 < i.first.val := by
      obtain ⟨j,hj,_⟩ := coalesce_has_input hp
      have hj' : j.last < i.first := of_decide_eq_true (List.mem_filter.mp hj).2
      exact Nat.zero_lt_of_lt hj'
    let bound : Fin ℓ := ⟨i.first.val-1,by omega⟩
    have hle : p.last ≤ bound := coalesce_upper (p := bound) (fun j hj => by
      have hlt : j.last < i.first := of_decide_eq_true (List.mem_filter.mp hj).2
      change j.last.val < i.first.val at hlt
      change j.last.val ≤ i.first.val-1
      omega) p hp
    change p.last.val ≤ i.first.val-1 at hle
    change p.last.val < i.first.val
    omega
  have hright (p : CreationInterval ℓ) (hp : p ∈ coalesce right) : i.last < p.first := by
    have hnon : i.last.val+1 < ℓ := by
      obtain ⟨j,hj,_⟩ := coalesce_has_input hp
      have hj' : i.last < j.first := of_decide_eq_true (List.mem_filter.mp hj).2
      exact (Nat.succ_le_of_lt hj').trans_lt j.first.isLt
    let bound : Fin ℓ := ⟨i.last.val+1,hnon⟩
    exact coalesce_lower (p := bound) (fun j hj =>
      Nat.succ_le_of_lt (of_decide_eq_true (List.mem_filter.mp hj).2 : i.last < j.first)) p hp
  have hs : Separated candidate := by
    apply List.pairwise_append.mpr
    refine ⟨(coalesce_partition left).separated,List.pairwise_cons.mpr
      ⟨hright,(coalesce_partition right).separated⟩,?_⟩
    intro p hp q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hleft p hp
    · exact (hleft p hp).trans (i.first_le_last.trans_lt (hright q hq))
  have hc : Covers candidate xs := by
    intro j hj
    rcases hiso j hj with rfl | hl | hr
    · exact ⟨j,List.mem_append_right _ List.mem_cons_self,Contains.refl j⟩
    · have hm : j ∈ left := List.mem_filter.mpr ⟨hj,decide_eq_true hl⟩
      obtain ⟨p,hp,hpi⟩ := (coalesce_partition left).covers j hm
      exact ⟨p,List.mem_append_left _ hp,hpi⟩
    · have hm : j ∈ right := List.mem_filter.mpr ⟨hj,decide_eq_true hr⟩
      obtain ⟨p,hp,hpi⟩ := (coalesce_partition right).covers j hm
      exact ⟨p,List.mem_append_right _ (List.mem_cons_of_mem _ hp),hpi⟩
  let p := (coalesce xs).get (label xs i hi)
  have hpi : p.Contains i := label_contains xs i hi
  obtain ⟨q,hq,hqp⟩ := (coalesce_partition xs).finest candidate hs hc p (List.get_mem ..)
  have hqi := hqp.trans hpi
  rcases List.mem_append.mp hq with hl | hr
  · exact (not_lt_of_ge (i.first_le_last.trans hqi.2) (hleft q hl)).elim
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact contains_antisymm hpi hqp
    · exact (not_lt_of_ge (hqi.1.trans i.first_le_last) (hright q hr)).elim

#print axioms isolated_label

private theorem subset_of_cover_both {a b : List (CreationInterval ℓ)} (hs : Separated a)
    (hab : Covers a b) (hba : Covers b a) : a ⊆ b := by
  intro i hi
  obtain ⟨j,hj,hji⟩ := hba i hi
  obtain ⟨k,hk,hkj⟩ := hab j hj
  have hki := hkj.trans hji
  have e := same_container hs hi hk (i.first_le_last.trans hki.2)
    (hki.1.trans i.first_le_last)
  subst k
  exact (contains_antisymm hkj hji) ▸ hj

theorem eq_of_cover_both {a b : List (CreationInterval ℓ)} (ha : Separated a) (hb : Separated b)
    (hab : Covers a b) (hba : Covers b a) : a = b := by
  let rel (i j : CreationInterval ℓ) := i.last < j.first
  have hIrrefl : Std.Irrefl rel := ⟨fun i hi => (not_lt_of_ge i.first_le_last) hi⟩
  have hAnti : Std.Antisymm rel := ⟨fun i j h h' =>
    ((not_lt_of_ge i.first_le_last) (h.trans (j.first_le_last.trans_lt h'))).elim⟩
  exact @List.Subset.antisymm_of_pairwise _ rel hAnti hIrrefl _ _ ha hb
    (subset_of_cover_both ha hab hba) (subset_of_cover_both hb hba hab)

/-- Adding new intervals to the previous patches gives exactly the same
partition as adding them to the original interval list. -/
theorem coalesce_append_patches (old new : List (CreationInterval ℓ)) :
    coalesce (coalesce old ++ new) = coalesce (old ++ new) := by
  have hOld := coalesce_partition old
  have hAll := coalesce_partition (old ++ new)
  have hNow := coalesce_partition (coalesce old ++ new)
  apply eq_of_cover_both hNow.separated hAll.separated
  · apply hAll.finest _ hNow.separated
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨p,hp,hpi⟩ := hOld.covers i hi
      obtain ⟨q,hq,hqp⟩ := hNow.covers p (List.mem_append_left _ hp)
      exact ⟨q,hq,hqp.trans hpi⟩
    · exact hNow.covers i (List.mem_append_right _ hi)
  · apply hNow.finest _ hAll.separated
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hOld.finest _ hAll.separated
        (fun j hj => hAll.covers j (List.mem_append_left _ hj)) i hi
    · exact hAll.covers i (List.mem_append_right _ hi)

/-- If an earlier interval belongs to an old patch, that patch and the
interval have the same label after the new intervals are added. -/
theorem label_append_old (old new : List (CreationInterval ℓ)) {i : CreationInterval ℓ}
    (hi : i ∈ old) (p : Fin (coalesce old).length) (hp : label old i hi = p) :
    let whole := old ++ new
    let same := coalesce_append_patches old new
    Fin.cast (congrArg List.length same) ((appendMerge old new).label p) =
      label whole i (List.mem_append_left _ hi) := by
  dsimp only
  apply containing_index_unique (coalesce_partition _).separated _ (label_contains _ _ _)
  have hl := label_contains (coalesce old ++ new) ((coalesce old).get p)
    (List.mem_append_left _ (List.get_mem ..))
  have h := hl.trans ((label_eq_iff old i hi p).mp hp)
  generalize coalesce_append_patches old new = he
  have hget (xs ys : List (CreationInterval ℓ)) (h : xs = ys) (p : Fin xs.length) :
      ys.get (Fin.cast (congrArg List.length h) p) = xs.get p := by cases h; rfl
  rw [hget _ _ he]
  exact h

#print axioms coalesce_append_patches

#print axioms coalesce_partition
#print axioms patch_width_lower


end CreationInterval
end DeletionCode.Explicit.LetterGraphCuts
