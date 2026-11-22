import DeletionCode.Explicit.PatchSupport
import DeletionCode.Explicit.RulePatchComponents

/-! The number of old patches met by the creation intervals of a new rule
(`d:first-event`). -/

namespace DeletionCode.Explicit.FirstEvent

open LetterGraphCuts LocalBudget RulePatch
open scoped BigOperators

variable {ℓ c s : ℕ}

/-- The old patches that intersect a new creation interval. -/
def touching (P : Patches ℓ c) (i : CreationInterval ℓ) : Finset (Fin c) :=
  Finset.univ.filter (fun p =>
    (P.positions p ∩ Finset.Icc i.first.val i.last.val).Nonempty)

private theorem middle_inside (P : Patches ℓ c) (i : CreationInterval ℓ)
    {p : Fin c} (hp : p ∈ middle (touching P i)) :
    P.positions p ⊆ Finset.Icc i.first.val i.last.val := by
  obtain ⟨_,⟨l,hl,hlp⟩,⟨r,hr,hpr⟩⟩ := Finset.mem_filter.mp hp
  obtain ⟨x,hx⟩ := (Finset.mem_filter.mp hl).2
  obtain ⟨y,hy⟩ := (Finset.mem_filter.mp hr).2
  obtain ⟨hxP,hxI⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyP,hyI⟩ := Finset.mem_inter.mp hy
  intro z hz
  obtain ⟨hzl,hzr⟩ := Finset.mem_Icc.mp hz
  have hxl := (Finset.mem_Icc.mp hxI).1
  have hxr := (Finset.mem_Icc.mp hxP).2
  have hyl := (Finset.mem_Icc.mp hyP).1
  have hyr := (Finset.mem_Icc.mp hyI).2
  have hlord := P.ordered hlp
  have hrord := P.ordered hpr
  exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩

theorem touching_card_le_eight (P : Patches ℓ c) (i : CreationInterval ℓ) {L : ℕ}
    (hL : 0 < L) (hwidth : ∀ p, L ≤ 2*(P.positions p).card)
    (hi : i.last.val+1-i.first.val ≤ 3*L) : (touching P i).card ≤ 8 := by
  let M := middle (touching P i)
  have hs : (↑M : Set (Fin c)).PairwiseDisjoint P.positions :=
    fun _ _ _ _ h => P.disjoint h
  have hu : M.biUnion P.positions ⊆ Finset.Icc i.first.val i.last.val := by
    intro z hz
    obtain ⟨p,hp,hz⟩ := Finset.mem_biUnion.mp hz
    exact middle_inside P i hp hz
  have hsum : ∑ p ∈ M, (P.positions p).card ≤ 3*L := by
    rw [← Finset.card_biUnion hs]
    exact (Finset.card_le_card hu).trans (by simpa only [Nat.card_Icc] using hi)
  have hlow : M.card * L ≤ 2 * ∑ p ∈ M, (P.positions p).card := by
    rw [Finset.mul_sum]
    simpa only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id] using
      (Finset.sum_le_sum (s := M) (fun p _ => hwidth p))
  have hb : M.card * L ≤ 6 * L := by omega
  have hm := Nat.le_of_mul_le_mul_right hb hL
  exact (card_le_middle_add_two (touching P i)).trans (Nat.add_le_add_right hm 2)

def touchedPatches (P : Patches ℓ c) (new : Fin s → CreationInterval ℓ) : Finset (Fin c) :=
  Finset.univ.biUnion (fun j => touching P (new j))

theorem touchedPatches_card (P : Patches ℓ c) (new : Fin s → CreationInterval ℓ) {L : ℕ}
    (hL : 0 < L) (hwidth : ∀ p, L ≤ 2*(P.positions p).card)
    (hnew : ∀ j, (new j).last.val+1-(new j).first.val ≤ 3*L) :
    (touchedPatches P new).card ≤ 8*s := by
  unfold touchedPatches
  calc
    _ ≤ ∑ j : Fin s, (touching P (new j)).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin s, 8 := Finset.sum_le_sum
      (fun j _ => touching_card_le_eight P (new j) hL hwidth (hnew j))
    _ = 8*s := by simp [Nat.mul_comm]

/-- Selecting the union of touched old rule sets and the new rule uses at
most the witness's rule budget. Duplicate touches only decrease the count. -/
theorem witness_rule_bound {d R : ℕ} (P : Patches ℓ c) (new : Fin s → CreationInterval ℓ)
    (componentRules : Fin c → Finset (Fin d)) {L : ℕ} (hL : 0 < L)
    (hwidth : ∀ p, L ≤ 2*(P.positions p).card)
    (hnew : ∀ j, (new j).last.val+1-(new j).first.val ≤ 3*L)
    (hcomp : ∀ p, (componentRules p).card ≤ R) :
    ((touchedPatches P new).biUnion componentRules).card + 1 ≤ 8*s*R + 1 := by
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ p ∈ touchedPatches P new, (componentRules p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ touchedPatches P new, R := Finset.sum_le_sum (fun p _ => hcomp p)
    _ = (touchedPatches P new).card * R := by simp
    _ ≤ 8*s*R := Nat.mul_le_mul_right R (touchedPatches_card P new hL hwidth hnew)


section ComponentCount

variable {d : ℕ}

/-- From the old incidence, compute the exact old rules retained by a new rule. -/
def retainedRules (a : Incidence d s c) (P : Patches ℓ c)
    (new : Fin s → CreationInterval ℓ) : Finset (Fin d) :=
  (touchedPatches P new).biUnion (fun p => componentRules a (.inr p))

theorem mem_retainedRules (a : Incidence d s c) (P : Patches ℓ c)
    (new : Fin s → CreationInterval ℓ) (i : Fin d) :
    i ∈ retainedRules a P new ↔
      ∃ p ∈ touchedPatches P new, (graph a).Reachable (.inr p) (.inl i) := by
  simp [retainedRules]

theorem retainedRules_bound (a : Incidence d s c) (P : Patches ℓ c)
    (new : Fin s → CreationInterval ℓ) {L R : ℕ} (hL : 0 < L)
    (hwidth : ∀ p, L ≤ 2*(P.positions p).card)
    (hnew : ∀ j, (new j).last.val+1-(new j).first.val ≤ 3*L)
    (hcomp : ∀ p : Fin c, (componentRules a (.inr p)).card ≤ R) :
    (retainedRules a P new).card + 1 ≤ 8*s*R+1 :=
  witness_rule_bound P new (fun p => componentRules a (.inr p)) hL hwidth hnew hcomp

/-- In the computed partition, every touched old patch gets the same new
label as the creation interval that touches it. -/
theorem touched_label (old new : List (CreationInterval ℓ))
    {p : Fin (CreationInterval.coalesce old).length} {i : CreationInterval ℓ}
    (hi : i ∈ new) (hp : p ∈ touching (CreationInterval.patches old) i) :
    (CreationInterval.appendMerge old new).label p =
      CreationInterval.label (CreationInterval.coalesce old ++ new) i (List.mem_append_right _ hi) := by
  obtain ⟨z,hz⟩ := (Finset.mem_filter.mp hp).2
  obtain ⟨h₁,h₂⟩ := Finset.mem_inter.mp hz
  obtain ⟨hpl,hpr⟩ := Finset.mem_Icc.mp h₁
  obtain ⟨hil,hir⟩ := Finset.mem_Icc.mp h₂
  exact CreationInterval.label_eq_of_intersects _
    (List.mem_append_left _ (List.get_mem ..)) (List.mem_append_right _ hi)
    (hpl.trans hir) (hil.trans hpr)

/-- Every retained old rule reaches the new rule in the enlarged graph.
The premise records that the old patch and an intersecting new interval
were assigned the same enlarged label. -/
theorem retained_reaches_new {d c' : ℕ}
    (old : Incidence d s c) (next : Incidence (d+1) s c') (merge : Fin c → Fin c')
    (hinc : ∀ i j, next (i.castSucc,j) = merge (old (i,j)))
    (P : Patches ℓ c) (new : Fin s → CreationInterval ℓ)
    (hjoin : ∀ j p, p ∈ touching P (new j) → merge p = next (Fin.last d,j))
    {i : Fin d} (hi : i ∈ retainedRules old P new) :
    (graph next).Reachable (.inl i.castSucc) (.inl (Fin.last d)) := by
  obtain ⟨p,hp,hreach⟩ := (mem_retainedRules old P new i).mp hi
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
  have hprev := hreach.symm.map (mergeHom old next merge hinc)
  change (graph next).Reachable (.inl i.castSucc) (.inr (merge p)) at hprev
  exact hprev.trans ((hjoin j p hj).symm ▸ (bubble_reaches next (Fin.last d) j).symm)

private def newIntervals (new : Fin s → CreationInterval ℓ) : List (CreationInterval ℓ) :=
  (List.finRange s).map new

private theorem mem_newIntervals (new : Fin s → CreationInterval ℓ) (j : Fin s) :
    new j ∈ newIntervals new :=
  List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩

private abbrev enlarged (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ) :=
  CreationInterval.coalesce old ++ newIntervals new

/-- Update every old endpoint by patch coalescence and assign the new rule's
endpoints using its creation intervals. -/
def extendIncidence (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ)
    (a : Incidence d s (CreationInterval.coalesce old).length) :
    Incidence (d+1) s (CreationInterval.coalesce (enlarged old new)).length :=
  fun (i,j) => Fin.lastCases
    (CreationInterval.label (enlarged old new) (new j) (List.mem_append_right _ (mem_newIntervals new j)))
    (fun k => (CreationInterval.appendMerge old (newIntervals new)).label (a (k,j))) i

theorem retained_new_component (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ)
    (a : Incidence d s (CreationInterval.coalesce old).length)
    {i : Fin d} (hi : i ∈ retainedRules a (CreationInterval.patches old) new) :
    i.castSucc ∈ componentRules (extendIncidence old new a) (.inl (Fin.last d)) := by
  apply (mem_componentRules _ _ _).mpr
  apply SimpleGraph.Reachable.symm
  apply retained_reaches_new a (extendIncidence old new a)
    (CreationInterval.appendMerge old (newIntervals new)).label _ (CreationInterval.patches old) new _ hi
  · intro i j
    simp [extendIncidence]
  · intro j p hp
    simpa [extendIncidence] using touched_label old (newIntervals new) (mem_newIntervals new j) hp

/-- Touching a computed old patch is equivalent to intersection of the
two closed intervals. -/
theorem touching_iff (old : List (CreationInterval ℓ)) (i : CreationInterval ℓ)
    (p : Fin (CreationInterval.coalesce old).length) :
    p ∈ touching (CreationInterval.patches old) i ↔
      let j := (CreationInterval.coalesce old).get p
      j.first ≤ i.last ∧ i.first ≤ j.last := by
  let j := (CreationInterval.coalesce old).get p
  constructor
  · intro h
    obtain ⟨z,hz⟩ := (Finset.mem_filter.mp h).2
    obtain ⟨hj,hi⟩ := Finset.mem_inter.mp hz
    exact ⟨(Finset.mem_Icc.mp hj).1.trans (Finset.mem_Icc.mp hi).2,
      (Finset.mem_Icc.mp hi).1.trans (Finset.mem_Icc.mp hj).2⟩
  · rintro ⟨hj,hi⟩
    let z := max j.first.val i.first.val
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,z,Finset.mem_inter.mpr
      ⟨Finset.mem_Icc.mpr ⟨le_max_left _ _,max_le j.first_le_last hi⟩,
        Finset.mem_Icc.mpr ⟨le_max_right _ _,max_le hj i.first_le_last⟩⟩⟩

/-- A patch never touched by a new interval remains the same interval. -/
theorem untouched_patch (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ)
    (p : Fin (CreationInterval.coalesce old).length)
    (h : p ∉ touchedPatches (CreationInterval.patches old) new) :
    (CreationInterval.coalesce (enlarged old new)).get
      ((CreationInterval.appendMerge old (newIntervals new)).label p) =
        (CreationInterval.coalesce old).get p := by
  let i := (CreationInterval.coalesce old).get p
  apply CreationInterval.isolated_label _ _ (List.mem_append_left _ (List.get_mem ..))
  intro j hj
  rcases List.mem_append.mp hj with hj | hj
  · obtain ⟨q,hq,eq⟩ := List.mem_iff_getElem.mp hj
    let qi : Fin (CreationInterval.coalesce old).length := ⟨q,hq⟩
    have he : (CreationInterval.coalesce old).get qi = j := eq
    have hs := (CreationInterval.coalesce_partition old).separated
    rcases lt_trichotomy qi p with hq | hq | hq
    · exact Or.inr (Or.inl (he ▸ List.Pairwise.rel_get_of_lt hs hq))
    · exact Or.inl (he.symm.trans (congrArg _ hq))
    · exact Or.inr (Or.inr (he ▸ List.Pairwise.rel_get_of_lt hs hq))
  · obtain ⟨k,_,rfl⟩ := List.mem_map.mp hj
    have ho : p ∉ touching (CreationInterval.patches old) (new k) :=
      fun ht => h (Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,ht⟩)
    have hr := mt ((touching_iff old (new k) p).mpr) ho
    change ¬ (i.first ≤ (new k).last ∧ (new k).first ≤ i.last) at hr
    push Not at hr
    by_cases hb : i.first ≤ (new k).last
    · exact Or.inr (Or.inr (hr hb))
    · exact Or.inr (Or.inl (lt_of_not_ge hb))

private theorem untouched_ne_new (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ)
    {p : Fin (CreationInterval.coalesce old).length}
    (h : p ∉ touchedPatches (CreationInterval.patches old) new) (j : Fin s) :
    (CreationInterval.appendMerge old (newIntervals new)).label p ≠
      CreationInterval.label (enlarged old new) (new j)
        (List.mem_append_right _ (mem_newIntervals new j)) := by
  intro he
  have hf := CreationInterval.label_contains (enlarged old new) (new j)
    (List.mem_append_right _ (mem_newIntervals new j))
  rw [← he,untouched_patch old new p h] at hf
  exact h (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,(touching_iff old (new j) p).mpr
    ⟨hf.1.trans (new j).first_le_last,(new j).first_le_last.trans hf.2⟩⟩)

private theorem untouched_label_injective (old : List (CreationInterval ℓ))
    (new : Fin s → CreationInterval ℓ) {p q : Fin (CreationInterval.coalesce old).length}
    (h : p ∉ touchedPatches (CreationInterval.patches old) new)
    (he : (CreationInterval.appendMerge old (newIntervals new)).label p =
      (CreationInterval.appendMerge old (newIntervals new)).label q) : p = q := by
  have hc := CreationInterval.label_contains (enlarged old new) ((CreationInterval.coalesce old).get q)
    (List.mem_append_left _ (List.get_mem ..))
  change ((CreationInterval.coalesce (enlarged old new)).get
      ((CreationInterval.appendMerge old (newIntervals new)).label q)).Contains
        ((CreationInterval.coalesce old).get q) at hc
  rw [← he,untouched_patch old new p h] at hc
  exact CreationInterval.containing_index_unique (CreationInterval.coalesce_partition old).separated
    hc (CreationInterval.Contains.refl _)

private theorem retained_of_same_old_patch (a : Incidence d s c) (P : Patches ℓ c)
    (new : Fin s → CreationInterval ℓ) {i k : Fin d} {j l : Fin s}
    (hi : i ∈ retainedRules a P new) (he : a (i,j) = a (k,l)) :
    k ∈ retainedRules a P new := by
  obtain ⟨p,hp,hi⟩ := (mem_retainedRules a P new i).mp hi
  refine (mem_retainedRules a P new k).mpr ⟨p,hp,?_⟩
  exact (hi.trans (bubble_reaches a i j)).trans (he.symm ▸ (bubble_reaches a k l).symm)

private theorem touching_is_retained
    (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ)
    (a : Incidence d s (CreationInterval.coalesce old).length)
    {i : Fin d} {j : Fin s}
    (h : a (i,j) ∈ touchedPatches (CreationInterval.patches old) new) :
    i ∈ retainedRules a (CreationInterval.patches old) new :=
  (mem_retainedRules a (CreationInterval.patches old) new i).mpr
    ⟨a (i,j),h,(bubble_reaches a i j).symm⟩

/-- Conversely, an old rule in the enlarged component already belonged to
a touched old component. Untouched old patches are unchanged and cannot
create any extra adjacency in the enlarged graph. -/
theorem new_component_old_iff (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ)
    (a : Incidence d s (CreationInterval.coalesce old).length) (i : Fin d) :
    i.castSucc ∈ componentRules (extendIncidence old new a) (.inl (Fin.last d)) ↔
      i ∈ retainedRules a (CreationInterval.patches old) new := by
  let next := extendIncidence old new a
  let retain := retainedRules a (CreationInterval.patches old) new
  let goodRule : Fin (d+1) → Prop := Fin.lastCases True (fun k => k ∈ retain)
  let good : Fin (d+1) ⊕ Fin (CreationInterval.coalesce (enlarged old new)).length → Prop
    | .inl k => goodRule k
    | .inr p => ∃ k j, goodRule k ∧ next (k,j) = p
  have entails (k l : Fin (d+1)) (j u : Fin s)
      (hk : goodRule k) (he : next (k,j) = next (l,u)) : goodRule l := by
    induction l using Fin.lastCases with
    | last => simp [goodRule]
    | cast l =>
      change (Fin.lastCases True (fun k => k ∈ retain) l.castSucc)
      simp only [Fin.lastCases_castSucc]
      by_contra hl
      have hu : a (l,u) ∉ touchedPatches (CreationInterval.patches old) new :=
        fun hh => hl (touching_is_retained old new a hh)
      induction k using Fin.lastCases with
      | last =>
        exact (untouched_ne_new old new hu j) (by simpa [next,extendIncidence] using he.symm)
      | cast k =>
        have hk' : k ∈ retain := by simpa [goodRule] using hk
        have hEq := untouched_label_injective old new hu (by simpa [next,extendIncidence] using he.symm)
        exact hl (retained_of_same_old_patch a _ new hk' hEq.symm)
  have closed {x y} (h : (graph next).Adj x y) (hx : good x) : good y := by
    rcases x with k | p <;> rcases y with l | q
    · have he := (adjacent_iff next (.inl k) (.inl l)).mpr h
      simp [adjacent] at he
    · obtain ⟨j,hj⟩ := (adj_rule_patch_iff next k q).mp h
      exact ⟨k,j,hx,hj⟩
    · obtain ⟨j,hj⟩ := (adj_rule_patch_iff next l p).mp h.symm
      obtain ⟨k,u,hk,hu⟩ := hx
      exact entails k l u j hk (hu.trans hj.symm)
    · have he := (adjacent_iff next (.inr p) (.inr q)).mpr h
      simp [adjacent] at he
  refine ⟨?_,retained_new_component old new a⟩
  intro hi
  have hroot : good (.inl (Fin.last d)) := by simp [good,goodRule]
  have hr := reachable_closed next good closed ((mem_componentRules next _ _).mp hi) hroot
  simpa [good,goodRule,retain] using hr

/-- The kept rule indices are the new rule and the old indices of touched
components, embedded in the enlarged rule index type. -/
theorem new_component_rules_exact (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ)
    (a : Incidence d s (CreationInterval.coalesce old).length) :
    componentRules (extendIncidence old new a) (.inl (Fin.last d)) =
      insert (Fin.last d) ((retainedRules a (CreationInterval.patches old) new).map
        Fin.castSuccEmb) := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [SimpleGraph.Reachable.rfl]
  | cast j =>
    rw [new_component_old_iff]
    simp [ne_of_lt (Fin.castSucc_lt_last j)]

theorem new_component_rule_count (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ)
    (a : Incidence d s (CreationInterval.coalesce old).length) :
    (componentRules (extendIncidence old new a) (.inl (Fin.last d))).card =
      (retainedRules a (CreationInterval.patches old) new).card + 1 := by
  rw [new_component_rules_exact,Finset.card_insert_of_notMem,Finset.card_map]
  intro h
  obtain ⟨i,_,he⟩ := Finset.mem_map.mp h
  exact (ne_of_lt (Fin.castSucc_lt_last i)) he

private def oldWitnessPatches (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ)
    (a : Incidence d s (CreationInterval.coalesce old).length) :
    Finset (Fin (CreationInterval.coalesce old).length) :=
  RulePatch.patches a (retainedRules a (CreationInterval.patches old) new)

private def newPatchLabels (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ) :
    Finset (Fin (CreationInterval.coalesce (enlarged old new)).length) :=
  Finset.univ.image (fun j => CreationInterval.label (enlarged old new) (new j)
    (List.mem_append_right _ (mem_newIntervals new j)))

private theorem touched_subset_oldWitness (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ)
    (a : Incidence d s (CreationInterval.coalesce old).length)
    (hsurj : Function.Surjective a) :
    touchedPatches (CreationInterval.patches old) new ⊆ oldWitnessPatches old new a := by
  intro p hp
  obtain ⟨⟨i,j⟩,hj⟩ := hsurj p
  exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_product.mpr
    ⟨touching_is_retained old new a (hj.symm ▸ hp),Finset.mem_univ _⟩,hj⟩

/-- The new component has all patches containing a new interval plus the
unchanged patches of the retained old components. -/
theorem new_component_patches_exact (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ)
    (a : Incidence d s (CreationInterval.coalesce old).length) :
    componentPatches (extendIncidence old new a) (.inl (Fin.last d)) =
      newPatchLabels old new ∪
        ((oldWitnessPatches old new a) \ touchedPatches (CreationInterval.patches old) new).image
          (CreationInterval.appendMerge old (newIntervals new)).label := by
  let next := extendIncidence old new a
  let changed := newPatchLabels old new
  let merge := (CreationInterval.appendMerge old (newIntervals new)).label
  rw [componentPatches_eq_incidence]
  ext p
  constructor
  · intro hp
    obtain ⟨⟨i,j⟩,hi,he⟩ := Finset.mem_image.mp hp
    have hmem := (Finset.mem_product.mp hi).1
    induction i using Fin.lastCases with
    | last =>
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨j,Finset.mem_univ _,by simpa [extendIncidence] using he⟩)
    | cast k =>
      have hk := (new_component_old_iff old new a k).mp hmem
      let oldPatch := a (k,j)
      have hold : oldPatch ∈ oldWitnessPatches old new a := Finset.mem_image.mpr
        ⟨(k,j),Finset.mem_product.mpr ⟨hk,Finset.mem_univ _⟩,rfl⟩
      have he' : merge oldPatch = p := by simpa [extendIncidence,merge,oldPatch] using he
      by_cases ht : oldPatch ∈ touchedPatches (CreationInterval.patches old) new
      · obtain ⟨j',_,hj'⟩ := Finset.mem_biUnion.mp ht
        have hh := touched_label old (newIntervals new) (mem_newIntervals new j') hj'
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j',Finset.mem_univ _,hh.symm.trans he'⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨oldPatch,Finset.mem_sdiff.mpr ⟨hold,ht⟩,he'⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨(Fin.last d,j),Finset.mem_product.mpr
        ⟨(mem_componentRules _ _ _).mpr SimpleGraph.Reachable.rfl,Finset.mem_univ _⟩,
        by simpa [extendIncidence] using hj⟩
    · obtain ⟨q,hq,he⟩ := Finset.mem_image.mp hp
      obtain ⟨⟨i,j⟩,hi,he'⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hq).1
      have hm := retained_new_component old new a (Finset.mem_product.mp hi).1
      exact Finset.mem_image.mpr ⟨(i.castSucc,j),Finset.mem_product.mpr
        ⟨hm,Finset.mem_univ _⟩,by simpa [extendIncidence,← he'] using he⟩

theorem new_component_patch_count (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ)
    (a : Incidence d s (CreationInterval.coalesce old).length) (hsurj : Function.Surjective a) :
    (componentPatches (extendIncidence old new a) (.inl (Fin.last d))).card =
      (oldWitnessPatches old new a).card - (touchedPatches (CreationInterval.patches old) new).card +
        (newPatchLabels old new).card := by
  let merge := (CreationInterval.appendMerge old (newIntervals new)).label
  let unmerged := (oldWitnessPatches old new a) \ touchedPatches (CreationInterval.patches old) new
  have hs : Set.InjOn merge (↑unmerged : Set (Fin (CreationInterval.coalesce old).length)) := by
    intro p hp q hq he
    exact untouched_label_injective old new (Finset.mem_sdiff.mp hp).2 he
  have hd : Disjoint (newPatchLabels old new) (unmerged.image merge) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hp
    obtain ⟨q,hq,hq'⟩ := Finset.mem_image.mp hq
    exact untouched_ne_new old new (Finset.mem_sdiff.mp hq).2 j (hq'.trans hj.symm)
  rw [new_component_patches_exact,Finset.card_union_of_disjoint hd,Finset.card_image_of_injOn hs,
    Finset.card_sdiff_of_subset (touched_subset_oldWitness old new a hsurj),Nat.add_comm]

#print axioms new_component_patch_count

#print axioms new_component_rule_count

#print axioms new_component_old_iff

#print axioms untouched_patch

#print axioms retained_new_component

#print axioms retained_reaches_new

/-- Count the independent cycles after adjoining the new rule to the touched
forest. Here `τ` counts old components, `μ` old merged patch vertices, and
`j` resulting patches containing a new interval. -/
theorem cycle_count_of_forest {oldRules oldPatches τ μ j G : ℕ}
    (hforest : oldRules*s+τ = oldRules+oldPatches) (hμ : μ ≤ oldPatches)
    (hbound : μ ≤ 8*s) (hG : 9*s ≤ G) :
    cycles (oldRules+1) s (oldPatches-μ+j) = s+μ-j-τ ∧
      cycles (oldRules+1) s (oldPatches-μ+j) ≤ G := by
  rw [cycles,Nat.add_mul,Nat.one_mul]
  omega

private def touchedComponents (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ)
    (a : Incidence d s (CreationInterval.coalesce old).length) :
    Finset (Finset (Fin d ⊕ Fin (CreationInterval.coalesce old).length)) :=
  (touchedPatches (CreationInterval.patches old) new).image (fun p => component a (.inr p))

private def rulesIn (C : Finset (Fin d ⊕ Fin c)) : Finset (Fin d) :=
  Finset.univ.filter (fun i => Sum.inl i ∈ C)

private def patchesIn (C : Finset (Fin d ⊕ Fin c)) : Finset (Fin c) :=
  Finset.univ.filter (fun p => Sum.inr p ∈ C)

private theorem touchedComponents_disjoint (old : List (CreationInterval ℓ))
    (new : Fin s → CreationInterval ℓ) (a : Incidence d s (CreationInterval.coalesce old).length) :
    (↑(touchedComponents old new a) :
      Set (Finset (Fin d ⊕ Fin (CreationInterval.coalesce old).length))).PairwiseDisjoint id := by
  intro C hC D hD hne
  change Disjoint C D
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hD
  have hp := (mem_component a (.inr p) x).mp hx
  have hq := (mem_component a (.inr q) x).mp hy
  exact hne (component_eq_of_reachable a (hp.trans hq.symm))

private theorem old_component_rules_union (old : List (CreationInterval ℓ))
    (new : Fin s → CreationInterval ℓ) (a : Incidence d s (CreationInterval.coalesce old).length) :
    retainedRules a (CreationInterval.patches old) new =
      (touchedComponents old new a).biUnion rulesIn := by
  ext i
  constructor
  · intro hi
    obtain ⟨p,hp,h⟩ := (mem_retainedRules a _ new i).mp hi
    exact Finset.mem_biUnion.mpr ⟨component a (.inr p),Finset.mem_image_of_mem _ hp,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mem_component _ _ _).mpr h⟩⟩
  · intro hi
    obtain ⟨C,hC,h⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hC
    exact (mem_retainedRules a _ new i).mpr
      ⟨p,hp,(mem_component _ _ _).mp (Finset.mem_filter.mp h).2⟩

private theorem old_component_patches_union (old : List (CreationInterval ℓ))
    (new : Fin s → CreationInterval ℓ) (a : Incidence d s (CreationInterval.coalesce old).length)
    (hsurj : Function.Surjective a) :
    oldWitnessPatches old new a = (touchedComponents old new a).biUnion patchesIn := by
  ext q
  constructor
  · intro hq
    obtain ⟨⟨i,j⟩,hi,hij⟩ := Finset.mem_image.mp hq
    obtain ⟨p,hp,hreach⟩ := (mem_retainedRules a _ new i).mp (Finset.mem_product.mp hi).1
    exact Finset.mem_biUnion.mpr ⟨component a (.inr p),Finset.mem_image_of_mem _ hp,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mem_component _ _ _).mpr
        (hij ▸ hreach.trans (bubble_reaches a i j))⟩⟩
  · intro hq
    obtain ⟨C,hC,hq⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨⟨i,j⟩,hij⟩ := hsurj q
    have hreach := (mem_component a (.inr p) (.inr q)).mp (Finset.mem_filter.mp hq).2
    have hk := (mem_retainedRules a _ new i).mpr
      ⟨p,hp,hreach.trans (hij ▸ (bubble_reaches a i j).symm)⟩
    exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_product.mpr ⟨hk,Finset.mem_univ _⟩,hij⟩

private theorem old_forest_count (old : List (CreationInterval ℓ))
    (new : Fin s → CreationInterval ℓ) (a : Incidence d s (CreationInterval.coalesce old).length)
    (hsurj : Function.Surjective a)
    (hforest : ∀ p, (componentRules a (.inr p)).card*s+1 =
      (componentRules a (.inr p)).card + (componentPatches a (.inr p)).card) :
    (retainedRules a (CreationInterval.patches old) new).card*s + (touchedComponents old new a).card =
      (retainedRules a (CreationInterval.patches old) new).card + (oldWitnessPatches old new a).card := by
  have hd := touchedComponents_disjoint old new a
  have hr : (↑(touchedComponents old new a) :
      Set (Finset (Fin d ⊕ Fin (CreationInterval.coalesce old).length))).PairwiseDisjoint rulesIn := by
    intro C hC D hD hne
    change Disjoint (rulesIn C) (rulesIn D)
    rw [Finset.disjoint_left]
    intro i hi hj
    exact (Finset.disjoint_left.mp (show Disjoint C D from hd hC hD hne))
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hp : (↑(touchedComponents old new a) :
      Set (Finset (Fin d ⊕ Fin (CreationInterval.coalesce old).length))).PairwiseDisjoint patchesIn := by
    intro C hC D hD hne
    change Disjoint (patchesIn C) (patchesIn D)
    rw [Finset.disjoint_left]
    intro i hi hj
    exact (Finset.disjoint_left.mp (hd hC hD hne))
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  rw [old_component_rules_union old new a,old_component_patches_union old new a hsurj,
    Finset.card_biUnion hr,Finset.card_biUnion hp,Finset.sum_mul]
  calc
    _ = ∑ C ∈ touchedComponents old new a, ((rulesIn C).card*s+1) := by
      rw [Finset.sum_add_distrib]
      simp
    _ = ∑ C ∈ touchedComponents old new a, ((rulesIn C).card+(patchesIn C).card) := by
      apply Finset.sum_congr rfl
      intro C hC
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hC
      exact hforest p
    _ = _ := Finset.sum_add_distrib

/-- The first-event rule component satisfies the manuscript's vertex and
cycle count once the old components satisfy the tree count. -/
theorem enlarged_component_counts (old : List (CreationInterval ℓ))
    (new : Fin s → CreationInterval ℓ) (a : Incidence d s (CreationInterval.coalesce old).length)
    (hsurj : Function.Surjective a)
    (hforest : ∀ p, (componentRules a (.inr p)).card*s+1 =
      (componentRules a (.inr p)).card + (componentPatches a (.inr p)).card)
    {L R : ℕ} (hL : 0 < L)
    (hwidth : ∀ p, L ≤ 2*((CreationInterval.patches old).positions p).card)
    (hnew : ∀ j, (new j).last.val+1-(new j).first.val ≤ 3*L)
    (hcomp : ∀ p : Fin (CreationInterval.coalesce old).length,
      (componentRules a (.inr p)).card ≤ R) :
    let next := extendIncidence old new a
    let r := (componentRules next (.inl (Fin.last d))).card
    let p := (componentPatches next (.inl (Fin.last d))).card
    r ≤ 8*s*R+1 ∧ cycles r s p ≤ 10*s := by
  dsimp only
  rw [new_component_rule_count,new_component_patch_count old new a hsurj]
  refine ⟨retainedRules_bound a _ new hL hwidth hnew hcomp,?_⟩
  exact (cycle_count_of_forest
    (old_forest_count old new a hsurj hforest)
    (Finset.card_le_card (touched_subset_oldWitness old new a hsurj))
    (touchedPatches_card _ new hL hwidth hnew)
    (show 9*s ≤ 10*s by omega)).2

#print axioms enlarged_component_counts

/-- The Boolean test uses multigraph edges, so two parallel bubbles can
trigger an event even when the underlying simple graph is a tree. -/
def componentEvent {d c : ℕ} (a : Incidence d s c) (R : ℕ) (i : Fin d) : Bool :=
  let rules := componentRules a (.inl i)
  let patches := componentPatches a (.inl i)
  decide (R < rules.card ∨ rules.card + patches.card ≤ rules.card*s)

theorem componentEvent_eq_false {d c : ℕ} (a : Incidence d s c) (R : ℕ) (i : Fin d) :
    componentEvent a R i = false ↔
      (componentRules a (.inl i)).card ≤ R ∧
      (componentRules a (.inl i)).card*s <
        (componentRules a (.inl i)).card + (componentPatches a (.inl i)).card := by
  simp [componentEvent]

theorem componentEvent_eq_true {d c : ℕ} (a : Incidence d s c) (R : ℕ) (i : Fin d) :
    componentEvent a R i = true ↔
      R < (componentRules a (.inl i)).card ∨
        0 < cycles (componentRules a (.inl i)).card s (componentPatches a (.inl i)).card := by
  simp only [componentEvent,decide_eq_true_eq,cycles]
  constructor
  · rintro (hr | hc)
    · exact Or.inl hr
    · exact Or.inr (by omega)
  · rintro (hr | hc)
    · exact Or.inl hr
    · exact Or.inr (by omega)

/-- When the enlarged component of the new rule stays below the event
threshold, every other component still meets the old threshold. -/
theorem all_preEvent_of_last (old : List (CreationInterval ℓ))
    (new : Fin s → CreationInterval ℓ) (a : Incidence d s (CreationInterval.coalesce old).length)
    (R : ℕ) (hbefore : ∀ i, componentEvent a R i = false)
    (hlast : componentEvent (extendIncidence old new a) R (Fin.last d) = false) :
    ∀ i, componentEvent (extendIncidence old new a) R i = false := by
  let next := extendIncidence old new a
  let label := (CreationInterval.appendMerge old (newIntervals new)).label
  let root : Fin (d+1) ⊕ Fin (CreationInterval.coalesce (enlarged old new)).length := .inl (Fin.last d)
  have hnext (i : Fin d) (j : Fin s) : next (i.castSucc,j) = label (a (i,j)) := by
    simp [next,label,extendIncidence]
  let embed := mergeHom a next label hnext
  intro k
  by_cases hconnected : (graph next).Reachable root (.inl k)
  · have he := component_eq_of_reachable next hconnected
    have hc := (componentEvent_eq_false next R (Fin.last d)).mp hlast
    apply (componentEvent_eq_false next R k).mpr
    change component next (.inl (Fin.last d)) = component next (.inl k) at he
    simpa only [componentRules,componentPatches,← he] using hc
  induction k using Fin.lastCases with
  | last => exact (hconnected SimpleGraph.Reachable.rfl).elim
  | cast k =>
    let reach (x : Fin d ⊕ Fin (CreationInterval.coalesce old).length) := (graph a).Reachable (.inl k) x
    have hquiet (p : Fin (CreationInterval.coalesce old).length) (hp : reach (.inr p)) :
        p ∉ touchedPatches (CreationInterval.patches old) new := by
      intro ht
      apply hconnected
      apply (mem_componentRules next _ _).mp
      apply (new_component_old_iff old new a k).mpr
      exact (mem_retainedRules a _ _ _).mpr ⟨p,ht,hp.symm⟩
    let imageReach := fun x => ∃ y, reach y ∧ embed y = x
    have hclosed {x y} (he : (graph next).Adj x y) (hx : imageReach x) : imageReach y := by
      obtain ⟨z,hz,rfl⟩ := hx
      cases z with
      | inl i =>
        change (graph next).Adj (.inl i.castSucc) y at he
        cases y with
        | inl j =>
          have h := (adjacent_iff next (.inl i.castSucc) (.inl j)).mpr he
          simp [adjacent] at h
        | inr p =>
          obtain ⟨j,hj⟩ := (adj_rule_patch_iff next _ _).mp he
          exact ⟨.inr (a (i,j)),hz.trans (bubble_reaches a i j),congrArg Sum.inr ((hnext i j).symm.trans hj)⟩
      | inr p =>
        change (graph next).Adj (.inr (label p)) y at he
        cases y with
        | inr u =>
          have h := (adjacent_iff next (.inr (label p)) (.inr u)).mpr he
          simp [adjacent] at h
        | inl i =>
          obtain ⟨j,hj⟩ := (adj_rule_patch_iff next i (label p)).mp he.symm
          have hq := hquiet p hz
          induction i using Fin.lastCases with
          | last => exact (untouched_ne_new old new hq j (by simpa [next,label,extendIncidence] using hj.symm)).elim
          | cast i =>
            have hpeq : p = a (i,j) := untouched_label_injective old new hq (by simpa [hnext,label] using hj.symm)
            have hr : (graph a).Reachable (.inr p) (.inl i) := hpeq.symm ▸ (bubble_reaches a i j).symm
            exact ⟨.inl i,hz.trans hr,rfl⟩
    have himage (y : Fin (d+1) ⊕ Fin (CreationInterval.coalesce (enlarged old new)).length) :
        (graph next).Reachable (.inl k.castSucc) y ↔ imageReach y := by
      constructor
      · intro h
        exact reachable_closed next imageReach (fun h => hclosed h) h
          ⟨.inl k,SimpleGraph.Reachable.rfl,rfl⟩
      · rintro ⟨z,hz,rfl⟩
        exact hz.map embed
    have hrules : componentRules next (.inl k.castSucc) =
        (componentRules a (.inl k)).image Fin.castSucc := by
      ext i
      rw [mem_componentRules,himage,Finset.mem_image]
      constructor
      · rintro ⟨(j|p),hj,he⟩
        · exact ⟨j,(mem_componentRules ..).mpr hj,Sum.inl.inj he⟩
        · cases he
      · rintro ⟨j,hj,rfl⟩
        exact ⟨.inl j,(mem_componentRules ..).mp hj,rfl⟩
    have hpatches : componentPatches next (.inl k.castSucc) =
        (componentPatches a (.inl k)).image label := by
      ext p
      rw [mem_componentPatches,himage,Finset.mem_image]
      constructor
      · rintro ⟨(j|u),hu,he⟩
        · cases he
        · exact ⟨u,(mem_componentPatches ..).mpr hu,Sum.inr.inj he⟩
      · rintro ⟨u,hu,rfl⟩
        exact ⟨.inr u,(mem_componentPatches ..).mp hu,rfl⟩
    have hcard₁ : (componentRules next (.inl k.castSucc)).card =
        (componentRules a (.inl k)).card := by
      rw [hrules,Finset.card_image_of_injective _ (Fin.castSucc_injective d)]
    have hcard₂ : (componentPatches next (.inl k.castSucc)).card =
        (componentPatches a (.inl k)).card := by
      rw [hpatches]
      apply Finset.card_image_of_injOn
      intro p hp u _ he
      exact untouched_label_injective old new (hquiet p ((mem_componentPatches ..).mp hp)) he
    change componentEvent next R k.castSucc = false
    apply (componentEvent_eq_false next R k.castSucc).mpr
    rw [hcard₁,hcard₂]
    exact (componentEvent_eq_false a R k).mp (hbefore k)

/-- Before the first event, the executable test gives the cutoff and the
tree identity for every old patch component. -/
theorem preEvent_patch_components {c : ℕ} (a : Incidence d s c) (R : ℕ)
    (hsurj : Function.Surjective a) (h : ∀ i, componentEvent a R i = false) (p : Fin c) :
    (componentRules a (.inr p)).card ≤ R ∧
      (componentRules a (.inr p)).card*s+1 =
        (componentRules a (.inr p)).card + (componentPatches a (.inr p)).card := by
  obtain ⟨⟨i,j⟩,he⟩ := hsurj p
  have hre : (graph a).Reachable (.inl i) (.inr p) := he ▸ bubble_reaches a i j
  have eq := component_eq_of_reachable a hre
  obtain ⟨hR,hstrict⟩ := (componentEvent_eq_false a R i).mp (h i)
  have hv : (componentRules a (.inl i)).card+(componentPatches a (.inl i)).card ≤
      (componentRules a (.inl i)).card*s+1 := component_vertices_le a (.inl i)
  have rEq : componentRules a (.inl i) = componentRules a (.inr p) := by
    unfold componentRules
    rw [eq]
  have pEq : componentPatches a (.inl i) = componentPatches a (.inr p) := by
    unfold componentPatches
    rw [eq]
  rw [rEq] at hR
  rw [rEq,pEq] at hstrict hv
  exact ⟨hR,by omega⟩

theorem first_event_counts (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ)
    (a : Incidence d s (CreationInterval.coalesce old).length) (hsurj : Function.Surjective a)
    {L R : ℕ} (hL : 0 < L)
    (hwidth : ∀ p, L ≤ 2*((CreationInterval.patches old).positions p).card)
    (hnew : ∀ j, (new j).last.val+1-(new j).first.val ≤ 3*L)
    (hbefore : ∀ i, componentEvent a R i = false) :
    let next := extendIncidence old new a
    let r := (componentRules next (.inl (Fin.last d))).card
    let p := (componentPatches next (.inl (Fin.last d))).card
    r ≤ 8*s*R+1 ∧ cycles r s p ≤ 10*s :=
  enlarged_component_counts old new a hsurj
    (fun p => (preEvent_patch_components a R hsurj hbefore p).2) hL hwidth hnew
    (fun p => (preEvent_patch_components a R hsurj hbefore p).1)

#print axioms first_event_counts

/-- The enlarged component is connected, has the asserted sizes and has
either a positive cycle count or more than the cutoff many rules. -/
theorem first_event_witness (old : List (CreationInterval ℓ)) (new : Fin s → CreationInterval ℓ)
    (a : Incidence d s (CreationInterval.coalesce old).length) (hsurj : Function.Surjective a)
    {L R : ℕ} (hL : 0 < L) (hs : 0 < s)
    (hwidth : ∀ p, L ≤ 2*((CreationInterval.patches old).positions p).card)
    (hnew : ∀ j, (new j).last.val+1-(new j).first.val ≤ 3*L)
    (hbefore : ∀ i, componentEvent a R i = false)
    (hevent : componentEvent (extendIncidence old new a) R (Fin.last d) = true) :
    let next := extendIncidence old new a
    let root : Fin (d+1) ⊕ Fin (CreationInterval.coalesce (enlarged old new)).length :=
      .inl (Fin.last d)
    let r := (componentRules next root).card
    let p := (componentPatches next root).card
    let g := cycles r s p
    (graph (componentIncidence next root)).Connected ∧
      r ≤ 8*s*R+1 ∧ g ≤ 10*s ∧ p = (s-1)*r+1-g ∧
      (g = 0 ∧ R < r ∨ 0 < g) := by
  dsimp only
  let next := extendIncidence old new a
  let root : Fin (d+1) ⊕ Fin (CreationInterval.coalesce (enlarged old new)).length :=
    .inl (Fin.last d)
  let r := (componentRules next root).card
  let p := (componentPatches next root).card
  have conn := componentIncidence_connected next root
  obtain ⟨hr,hg⟩ := first_event_counts old new a hsurj hL hwidth hnew hbefore
  have hv : r+p ≤ r*s+1 := component_vertices_le next root
  have hm : r*s = (s-1)*r+r := by
    calc
      r*s = r*((s-1)+1) := congrArg (r*·) (by omega)
      _ = _ := by ring
  have hpc : p = (s-1)*r+1-cycles r s p := by
    unfold cycles
    omega
  have he : R < r ∨ 0 < cycles r s p := (componentEvent_eq_true _ _ _).mp hevent
  exact ⟨conn,hr,hg,hpc,by
    by_cases hz : cycles r s p = 0
    · exact Or.inl ⟨hz,he.resolve_right (by omega)⟩
    · exact Or.inr (Nat.pos_of_ne_zero hz)⟩

#print axioms all_preEvent_of_last
#print axioms first_event_witness

end ComponentCount

#print axioms retainedRules_bound
#print axioms cycle_count_of_forest

end DeletionCode.Explicit.FirstEvent
