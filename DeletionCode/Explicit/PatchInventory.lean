import DeletionCode.Explicit.GateHistory

/-! Transfer letter-graph inventories when a gate is installed and its
creation interval is merged into the patch partition. -/

namespace DeletionCode.Explicit.LetterGraphCuts

open LetterSequence LocalBudget SelectedReplay
open scoped BigOperators

variable {ℓ a u v r c d : ℕ} {α : Type*}

private theorem lift_reaches {E : Letter ℓ α → Letter ℓ α → Prop} {n : ℕ}
    (w : Lift ℓ n α) (hw : w.Follows E) {i j : Fin n} (hij : i ≤ j) :
    Relation.ReflTransGen E (w.letters i) (w.letters j) := by
  rcases lt_or_eq_of_le hij with h | rfl
  · exact (reaches_of_follows w hw h).to_reflTransGen
  · exact .refl

/-- Two original letters from opposite flanks bound the part of the
creation interval in which the gate changes the graph. -/
structure Gate.InPatch (g : Gate ℓ a u v r α) (P : Patches ℓ c) (p : Fin c) where
  leftOffset : Fin a
  rightOffset : Fin r
  lo : Fin ℓ
  hi : Fin ℓ
  left_original : g.negative.letters ⟨leftOffset.val,by omega⟩ = .original lo
  right_original : g.negative.letters ⟨a+u+rightOffset.val,by omega⟩ = .original hi
  lo_inside : P.first p ≤ lo.val
  hi_inside : hi.val ≤ P.last p

def Gate.marks (g : Gate ℓ a u v r α) : Finset ℕ :=
  ((g.removed.filterMap Letter.position).map Fin.val).toFinset

@[simp] theorem Gate.mem_marks (g : Gate ℓ a u v r α) {k : ℕ} :
    k ∈ g.marks ↔ ∃ z ∈ (g.removed.filterMap Letter.position).toFinset, z.val = k := by
  simp [Gate.marks]

theorem Gate.marks_card_le (g : Gate ℓ a u v r α) : g.marks.card ≤ u := by
  calc
    g.marks.card ≤ ((g.removed.filterMap Letter.position).map Fin.val).length :=
      List.toFinset_card_le _
    _ ≤ g.removed.length := by simpa using List.length_filterMap_le (f := Letter.position) g.removed
    _ = u := g.length_removed

theorem Gate.InPatch.marks_inside {g : Gate ℓ a u v r α} {P : Patches ℓ c} {p : Fin c}
    (h : g.InPatch P p) : g.marks ⊆ P.positions p := by
  intro z hz
  obtain ⟨i,hi,rfl⟩ := g.mem_marks.mp hz
  obtain ⟨w,hw,hi⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hi)
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp (show w ∈ g.removed from hw)
  have hmid : (g.negative.letters ⟨a+j.val,by omega⟩).position = some i := hj ▸ hi
  have hlo := g.negative.increasing (show (⟨h.leftOffset.val,by omega⟩ : Fin (a+u+r)) <
      ⟨a+j.val,by omega⟩ from h.leftOffset.isLt.trans_le (Nat.le_add_right a j.val))
    (by rw [h.left_original]; rfl) hmid
  have hhi := g.negative.increasing (show (⟨a+j.val,by omega⟩ : Fin (a+u+r)) <
      ⟨a+u+h.rightOffset.val,by omega⟩ from by change a+j.val < a+u+h.rightOffset.val; omega)
    hmid (by rw [h.right_original]; rfl)
  change h.lo.val < i.val at hlo
  change i.val < h.hi.val at hhi
  exact Finset.mem_Icc.mpr ⟨h.lo_inside.trans hlo.le,hhi.le.trans h.hi_inside⟩

theorem Gate.InPatch.brackets {g : Gate ℓ a u v r α} {P : Patches ℓ c} {p : Fin c}
    (h : g.InPatch P p) {E : Letter ℓ α → Letter ℓ α → Prop} (hw : g.negative.Follows E)
    {w : Letter ℓ α} (hv : w ∈ g.inserted) :
    HasBrackets (g.edges E) P p w := by
  have ha := g.left_pos
  have hr := g.right_pos
  have left := lift_reaches g.negative hw
    (show (⟨h.leftOffset.val,by omega⟩ : Fin (a+u+r)) ≤ ⟨a-1,by omega⟩ from by
      change h.leftOffset.val ≤ a-1
      omega)
  have right := lift_reaches g.negative hw
    (show (⟨a+u,by omega⟩ : Fin (a+u+r)) ≤ ⟨a+u+h.rightOffset.val,by omega⟩ from by
      change a+u ≤ a+u+h.rightOffset.val
      omega)
  rw [h.left_original] at left
  rw [h.right_original] at right
  have hl := g.negative.increasing
    (show (⟨h.leftOffset.val,by omega⟩ : Fin (a+u+r)) < ⟨a+u+h.rightOffset.val,by omega⟩ from by
      change h.leftOffset.val < a+u+h.rightOffset.val
      omega)
    (by rw [h.left_original]; rfl) (by rw [h.right_original]; rfl)
  exact gate_brackets P p g.left g.right hv h.lo_inside h.hi_inside hl left right

/-- The new intervals contain the previous patches under their new labels. -/
structure PatchMerge (P : Patches ℓ c) (Q : Patches ℓ d) where
  label : Fin c → Fin d
  first_le : ∀ p, Q.first (label p) ≤ P.first p
  last_le : ∀ p, P.last p ≤ Q.last (label p)

def PatchMerge.sources {P : Patches ℓ c} {Q : Patches ℓ d}
    (merge : PatchMerge P Q) (p : Fin d) : Finset (Fin c) :=
  Finset.univ.filter (fun i => merge.label i = p)

@[simp] theorem PatchMerge.mem_sources {P : Patches ℓ c} {Q : Patches ℓ d}
    (merge : PatchMerge P Q) {i : Fin c} {p : Fin d} :
    i ∈ merge.sources p ↔ merge.label i = p := by
  simp [PatchMerge.sources]

/-- Rebuild marks after relabelling the old patches and inserting the
marks of one gate in its new patch. -/
def PatchMerge.withGate {P : Patches ℓ c} {Q : Patches ℓ d}
    (merge : PatchMerge P Q) (g : Gate ℓ a u v r α) (p : Fin d) (hg : g.InPatch Q p) :
    Patches ℓ d :=
  { Q with
    marks := fun j => (merge.sources j).biUnion P.marks ∪ if j = p then g.marks else ∅
    marks_inside := by
      intro j z hz
      rcases Finset.mem_union.mp hz with hold | hnew
      · obtain ⟨i,hi,hmark⟩ := Finset.mem_biUnion.mp hold
        have hlabel := (merge.mem_sources).mp hi
        subst j
        obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp (P.marks_inside i hmark)
        exact Finset.mem_Icc.mpr ⟨(merge.first_le i).trans hlo,hhi.trans (merge.last_le i)⟩
      · by_cases he : j = p
        · subst j
          exact hg.marks_inside (by simpa using hnew)
        · simp [he] at hnew }

def PatchMerge.ownerAfter {P : Patches ℓ c} {Q : Patches ℓ d}
    (merge : PatchMerge P Q) (owner : ℕ → Option (Fin c)) (entry : ℕ) (p : Fin d)
    (id : ℕ) : Option (Fin d) :=
  if id = entry then some p else (owner id).map merge.label

def PatchMerge.stockAfter [DecidableEq α] {P : Patches ℓ c} {Q : Patches ℓ d}
    (merge : PatchMerge P Q) (stock : Fin c → Finset (Letter ℓ α))
    (g : Gate ℓ a u v r α) (p j : Fin d) : Finset (Letter ℓ α) :=
  (merge.sources j).biUnion stock ∪ if j = p then g.inserted.toFinset else ∅

theorem PatchMerge.marks_after {P : Patches ℓ c} {Q : Patches ℓ d}
    (merge : PatchMerge P Q) (g : Gate ℓ a u v r α) (p : Fin d) (hg : g.InPatch Q p)
    {marked : Finset (Fin ℓ)}
    (hold : ∀ z ∈ marked, z.val ∈ Finset.univ.biUnion P.marks) :
    ∀ z ∈ marked ∪ (g.removed.filterMap Letter.position).toFinset,
      z.val ∈ Finset.univ.biUnion (merge.withGate g p hg).marks := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp (hold z hz)
    refine Finset.mem_biUnion.mpr ⟨merge.label i,Finset.mem_univ _,Finset.mem_union_left _ ?_⟩
    exact Finset.mem_biUnion.mpr ⟨i,(merge.mem_sources).mpr rfl,hi⟩
  · refine Finset.mem_biUnion.mpr ⟨p,Finset.mem_univ _,Finset.mem_union_right _ ?_⟩
    simpa using g.mem_marks.mpr ⟨z,hz,rfl⟩

theorem PatchMerge.inventory_after [DecidableEq α] {P : Patches ℓ c} {Q : Patches ℓ d}
    (merge : PatchMerge P Q) (g : Gate ℓ a u v r α) (p : Fin d) (hg : g.InPatch Q p)
    {E : Letter ℓ α → Letter ℓ α → Prop} (hw : g.negative.Follows E)
    (hentry : ∀ offset symbol, ¬ Incident E (.fresh g.entry offset symbol))
    {owner : ℕ → Option (Fin c)} {stock : Fin c → Finset (Letter ℓ α)}
    (hinventory : FreshInventory E P owner stock) :
    FreshInventory (g.edges E) (merge.withGate g p hg) (merge.ownerAfter owner g.entry p)
      (merge.stockAfter stock g p) := by
  intro id offset symbol h
  rcases g.incident_after hw h with hold | hnew
  · obtain ⟨i,hi,hstock,lo,hi',hl,hr,hlt,hleft,hright⟩ := hinventory id offset symbol hold
    have hid : id ≠ g.entry := fun h => hentry offset symbol (h ▸ hold)
    refine ⟨merge.label i,by simp [PatchMerge.ownerAfter,hid,hi],Finset.mem_union_left _ ?_,?_⟩
    · exact Finset.mem_biUnion.mpr ⟨i,(merge.mem_sources).mpr rfl,hstock⟩
    · have retain : E ≤ g.edges E := fun _ _ h => Or.inl h
      exact ⟨lo,hi',(merge.first_le i).trans hl,hr.trans (merge.last_le i),hlt,
        Relation.ReflTransGen.mono retain _ _ hleft,Relation.ReflTransGen.mono retain _ _ hright⟩
  · obtain ⟨j,he⟩ := g.mem_inserted.mp hnew
    have hid := (Letter.fresh.inj he).1
    refine ⟨p,by simp [PatchMerge.ownerAfter,hid],Finset.mem_union_right _ ?_,
      hg.brackets hw hnew⟩
    simpa using hnew

theorem PatchMerge.stockAfter_card_le [DecidableEq α] {P : Patches ℓ c} {Q : Patches ℓ d}
    (merge : PatchMerge P Q) (stock : Fin c → Finset (Letter ℓ α))
    (g : Gate ℓ a u v r α) (p j : Fin d) :
    (merge.stockAfter stock g p j).card ≤
      (∑ i ∈ merge.sources j, (stock i).card) + if j = p then v else 0 := by
  classical
  have hinsert : g.inserted.toFinset.card ≤ v := by
    simpa only [g.length_inserted] using List.toFinset_card_le g.inserted
  unfold PatchMerge.stockAfter
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add Finset.card_biUnion_le
  split <;> simp [*]

theorem PatchMerge.marksAfter_card_le {P : Patches ℓ c} {Q : Patches ℓ d}
    (merge : PatchMerge P Q) (g : Gate ℓ a u v r α) (p j : Fin d) (hg : g.InPatch Q p) :
    ((merge.withGate g p hg).marks j).card ≤
      (∑ i ∈ merge.sources j, (P.marks i).card) + if j = p then u else 0 := by
  classical
  change ((merge.sources j).biUnion P.marks ∪ if j = p then g.marks else ∅).card ≤ _
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add Finset.card_biUnion_le
  split <;> simp [*,g.marks_card_le]

#print axioms PatchMerge.marks_after
#print axioms PatchMerge.inventory_after

end DeletionCode.Explicit.LetterGraphCuts
