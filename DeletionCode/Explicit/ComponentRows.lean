import DeletionCode.Explicit.RulePatchComponents

/-! Assign each rule to its component's least rule and retain chronological row order. -/

namespace DeletionCode.Explicit.RulePatch

variable {d s c : ℕ} {V : Type*}

def representative (a : Incidence d s c) (i : Fin d) : Fin d :=
  ((List.finRange d).find? fun j => decide (j ∈ componentRules a (.inl i))).getD i

theorem representative_mem (a : Incidence d s c) (i : Fin d) :
    representative a i ∈ componentRules a (.inl i) := by
  have hi : i ∈ componentRules a (.inl i) := (mem_componentRules ..).mpr SimpleGraph.Reachable.rfl
  unfold representative
  cases h : (List.finRange d).find? (fun j => decide (j ∈ componentRules a (.inl i))) with
  | some j =>
    have he := List.find?_some h
    exact of_decide_eq_true he
  | none => exact hi

theorem representative_eq_iff (a : Incidence d s c) (i j : Fin d) :
    representative a i = representative a j ↔ (graph a).Reachable (.inl i) (.inl j) := by
  constructor
  · intro he
    have hi := (mem_componentRules a (.inl i) _).mp (representative_mem a i)
    have hj := (mem_componentRules a (.inl j) _).mp (representative_mem a j)
    rw [he] at hi
    exact hi.trans hj.symm
  · intro h
    have he : componentRules a (.inl i) = componentRules a (.inl j) := by
      unfold componentRules
      rw [component_eq_of_reachable a h]
    have hh : ((List.finRange d).find? fun k => decide (k ∈ componentRules a (.inl i))) ≠ none := by
      intro hn
      have hi : i ∈ componentRules a (.inl i) := (mem_componentRules ..).mpr SimpleGraph.Reachable.rfl
      have hf := List.find?_eq_none.mp hn i (by simp)
      simp [hi] at hf
    unfold representative
    rw [← he]
    cases hpick : (List.finRange d).find? (fun k => decide (k ∈ componentRules a (.inl i))) with
    | none => exact (hh hpick).elim
    | some _ => rfl

def ids (a : Incidence d s c) (p : Fin d) : List (Fin d) :=
  (List.finRange d).filter (fun j => representative a j == p)

theorem mem_ids (a : Incidence d s c) (p i : Fin d) :
    i ∈ ids a p ↔ representative a i = p := by
  simp [ids]

def partRows (a : Incidence d s c) (row : Fin d → V) (p : Fin d) : List V :=
  (ids a p).map row

theorem mem_partRows (a : Incidence d s c) (row : Fin d → V) (p : Fin d) (v : V) :
    v ∈ partRows a row p ↔ ∃ i, representative a i = p ∧ row i = v := by
  simp [partRows,List.mem_map,mem_ids]

theorem partRows_length_le (a : Incidence d s c) (row : Fin d → V) (p : Fin d)
    {R : ℕ} (h : ∀ i : Fin d, (componentRules a (.inl i)).card ≤ R) :
    (partRows a row p).length ≤ R := by
  rw [partRows,List.length_map]
  have hn : (ids a p).Nodup := (List.nodup_finRange _).filter _
  rw [← List.toFinset_card_of_nodup hn]
  apply (Finset.card_le_card (t := componentRules a (.inl p)) ?_).trans (h p)
  intro i hi
  have he := (mem_ids a p i).mp (List.mem_toFinset.mp hi)
  have hs := (mem_componentRules a (.inl i) _).mp (representative_mem a i)
  rw [he] at hs
  exact (mem_componentRules ..).mpr hs.symm

/-- Rules in different components cannot have bubbles in a common patch. -/
theorem representatives_eq_of_patch (a : Incidence d s c)
    {e f : Fin d × Fin s} (hp : a e = a f) :
    representative a e.1 = representative a f.1 := by
  apply (representative_eq_iff a _ _).mpr
  have he := bubble_reaches a e.1 e.2
  have hf := bubble_reaches a f.1 f.2
  have hn : a (e.1,e.2) = a (f.1,f.2) := hp
  rw [hn] at he
  exact he.trans hf.symm

#print axioms representative_eq_iff
#print axioms partRows_length_le

end DeletionCode.Explicit.RulePatch
