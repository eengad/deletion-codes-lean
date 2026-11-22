import DeletionCode.Explicit.GateGeometry

/-! Attach the individual gates to the computed patch partition and count
their marks and inserted letters using the rule–patch graph. -/

namespace DeletionCode.Explicit.LetterGraphCuts

open LetterSequence LocalBudget RulePatch SelectedReplay

variable {ℓ a u v r d s : ℕ} {α : Type*}

/-- The data of a gate used to build the rule–patch graph and its inventories. -/
structure GateData (ℓ : ℕ) (α : Type*) where
  id : ℕ
  interval : CreationInterval ℓ
  marks : Finset ℕ
  inserted : Finset (Letter ℓ α)
  marks_inside : marks ⊆ Finset.Icc interval.first.val interval.last.val

theorem Gate.marks_subset_positions (g : Gate ℓ a u v r α) :
    g.marks ⊆ g.negative.positions := by
  intro k hk
  obtain ⟨p,hp,rfl⟩ := g.mem_marks.mp hk
  obtain ⟨w,hw,hwp⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hp)
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp (show w ∈ g.removed from hw)
  exact g.negative.mem_positions.mpr ⟨⟨a+j.val,by omega⟩,p,hj ▸ hwp,rfl⟩

def Gate.data [DecidableEq α] (g : Gate ℓ a u v r α) (hn : g.negative.positions.Nonempty) :
    GateData ℓ α where
  id := g.entry
  interval := g.creationInterval hn
  marks := g.marks
  inserted := g.inserted.toFinset
  marks_inside := by
    intro p hp
    exact Finset.mem_Icc.mpr (CreationInterval.ofLift_contains_position g.negative hn
      (g.marks_subset_positions hp))

theorem Gate.data_card [DecidableEq α] (g : Gate ℓ a u v r α) (hn : g.negative.positions.Nonempty) :
    (g.data hn).marks.card ≤ u ∧ (g.data hn).inserted.card ≤ v :=
  ⟨g.marks_card_le,by simpa only [Gate.data,g.length_inserted] using List.toFinset_card_le g.inserted⟩

namespace PatchTable

variable (data : Fin d × Fin s → GateData ℓ α)

def intervals : List (CreationInterval ℓ) :=
  (edgeList d s).map (fun e => (data e).interval)

theorem interval_mem (e : Fin d × Fin s) : (data e).interval ∈ intervals data :=
  List.mem_map.mpr ⟨e,mem_edgeList e,rfl⟩

abbrev patchCount := (CreationInterval.coalesce (intervals data)).length

def incidence : Incidence d s (patchCount data) :=
  fun e => CreationInterval.label (intervals data) (data e).interval (interval_mem data e)

/-- Every output patch is incident to some bubble. -/
theorem incidence_surjective : Function.Surjective (incidence data) := by
  intro p
  obtain ⟨i,hi,hfit⟩ := CreationInterval.coalesce_has_input
    (show (CreationInterval.coalesce (intervals data)).get p ∈
      CreationInterval.coalesce (intervals data) from List.get_mem ..)
  obtain ⟨e,_,he⟩ := List.mem_map.mp hi
  have hf : ((CreationInterval.coalesce (intervals data)).get p).Contains (data e).interval :=
    he.symm ▸ hfit
  exact ⟨e,(CreationInterval.label_eq_iff (intervals data) (data e).interval (interval_mem data e) p).mpr hf⟩

/-- Marks and inserted letters are grouped by the computed patch labels.
Bubble edges retain their multiplicity even if they share a rule and patch. -/
def patches : Patches ℓ (patchCount data) :=
  { CreationInterval.patches (intervals data) with
    marks := fun p => (atPatch (incidence data) Finset.univ p).biUnion (fun e => (data e).marks)
    marks_inside := by
      intro p k hk
      obtain ⟨e,he,hk⟩ := Finset.mem_biUnion.mp hk
      have hp := (Finset.mem_filter.mp he).2
      have h := CreationInterval.patches_contains (intervals data) (data e).interval
        (interval_mem data e)
      change (CreationInterval.patches (intervals data)).first (incidence data e) ≤ _ ∧
        _ ≤ (CreationInterval.patches (intervals data)).last (incidence data e) at h
      rw [hp] at h
      obtain ⟨hl,hr⟩ := Finset.mem_Icc.mp ((data e).marks_inside hk)
      exact Finset.mem_Icc.mpr ⟨h.1.trans hl,hr.trans h.2⟩ }

def stock [DecidableEq α] (p : Fin (patchCount data)) : Finset (Letter ℓ α) :=
  (atPatch (incidence data) Finset.univ p).biUnion (fun e => (data e).inserted)

def owner (id : ℕ) : Option (Fin (patchCount data)) :=
  ((edgeList d s).find? (fun e => decide ((data e).id = id))).map (incidence data)

theorem owner_of_gate (hid : Function.Injective (fun e => (data e).id)) (e : Fin d × Fin s) :
    owner data (data e).id = some (incidence data e) := by
  unfold owner
  generalize hfind : (edgeList d s).find? (fun f => decide ((data f).id = (data e).id)) = result
  cases result with
  | none =>
    have h := List.find?_eq_none.mp hfind e (mem_edgeList e)
    simp at h
  | some f =>
    have he := List.find?_some (p := fun f => decide ((data f).id = (data e).id)) hfind
    rw [hid (of_decide_eq_true he)]
    rfl

theorem incidence_contains (e : Fin d × Fin s) :
    (patches data).first (incidence data e) ≤ (data e).interval.first.val ∧
      (data e).interval.last.val ≤ (patches data).last (incidence data e) :=
  CreationInterval.patches_contains (intervals data) (data e).interval (interval_mem data e)

private theorem mem_incident (e : Fin d × Fin s) :
    e ∈ atPatch (incidence data) Finset.univ (incidence data e) := by
  simp [atPatch,edges]

theorem marks_at_gate (e : Fin d × Fin s) :
    (data e).marks ⊆ (patches data).marks (incidence data e) :=
  fun _ h => Finset.mem_biUnion.mpr ⟨e,mem_incident data e,h⟩

theorem stock_at_gate [DecidableEq α] (e : Fin d × Fin s) :
    (data e).inserted ⊆ stock data (incidence data e) :=
  fun _ h => Finset.mem_biUnion.mpr ⟨e,mem_incident data e,h⟩

theorem patch_width {L : ℕ}
    (h : ∀ e, L ≤ 2 * ((data e).interval.last.val+1-(data e).interval.first.val))
    (p : Fin (patchCount data)) : L ≤ 2 * ((patches data).positions p).card := by
  apply CreationInterval.patch_width_lower (intervals data) _ p
  intro i hi
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hi
  exact h e

/-- The local budget uses the rule count in the component of the current
patch, after recomputing the incidence. A merge may change that component. -/
theorem capacity [DecidableEq α] {R b : ℕ}
    (hmark : ∀ e, (data e).marks.card ≤ b)
    (hstock : ∀ e, (data e).inserted.card ≤ b)
    (p : Fin (patchCount data)) (rules : Finset (Fin d)) (hr : rules.card ≤ R)
    (hcomponent : ∀ i, (graph (incidence data)).Reachable (.inl i) (.inr p) → i ∈ rules) :
    ((patches data).marks p).card ≤ s*b*R ∧ (stock data p).card ≤ s*b*R := by
  have hc := gates_per_patch (incidence data) p rules hr hcomponent
  exact ⟨marks_per_patch (incidence data) p _ hc hmark,
    sum_over_gates (incidence data) p _ hc (fun e _ => hstock e)⟩

/-- The graph witnesses attached to the records, expressed before assigning
current patch labels. -/
def RecordsGraph [DecidableEq α] (E : Letter ℓ α → Letter ℓ α → Prop)
    (marked : Finset (Fin ℓ)) : Prop :=
  (∀ z ∈ marked, ∃ e, z.val ∈ (data e).marks) ∧
  (∀ id k x, Incident E (.fresh id k x) →
    ∃ e, (data e).id = id ∧ .fresh id k x ∈ (data e).inserted ∧
      ∃ lo hi : Fin ℓ, (data e).interval.first ≤ lo ∧ hi ≤ (data e).interval.last ∧ lo < hi ∧
        Relation.ReflTransGen E (.original lo) (.fresh id k x) ∧
        Relation.ReflTransGen E (.fresh id k x) (.original hi))

theorem initial_records [DecidableEq α] : RecordsGraph data originalEdges ∅ := by
  refine ⟨by simp,?_⟩
  intro id k x h
  obtain ⟨other,h⟩ := h
  cases other <;> simp [originalEdges] at h

theorem RecordsGraph.entry_unused [DecidableEq α]
    {E : Letter ℓ α → Letter ℓ α → Prop} {marked : Finset (Fin ℓ)}
    (h : RecordsGraph data E marked) {id : ℕ} (hnew : ∀ e, (data e).id ≠ id)
    (k : ℕ) (x : α) : ¬ Incident E (.fresh id k x) := by
  intro hv
  obtain ⟨e,he,_,_⟩ := h.2 id k x hv
  exact hnew e he

/-- Adding a gate preserves the graph witnesses of the old records and
adds the witnesses for its own record. The rule and bubble labels may
change because the patch table is rebuilt from the enlarged record set. -/
theorem RecordsGraph.extend [DecidableEq α] {d' s' : ℕ}
    {new : Fin d' × Fin s' → GateData ℓ α}
    {E : Letter ℓ α → Letter ℓ α → Prop} {marked : Finset (Fin ℓ)}
    (h : RecordsGraph data E marked) (g : Gate ℓ a u v r α)
    (hneg : g.negative.Follows E) (hn : g.negative.positions.Nonempty)
    (hl : g.negative.freshOffsets.card < a) (hr : g.negative.freshOffsets.card < r)
    (hkeep : ∀ e, ∃ f, new f = data e) (hgate : ∃ f, new f = g.data hn) :
    RecordsGraph new (g.edges E) (marked ∪ (g.removed.filterMap Letter.position).toFinset) := by
  obtain ⟨newGate,hnewGate⟩ := hgate
  refine ⟨?_,?_⟩
  · intro z hz
    rcases Finset.mem_union.mp hz with ho | hg
    · obtain ⟨e,he⟩ := h.1 z ho
      obtain ⟨f,hf⟩ := hkeep e
      exact ⟨f,hf ▸ he⟩
    · exact ⟨newGate,hnewGate ▸ g.mem_marks.mpr ⟨z,hg,rfl⟩⟩
  · intro id k x hv
    rcases g.incident_after hneg hv with ho | hg
    · obtain ⟨e,he,hstock,lo,hi,hlo,hhi,hlt,hleft,hright⟩ := h.2 id k x ho
      obtain ⟨f,hf⟩ := hkeep e
      have includeEdges : E ≤ g.edges E := fun _ _ h => Or.inl h
      refine ⟨f,hf ▸ he,hf ▸ hstock,lo,hi,hf ▸ hlo,hf ▸ hhi,hlt,?_,?_⟩
      · exact Relation.ReflTransGen.mono includeEdges _ _ hleft
      · exact Relation.ReflTransGen.mono includeEdges _ _ hright
    · obtain ⟨i,hi⟩ := g.mem_inserted.mp hg
      have hid : (g.data hn).id = id := (Letter.fresh.inj hi).1.symm
      let iv := g.creationInterval hn
      let one := CreationInterval.toPatches [iv] (List.pairwise_singleton _ _)
      obtain ⟨fit⟩ := g.inPatch_of_creation one 0 hn hl hr le_rfl le_rfl
      obtain ⟨lo,hi',hlo,hhi,hlt,hleft,hright⟩ := fit.brackets hneg hg
      exact ⟨newGate,hnewGate ▸ hid,hnewGate ▸ List.mem_toFinset.mpr hg,lo,hi',
        hnewGate ▸ hlo,hnewGate ▸ hhi,hlt,hleft,hright⟩

theorem records_marked [DecidableEq α] {E : Letter ℓ α → Letter ℓ α → Prop}
    {marked : Finset (Fin ℓ)} (h : RecordsGraph data E marked) :
    ∀ z ∈ marked, z.val ∈ Finset.univ.biUnion (patches data).marks := by
  intro z hz
  obtain ⟨e,he⟩ := h.1 z hz
  exact Finset.mem_biUnion.mpr ⟨incidence data e,Finset.mem_univ _,marks_at_gate data e he⟩

theorem records_inventory [DecidableEq α] {E : Letter ℓ α → Letter ℓ α → Prop}
    {marked : Finset (Fin ℓ)} (h : RecordsGraph data E marked)
    (hid : Function.Injective (fun e => (data e).id)) :
    FreshInventory E (patches data) (owner data) (stock data) := by
  intro id k x hv
  obtain ⟨e,he,hstock,lo,hi,hl,hr,hlt,hleft,hright⟩ := h.2 id k x hv
  have hc := incidence_contains data e
  refine ⟨incidence data e,?_,stock_at_gate data e hstock,?_⟩
  · rw [← he]
    exact owner_of_gate data hid e
  · exact ⟨lo,hi,hc.1.trans hl,hr.trans hc.2,hlt,hleft,hright⟩

/-- Apply the old-graph budget using the computed patch table, before a
first event. Only the bounded component rule sets and the gate records
remain as inputs to the counting argument. -/
theorem path_budget [DecidableEq α] {E : Letter ℓ α → Letter ℓ α → Prop}
    {marked : Finset (Fin ℓ)} (H : History ℓ α E marked) (hgraph : RecordsGraph data E marked)
    (hid : Function.Injective (fun e => (data e).id)) {L b R m : ℕ}
    (hL : 2 ≤ L) (hcap : 4*(s*b*R) ≤ L)
    (hwidth : ∀ e, L ≤ 2 * ((data e).interval.last.val+1-(data e).interval.first.val))
    (hmark : ∀ e, (data e).marks.card ≤ b) (hstock : ∀ e, (data e).inserted.card ≤ b)
    (hcomponents : ∀ p, ∃ rules : Finset (Fin d), rules.card ≤ R ∧
      ∀ i, (graph (incidence data)).Reachable (.inl i) (.inr p) → i ∈ rules)
    (w : Lift ℓ m α) (hmin : L ≤ m) (hmax : m ≤ 3*L) (hw : w.Follows E) :
    w.freshOffsets.card ≤ 14*(s*b*R) ∧ w.omissions.card ≤ 14*(s*b*R) := by
  have caps (p : Fin (patchCount data)) :
      ((patches data).marks p).card ≤ s*b*R ∧ (stock data p).card ≤ s*b*R := by
    obtain ⟨rules,hr,hc⟩ := hcomponents p
    exact capacity data hmark hstock p rules hr hc
  exact old_graph_path_budget H (patches data) (owner data) (stock data) hL
    (patch_width data hwidth) hcap (fun p => (caps p).1) (fun p => (caps p).2)
    (records_marked data hgraph) (records_inventory data hgraph hid) w hmin hmax hw

#print axioms path_budget

end PatchTable
end DeletionCode.Explicit.LetterGraphCuts
