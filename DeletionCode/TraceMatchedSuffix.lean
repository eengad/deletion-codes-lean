import DeletionCode.TraceSeparation

/-!
Separation forces a long matched suffix immediately before each edit column.
The suffix is extracted from the actual trace, and therefore is a common
suffix of its source and target prefixes, with its full length proved.
-/
namespace DeletionCode.TraceMatchedSuffix

open AlignmentTrace FiniteConflictGraph TraceSeparation

theorem matchedCount_le_length (trace : Trace) : trace.matchedCount ≤ trace.length := by
  have h := trace.length_eq_counts
  omega

theorem matchedAnchor_le_index (trace : Trace) (i : ℕ) : trace.matchedAnchor i ≤ i := by
  have h := matchedCount_le_length (trace.take i)
  have hlen := List.length_take_le i trace
  exact h.trans hlen

theorem matchedAnchor_gap_le (trace : Trace) (i j : ℕ) (hij : i ≤ j) :
    trace.matchedAnchor j ≤ trace.matchedAnchor i + (j - i) := by
  have hsplit : trace.take j = trace.take i ++ (trace.drop i).take (j - i) := by
    conv_lhs => rw [show j = i + (j - i) by omega, List.take_add]
  have hcount := congrArg Trace.matchedCount hsplit
  rw [Trace.matchedCount_append] at hcount
  have h := matchedCount_le_length ((trace.drop i).take (j - i))
  have hlen := List.length_take_le (j - i) (trace.drop i)
  change Trace.matchedCount (trace.take j) ≤ Trace.matchedCount (trace.take i) + (j - i)
  omega

/-- A trace made entirely of matched columns has identical projections,
and each column contributes one letter to that word. -/
theorem matched_projections (trace : Trace)
    (hmatched : ∀ col ∈ trace, col.isEdit = false) :
    trace.source = trace.target ∧ trace.source.length = trace.length := by
  induction trace with
  | nil => exact ⟨rfl, rfl⟩
  | cons col rest ih =>
    have hcol := hmatched col (List.mem_cons_self)
    have hrest : ∀ c ∈ rest, c.isEdit = false := by
      intro c hc
      exact hmatched c (List.mem_cons_of_mem col hc)
    have h := ih hrest
    cases col with
    | matched bit =>
      simp only [Trace.source, Trace.target, List.length_cons]
      exact ⟨congrArg (List.cons bit) h.1, congrArg (fun n => n + 1) h.2⟩
    | deletion bit => simp only [Column.isEdit, Bool.true_eq_false] at hcol
    | insertion bit => simp only [Column.isEdit, Bool.true_eq_false] at hcol

/-- A concrete edit-free interval of columns supplies a common suffix of
the source and target prefixes. -/
theorem common_suffix_of_matched_range (trace : Trace) (i m : ℕ)
    (hm : m ≤ i) (hi : i ≤ trace.length)
    (hno : ∀ j : Fin trace.length, i - m ≤ j.val → j.val < i → ¬ EditIndex trace j) :
    ∃ a b common : List Bool,
      Trace.source (trace.take i) = a ++ common ∧
      Trace.target (trace.take i) = b ++ common ∧ common.length = m := by
  let suffix : Trace := (trace.drop (i - m)).take m
  have hlength : suffix.length = m := by
    simp only [suffix, List.length_take, List.length_drop]
    omega
  have hmatched : ∀ col ∈ suffix, col.isEdit = false := by
    intro col hcol
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hcol
    have hjm : j < m := by omega
    have hbound : i - m + j < trace.length := by omega
    have hget' : trace.get ⟨i - m + j, hbound⟩ = col := by
      simpa only [suffix, List.get_eq_getElem, List.getElem_take, List.getElem_drop] using hget
    have hnot := hno ⟨i - m + j, hbound⟩
      (by change i - m ≤ i - m + j; omega)
      (by change i - m + j < i; omega)
    change ¬ (trace.get ⟨i - m + j, hbound⟩).isEdit = true at hnot
    rw [hget'] at hnot
    cases hbool : col.isEdit <;> simp_all
  obtain ⟨hproj, hprojlen⟩ := matched_projections suffix hmatched
  have hsplit : trace.take i = trace.take (i - m) ++ suffix := by
    dsimp [suffix]
    conv_lhs => rw [show i = (i - m) + m by omega, List.take_add]
  refine ⟨Trace.source (trace.take (i - m)), Trace.target (trace.take (i - m)), suffix.source,
    ?_, ?_, hprojlen.trans hlength⟩
  · rw [hsplit, Trace.source_append]
  · rw [hsplit, Trace.target_append, ← hproj]

/-- Before any separated edit, at least L-1 consecutive matched columns
give an actual common suffix of the two projected prefixes. -/
theorem common_suffix_before_edit {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    ∃ a b common : List Bool,
      Trace.source (trace.take i.val) = a ++ common ∧
      Trace.target (trace.take i.val) = b ++ common ∧ L - 1 ≤ common.length := by
  have hanchor := (hsep.1 i hi).1
  have hindex := matchedAnchor_le_index trace i.val
  have hm : L - 1 ≤ i.val := by omega
  have hno : ∀ j : Fin trace.length,
      i.val - (L - 1) ≤ j.val → j.val < i.val → ¬ EditIndex trace j := by
    intro j hjlow hjbefore hj
    have hgap := hsep.2 j i hj hi hjbefore
    have hsmall := matchedAnchor_gap_le trace j.val i.val (Nat.le_of_lt hjbefore)
    omega
  obtain ⟨a, b, common, hs, ht, hlen⟩ := common_suffix_of_matched_range trace i.val (L - 1)
    hm (Nat.le_of_lt i.isLt) hno
  exact ⟨a, b, common, hs, ht, by omega⟩

#print axioms matchedAnchor_gap_le
#print axioms matched_projections
#print axioms common_suffix_of_matched_range
#print axioms common_suffix_before_edit

end DeletionCode.TraceMatchedSuffix
