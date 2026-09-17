import DeletionCode.EditAlignment

/-!
Explicit alignment data. Unlike the proposition EditAlignment.Alignment, a
trace retains which matched and edit columns were used. Its projections and
counters compute the two words and exact edit counts. Matched-column anchors
are counts in the actual preceding prefix, as in the manuscript; no separation
convention is imposed here.
-/

namespace DeletionCode.AlignmentTrace

open EditAlignment

inductive Column where
  | matched (bit : Bool)
  | deletion (bit : Bool)
  | insertion (bit : Bool)
  deriving DecidableEq, Repr

def Column.isEdit : Column → Bool
  | .matched _ => false
  | .deletion _ => true
  | .insertion _ => true

abbrev Trace := List Column

namespace Trace

def source : Trace → Word
  | [] => []
  | .matched bit :: rest => bit :: source rest
  | .deletion bit :: rest => bit :: source rest
  | .insertion _ :: rest => source rest

def target : Trace → Word
  | [] => []
  | .matched bit :: rest => bit :: target rest
  | .deletion _ :: rest => target rest
  | .insertion bit :: rest => bit :: target rest

def deletions : Trace → ℕ
  | [] => 0
  | .matched _ :: rest => deletions rest
  | .deletion _ :: rest => deletions rest + 1
  | .insertion _ :: rest => deletions rest

def insertions : Trace → ℕ
  | [] => 0
  | .matched _ :: rest => insertions rest
  | .deletion _ :: rest => insertions rest
  | .insertion _ :: rest => insertions rest + 1

def matchedCount : Trace → ℕ
  | [] => 0
  | .matched _ :: rest => matchedCount rest + 1
  | .deletion _ :: rest => matchedCount rest
  | .insertion _ :: rest => matchedCount rest

theorem source_append (left right : Trace) :
    source (left ++ right) = source left ++ source right := by
  induction left with
  | nil => rfl
  | cons col rest ih => cases col <;> simp [source, ih]

theorem target_append (left right : Trace) :
    target (left ++ right) = target left ++ target right := by
  induction left with
  | nil => rfl
  | cons col rest ih => cases col <;> simp [target, ih]

theorem deletions_append (left right : Trace) :
    deletions (left ++ right) = deletions left + deletions right := by
  induction left with
  | nil => simp [deletions]
  | cons col rest ih =>
    cases col <;> simp only [List.cons_append, deletions, ih] <;> omega

theorem insertions_append (left right : Trace) :
    insertions (left ++ right) = insertions left + insertions right := by
  induction left with
  | nil => simp [insertions]
  | cons col rest ih =>
    cases col <;> simp only [List.cons_append, insertions, ih] <;> omega

theorem matchedCount_append (left right : Trace) :
    matchedCount (left ++ right) = matchedCount left + matchedCount right := by
  induction left with
  | nil => simp [matchedCount]
  | cons col rest ih =>
    cases col <;> simp only [List.cons_append, matchedCount, ih] <;> omega

theorem source_length (trace : Trace) :
    trace.source.length = trace.matchedCount + trace.deletions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;> simp only [source, matchedCount, deletions, List.length_cons] <;> omega

theorem target_length (trace : Trace) :
    trace.target.length = trace.matchedCount + trace.insertions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;> simp only [target, matchedCount, insertions, List.length_cons] <;> omega

theorem length_eq_counts (trace : Trace) :
    trace.length = trace.matchedCount + trace.deletions + trace.insertions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;>
      simp only [List.length_cons, matchedCount, deletions, insertions] <;> omega

/-- Every computational trace is a genuine alignment of its projections. -/
theorem alignment (trace : Trace) :
    Alignment trace.source trace.target trace.deletions trace.insertions := by
  induction trace with
  | nil => exact Alignment.nil
  | cons col rest ih =>
    cases col with
    | matched bit => exact Alignment.matched bit ih
    | deletion bit => exact Alignment.deletion bit ih
    | insertion bit => exact Alignment.insertion bit ih

/-- Number of matched columns strictly before column j. At j = trace.length,
this is the right boundary anchor. Indices beyond the trace saturate there. -/
def matchedAnchor (trace : Trace) (j : ℕ) : ℕ := matchedCount (trace.take j)

/-- Number of source letters strictly before column j, counting deletions. -/
def sourcePosition (trace : Trace) (j : ℕ) : ℕ := (source (trace.take j)).length

/-- Number of target letters strictly before column j, counting insertions. -/
def targetPosition (trace : Trace) (j : ℕ) : ℕ := (target (trace.take j)).length

theorem matchedAnchor_at_column (pre suffix : Trace) (col : Column) :
    matchedAnchor (pre ++ col :: suffix) pre.length = pre.matchedCount := by
  simp [matchedAnchor]

theorem sourcePosition_at_column (pre suffix : Trace) (col : Column) :
    sourcePosition (pre ++ col :: suffix) pre.length = pre.source.length := by
  simp [sourcePosition]

theorem targetPosition_at_column (pre suffix : Trace) (col : Column) :
    targetPosition (pre ++ col :: suffix) pre.length = pre.target.length := by
  simp [targetPosition]

@[simp] theorem matchedAnchor_zero (trace : Trace) : matchedAnchor trace 0 = 0 := rfl

@[simp] theorem matchedAnchor_end (trace : Trace) :
    matchedAnchor trace trace.length = trace.matchedCount := by
  simp [matchedAnchor]

theorem matchedAnchor_le (trace : Trace) (j : ℕ) :
    matchedAnchor trace j ≤ trace.matchedCount := by
  have h := matchedCount_append (trace.take j) (trace.drop j)
  rw [List.take_append_drop] at h
  unfold matchedAnchor
  omega

/-- The source position is the matched anchor plus preceding deletions. -/
theorem sourcePosition_eq (trace : Trace) (j : ℕ) :
    sourcePosition trace j = matchedAnchor trace j + deletions (trace.take j) :=
  source_length (trace.take j)

/-- The target position is the matched anchor plus preceding insertions. -/
theorem targetPosition_eq (trace : Trace) (j : ℕ) :
    targetPosition trace j = matchedAnchor trace j + insertions (trace.take j) :=
  target_length (trace.take j)

/-- For a source of length n with d deletions, the right boundary anchor is n-d. -/
theorem matchedAnchor_end_eq_sub (trace : Trace) (n d : ℕ)
    (hsource : trace.source.length = n) (hdel : trace.deletions = d) :
    matchedAnchor trace trace.length = n - d := by
  rw [matchedAnchor_end]
  have h := source_length trace
  omega

end Trace

/-- Propositional alignability has an explicit trace witness. Different
traces can remain distinct data even when their word projections agree. -/
theorem exists_trace_of_alignment {y z : Word} {d i : ℕ}
    (h : Alignment y z d i) :
    ∃ trace : Trace, trace.source = y ∧ trace.target = z ∧
      trace.deletions = d ∧ trace.insertions = i := by
  induction h with
  | nil => exact ⟨[], rfl, rfl, rfl, rfl⟩
  | matched bit h ih =>
    obtain ⟨trace, hs, ht, hd, hi⟩ := ih
    refine ⟨Column.matched bit :: trace, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Trace.source, Trace.target, Trace.deletions, Trace.insertions, hs, ht, hd, hi]
  | deletion bit h ih =>
    obtain ⟨trace, hs, ht, hd, hi⟩ := ih
    refine ⟨Column.deletion bit :: trace, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Trace.source, Trace.target, Trace.deletions, Trace.insertions, hs, ht, hd, hi]
  | insertion bit h ih =>
    obtain ⟨trace, hs, ht, hd, hi⟩ := ih
    refine ⟨Column.insertion bit :: trace, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Trace.source, Trace.target, Trace.deletions, Trace.insertions, hs, ht, hd, hi]

/-- Exact equivalence with the already verified alignment proposition. -/
theorem alignment_iff_exists_trace (y z : Word) (d i : ℕ) :
    Alignment y z d i ↔
      ∃ trace : Trace, trace.source = y ∧ trace.target = z ∧
        trace.deletions = d ∧ trace.insertions = i := by
  constructor
  · exact exists_trace_of_alignment
  · rintro ⟨trace, rfl, rfl, rfl, rfl⟩
    exact trace.alignment

/-- Confusability yields actual finite alignment data with the exact counters. -/
theorem trace_of_equal_length_confusability (y z u : Word) (n t : ℕ)
    (hy : y.length = n) (hz : z.length = n)
    (hyu : WithinEdits t y u) (hzu : WithinEdits t z u) :
    ∃ (d : ℕ) (trace : Trace), d ≤ t ∧ trace.source = y ∧ trace.target = z ∧
      trace.deletions = d ∧ trace.insertions = d := by
  obtain ⟨d, hd, halign⟩ := equal_length_confusability y z u n t hy hz hyu hzu
  obtain ⟨trace, hs, ht, hdel, hins⟩ := exists_trace_of_alignment halign
  exact ⟨d, trace, hd, hs, ht, hdel, hins⟩

#print axioms Trace.alignment
#print axioms alignment_iff_exists_trace
#print axioms Trace.matchedAnchor_at_column
#print axioms Trace.sourcePosition_eq
#print axioms Trace.matchedAnchor_end_eq_sub
#print axioms trace_of_equal_length_confusability

end DeletionCode.AlignmentTrace
