import DeletionCode.Qary.EditAlignment

/-!
Explicit alignment data. Unlike the proposition EditAlignment.Alignment, a
trace retains which matched and edit columns were used. Its projections and
counters compute the two words and exact edit counts. A substitution column
holds distinct source and target alphabet symbols. Matched-column anchors
are counts in the actual preceding prefix, as in the manuscript; no
separation convention is imposed here.
-/

namespace DeletionCode.Qary.AlignmentTrace

open DeletionCode.Qary.EditAlignment

inductive Column (α : Type*) where
  | matched (bit : α)
  | deletion (bit : α)
  | insertion (bit : α)
  | substitution (old new : α) (ne : old ≠ new)
  deriving DecidableEq, Repr

variable {α : Type*}

def Column.isEdit : Column α → Bool
  | .matched _ => false
  | .deletion _ => true
  | .insertion _ => true
  | .substitution _ _ _ => true

abbrev Trace (α : Type*) := List (Column α)

namespace Trace

def source : Trace α → Word α
  | [] => []
  | .matched bit :: rest => bit :: source rest
  | .deletion bit :: rest => bit :: source rest
  | .insertion _ :: rest => source rest
  | .substitution old _ _ :: rest => old :: source rest

def target : Trace α → Word α
  | [] => []
  | .matched bit :: rest => bit :: target rest
  | .deletion _ :: rest => target rest
  | .insertion bit :: rest => bit :: target rest
  | .substitution _ new _ :: rest => new :: target rest

def deletions : Trace α → ℕ
  | [] => 0
  | .matched _ :: rest => deletions rest
  | .deletion _ :: rest => deletions rest + 1
  | .insertion _ :: rest => deletions rest
  | .substitution _ _ _ :: rest => deletions rest

def insertions : Trace α → ℕ
  | [] => 0
  | .matched _ :: rest => insertions rest
  | .deletion _ :: rest => insertions rest
  | .insertion _ :: rest => insertions rest + 1
  | .substitution _ _ _ :: rest => insertions rest

def substitutions : Trace α → ℕ
  | [] => 0
  | .matched _ :: rest => substitutions rest
  | .deletion _ :: rest => substitutions rest
  | .insertion _ :: rest => substitutions rest
  | .substitution _ _ _ :: rest => substitutions rest + 1

def matchedCount : Trace α → ℕ
  | [] => 0
  | .matched _ :: rest => matchedCount rest + 1
  | .deletion _ :: rest => matchedCount rest
  | .insertion _ :: rest => matchedCount rest
  | .substitution _ _ _ :: rest => matchedCount rest

/-- The cost of a trace: its number of edit columns. -/
def cost (trace : Trace α) : ℕ := trace.deletions + trace.insertions + trace.substitutions

theorem source_append (left right : Trace α) :
    source (left ++ right) = source left ++ source right := by
  induction left with
  | nil => rfl
  | cons col rest ih => cases col <;> simp [source, ih]

theorem target_append (left right : Trace α) :
    target (left ++ right) = target left ++ target right := by
  induction left with
  | nil => rfl
  | cons col rest ih => cases col <;> simp [target, ih]

theorem deletions_append (left right : Trace α) :
    deletions (left ++ right) = deletions left + deletions right := by
  induction left with
  | nil => simp [deletions]
  | cons col rest ih =>
    cases col <;> simp only [List.cons_append, deletions, ih] <;> omega

theorem insertions_append (left right : Trace α) :
    insertions (left ++ right) = insertions left + insertions right := by
  induction left with
  | nil => simp [insertions]
  | cons col rest ih =>
    cases col <;> simp only [List.cons_append, insertions, ih] <;> omega

theorem substitutions_append (left right : Trace α) :
    substitutions (left ++ right) = substitutions left + substitutions right := by
  induction left with
  | nil => simp [substitutions]
  | cons col rest ih =>
    cases col <;> simp only [List.cons_append, substitutions, ih] <;> omega

theorem matchedCount_append (left right : Trace α) :
    matchedCount (left ++ right) = matchedCount left + matchedCount right := by
  induction left with
  | nil => simp [matchedCount]
  | cons col rest ih =>
    cases col <;> simp only [List.cons_append, matchedCount, ih] <;> omega

theorem source_length (trace : Trace α) :
    trace.source.length = trace.matchedCount + trace.deletions + trace.substitutions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;>
      simp only [source, matchedCount, deletions, substitutions, List.length_cons] <;> omega

theorem target_length (trace : Trace α) :
    trace.target.length = trace.matchedCount + trace.insertions + trace.substitutions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;>
      simp only [target, matchedCount, insertions, substitutions, List.length_cons] <;> omega

theorem length_eq_counts (trace : Trace α) :
    trace.length =
      trace.matchedCount + trace.deletions + trace.insertions + trace.substitutions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;>
      simp only [List.length_cons, matchedCount, deletions, insertions, substitutions] <;> omega

/-- Every computational trace is a genuine alignment of its projections. -/
theorem alignment (trace : Trace α) :
    Alignment trace.source trace.target trace.deletions trace.insertions trace.substitutions := by
  induction trace with
  | nil => exact Alignment.nil
  | cons col rest ih =>
    cases col with
    | matched bit => exact Alignment.matched bit ih
    | deletion bit => exact Alignment.deletion bit ih
    | insertion bit => exact Alignment.insertion bit ih
    | substitution old new hne => exact Alignment.substitution old new hne ih

/-- Number of matched columns strictly before column j. At j = trace.length,
this is the right boundary anchor. Indices beyond the trace saturate there. -/
def matchedAnchor (trace : Trace α) (j : ℕ) : ℕ := matchedCount (trace.take j)

/-- Number of source letters strictly before column j, counting deletions
and substitutions. -/
def sourcePosition (trace : Trace α) (j : ℕ) : ℕ := (source (trace.take j)).length

/-- Number of target letters strictly before column j, counting insertions
and substitutions. -/
def targetPosition (trace : Trace α) (j : ℕ) : ℕ := (target (trace.take j)).length

theorem matchedAnchor_at_column (pre suffix : Trace α) (col : Column α) :
    matchedAnchor (pre ++ col :: suffix) pre.length = pre.matchedCount := by
  simp [matchedAnchor]

theorem sourcePosition_at_column (pre suffix : Trace α) (col : Column α) :
    sourcePosition (pre ++ col :: suffix) pre.length = pre.source.length := by
  simp [sourcePosition]

theorem targetPosition_at_column (pre suffix : Trace α) (col : Column α) :
    targetPosition (pre ++ col :: suffix) pre.length = pre.target.length := by
  simp [targetPosition]

@[simp] theorem matchedAnchor_zero (trace : Trace α) : matchedAnchor trace 0 = 0 := rfl

@[simp] theorem matchedAnchor_end (trace : Trace α) :
    matchedAnchor trace trace.length = trace.matchedCount := by
  simp [matchedAnchor]

theorem matchedAnchor_le (trace : Trace α) (j : ℕ) :
    matchedAnchor trace j ≤ trace.matchedCount := by
  have h := matchedCount_append (trace.take j) (trace.drop j)
  rw [List.take_append_drop] at h
  unfold matchedAnchor
  omega

/-- The source position is the matched anchor plus the preceding deletions
and substitutions. -/
theorem sourcePosition_eq (trace : Trace α) (j : ℕ) :
    sourcePosition trace j =
      matchedAnchor trace j + deletions (trace.take j) + substitutions (trace.take j) :=
  source_length (trace.take j)

/-- The target position is the matched anchor plus the preceding insertions
and substitutions. -/
theorem targetPosition_eq (trace : Trace α) (j : ℕ) :
    targetPosition trace j =
      matchedAnchor trace j + insertions (trace.take j) + substitutions (trace.take j) :=
  target_length (trace.take j)

/-- For a source of length n with d deletions and s substitutions, the right
boundary anchor is n-d-s. -/
theorem matchedAnchor_end_eq_sub (trace : Trace α) (n d s : ℕ)
    (hsource : trace.source.length = n) (hdel : trace.deletions = d)
    (hsub : trace.substitutions = s) :
    matchedAnchor trace trace.length = n - d - s := by
  rw [matchedAnchor_end]
  have h := source_length trace
  omega

end Trace

/-- Propositional alignability has an explicit trace witness. Different
traces can remain distinct data even when their word projections agree. -/
theorem exists_trace_of_alignment {y z : Word α} {d i s : ℕ}
    (h : Alignment y z d i s) :
    ∃ trace : Trace α, trace.source = y ∧ trace.target = z ∧
      trace.deletions = d ∧ trace.insertions = i ∧ trace.substitutions = s := by
  induction h with
  | nil => exact ⟨[], rfl, rfl, rfl, rfl, rfl⟩
  | matched bit h ih =>
    obtain ⟨trace, hs, ht, hd, hi, hsub⟩ := ih
    refine ⟨Column.matched bit :: trace, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Trace.source, Trace.target, Trace.deletions, Trace.insertions,
        Trace.substitutions, hs, ht, hd, hi, hsub]
  | deletion bit h ih =>
    obtain ⟨trace, hs, ht, hd, hi, hsub⟩ := ih
    refine ⟨Column.deletion bit :: trace, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Trace.source, Trace.target, Trace.deletions, Trace.insertions,
        Trace.substitutions, hs, ht, hd, hi, hsub]
  | insertion bit h ih =>
    obtain ⟨trace, hs, ht, hd, hi, hsub⟩ := ih
    refine ⟨Column.insertion bit :: trace, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Trace.source, Trace.target, Trace.deletions, Trace.insertions,
        Trace.substitutions, hs, ht, hd, hi, hsub]
  | substitution old new hne h ih =>
    obtain ⟨trace, hs, ht, hd, hi, hsub⟩ := ih
    refine ⟨Column.substitution old new hne :: trace, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Trace.source, Trace.target, Trace.deletions, Trace.insertions,
        Trace.substitutions, hs, ht, hd, hi, hsub]

/-- Exact equivalence with the already verified alignment proposition. -/
theorem alignment_iff_exists_trace (y z : Word α) (d i s : ℕ) :
    Alignment y z d i s ↔
      ∃ trace : Trace α, trace.source = y ∧ trace.target = z ∧
        trace.deletions = d ∧ trace.insertions = i ∧ trace.substitutions = s := by
  constructor
  · exact exists_trace_of_alignment
  · rintro ⟨trace, rfl, rfl, rfl, rfl, rfl⟩
    exact trace.alignment

/-- Confusability yields actual finite alignment data with the exact counters:
equally many deletions and insertions, and cost at most 2t. -/
theorem trace_of_equal_length_confusability (y z u : Word α) (n t : ℕ)
    (hy : y.length = n) (hz : z.length = n)
    (hyu : WithinEdits t y u) (hzu : WithinEdits t z u) :
    ∃ (d s : ℕ) (trace : Trace α), 2 * d + s ≤ 2 * t ∧
      trace.source = y ∧ trace.target = z ∧
      trace.deletions = d ∧ trace.insertions = d ∧ trace.substitutions = s := by
  obtain ⟨d, s, hcost, halign⟩ := equal_length_confusability y z u n t hy hz hyu hzu
  obtain ⟨trace, hs, ht, hdel, hins, hsub⟩ := exists_trace_of_alignment halign
  exact ⟨d, s, trace, hcost, hs, ht, hdel, hins, hsub⟩

#print axioms Trace.alignment
#print axioms alignment_iff_exists_trace
#print axioms Trace.matchedAnchor_at_column
#print axioms Trace.sourcePosition_eq
#print axioms Trace.matchedAnchor_end_eq_sub
#print axioms trace_of_equal_length_confusability

end DeletionCode.Qary.AlignmentTrace
