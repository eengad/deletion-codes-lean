import DeletionCode.Qary.FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin

/-!
The finite index set consists of the actual deletion, insertion and
substitution columns of a trace. Orientations, letters, source positions, and
isolated one-edit targets are read from those columns. Its cardinalities
are derived from the trace counters, including the balanced Fin (2*t)
enumeration of a trace with d deletions, d insertions and 2t-2d
substitutions.
-/
namespace DeletionCode.Qary.TraceEditData

open DeletionCode.Qary.AlignmentTrace DeletionCode.Qary.FiniteConflictGraph DeletionCode.Qary.HeaderRecovery
open scoped BigOperators

variable {α : Type*}

def EditColumn (trace : Trace α) := {i : Fin trace.length // EditIndex trace i}

instance editColumnFintype (trace : Trace α) : Fintype (EditColumn trace) := by
  unfold EditColumn EditIndex
  infer_instance

def column (trace : Trace α) (c : EditColumn trace) : Column α := trace.get c.val

def position (trace : Trace α) (c : EditColumn trace) : ℕ := trace.sourcePosition c.val.val

theorem column_isEdit (trace : Trace α) (c : EditColumn trace) :
    (column trace c).isEdit = true := c.property

theorem column_cases (trace : Trace α) (c : EditColumn trace) :
    (∃ bit, column trace c = .deletion bit) ∨ (∃ bit, column trace c = .insertion bit) ∨
      (∃ (old new : α) (hne : old ≠ new), column trace c = .substitution old new hne) := by
  have h := column_isEdit trace c
  cases hc : column trace c with
  | matched bit => simp only [hc, Column.isEdit, Bool.false_eq_true] at h
  | deletion bit => exact Or.inl ⟨bit, rfl⟩
  | insertion bit => exact Or.inr (Or.inl ⟨bit, rfl⟩)
  | substitution old new hne => exact Or.inr (Or.inr ⟨old, new, hne, rfl⟩)

/-- The matched-column branch is unreachable in the actual edit index type,
as proved by column_cases. Its unused value makes this a direct computation. -/
def orientation (trace : Trace α) (c : EditColumn trace) : Orientation :=
  match column trace c with
  | .matched _ => .deletion
  | .deletion _ => .deletion
  | .insertion _ => .insertion
  | .substitution _ _ _ => .substitution

/-- The letter of the column: the deleted, inserted, or replaced source letter. -/
def bit (trace : Trace α) (c : EditColumn trace) : α :=
  match column trace c with
  | .matched b => b
  | .deletion b => b
  | .insertion b => b
  | .substitution b _ _ => b

/-- The target symbol, used to perform a substitution. -/
def newBit (trace : Trace α) (c : EditColumn trace) : α :=
  match column trace c with
  | .matched b => b
  | .deletion b => b
  | .insertion b => b
  | .substitution _ b _ => b

theorem orientation_of_deletion (trace : Trace α) (c : EditColumn trace) (b : α)
    (hc : column trace c = .deletion b) : orientation trace c = .deletion := by
  simp [orientation, hc]

theorem orientation_of_insertion (trace : Trace α) (c : EditColumn trace) (b : α)
    (hc : column trace c = .insertion b) : orientation trace c = .insertion := by
  simp [orientation, hc]

theorem bit_of_deletion (trace : Trace α) (c : EditColumn trace) (b : α)
    (hc : column trace c = .deletion b) : bit trace c = b := by simp [bit, hc]

theorem bit_of_insertion (trace : Trace α) (c : EditColumn trace) (b : α)
    (hc : column trace c = .insertion b) : bit trace c = b := by simp [bit, hc]

theorem orientation_of_substitution (trace : Trace α) (c : EditColumn trace) (b : α) (new : α) (hne : b ≠ new)
    (hc : column trace c = .substitution b new hne) : orientation trace c = .substitution := by
  simp [orientation, hc]

theorem bit_of_substitution (trace : Trace α) (c : EditColumn trace) (b : α) (new : α) (hne : b ≠ new)
    (hc : column trace c = .substitution b new hne) : bit trace c = b := by simp [bit, hc]

/-- Perform this one actual edit on the original source, independently of
the other edit columns in the trace. -/
def oneEditTarget (trace : Trace α) (c : EditColumn trace) : List α :=
  match orientation trace c with
  | .deletion => trace.source.eraseIdx (position trace c)
  | .insertion => trace.source.take (position trace c) ++
      bit trace c :: trace.source.drop (position trace c)
  | .substitution => trace.source.take (position trace c) ++
      newBit trace c :: trace.source.drop (position trace c + 1)

theorem oneEditTarget_of_deletion (trace : Trace α) (c : EditColumn trace) (b : α)
    (hc : column trace c = .deletion b) :
    oneEditTarget trace c = trace.source.eraseIdx (position trace c) := by
  simp only [oneEditTarget, orientation_of_deletion trace c b hc]

theorem oneEditTarget_of_insertion (trace : Trace α) (c : EditColumn trace) (b : α)
    (hc : column trace c = .insertion b) :
    oneEditTarget trace c = trace.source.take (position trace c) ++
      b :: trace.source.drop (position trace c) := by
  simp only [oneEditTarget, orientation_of_insertion trace c b hc, bit_of_insertion trace c b hc]

theorem oneEditTarget_of_substitution (trace : Trace α) (c : EditColumn trace) (b : α) (new : α) (hne : b ≠ new)
    (hc : column trace c = .substitution b new hne) :
    oneEditTarget trace c = trace.source.take (position trace c) ++
      new :: trace.source.drop (position trace c + 1) := by
  simp only [oneEditTarget, orientation_of_substitution trace c b new hne hc,
    newBit, hc]

def isDeletion : Column α → Bool
  | .deletion _ => true
  | _ => false

def isInsertion : Column α → Bool
  | .insertion _ => true
  | _ => false

def isSubstitution : Column α → Bool
  | .substitution _ _ _ => true
  | _ => false

private theorem isDeletion_edit (col : Column α) (h : isDeletion col = true) : col.isEdit = true := by
  cases col <;> simp_all only [isDeletion, Column.isEdit, Bool.false_eq_true]

private theorem isInsertion_edit (col : Column α) (h : isInsertion col = true) : col.isEdit = true := by
  cases col <;> simp_all only [isInsertion, Column.isEdit, Bool.false_eq_true]

private theorem isSubstitution_edit (col : Column α) (h : isSubstitution col = true) :
    col.isEdit = true := by
  cases col <;> simp_all only [isSubstitution, Column.isEdit, Bool.false_eq_true]

theorem orientation_eq_deletion_iff (trace : Trace α) (c : EditColumn trace) :
    orientation trace c = .deletion ↔ isDeletion (column trace c) = true := by
  rcases column_cases trace c with ⟨b, hc⟩ | ⟨b, hc⟩ | ⟨b, new, hne, hc⟩
  · simp only [orientation_of_deletion trace c b hc, hc, isDeletion]
  · simp only [orientation_of_insertion trace c b hc, hc, isDeletion, reduceCtorEq,
      Bool.false_eq_true]
  · simp only [orientation_of_substitution trace c b new hne hc, hc, isDeletion, reduceCtorEq,
      Bool.false_eq_true]

theorem orientation_eq_insertion_iff (trace : Trace α) (c : EditColumn trace) :
    orientation trace c = .insertion ↔ isInsertion (column trace c) = true := by
  rcases column_cases trace c with ⟨b, hc⟩ | ⟨b, hc⟩ | ⟨b, new, hne, hc⟩
  · simp only [orientation_of_deletion trace c b hc, hc, isInsertion, reduceCtorEq,
      Bool.false_eq_true]
  · simp only [orientation_of_insertion trace c b hc, hc, isInsertion]
  · simp only [orientation_of_substitution trace c b new hne hc, hc, isInsertion, reduceCtorEq,
      Bool.false_eq_true]

theorem orientation_eq_substitution_iff (trace : Trace α) (c : EditColumn trace) :
    orientation trace c = .substitution ↔ isSubstitution (column trace c) = true := by
  rcases column_cases trace c with ⟨b, hc⟩ | ⟨b, hc⟩ | ⟨b, new, hne, hc⟩
  · simp only [orientation_of_deletion trace c b hc, hc, isSubstitution, reduceCtorEq,
      Bool.false_eq_true]
  · simp only [orientation_of_insertion trace c b hc, hc, isSubstitution, reduceCtorEq,
      Bool.false_eq_true]
  · simp only [orientation_of_substitution trace c b new hne hc, hc, isSubstitution]

/-- Counting predicate-selected finite indices is the actual list count. -/
theorem card_column_predicate (trace : Trace α) (p : Column α → Bool) :
    Fintype.card {i : Fin trace.length // p (trace.get i) = true} = trace.countP p := by
  classical
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  induction trace with
  | nil => simp
  | cons col rest ih =>
    simp only [List.length_cons, Fin.sum_univ_succ, List.get_cons_zero,
      List.get_cons_succ', List.countP_cons, ih]
    by_cases hp : p col = true <;> simp_all [Nat.add_comm]

theorem countP_isDeletion (trace : Trace α) : trace.countP isDeletion = trace.deletions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;> simp [isDeletion, List.countP_cons, Trace.deletions, ih]

theorem countP_isInsertion (trace : Trace α) : trace.countP isInsertion = trace.insertions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;> simp [isInsertion, List.countP_cons, Trace.insertions, ih]

theorem countP_isSubstitution (trace : Trace α) :
    trace.countP isSubstitution = trace.substitutions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;> simp [isSubstitution, List.countP_cons, Trace.substitutions, ih]

theorem countP_isEdit (trace : Trace α) :
    trace.countP Column.isEdit = trace.deletions + trace.insertions + trace.substitutions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;>
      simp only [List.countP_cons, Column.isEdit, Bool.false_eq_true,
        ite_true, ite_false, Trace.deletions, Trace.insertions, Trace.substitutions, ih] <;> omega

theorem card_editColumn (trace : Trace α) :
    Fintype.card (EditColumn trace) =
      trace.deletions + trace.insertions + trace.substitutions :=
  (card_column_predicate trace Column.isEdit).trans (countP_isEdit trace)

def deletionColumnEquiv (trace : Trace α) :
    {c : EditColumn trace // orientation trace c = .deletion} ≃
      {i : Fin trace.length // isDeletion (trace.get i) = true} where
  toFun c := ⟨c.val.val, (orientation_eq_deletion_iff trace c.val).mp c.property⟩
  invFun i := ⟨⟨i.val, isDeletion_edit (trace.get i.val) i.property⟩,
    (orientation_eq_deletion_iff trace _).mpr i.property⟩
  left_inv c := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

def insertionColumnEquiv (trace : Trace α) :
    {c : EditColumn trace // orientation trace c = .insertion} ≃
      {i : Fin trace.length // isInsertion (trace.get i) = true} where
  toFun c := ⟨c.val.val, (orientation_eq_insertion_iff trace c.val).mp c.property⟩
  invFun i := ⟨⟨i.val, isInsertion_edit (trace.get i.val) i.property⟩,
    (orientation_eq_insertion_iff trace _).mpr i.property⟩
  left_inv c := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

theorem card_deletionColumns (trace : Trace α) :
    Fintype.card {c : EditColumn trace // orientation trace c = .deletion} = trace.deletions :=
  (Fintype.card_congr (deletionColumnEquiv trace)).trans
    ((card_column_predicate trace isDeletion).trans (countP_isDeletion trace))

theorem card_insertionColumns (trace : Trace α) :
    Fintype.card {c : EditColumn trace // orientation trace c = .insertion} = trace.insertions :=
  (Fintype.card_congr (insertionColumnEquiv trace)).trans
    ((card_column_predicate trace isInsertion).trans (countP_isInsertion trace))

def substitutionColumnEquiv (trace : Trace α) :
    {c : EditColumn trace // orientation trace c = .substitution} ≃
      {i : Fin trace.length // isSubstitution (trace.get i) = true} where
  toFun c := ⟨c.val.val, (orientation_eq_substitution_iff trace c.val).mp c.property⟩
  invFun i := ⟨⟨i.val, isSubstitution_edit (trace.get i.val) i.property⟩,
    (orientation_eq_substitution_iff trace _).mpr i.property⟩
  left_inv c := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

theorem card_substitutionColumns (trace : Trace α) :
    Fintype.card {c : EditColumn trace // orientation trace c = .substitution} =
      trace.substitutions :=
  (Fintype.card_congr (substitutionColumnEquiv trace)).trans
    ((card_column_predicate trace isSubstitution).trans (countP_isSubstitution trace))

/-- The balanced finite enumeration is obtained from the proved exact count:
equally many deletions and insertions, and 2t edit columns in all. -/
noncomputable def editEquiv (trace : Trace α) (t : ℕ)
    (hbal : trace.deletions = trace.insertions)
    (hsum : 2 * trace.deletions + trace.substitutions = 2 * t) :
    Fin (2 * t) ≃ EditColumn trace :=
  (Fintype.equivFinOfCardEq (show Fintype.card (EditColumn trace) = 2 * t by
    rw [card_editColumn]
    omega)).symm

def sourcePrefix (trace : Trace α) (c : EditColumn trace) : List α :=
  Trace.source (trace.take c.val.val)

def sourceSuffix (trace : Trace α) (c : EditColumn trace) : List α :=
  Trace.source (trace.drop (c.val.val + 1))

def targetPrefix (trace : Trace α) (c : EditColumn trace) : List α :=
  Trace.target (trace.take c.val.val)

def targetSuffix (trace : Trace α) (c : EditColumn trace) : List α :=
  Trace.target (trace.drop (c.val.val + 1))

theorem position_eq_sourcePrefix_length (trace : Trace α) (c : EditColumn trace) :
    position trace c = (sourcePrefix trace c).length := rfl

/-- The selected trace column is recovered from the exact prefix/suffix split. -/
theorem split_column (trace : Trace α) (c : EditColumn trace) :
    trace = trace.take c.val.val ++ column trace c :: trace.drop (c.val.val + 1) := by
  have hd : trace.drop c.val.val = column trace c :: trace.drop (c.val.val + 1) :=
    List.drop_eq_getElem_cons c.val.isLt
  calc
    trace = trace.take c.val.val ++ trace.drop c.val.val :=
      (List.take_append_drop c.val.val trace).symm
    _ = _ := by rw [hd]

theorem source_split (trace : Trace α) (c : EditColumn trace) :
    trace.source = sourcePrefix trace c ++
      Trace.source [column trace c] ++ sourceSuffix trace c := by
  calc
    trace.source = Trace.source
        (trace.take c.val.val ++ column trace c :: trace.drop (c.val.val + 1)) :=
      congrArg Trace.source (split_column trace c)
    _ = _ := by
      rw [Trace.source_append]
      cases hc : column trace c <;> simp [sourcePrefix, sourceSuffix, Trace.source]

theorem target_split (trace : Trace α) (c : EditColumn trace) :
    trace.target = targetPrefix trace c ++
      Trace.target [column trace c] ++ targetSuffix trace c := by
  calc
    trace.target = Trace.target
        (trace.take c.val.val ++ column trace c :: trace.drop (c.val.val + 1)) :=
      congrArg Trace.target (split_column trace c)
    _ = _ := by
      rw [Trace.target_append]
      cases hc : column trace c <;> simp [targetPrefix, targetSuffix, Trace.target]

theorem source_split_of_deletion (trace : Trace α) (c : EditColumn trace) (b : α)
    (hc : column trace c = .deletion b) :
    trace.source = sourcePrefix trace c ++ b :: sourceSuffix trace c := by
  simpa only [hc, Trace.source, List.append_assoc, List.singleton_append] using source_split trace c

theorem source_split_of_insertion (trace : Trace α) (c : EditColumn trace) (b : α)
    (hc : column trace c = .insertion b) :
    trace.source = sourcePrefix trace c ++ sourceSuffix trace c := by
  simpa only [hc, Trace.source, List.append_nil] using source_split trace c

theorem target_split_of_deletion (trace : Trace α) (c : EditColumn trace) (b : α)
    (hc : column trace c = .deletion b) :
    trace.target = targetPrefix trace c ++ targetSuffix trace c := by
  simpa only [hc, Trace.target, List.append_nil] using target_split trace c

theorem target_split_of_insertion (trace : Trace α) (c : EditColumn trace) (b : α)
    (hc : column trace c = .insertion b) :
    trace.target = targetPrefix trace c ++ b :: targetSuffix trace c := by
  simpa only [hc, Trace.target, List.append_assoc, List.singleton_append] using target_split trace c

theorem source_split_of_substitution (trace : Trace α) (c : EditColumn trace) (b : α) (new : α) (hne : b ≠ new)
    (hc : column trace c = .substitution b new hne) :
    trace.source = sourcePrefix trace c ++ b :: sourceSuffix trace c := by
  simpa only [hc, Trace.source, List.append_assoc, List.singleton_append] using source_split trace c

theorem target_split_of_substitution (trace : Trace α) (c : EditColumn trace) (b : α) (new : α) (hne : b ≠ new)
    (hc : column trace c = .substitution b new hne) :
    trace.target = targetPrefix trace c ++ new :: targetSuffix trace c := by
  simpa only [hc, Trace.target, List.append_assoc, List.singleton_append] using target_split trace c

theorem oneEditTarget_deletion_split (trace : Trace α) (c : EditColumn trace) (b : α)
    (hc : column trace c = .deletion b) :
    oneEditTarget trace c = sourcePrefix trace c ++ sourceSuffix trace c := by
  rw [oneEditTarget_of_deletion trace c b hc, position_eq_sourcePrefix_length,
    source_split_of_deletion trace c b hc]
  rw [List.eraseIdx_append_of_length_le (Nat.le_refl _)]
  simp

theorem oneEditTarget_insertion_split (trace : Trace α) (c : EditColumn trace) (b : α)
    (hc : column trace c = .insertion b) :
    oneEditTarget trace c = sourcePrefix trace c ++ b :: sourceSuffix trace c := by
  rw [oneEditTarget_of_insertion trace c b hc, position_eq_sourcePrefix_length,
    source_split_of_insertion trace c b hc]
  simp

theorem oneEditTarget_substitution_split (trace : Trace α) (c : EditColumn trace) (b : α) (new : α) (hne : b ≠ new)
    (hc : column trace c = .substitution b new hne) :
    oneEditTarget trace c = sourcePrefix trace c ++ new :: sourceSuffix trace c := by
  rw [oneEditTarget_of_substitution trace c b new hne hc, position_eq_sourcePrefix_length,
    source_split_of_substitution trace c b new hne hc]
  simp

theorem deletion_position_lt (trace : Trace α) (c : EditColumn trace) (b : α)
    (hc : column trace c = .deletion b) : position trace c < trace.source.length := by
  have h := congrArg List.length (source_split_of_deletion trace c b hc)
  simp only [List.length_append, List.length_cons] at h
  rw [position_eq_sourcePrefix_length]
  omega

theorem substitution_position_lt (trace : Trace α) (c : EditColumn trace) (b : α) (new : α) (hne : b ≠ new)
    (hc : column trace c = .substitution b new hne) : position trace c < trace.source.length := by
  have h := congrArg List.length (source_split_of_substitution trace c b new hne hc)
  simp only [List.length_append, List.length_cons] at h
  rw [position_eq_sourcePrefix_length]
  omega

theorem insertion_position_le (trace : Trace α) (c : EditColumn trace) (b : α)
    (hc : column trace c = .insertion b) : position trace c ≤ trace.source.length := by
  have h := congrArg List.length (source_split_of_insertion trace c b hc)
  simp only [List.length_append] at h
  rw [position_eq_sourcePrefix_length]
  omega

#print axioms card_column_predicate
#print axioms card_editColumn
#print axioms card_deletionColumns
#print axioms card_insertionColumns
#print axioms card_substitutionColumns
#print axioms editEquiv
#print axioms split_column
#print axioms oneEditTarget_deletion_split
#print axioms oneEditTarget_insertion_split
#print axioms oneEditTarget_substitution_split

end DeletionCode.Qary.TraceEditData
