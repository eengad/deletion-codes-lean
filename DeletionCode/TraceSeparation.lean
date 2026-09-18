import DeletionCode.FiniteConflictGraph

/-!
Matched-column separation implies separation in both actual word coordinate
systems. Prefix deletion/insertion counts are proved monotone from trace
concatenation. Thus the source neighborhoods used in the coverage proof are
in bounds and disjoint; the same facts hold for the target neighborhoods.
No uniqueness or prescribed number of edits is needed for these conclusions.
-/
namespace DeletionCode.TraceSeparation

open AlignmentTrace FiniteConflictGraph

/-- An additive natural-valued trace counter never decreases on taking a prefix. -/
theorem counter_take_le (counter : Trace → ℕ)
    (happend : ∀ a b, counter (a ++ b) = counter a + counter b)
    (trace : Trace) (i : ℕ) : counter (trace.take i) ≤ counter trace := by
  have h := happend (trace.take i) (trace.drop i)
  rw [List.take_append_drop] at h
  omega

/-- Prefix counter monotonicity is derived from the actual list decomposition. -/
theorem counter_take_mono (counter : Trace → ℕ)
    (happend : ∀ a b, counter (a ++ b) = counter a + counter b)
    (trace : Trace) {i j : ℕ} (hij : i ≤ j) :
    counter (trace.take i) ≤ counter (trace.take j) := by
  have h := counter_take_le counter happend (trace.take j) i
  simpa only [List.take_take, Nat.min_eq_left hij, Nat.min_eq_right hij] using h

theorem deletions_take_mono (trace : Trace) {i j : ℕ} (hij : i ≤ j) :
    Trace.deletions (trace.take i) ≤ Trace.deletions (trace.take j) :=
  counter_take_mono Trace.deletions Trace.deletions_append trace hij

theorem insertions_take_mono (trace : Trace) {i j : ℕ} (hij : i ≤ j) :
    Trace.insertions (trace.take i) ≤ Trace.insertions (trace.take j) :=
  counter_take_mono Trace.insertions Trace.insertions_append trace hij

theorem substitutions_take_mono (trace : Trace) {i j : ℕ} (hij : i ≤ j) :
    Trace.substitutions (trace.take i) ≤ Trace.substitutions (trace.take j) :=
  counter_take_mono Trace.substitutions Trace.substitutions_append trace hij

theorem matchedAnchor_mono (trace : Trace) {i j : ℕ} (hij : i ≤ j) :
    trace.matchedAnchor i ≤ trace.matchedAnchor j :=
  counter_take_mono Trace.matchedCount Trace.matchedCount_append trace hij

/-- An anchor gap remains at least as large in source coordinates. -/
theorem sourcePosition_gap (trace : Trace) {i j B : ℕ} (hij : i ≤ j)
    (hgap : trace.matchedAnchor i + B ≤ trace.matchedAnchor j) :
    trace.sourcePosition i + B ≤ trace.sourcePosition j := by
  have hc := deletions_take_mono trace hij
  have hs := substitutions_take_mono trace hij
  have hi := trace.sourcePosition_eq i
  have hj := trace.sourcePosition_eq j
  omega

/-- An anchor gap remains at least as large in target coordinates. -/
theorem targetPosition_gap (trace : Trace) {i j B : ℕ} (hij : i ≤ j)
    (hgap : trace.matchedAnchor i + B ≤ trace.matchedAnchor j) :
    trace.targetPosition i + B ≤ trace.targetPosition j := by
  have hc := insertions_take_mono trace hij
  have hs := substitutions_take_mono trace hij
  have hi := trace.targetPosition_eq i
  have hj := trace.targetPosition_eq j
  omega

theorem sourcePosition_mono (trace : Trace) {i j : ℕ} (hij : i ≤ j) :
    trace.sourcePosition i ≤ trace.sourcePosition j := by
  have h := sourcePosition_gap trace (B := 0) hij (by
    simpa only [Nat.add_zero] using matchedAnchor_mono trace hij)
  simpa only [Nat.add_zero] using h

theorem targetPosition_mono (trace : Trace) {i j : ℕ} (hij : i ≤ j) :
    trace.targetPosition i ≤ trace.targetPosition j := by
  have h := targetPosition_gap trace (B := 0) hij (by
    simpa only [Nat.add_zero] using matchedAnchor_mono trace hij)
  simpa only [Nat.add_zero] using h

/-- Every separated edit has the stated margin at both source boundaries. -/
theorem sourcePosition_margins {trace : Trace} {B : ℕ}
    (hsep : Separated B trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    B ≤ trace.sourcePosition i.val ∧
      trace.sourcePosition i.val + B ≤ trace.source.length := by
  have hm := hsep.1 i hi
  have hc := counter_take_le Trace.deletions Trace.deletions_append trace i.val
  have hs := counter_take_le Trace.substitutions Trace.substitutions_append trace i.val
  have hp := trace.sourcePosition_eq i.val
  have hn := trace.source_length
  constructor <;> omega

/-- Every separated edit has the stated margin at both target boundaries. -/
theorem targetPosition_margins {trace : Trace} {B : ℕ}
    (hsep : Separated B trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    B ≤ trace.targetPosition i.val ∧
      trace.targetPosition i.val + B ≤ trace.target.length := by
  have hm := hsep.1 i hi
  have hc := counter_take_le Trace.insertions Trace.insertions_append trace i.val
  have hs := counter_take_le Trace.substitutions Trace.substitutions_append trace i.val
  have hp := trace.targetPosition_eq i.val
  have hn := trace.target_length
  constructor <;> omega

/-- The source positions of any ordered pair of edits retain the full gap B. -/
theorem sourcePosition_separated {trace : Trace} {B : ℕ}
    (hsep : Separated B trace) (i j : Fin trace.length)
    (hi : EditIndex trace i) (hj : EditIndex trace j) (hij : i.val < j.val) :
    trace.sourcePosition i.val + B ≤ trace.sourcePosition j.val :=
  sourcePosition_gap trace (Nat.le_of_lt hij) (hsep.2 i j hi hj hij)

/-- The target positions of any ordered pair of edits retain the full gap B. -/
theorem targetPosition_separated {trace : Trace} {B : ℕ}
    (hsep : Separated B trace) (i j : Fin trace.length)
    (hi : EditIndex trace i) (hj : EditIndex trace j) (hij : i.val < j.val) :
    trace.targetPosition i.val + B ≤ trace.targetPosition j.val :=
  targetPosition_gap trace (Nat.le_of_lt hij) (hsep.2 i j hi hj hij)

def neighborhoodLeft (L position : ℕ) : ℕ := position - (L - 1)

def neighborhoodRight (L position : ℕ) : ℕ := position + L + 1

/-- The half-open form of the paper's inclusive interval [a-L+1,a+L]. -/
def neighborhood (L position : ℕ) : Set ℕ :=
  Set.Ico (neighborhoodLeft L position) (neighborhoodRight L position)

/-- A neighborhood has length 2L and stays within the corresponding finite word. -/
theorem neighborhood_bounds {L position n : ℕ} (hL : 1 ≤ L)
    (hmargins : 4 * L ≤ position ∧ position + 4 * L ≤ n) :
    neighborhoodLeft L position + 2 * L = neighborhoodRight L position ∧
      neighborhoodRight L position ≤ n := by
  unfold neighborhoodLeft neighborhoodRight
  constructor <;> omega

theorem neighborhood_subset {L position n : ℕ} (hL : 1 ≤ L)
    (hmargins : 4 * L ≤ position ∧ position + 4 * L ≤ n) :
    neighborhood L position ⊆ Set.Ico 0 n := by
  have hbound := (neighborhood_bounds hL hmargins).2
  intro r hr
  exact ⟨Nat.zero_le r, lt_of_lt_of_le hr.2 hbound⟩

/-- A gap of 4L puts the entire earlier neighborhood before the later one. -/
theorem neighborhood_ordered {L a b : ℕ} (hL : 1 ≤ L)
    (hgap : a + 4 * L ≤ b) : neighborhoodRight L a ≤ neighborhoodLeft L b := by
  unfold neighborhoodLeft neighborhoodRight
  omega

theorem neighborhood_disjoint_of_gap {L a b : ℕ} (hL : 1 ≤ L)
    (hgap : a + 4 * L ≤ b) : Disjoint (neighborhood L a) (neighborhood L b) := by
  have horder := neighborhood_ordered hL hgap
  apply Set.disjoint_left.mpr
  intro r ha hb
  have hra := ha.2
  have hrb := hb.1
  omega

theorem source_neighborhood_bounds {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    neighborhoodLeft L (trace.sourcePosition i.val) + 2 * L =
        neighborhoodRight L (trace.sourcePosition i.val) ∧
      neighborhoodRight L (trace.sourcePosition i.val) ≤ trace.source.length :=
  neighborhood_bounds hL (sourcePosition_margins hsep i hi)

theorem target_neighborhood_bounds {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    neighborhoodLeft L (trace.targetPosition i.val) + 2 * L =
        neighborhoodRight L (trace.targetPosition i.val) ∧
      neighborhoodRight L (trace.targetPosition i.val) ≤ trace.target.length :=
  neighborhood_bounds hL (targetPosition_margins hsep i hi)

theorem source_neighborhood_subset {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    neighborhood L (trace.sourcePosition i.val) ⊆ Set.Ico 0 trace.source.length :=
  neighborhood_subset hL (sourcePosition_margins hsep i hi)

theorem target_neighborhood_subset {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    neighborhood L (trace.targetPosition i.val) ⊆ Set.Ico 0 trace.target.length :=
  neighborhood_subset hL (targetPosition_margins hsep i hi)

theorem source_neighborhood_ordered {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i j : Fin trace.length)
    (hi : EditIndex trace i) (hj : EditIndex trace j) (hij : i.val < j.val) :
    neighborhoodRight L (trace.sourcePosition i.val) ≤
      neighborhoodLeft L (trace.sourcePosition j.val) :=
  neighborhood_ordered hL (sourcePosition_separated hsep i j hi hj hij)

theorem target_neighborhood_ordered {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i j : Fin trace.length)
    (hi : EditIndex trace i) (hj : EditIndex trace j) (hij : i.val < j.val) :
    neighborhoodRight L (trace.targetPosition i.val) ≤
      neighborhoodLeft L (trace.targetPosition j.val) :=
  neighborhood_ordered hL (targetPosition_separated hsep i j hi hj hij)

/-- Distinct edit columns have disjoint actual source neighborhoods. -/
theorem source_neighborhood_disjoint {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i j : Fin trace.length)
    (hi : EditIndex trace i) (hj : EditIndex trace j) (hne : i ≠ j) :
    Disjoint (neighborhood L (trace.sourcePosition i.val))
      (neighborhood L (trace.sourcePosition j.val)) := by
  have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
  by_cases hij : i.val < j.val
  · exact neighborhood_disjoint_of_gap hL (sourcePosition_separated hsep i j hi hj hij)
  · exact (neighborhood_disjoint_of_gap hL
      (sourcePosition_separated hsep j i hj hi (by omega))).symm

/-- The corresponding target neighborhoods are disjoint as well. -/
theorem target_neighborhood_disjoint {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i j : Fin trace.length)
    (hi : EditIndex trace i) (hj : EditIndex trace j) (hne : i ≠ j) :
    Disjoint (neighborhood L (trace.targetPosition i.val))
      (neighborhood L (trace.targetPosition j.val)) := by
  have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
  by_cases hij : i.val < j.val
  · exact neighborhood_disjoint_of_gap hL (targetPosition_separated hsep i j hi hj hij)
  · exact (neighborhood_disjoint_of_gap hL
      (targetPosition_separated hsep j i hj hi (by omega))).symm

#print axioms counter_take_mono
#print axioms sourcePosition_margins
#print axioms targetPosition_margins
#print axioms sourcePosition_separated
#print axioms targetPosition_separated
#print axioms source_neighborhood_bounds
#print axioms target_neighborhood_bounds
#print axioms source_neighborhood_disjoint
#print axioms target_neighborhood_disjoint

end DeletionCode.TraceSeparation
