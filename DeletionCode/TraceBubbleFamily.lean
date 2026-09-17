import DeletionCode.TraceEditData
import DeletionCode.RunBubbleConstruction
import DeletionCode.TraceSeparation

/-!
Every actual edit column of a separated trace is assigned a local bubble for
that one edit on the original source. The target and orientation occur in
the type, so the family cannot substitute an unrelated local replacement.
The finite balanced enumeration is inherited from the proved column counts.
-/
namespace DeletionCode.TraceBubbleFamily

open Windows HeaderRecovery CatalogueWords AlignmentTrace FiniteConflictGraph
open RunBubbleConstruction TraceEditData

def BubbleAt (trace : Trace) (k : ℕ) (c : EditColumn trace) :=
  LocalBubble k trace.source (oneEditTarget trace c) (position trace c) (orientation trace c)

/-- Matched-column margins place every actual edit sufficiently far inside
the original source for the constructive run and flank extraction. -/
theorem position_margins (trace : Trace) (k : ℕ)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    4 * windowLength k ≤ position trace c ∧
      position trace c + 4 * windowLength k ≤ trace.source.length :=
  TraceSeparation.sourcePosition_margins hsep c.val c.property

/-- The local bubble is constructed for the actual edit at its actual
source position. No catalogue word or substring presentation is supplied. -/
theorem exists_bubbleAt (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    Nonempty (BubbleAt trace k c) := by
  have hm := position_margins trace k hsep c
  rcases column_cases trace c with ⟨b, hc⟩ | ⟨b, hc⟩
  · unfold BubbleAt
    rw [orientation_of_deletion trace c b hc, oneEditTarget_of_deletion trace c b hc]
    exact exists_deletion_bubble trace.source (position trace c) k hx hm.1 hm.2
  · unfold BubbleAt
    rw [orientation_of_insertion trace c b hc, oneEditTarget_of_insertion trace c b hc]
    obtain ⟨p, _⟩ := exists_insertion_bubble trace.source (position trace c) k b hx hm.1 hm.2
    exact ⟨p⟩

noncomputable def bubbleAt (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    BubbleAt trace k c := Classical.choice (exists_bubbleAt trace k hx hsep c)

theorem bubbleAt_orientation (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    (bubbleAt trace k hx hsep c).bubble.orientation = orientation trace c :=
  (bubbleAt trace k hx hsep c).orientation_eq

theorem bubbleAt_source (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    trace.source = (bubbleAt trace k hx hsep c).before ++
      (bubbleAt trace k hx hsep c).bubble.negativeWord ++ (bubbleAt trace k hx hsep c).after :=
  (bubbleAt trace k hx hsep c).source_eq

theorem bubbleAt_target (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    oneEditTarget trace c = (bubbleAt trace k hx hsep c).before ++
      (bubbleAt trace k hx hsep c).bubble.positiveWord ++ (bubbleAt trace k hx hsep c).after :=
  (bubbleAt trace k hx hsep c).target_eq

/-- Grammar words indexed by the actual trace edit columns. -/
noncomputable def bubbleWords (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) : EditColumn trace → BubbleWord k :=
  fun c => (bubbleAt trace k hx hsep c).bubble

/-- The same constructed bubbles in the derived balanced Fin (2*t) indexing. -/
noncomputable def indexedBubbleWords (trace : Trace) (k t : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace)
    (hdel : trace.deletions = t) (hins : trace.insertions = t) : Fin (2 * t) → BubbleWord k :=
  fun i => bubbleWords trace k hx hsep (editEquiv trace t hdel hins i)

theorem indexedBubbleWords_orientation (trace : Trace) (k t : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace)
    (hdel : trace.deletions = t) (hins : trace.insertions = t) (i : Fin (2 * t)) :
    (indexedBubbleWords trace k t hx hsep hdel hins i).orientation =
      orientation trace (editEquiv trace t hdel hins i) :=
  bubbleAt_orientation trace k hx hsep (editEquiv trace t hdel hins i)

#print axioms position_margins
#print axioms exists_bubbleAt
#print axioms bubbleAt
#print axioms bubbleAt_source
#print axioms bubbleAt_target
#print axioms indexedBubbleWords_orientation

end DeletionCode.TraceBubbleFamily
