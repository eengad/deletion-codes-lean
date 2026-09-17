import DeletionCode.MaximalRuns

/-!
An interior edit determines the manuscript's local bubble word grammar.
The maximal run is extracted from the actual word, its length is bounded
by source uniqueness, and the two flanks are trimmed to length L-rho.
This module proves the word and boundary-bit conditions; the catalogue's
simple-path and intersection conditions are separate geometric obligations.
-/

namespace DeletionCode.RunBubbleConstruction

open Windows HeaderRecovery CatalogueWords MaximalRuns

/-- Trimming the words on both sides of a displayed run leaves an actual
grammar bubble and records exactly which exterior words were removed. -/
structure TrimmedRun (k : ℕ) (pre suffix : List Bool) (rho : ℕ)
    (bit : Bool) (orientation : Orientation) where
  bubble : BubbleWord k
  before : List Bool
  after : List Bool
  rho_eq : bubble.rho = rho
  bit_eq : bubble.bit = bit
  orientation_eq : bubble.orientation = orientation
  pre_eq : pre = before ++ bubble.left
  suffix_eq : suffix = bubble.right ++ after
  left_boundary : bubble.left.getLast? = some (!bubble.bit)
  right_boundary : bubble.right.head? = some (!bubble.bit)

/-- The flanks are explicitly the last L-rho letters before the run and
the first L-rho letters after it. Their existing boundary bits survive. -/
def trimRun (k : ℕ) (pre suffix : List Bool) (rho : ℕ)
    (bit : Bool) (orientation : Orientation)
    (hrho : 1 ≤ rho) (hrho' : rho ≤ k + 1)
    (hpre : windowLength k - rho ≤ pre.length)
    (hsuffix : windowLength k - rho ≤ suffix.length)
    (hleft : pre.getLast? = some (!bit))
    (hright : suffix.head? = some (!bit)) :
    TrimmedRun k pre suffix rho bit orientation := by
  have hflank : 0 < windowLength k - rho := by
    unfold windowLength
    omega
  refine {
    bubble := {
      left := pre.drop (pre.length - (windowLength k - rho))
      right := suffix.take (windowLength k - rho)
      rho := rho
      bit := bit
      orientation := orientation
      rho_lower := hrho
      rho_upper := hrho'
      left_length := by simp only [List.length_drop]; omega
      right_length := by
        simp only [List.length_take, Nat.min_eq_left hsuffix]
    }
    before := pre.take (pre.length - (windowLength k - rho))
    after := suffix.drop (windowLength k - rho)
    rho_eq := rfl
    bit_eq := rfl
    orientation_eq := rfl
    pre_eq := (List.take_append_drop _ pre).symm
    suffix_eq := (List.take_append_drop _ suffix).symm
    left_boundary := ?_
    right_boundary := ?_
  }
  · change (pre.drop (pre.length - (windowLength k - rho))).getLast? = some (!bit)
    rw [List.getLast?_drop, ite_eq_right (by omega)]
    exact hleft
  · change (suffix.take (windowLength k - rho)).head? = some (!bit)
    rw [List.head?_take, ite_eq_right (by omega)]
    exact hright

namespace TrimmedRun

variable {k rho : ℕ} {pre suffix : List Bool} {bit : Bool} {orientation : Orientation}

theorem long_eq (r : TrimmedRun k pre suffix rho bit orientation) :
    pre ++ List.replicate rho bit ++ suffix =
      r.before ++ r.bubble.longWord ++ r.after := by
  calc
    _ = (r.before ++ r.bubble.left) ++ List.replicate rho bit ++
        (r.bubble.right ++ r.after) :=
      congrArg₂ (fun (p s : List Bool) => p ++ List.replicate rho bit ++ s)
        r.pre_eq r.suffix_eq
    _ = _ := by
      simp only [BubbleWord.longWord, r.rho_eq, r.bit_eq, List.append_assoc]

theorem short_eq (r : TrimmedRun k pre suffix rho bit orientation) :
    pre ++ List.replicate (rho - 1) bit ++ suffix =
      r.before ++ r.bubble.shortWord ++ r.after := by
  calc
    _ = (r.before ++ r.bubble.left) ++ List.replicate (rho - 1) bit ++
        (r.bubble.right ++ r.after) :=
      congrArg₂ (fun (p s : List Bool) => p ++ List.replicate (rho - 1) bit ++ s)
        r.pre_eq r.suffix_eq
    _ = _ := by
      simp only [BubbleWord.shortWord, r.rho_eq, r.bit_eq, List.append_assoc]

theorem before_length (r : TrimmedRun k pre suffix rho bit orientation) :
    r.before.length + (windowLength k - rho) = pre.length := by
  have h := congrArg List.length r.pre_eq
  simpa only [List.length_append, r.bubble.left_length, r.rho_eq] using h.symm

end TrimmedRun

/-- A single local replacement, with exact exterior words and source and
target paths. The edit position belongs to the displayed longer run. -/
structure LocalBubble (k : ℕ) (source target : List Bool) (pos : ℕ)
    (orientation : Orientation) where
  bubble : BubbleWord k
  before : List Bool
  after : List Bool
  orientation_eq : bubble.orientation = orientation
  source_eq : source = before ++ bubble.negativeWord ++ after
  target_eq : target = before ++ bubble.positiveWord ++ after
  left_boundary : bubble.left.getLast? = some (!bubble.bit)
  right_boundary : bubble.right.head? = some (!bubble.bit)
  edit_start : before.length + bubble.left.length ≤ pos
  edit_stop : pos < before.length + windowLength k

namespace LocalBubble

variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem start_le (p : LocalBubble k source target pos orientation) :
    p.before.length ≤ pos := by
  have h := p.edit_start
  omega

/-- The entire longer local word ends at most L positions after the edit. -/
theorem long_end_le (p : LocalBubble k source target pos orientation) :
    p.before.length + p.bubble.longWord.length ≤ pos + windowLength k := by
  have h := p.edit_start
  have hrho := p.bubble.rho_upper
  rw [p.bubble.left_length] at h
  rw [p.bubble.longWord_length]
  simp only [longLength, BubbleWord.header]
  unfold windowLength at *
  omega

theorem long_interval_bounds (p : LocalBubble k source target pos orientation) :
    pos + 1 - windowLength k ≤ p.before.length ∧
      p.before.length + p.bubble.longWord.length ≤ pos + windowLength k := by
  constructor
  · have h := p.edit_stop
    omega
  · exact p.long_end_le

end LocalBubble

private theorem interior_flanks (k rho pos : ℕ) (pre suffix : List Bool)
    (hrho : rho ≤ k + 1) (hstart : pre.length ≤ pos)
    (hstop : pos < pre.length + rho)
    (hleft : 4 * windowLength k ≤ pos)
    (hright : pos + 4 * windowLength k ≤ pre.length + rho + suffix.length) :
    windowLength k - rho ≤ pre.length ∧
      windowLength k - rho ≤ suffix.length ∧ 0 < pre.length ∧ 0 < suffix.length := by
  unfold windowLength at *
  omega

/-- Every sufficiently interior deletion in a k-unique finite source has
the catalogue word grammar, including the opposite boundary bits. The
deleted position may be anywhere in its extracted maximal run. -/
theorem exists_deletion_bubble (word : List Bool) (pos k : ℕ)
    (hx : KUnique (listLetters word) word.length k)
    (hleft : 4 * windowLength k ≤ pos)
    (hright : pos + 4 * windowLength k ≤ word.length) :
    Nonempty (LocalBubble k word (word.eraseIdx pos) pos .deletion) := by
  have hpos : pos < word.length := by
    unfold windowLength at hright
    omega
  obtain ⟨pre, suffix, rho, bit, hrho, hrho', hword, hstart, hstop, hpre, hsuffix⟩ :=
    exists_maximal_run_unique word pos k hpos hx
  have hlength := congrArg List.length hword
  simp only [List.length_append, List.length_replicate] at hlength
  have hmargins := interior_flanks k rho pos pre suffix (by omega) hstart hstop
    hleft (by omega)
  have hpreBit : pre.getLast? = some (!bit) := by
    rcases hpre with hempty | hbit
    · subst pre
      simp at hmargins
    · exact hbit
  have hsuffixBit : suffix.head? = some (!bit) := by
    rcases hsuffix with hempty | hbit
    · subst suffix
      simp at hmargins
    · exact hbit
  let r := trimRun k pre suffix rho bit .deletion (by omega) (by omega)
    hmargins.1 hmargins.2.1 hpreBit hsuffixBit
  have hshort : word.eraseIdx pos = pre ++ List.replicate (rho - 1) bit ++ suffix := by
    rw [hword]
    exact eraseIdx_in_run pre suffix rho bit pos hstart hstop
  have hbefore := r.before_length
  have hrhoL : rho ≤ windowLength k := by unfold windowLength; omega
  refine ⟨{
    bubble := r.bubble
    before := r.before
    after := r.after
    orientation_eq := r.orientation_eq
    source_eq := ?_
    target_eq := ?_
    left_boundary := r.left_boundary
    right_boundary := r.right_boundary
    edit_start := ?_
    edit_stop := ?_
  }⟩
  · simpa only [BubbleWord.negativeWord, r.orientation_eq] using hword.trans r.long_eq
  · simpa only [BubbleWord.positiveWord, r.orientation_eq] using hshort.trans r.short_eq
  · rw [r.bubble.left_length, r.rho_eq]
    omega
  · omega

/-- An interior insertion has the same grammar, with the source and
target paths reversed. The run bit is the actual inserted bit. -/
theorem exists_insertion_bubble (word : List Bool) (pos k : ℕ) (bit : Bool)
    (hx : KUnique (listLetters word) word.length k)
    (hleft : 4 * windowLength k ≤ pos)
    (hright : pos + 4 * windowLength k ≤ word.length) :
    ∃ p : LocalBubble k word (word.take pos ++ bit :: word.drop pos) pos .insertion,
      p.bubble.bit = bit := by
  have hpos : pos ≤ word.length := by omega
  obtain ⟨pre, suffix, rho, hrho, hrho', hlong, hshort, hstart, hstop, hpre, hsuffix⟩ :=
    exists_insertion_run_at_gap_unique word pos bit k hpos hx
  have hlength := congrArg List.length hshort
  simp only [List.length_append, List.length_replicate] at hlength
  have hmargins := interior_flanks k rho pos pre suffix hrho' hstart hstop
    hleft (by omega)
  have hpreBit : pre.getLast? = some (!bit) := by
    rcases hpre with hempty | hbit
    · subst pre
      simp at hmargins
    · exact hbit
  have hsuffixBit : suffix.head? = some (!bit) := by
    rcases hsuffix with hempty | hbit
    · subst suffix
      simp at hmargins
    · exact hbit
  let r := trimRun k pre suffix rho bit .insertion (by omega) hrho'
    hmargins.1 hmargins.2.1 hpreBit hsuffixBit
  have hbefore := r.before_length
  have hrhoL : rho ≤ windowLength k := by unfold windowLength; omega
  refine ⟨{
    bubble := r.bubble
    before := r.before
    after := r.after
    orientation_eq := r.orientation_eq
    source_eq := ?_
    target_eq := ?_
    left_boundary := r.left_boundary
    right_boundary := r.right_boundary
    edit_start := ?_
    edit_stop := ?_
  }, r.bit_eq⟩
  · simpa only [BubbleWord.negativeWord, r.orientation_eq] using hshort.trans r.short_eq
  · simpa only [BubbleWord.positiveWord, r.orientation_eq] using hlong.trans r.long_eq
  · rw [r.bubble.left_length, r.rho_eq]
    omega
  · omega

#print axioms trimRun
#print axioms exists_deletion_bubble
#print axioms exists_insertion_bubble

end DeletionCode.RunBubbleConstruction
