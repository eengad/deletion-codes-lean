import DeletionCode.Explicit.Borrowed.BubbleWords
import DeletionCode.Explicit.Borrowed.Endpoints
import DeletionCode.Qary.SpectrumLocalization

/-!
Actual finite local words obtained by trimming the common prefix and suffix.
The source and target have exactly the same exterior context. Their central
blocks are the original removed block and its recorded replacement.
-/
namespace DeletionCode.Explicit.Borrowed

open DeletionCode.Burst
open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords
open DeletionCode.Qary.SpectrumLocalization

variable {α : Type*}

structure LocalContext (α : Type*) (K b L : ℕ) (source target : Word α) (pos : ℕ) where
  bubble : BubbleWord α K b L
  before : Word α
  after : Word α
  source_eq : source = before ++ bubble.negativeWord ++ after
  target_eq : target = before ++ bubble.positiveWord ++ after
  edit_pos : before.length + bubble.left.length = pos

namespace LocalContext

variable {K b L pos : ℕ} {source target : Word α}

theorem source_length (c : LocalContext α K b L source target pos) :
    source.length = c.before.length + c.bubble.negativeWord.length + c.after.length := by
  simpa only [List.length_append] using congrArg List.length c.source_eq

theorem target_length (c : LocalContext α K b L source target pos) :
    target.length = c.before.length + c.bubble.positiveWord.length + c.after.length := by
  simpa only [List.length_append] using congrArg List.length c.target_eq

theorem negative_occurrence [Inhabited α] (c : LocalContext α K b L source target pos) :
    Agree (listLetters c.bubble.negativeWord) 0 (listLetters source)
      c.before.length c.bubble.negativeWord.length := by
  intro i hi
  simp only [c.source_eq, List.append_assoc, listLetters_middle _ _ _ i hi, Nat.zero_add]

theorem positive_occurrence [Inhabited α] (c : LocalContext α K b L source target pos) :
    Agree (listLetters c.bubble.positiveWord) 0 (listLetters target)
      c.before.length c.bubble.positiveWord.length := by
  intro i hi
  simp only [c.target_eq, List.append_assoc, listLetters_middle _ _ _ i hi, Nat.zero_add]

theorem source_interval_bounds (c : LocalContext α K b L source target pos) :
    pos - (L - 1) ≤ c.before.length ∧
      c.before.length + c.bubble.negativeWord.length ≤
        pos + c.bubble.removed.length + (L - 1) := by
  have he := c.edit_pos
  have hl := c.bubble.left_upper
  have hr := c.bubble.right_upper
  simp only [BubbleWord.negativeWord, List.length_append]
  omega

end LocalContext

variable [Inhabited α]

theorem exists_localContext {K b L : ℕ} (hwindow : 3 * (K + b + 1) ≤ L)
    (e : Edit α) (x : Word α)
    (he : e.Valid b x)
    (p : PrefixBoundary (k := K) (b := b) e x)
    (q : SuffixBoundary (k := K) (b := b) e x)
    (hleft : 2 * (L + b) ≤ e.pos)
    (hright : e.pos + e.removed + 2 * (L + b) ≤ x.length) :
    ∃ c : LocalContext α K b L x (e.apply x) e.pos,
      c.before.length + (L - 1) = p.index ∧
      c.after.length + (L - 1) = q.suffix ∧
      c.bubble.removed = e.sourceBlock x ∧ c.bubble.replacement = e.replacement := by
  let m := L - 1
  let a := p.index - m
  let d := x.length - e.pos - e.removed
  let z := m - (q.suffix - d)
  let pre := x.take e.pos
  let suffix := x.drop (e.pos + e.removed)
  have hm : 3 * K + 3 * b + 2 ≤ m := by dsimp [m]; omega
  have hv := he.2.1
  unfold Edit.InBounds at hv
  have hpre : pre.length = e.pos := List.length_take_of_le (by omega)
  have hsuf : suffix.length = d := by dsimp [suffix, d]; simp only [List.length_drop]; omega
  have hU : (e.sourceBlock x).length = e.removed := e.sourceBlock_length x he.2.1
  have hp0 := p.before
  have hp1 := p.upper
  have hq0 := q.before
  have hq1 := q.upper
  have ha : a ≤ pre.length := by dsimp [a]; omega
  have ham : a + m = p.index := by dsimp [a]; omega
  have hz : z ≤ suffix.length := by dsimp [z, d] at *; omega
  have hafter : suffix.length - z + m = q.suffix := by dsimp [z, d] at *; omega
  let bubble : BubbleWord α K b L := {
    left := pre.drop a
    right := suffix.take z
    removed := e.sourceBlock x
    replacement := e.replacement
    removed_bound := by rw [hU]; exact he.1.1
    replacement_bound := he.1.2
    different := he.2.2
    left_lower := by simp only [List.length_drop, hpre]; dsimp [a, m] at *; omega
    left_upper := by simp only [List.length_drop, hpre]; dsimp [a, m] at *; omega
    right_lower := by rw [List.length_take_of_le hz]; dsimp [z, d, m] at *; omega
    right_upper := by rw [List.length_take_of_le hz]; dsimp [z, m]; omega
  }
  let c : LocalContext α K b L x (e.apply x) e.pos := {
    bubble := bubble
    before := pre.take a
    after := suffix.drop z
    source_eq := by
      change x = pre.take a ++ ((pre.drop a ++ e.sourceBlock x) ++ suffix.take z) ++ suffix.drop z
      calc
        x = pre ++ e.sourceBlock x ++ suffix := (e.decomposition x).symm
        _ = _ := by
          simp only [List.append_assoc, List.take_append_drop]
          rw [← List.append_assoc (pre.take a) (pre.drop a), List.take_append_drop]
    target_eq := by
      change e.apply x = pre.take a ++ ((pre.drop a ++ e.replacement) ++ suffix.take z) ++ suffix.drop z
      change pre ++ e.replacement ++ suffix = _
      simp only [List.append_assoc, List.take_append_drop]
      rw [← List.append_assoc (pre.take a) (pre.drop a), List.take_append_drop]
    edit_pos := by
      change (pre.take a).length + (pre.drop a).length = e.pos
      rw [List.length_take_of_le ha, List.length_drop, hpre]
      omega
  }
  refine ⟨c, ?_, ?_, rfl, rfl⟩
  · change (pre.take a).length + m = p.index
    rw [List.length_take_of_le ha]
    exact ham
  · change (suffix.drop z).length + m = q.suffix
    simpa only [List.length_drop] using hafter

#print axioms exists_localContext

end DeletionCode.Explicit.Borrowed
