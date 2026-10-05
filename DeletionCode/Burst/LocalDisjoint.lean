import DeletionCode.Burst.LocalSpectrum
import Mathlib.Data.Nat.Dist

/-!
Different local bubbles in one source have disjoint vertices when their
source neighborhoods are disjoint. Both sides are realized by actual bounded
replacements in the common source. Equal windows would have a surviving
source letter in both disjoint intervals, contrary to source rigidity.
-/
namespace DeletionCode.Burst.LocalBubble

open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords
open DeletionCode.Qary.SpectrumLocalization

variable {α : Type*} [Inhabited α]
variable {k b pos : ℕ} {source target : Word α}

def pathWord (p : LocalBubble α k b source target pos) (side : Bool) : Word α :=
  if side then p.bubble.positiveWord else p.bubble.negativeWord

def canonicalEdit (p : LocalBubble α k b source target pos) (side : Bool) : Edit α :=
  if side then ⟨p.before.length + p.bubble.left.length,
    p.bubble.removed.length, p.bubble.replacement⟩ else ⟨0, 0, []⟩

theorem canonical_bounded (p : LocalBubble α k b source target pos) (side : Bool) :
    (p.canonicalEdit side).Bounded b := by
  cases side
  · simp [canonicalEdit, Edit.Bounded]
  · exact ⟨p.bubble.removed_bound, p.bubble.replacement_bound⟩

theorem canonical_inBounds (p : LocalBubble α k b source target pos) (side : Bool) :
    (p.canonicalEdit side).InBounds source.length := by
  have hn := p.toLocalContext.source_length
  cases side
  · simp [canonicalEdit, Edit.InBounds]
  · simp only [canonicalEdit, ite_true, Edit.InBounds]
    simp only [BubbleWord.negativeWord, List.length_append] at hn
    omega

theorem canonical_word (p : LocalBubble α k b source target pos) (side : Bool) :
    (p.canonicalEdit side).word (listLetters source) =
      listLetters (p.before ++ (p.pathWord side ++ p.after)) := by
  cases side
  · have hword : (p.canonicalEdit false).word (listLetters source) = listLetters source := by
      funext i
      simp [canonicalEdit, Edit.word]
    rw [hword]
    exact congrArg listLetters (by simpa only [pathWord, Bool.false_eq_true, ite_false,
      List.append_assoc] using p.toLocalContext.source_eq)
  · rw [← Edit.listLetters_apply _ _ (p.canonical_inBounds true)]
    have hs : source = p.before ++ p.bubble.negativeWord ++ p.after := p.toLocalContext.source_eq
    have happly : (p.canonicalEdit true).apply source =
        p.before ++ p.bubble.positiveWord ++ p.after := by
      change (Edit.mk _ _ _).apply source = _
      exact (congrArg (fun word => (p.canonicalEdit true).apply word) hs).trans
        (p.bubble.apply_context p.before p.after)
    rw [happly]
    simp only [pathWord, ite_true, List.append_assoc]

theorem canonical_length (p : LocalBubble α k b source target pos) (side : Bool) :
    (p.canonicalEdit side).outputLength source.length =
      p.before.length + (p.pathWord side).length + p.after.length := by
  have hn := p.toLocalContext.source_length
  cases side
  · simpa only [canonicalEdit, pathWord, Bool.false_eq_true, ite_false,
      Edit.outputLength, List.length_nil, Nat.sub_zero, Nat.add_zero] using hn
  · simp only [canonicalEdit, pathWord, ite_true, Edit.outputLength,
      BubbleWord.positiveWord, List.length_append]
    simp only [BubbleWord.negativeWord, List.length_append] at hn
    omega

theorem canonical_occurrence (p : LocalBubble α k b source target pos) (side : Bool) :
    Agree (listLetters (p.pathWord side)) 0
      ((p.canonicalEdit side).word (listLetters source)) p.before.length
      (p.pathWord side).length := by
  intro i hi
  rw [p.canonical_word side, listLetters_middle _ _ _ i hi, Nat.zero_add]

theorem origin_local_bounds (p : LocalBubble α k b source target pos) (side : Bool)
    {i r : ℕ} (hi : p.before.length ≤ i ∧ i < p.before.length + (p.pathWord side).length)
    (hr : (p.canonicalEdit side).origin i = some r) :
    p.before.length ≤ r ∧ r < p.before.length + p.bubble.negativeWord.length := by
  cases side
  · have hir : i = r := by simpa [canonicalEdit, Edit.origin] using hr
    simpa only [pathWord, Bool.false_eq_true, ite_false, hir] using hi
  · rcases (p.canonicalEdit true).origin_before_or_after hr with hbefore | hafter
    · simp only [canonicalEdit, ite_true] at hbefore
      simp only [BubbleWord.negativeWord, List.length_append]
      omega
    · simp only [canonicalEdit, ite_true] at hafter
      simp only [pathWord, ite_true, BubbleWord.positiveWord, List.length_append] at hi
      simp only [BubbleWord.negativeWord, List.length_append]
      omega

theorem windows_ne_of_intervals {pos₁ pos₂ : ℕ} {target₁ target₂ : Word α}
    (hk : 1 ≤ k) (hx : KUnique (listLetters source) source.length k)
    (p : LocalBubble α k b source target₁ pos₁)
    (q : LocalBubble α k b source target₂ pos₂)
    (hdis : p.before.length + p.bubble.negativeWord.length ≤ q.before.length ∨
      q.before.length + q.bubble.negativeWord.length ≤ p.before.length)
    (side₁ side₂ : Bool) (i j : ℕ)
    (hi : i + (windowLength k b - 1) ≤ (p.pathWord side₁).length)
    (hj : j + (windowLength k b - 1) ≤ (q.pathWord side₂).length) :
    ¬ Agree (listLetters (p.pathWord side₁)) i (listLetters (q.pathWord side₂)) j
      (windowLength k b - 1) := by
  intro hag
  have hp := p.canonical_occurrence side₁
  have hq := q.canonical_occurrence side₂
  have hplen := p.canonical_length side₁
  have hqlen := q.canonical_length side₂
  have hglobal : Agree ((p.canonicalEdit side₁).word (listLetters source))
      (p.before.length + i) ((q.canonicalEdit side₂).word (listLetters source))
      (q.before.length + j) (windowLength k b - 1) := by
    intro a ha
    have hp' := hp (i + a) (by omega)
    have hq' := hq (j + a) (by omega)
    simp only [Nat.zero_add] at hp' hq'
    simpa only [Nat.add_assoc] using hp'.symm.trans ((hag a ha).trans hq')
  obtain ⟨s, r, hsk, _, hsource⟩ := Rigidity.shared_source_letters hk _ hx
    (p.canonicalEdit side₁) (q.canonicalEdit side₂)
    (p.canonical_bounded side₁) (q.canonical_bounded side₂)
    (p.canonical_inBounds side₁) (q.canonical_inBounds side₂)
    (p.before.length + i) (q.before.length + j) (by omega) (by omega) hglobal
  have h0 := hsource 0 (by omega)
  have hrp := p.origin_local_bounds side₁ (by omega) h0.1
  have hrq := q.origin_local_bounds side₂ (by omega) h0.2
  omega

theorem windows_ne_of_separation {pos₁ pos₂ : ℕ} {target₁ target₂ : Word α}
    (hk : 1 ≤ k) (hx : KUnique (listLetters source) source.length k)
    (p : LocalBubble α k b source target₁ pos₁)
    (q : LocalBubble α k b source target₂ pos₂)
    (hsep : 2 * (windowLength k b - 1) + b ≤ Nat.dist pos₁ pos₂)
    (side₁ side₂ : Bool) (i j : ℕ)
    (hi : i + (windowLength k b - 1) ≤ (p.pathWord side₁).length)
    (hj : j + (windowLength k b - 1) ≤ (q.pathWord side₂).length) :
    ¬ Agree (listLetters (p.pathWord side₁)) i (listLetters (q.pathWord side₂)) j
      (windowLength k b - 1) := by
  apply windows_ne_of_intervals hk hx p q ?_ side₁ side₂ i j hi hj
  have hp := p.toLocalContext.source_interval_bounds
  have hq := q.toLocalContext.source_interval_bounds
  have hup := p.bubble.removed_bound
  have huq := q.bubble.removed_bound
  have hstartp := p.toLocalContext.edit_pos
  have hstartq := q.toLocalContext.edit_pos
  have hleftp := p.bubble.left_upper
  have hleftq := q.bubble.left_upper
  unfold Nat.dist at hsep
  omega

#print axioms windows_ne_of_intervals
#print axioms windows_ne_of_separation

end DeletionCode.Burst.LocalBubble
