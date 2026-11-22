import DeletionCode.Explicit.Borrowed.LocalBubble
import DeletionCode.Burst.LocalSpectrum

/-!
The exact spectrum change of a local burst, and relocation of an already
proved local bubble to another occurrence of its negative word. This allows
source-derived geometry to be used inside a chronological edit history.
-/
namespace DeletionCode.Explicit.Borrowed

open DeletionCode.Burst
open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords
open DeletionCode.Qary.SignedSupport DeletionCode.Qary.SpectrumLocalization

variable {α : Type*} [Inhabited α]

omit [Inhabited α] in
theorem BubbleWord.apply_context {K b L : ℕ} (p : BubbleWord α K b L) (before after : Word α) :
    (Edit.mk (before.length + p.left.length) p.removed.length p.replacement).apply
      (before ++ p.negativeWord ++ after) = before ++ p.positiveWord ++ after := by
  simpa only [BubbleWord.negativeWord, BubbleWord.positiveWord, List.length_append,
    List.append_assoc] using Edit.apply_split (before ++ p.left) p.removed p.replacement
      (p.right ++ after)

namespace LocalBubble

variable {K b L pos : ℕ} {source target : Word α}

theorem spectrum_delta (p : LocalBubble α K b L source target pos)
    (hwindow : 3 * (K + b + 1) ≤ L)
    (g : Gram α L) :
    wordSpectrum (listLetters target) target.length L g -
      wordSpectrum (listLetters source) source.length L g =
      wordSpectrum (listLetters p.bubble.positiveWord) p.bubble.positiveWord.length
        L g -
      wordSpectrum (listLetters p.bubble.negativeWord) p.bubble.negativeWord.length
        L g := by
  have hn := (p.bubble.negativeWord_length_bounds hwindow).1
  have hp := (p.bubble.positiveWord_length_bounds hwindow).1
  have hL : 1 ≤ L := by omega
  have hlast : Agree (listLetters p.bubble.negativeWord)
      (p.bubble.negativeWord.length + 1 - L)
      (listLetters p.bubble.positiveWord)
      (p.bubble.positiveWord.length + 1 - L) (L - 1) := by
    have hnidx : p.bubble.negativeWord.length + 1 - L =
        p.bubble.negativeWord.length - (L - 1) := by omega
    have hpidx : p.bubble.positiveWord.length + 1 - L =
        p.bubble.positiveWord.length - (L - 1) := by omega
    rw [hnidx, hpidx]
    exact p.terminal_agreement
  have h := context_replacement p.before p.bubble.negativeWord p.bubble.positiveWord p.after
    L hL (by omega) (by omega) p.initial_agreement hlast g
  simpa only [p.toLocalContext.source_eq, p.toLocalContext.target_eq,
    List.length_append, List.append_assoc, Nat.add_assoc] using h

theorem recontextualize (p : LocalBubble α K b L source target pos)
    (word : Word α) (s : ℕ) (hs : s + p.bubble.negativeWord.length ≤ word.length)
    (hag : Agree (listLetters p.bubble.negativeWord) 0 (listLetters word) s
      p.bubble.negativeWord.length) :
    ∃ q : LocalBubble α K b L word
      ((Edit.mk (s + p.bubble.left.length) p.bubble.removed.length
        p.bubble.replacement).apply word) (s + p.bubble.left.length),
      q.bubble = p.bubble ∧ q.before.length = s := by
  let before := word.take s
  let after := word.drop (s + p.bubble.negativeWord.length)
  have hbefore : before.length = s := List.length_take_of_le (by omega)
  have hsource : word = before ++ p.bubble.negativeWord ++ after :=
    context_eq_of_agree word p.bubble.negativeWord s hs hag
  have htarget : (Edit.mk (s + p.bubble.left.length) p.bubble.removed.length
      p.bubble.replacement).apply word = before ++ p.bubble.positiveWord ++ after := by
    rw [hsource, ← hbefore]
    exact p.bubble.apply_context before after
  exact ⟨{
    bubble := p.bubble
    before := before
    after := after
    source_eq := hsource
    target_eq := htarget
    edit_pos := by rw [hbefore]
    initial_agreement := p.initial_agreement
    terminal_agreement := p.terminal_agreement
    negative_unique := p.negative_unique
    positive_unique := p.positive_unique
    endpoints := p.endpoints
  }, rfl, hbefore⟩

end LocalBubble

#print axioms LocalBubble.spectrum_delta
#print axioms LocalBubble.recontextualize

/-- Manuscript `lem:local-bubble`: one interior edit gives a local bubble with the same
spectrum difference as the full edit. The packet includes both occurrences and their geometry. -/
theorem local_bubble {K b L : ℕ} (hk : 1 ≤ K) (hwindow : 3 * (K + b + 1) ≤ L)
    (e : Edit α) (x : Word α) (he : e.Valid b x) (hx : KUnique (listLetters x) x.length K)
    (hleft : 2 * (L + b) ≤ e.pos) (hright : e.pos + e.removed + 2 * (L + b) ≤ x.length) :
    ∃ p : LocalBubble α K b L x (e.apply x) e.pos,
      p.bubble.removed = e.sourceBlock x ∧ p.bubble.replacement = e.replacement ∧
      (L ≤ p.bubble.negativeWord.length ∧ p.bubble.negativeWord.length ≤ 2 * (L - 1) + b) ∧
      (L ≤ p.bubble.positiveWord.length ∧ p.bubble.positiveWord.length ≤ 2 * (L - 1) + b) ∧
      wordSpectrum (listLetters (e.apply x)) (e.apply x).length L -
          wordSpectrum (listLetters x) x.length L =
        wordSpectrum (listLetters p.bubble.positiveWord) p.bubble.positiveWord.length L -
          wordSpectrum (listLetters p.bubble.negativeWord) p.bubble.negativeWord.length L := by
  obtain ⟨p, hU, hV⟩ := exists_localBubble hk hwindow e x he hx hleft hright
  exact ⟨p, hU, hV, p.bubble.negativeWord_length_bounds hwindow,
    p.bubble.positiveWord_length_bounds hwindow, funext (p.spectrum_delta hwindow)⟩

#print axioms local_bubble

end DeletionCode.Explicit.Borrowed
