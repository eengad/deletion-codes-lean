import DeletionCode.Burst.LocalBubble

/-!
The exact spectrum change of a local burst, and relocation of an already
proved local bubble to another occurrence of its negative word. This allows
source-derived geometry to be used inside a chronological edit history.
-/
namespace DeletionCode.Burst

open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords
open DeletionCode.Qary.SignedSupport DeletionCode.Qary.SpectrumLocalization

variable {α : Type*} [Inhabited α]

theorem substring_eq_of_agree (x p : Word α) (s : ℕ) (hs : s + p.length ≤ x.length)
    (hag : Agree (listLetters p) 0 (listLetters x) s p.length) :
    (x.drop s).take p.length = p := by
  have hlen : ((x.drop s).take p.length).length = p.length := by
    apply List.length_take_of_le
    simp only [List.length_drop]
    omega
  apply eq_of_listLetters hlen
  intro i hi
  have hip : i < p.length := by rw [hlen] at hi; exact hi
  have hh := hag i hip
  simp only [Nat.zero_add] at hh ⊢
  simpa only [listLetters, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hip, List.getElem?_drop] using hh.symm

theorem context_eq_of_agree (x p : Word α) (s : ℕ) (hs : s + p.length ≤ x.length)
    (hag : Agree (listLetters p) 0 (listLetters x) s p.length) :
    x = x.take s ++ p ++ x.drop (s + p.length) := by
  have heq := (Edit.mk s p.length []).decomposition x
  have hm : (Edit.mk s p.length []).sourceBlock x = p := substring_eq_of_agree x p s hs hag
  rw [hm] at heq
  exact heq.symm

omit [Inhabited α] in
theorem BubbleWord.apply_context {k b : ℕ} (p : BubbleWord α k b) (before after : Word α) :
    (Edit.mk (before.length + p.left.length) p.removed.length p.replacement).apply
      (before ++ p.negativeWord ++ after) = before ++ p.positiveWord ++ after := by
  simpa only [BubbleWord.negativeWord, BubbleWord.positiveWord, List.length_append,
    List.append_assoc] using Edit.apply_split (before ++ p.left) p.removed p.replacement
      (p.right ++ after)

namespace LocalBubble

variable {k b pos : ℕ} {source target : Word α}

theorem spectrum_delta (p : LocalBubble α k b source target pos)
    (g : Gram α (windowLength k b)) :
    wordSpectrum (listLetters target) target.length (windowLength k b) g -
      wordSpectrum (listLetters source) source.length (windowLength k b) g =
      wordSpectrum (listLetters p.bubble.positiveWord) p.bubble.positiveWord.length
        (windowLength k b) g -
      wordSpectrum (listLetters p.bubble.negativeWord) p.bubble.negativeWord.length
        (windowLength k b) g := by
  have hn := p.bubble.negativeWord_length_bounds.1
  have hp := p.bubble.positiveWord_length_bounds.1
  have hL : 1 ≤ windowLength k b := by unfold windowLength; omega
  have hlast : Agree (listLetters p.bubble.negativeWord)
      (p.bubble.negativeWord.length + 1 - windowLength k b)
      (listLetters p.bubble.positiveWord)
      (p.bubble.positiveWord.length + 1 - windowLength k b) (windowLength k b - 1) := by
    have hnidx : p.bubble.negativeWord.length + 1 - windowLength k b =
        p.bubble.negativeWord.length - (windowLength k b - 1) := by omega
    have hpidx : p.bubble.positiveWord.length + 1 - windowLength k b =
        p.bubble.positiveWord.length - (windowLength k b - 1) := by omega
    rw [hnidx, hpidx]
    exact p.terminal_agreement
  have h := context_replacement p.before p.bubble.negativeWord p.bubble.positiveWord p.after
    (windowLength k b) hL (by omega) (by omega) p.initial_agreement hlast g
  simpa only [p.toLocalContext.source_eq, p.toLocalContext.target_eq,
    List.length_append, List.append_assoc, Nat.add_assoc] using h

theorem recontextualize (p : LocalBubble α k b source target pos)
    (word : Word α) (s : ℕ) (hs : s + p.bubble.negativeWord.length ≤ word.length)
    (hag : Agree (listLetters p.bubble.negativeWord) 0 (listLetters word) s
      p.bubble.negativeWord.length) :
    ∃ q : LocalBubble α k b word
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

end DeletionCode.Burst
