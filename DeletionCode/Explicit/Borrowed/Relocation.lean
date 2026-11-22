import DeletionCode.Explicit.Borrowed.LocalSpectrum

/-!
A burst bubble constructed in the original source can be placed in an actual
intermediate word when its whole source neighborhood is unchanged there.
The edit's central blocks and chronological position determine the placement.
-/
namespace DeletionCode.Explicit.Borrowed.LocalBubble

open DeletionCode.Burst
open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords

variable {α : Type*} [Inhabited α]

theorem relocate {K b L pos : ℕ} {source target : Word α}
    (packet : LocalBubble α K b L source target pos) (word : Word α) (e : Edit α)
    (hu : packet.bubble.removed.length = e.removed)
    (hv : packet.bubble.replacement = e.replacement)
    (hsource : L + b ≤ pos)
    (hleft : L + b ≤ e.pos)
    (hright : e.pos + e.removed + (L - 1) ≤ word.length)
    (hag : Agree (listLetters word) (e.pos - (L + b))
      (listLetters source) (pos - (L + b)) (2 * (L + b))) :
    ∃ q : LocalBubble α K b L word (e.apply word) e.pos, q.bubble = packet.bubble := by
  let s := e.pos - packet.bubble.left.length
  have hl := packet.bubble.left_upper
  have hr := packet.bubble.right_upper
  have hU := packet.bubble.removed_bound
  have hpos := packet.toLocalContext.edit_pos
  have hlen : packet.bubble.negativeWord.length =
      packet.bubble.left.length + packet.bubble.removed.length + packet.bubble.right.length := by
    simp only [BubbleWord.negativeWord, List.length_append]
  have hs : s + packet.bubble.left.length = e.pos := by dsimp [s]; omega
  have hbound : s + packet.bubble.negativeWord.length ≤ word.length := by omega
  have hocc : Agree (listLetters packet.bubble.negativeWord) 0 (listLetters word) s
      packet.bubble.negativeWord.length := by
    intro i hi
    let offset := L + b - packet.bubble.left.length + i
    have hoff : offset < 2 * (L + b) := by dsimp [offset]; omega
    have hmid := hag offset hoff
    have hsrc := packet.toLocalContext.negative_occurrence i hi
    have ha : pos - (L + b) + offset = packet.before.length + i := by
      dsimp [offset]
      omega
    have hc : e.pos - (L + b) + offset = s + i := by
      dsimp [offset, s]
      omega
    rw [ha, hc] at hmid
    exact hsrc.trans hmid.symm
  obtain ⟨q, hq, _⟩ := packet.recontextualize word s hbound hocc
  have heq : Edit.mk (s + packet.bubble.left.length) packet.bubble.removed.length
      packet.bubble.replacement = e := by
    rw [hs, hu, hv]
  have hex : ∃ q' : LocalBubble α K b L word
      ((Edit.mk (s + packet.bubble.left.length) packet.bubble.removed.length
        packet.bubble.replacement).apply word) (s + packet.bubble.left.length),
      q'.bubble = packet.bubble := ⟨q, hq⟩
  rw [heq, hs] at hex
  exact hex

#print axioms relocate

end DeletionCode.Explicit.Borrowed.LocalBubble
