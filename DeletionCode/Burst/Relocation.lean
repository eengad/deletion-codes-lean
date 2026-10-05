import DeletionCode.Burst.LocalSpectrum

/-!
A burst bubble constructed in the original source can be placed in an actual
intermediate word when its whole source neighborhood is unchanged there.
The edit's central blocks and chronological position determine the placement.
-/
namespace DeletionCode.Burst.LocalBubble

open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords

variable {α : Type*} [Inhabited α]

theorem relocate {k b pos : ℕ} {source target : Word α}
    (packet : LocalBubble α k b source target pos) (word : Word α) (e : Edit α)
    (hu : packet.bubble.removed.length = e.removed)
    (hv : packet.bubble.replacement = e.replacement)
    (hsource : windowLength k b + b ≤ pos)
    (hleft : windowLength k b + b ≤ e.pos)
    (hright : e.pos + e.removed + (windowLength k b - 1) ≤ word.length)
    (hag : Agree (listLetters word) (e.pos - (windowLength k b + b))
      (listLetters source) (pos - (windowLength k b + b)) (2 * (windowLength k b + b))) :
    ∃ q : LocalBubble α k b word (e.apply word) e.pos, q.bubble = packet.bubble := by
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
    let offset := windowLength k b + b - packet.bubble.left.length + i
    have hoff : offset < 2 * (windowLength k b + b) := by dsimp [offset]; omega
    have hmid := hag offset hoff
    have hsrc := packet.toLocalContext.negative_occurrence i hi
    have ha : pos - (windowLength k b + b) + offset = packet.before.length + i := by
      dsimp [offset]
      omega
    have hc : e.pos - (windowLength k b + b) + offset = s + i := by
      dsimp [offset, s]
      omega
    rw [ha, hc] at hmid
    exact hsrc.trans hmid.symm
  obtain ⟨q, hq, _⟩ := packet.recontextualize word s hbound hocc
  have heq : Edit.mk (s + packet.bubble.left.length) packet.bubble.removed.length
      packet.bubble.replacement = e := by
    rw [hs, hu, hv]
  have hex : ∃ q' : LocalBubble α k b word
      ((Edit.mk (s + packet.bubble.left.length) packet.bubble.removed.length
        packet.bubble.replacement).apply word) (s + packet.bubble.left.length),
      q'.bubble = packet.bubble := ⟨q, hq⟩
  rw [heq, hs] at hex
  exact hex

#print axioms relocate

end DeletionCode.Burst.LocalBubble
