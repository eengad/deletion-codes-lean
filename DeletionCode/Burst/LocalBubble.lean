import DeletionCode.Burst.LocalContext
import DeletionCode.Qary.BubblePathSimplicity

/-!
Every sufficiently interior nontrivial burst in a k-unique source yields an
actual catalogue bubble. Both paths are simple, have the same boundary
vertices, and meet only at those vertices. The words, their exterior context,
and all geometry are derived from the edit itself.
-/
namespace DeletionCode.Burst

open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords

variable {α : Type*} [Inhabited α]

structure LocalBubble (α : Type*) [Inhabited α] (k b : ℕ)
    (source target : Word α) (pos : ℕ) extends LocalContext α k b source target pos where
  initial_agreement : Agree (listLetters bubble.negativeWord) 0
    (listLetters bubble.positiveWord) 0 (windowLength k b - 1)
  terminal_agreement : Agree (listLetters bubble.negativeWord)
    (bubble.negativeWord.length - (windowLength k b - 1))
    (listLetters bubble.positiveWord)
    (bubble.positiveWord.length - (windowLength k b - 1)) (windowLength k b - 1)
  negative_unique : KUnique (listLetters bubble.negativeWord)
    bubble.negativeWord.length (windowLength k b - 1)
  positive_unique : KUnique (listLetters bubble.positiveWord)
    bubble.positiveWord.length (windowLength k b - 1)
  endpoints : ∀ i j, i + (windowLength k b - 1) ≤ bubble.negativeWord.length →
    j + (windowLength k b - 1) ≤ bubble.positiveWord.length →
    Agree (listLetters bubble.negativeWord) i (listLetters bubble.positiveWord) j
      (windowLength k b - 1) →
    (i = 0 ∧ j = 0) ∨
      (i = bubble.negativeWord.length - (windowLength k b - 1) ∧
        j = bubble.positiveWord.length - (windowLength k b - 1))

theorem context_geometry {k b : ℕ} (hk : 1 ≤ k) (e : Edit α) (x : Word α)
    (he : e.Valid b x) (hx : KUnique (listLetters x) x.length k)
    (p : PrefixBoundary (k := k) (b := b) e x)
    (q : SuffixBoundary (k := k) (b := b) e x)
    (c : LocalContext α k b x (e.apply x) e.pos)
    (hp : c.before.length + (windowLength k b - 1) = p.index)
    (hq : c.after.length + (windowLength k b - 1) = q.suffix) :
    ∃ packet : LocalBubble α k b x (e.apply x) e.pos, packet.toLocalContext = c := by
  have hn := c.bubble.negativeWord_length_bounds.1
  have hn' := c.bubble.positiveWord_length_bounds.1
  have hsource := c.source_length
  have htarget := c.target_length
  rw [e.apply_length x he.2.1] at htarget
  have hneg := c.negative_occurrence
  have hpos := c.positive_occurrence
  rw [e.listLetters_apply x he.2.1] at hpos
  have hp' : windowLength k b - 1 ≤ p.index := by omega
  have hq' : windowLength k b - 1 ≤ q.suffix := by omega
  have hinit : Agree (listLetters c.bubble.negativeWord) 0
      (listLetters c.bubble.positiveWord) 0 (windowLength k b - 1) := by
    intro i hi
    have hmid := p.agree (c.before.length + i) (by omega)
    have hn' := hneg i (by omega)
    have hp' := hpos i (by omega)
    simp only [Nat.zero_add] at hn' hp' hmid ⊢
    exact hn'.trans (hmid.trans hp'.symm)
  have hterm : Agree (listLetters c.bubble.negativeWord)
      (c.bubble.negativeWord.length - (windowLength k b - 1))
      (listLetters c.bubble.positiveWord)
      (c.bubble.positiveWord.length - (windowLength k b - 1)) (windowLength k b - 1) := by
    intro i hi
    have hmid := q.agree i (by omega)
    have hnidx : c.before.length + (c.bubble.negativeWord.length - (windowLength k b - 1) + i) =
        x.length - q.suffix + i := by omega
    have hpidx : c.before.length + (c.bubble.positiveWord.length - (windowLength k b - 1) + i) =
        e.outputLength x.length - q.suffix + i := by omega
    have hneg' := hneg (c.bubble.negativeWord.length - (windowLength k b - 1) + i) (by omega)
    have hpos' := hpos (c.bubble.positiveWord.length - (windowLength k b - 1) + i) (by omega)
    simp only [Nat.zero_add, hnidx] at hneg'
    simp only [Nat.zero_add, hpidx] at hpos'
    exact hneg'.trans (hmid.trans hpos'.symm)
  have hnegative : KUnique (listLetters c.bubble.negativeWord)
      c.bubble.negativeWord.length (windowLength k b - 1) :=
    Qary.BubblePathSimplicity.substring_unique (listLetters x) _ x.length _ _ c.before.length
      (Qary.SpectrumPath.kunique_mono _ _ _ _ hx (by unfold windowLength; omega))
      (by omega) hneg
  have hpositive : KUnique (listLetters c.bubble.positiveWord)
      c.bubble.positiveWord.length (windowLength k b - 1) :=
    Qary.BubblePathSimplicity.substring_unique (e.word (listLetters x)) _
      (e.outputLength x.length) _ _ c.before.length
      (Rigidity.one_burst_unique hk _ hx e he.1 he.2.1) (by omega) hpos
  have hend : ∀ i j, i + (windowLength k b - 1) ≤ c.bubble.negativeWord.length →
      j + (windowLength k b - 1) ≤ c.bubble.positiveWord.length →
      Agree (listLetters c.bubble.negativeWord) i (listLetters c.bubble.positiveWord) j
        (windowLength k b - 1) →
      (i = 0 ∧ j = 0) ∨
        (i = c.bubble.negativeWord.length - (windowLength k b - 1) ∧
          j = c.bubble.positiveWord.length - (windowLength k b - 1)) := by
    intro i j hi hj hag
    have hglobal : Agree (listLetters x) (c.before.length + i)
        (e.word (listLetters x)) (c.before.length + j) (windowLength k b - 1) := by
      intro a ha
      have hn' := hneg (i + a) (by omega)
      have hp' := hpos (j + a) (by omega)
      simp only [Nat.zero_add] at hn' hp'
      simpa only [Nat.zero_add, Nat.add_assoc] using
        hn'.symm.trans ((hag a ha).trans hp')
    have ends := global_endpoints hk e x he hx p q hp' hq' (c.before.length + i)
      (c.before.length + j) (by omega) (by omega) hglobal
    rcases ends with hfirst | hlast
    · left; omega
    · right; omega
  exact ⟨{
    toLocalContext := c
    initial_agreement := hinit
    terminal_agreement := hterm
    negative_unique := hnegative
    positive_unique := hpositive
    endpoints := hend
  }, rfl⟩

theorem exists_localBubble {k b : ℕ} (hk : 1 ≤ k) (e : Edit α) (x : Word α)
    (he : e.Valid b x) (hx : KUnique (listLetters x) x.length k)
    (hleft : 2 * (windowLength k b + b) ≤ e.pos)
    (hright : e.pos + e.removed + 2 * (windowLength k b + b) ≤ x.length) :
    ∃ packet : LocalBubble α k b x (e.apply x) e.pos,
      packet.bubble.removed = e.sourceBlock x ∧ packet.bubble.replacement = e.replacement := by
  obtain ⟨p⟩ := exists_prefixBoundary hk e x he hx (by unfold windowLength at *; omega)
  obtain ⟨q⟩ := exists_suffixBoundary hk e x he hx (by unfold windowLength at *; omega)
  obtain ⟨c, hp, hq, hU, hV⟩ := exists_localContext e x he p q hleft hright
  obtain ⟨packet, hc⟩ := context_geometry hk e x he hx p q c hp hq
  refine ⟨packet, ?_, ?_⟩
  · rw [hc]
    exact hU
  · rw [hc]
    exact hV

#print axioms context_geometry
#print axioms exists_localBubble

end DeletionCode.Burst
