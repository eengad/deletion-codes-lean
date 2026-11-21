import DeletionCode.Burst.PrefixBoundary
import DeletionCode.Burst.Reversal

/-!
The last actual mismatch is localized by applying the first-mismatch theorem
to the reversed edit. Prefix and suffix agreement are independent: they may
overlap when the two words have different lengths.
-/
namespace DeletionCode.Burst

open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords

variable {α : Type*} [Inhabited α]

structure SuffixBoundary {k b : ℕ} (e : Edit α) (x : Word α) where
  suffix : ℕ
  before : x.length - e.pos - e.removed ≤ suffix
  upper : suffix < x.length - e.pos - e.removed + k + b
  source_bound : suffix < x.length
  target_bound : suffix < e.outputLength x.length
  agree : Agree (listLetters x) (x.length - suffix)
    (e.word (listLetters x)) (e.outputLength x.length - suffix) suffix
  different : listLetters x (x.length - suffix - 1) ≠
    e.word (listLetters x) (e.outputLength x.length - suffix - 1)

theorem exists_suffixBoundary {k b : ℕ} (hk : 1 ≤ k) (e : Edit α) (x : Word α)
    (he : e.Valid b x) (hx : KUnique (listLetters x) x.length k)
    (hroom : k + 2 * b ≤ e.pos) :
    Nonempty (SuffixBoundary (k := k) (b := b) e x) := by
  have hrvalid := e.reverseOn_valid x he
  have hrroom : (e.reverseOn x.length).pos + k + 2 * b ≤ x.reverse.length := by
    have hv := he.2.1
    unfold Edit.InBounds at hv
    simp only [Edit.reverseOn, List.length_reverse]
    omega
  obtain ⟨p⟩ := exists_prefixBoundary hk (e.reverseOn x.length) x.reverse
    hrvalid (unique_reverse x hx) hrroom
  have hlen : (e.reverseOn x.length).outputLength x.reverse.length =
      e.outputLength x.length := by
    simp only [Edit.reverseOn, Edit.outputLength, List.length_reverse]
  have hword : (e.reverseOn x.length).word (listLetters x.reverse) =
      listLetters (e.apply x).reverse := by
    rw [← (e.reverseOn x.length).listLetters_apply x.reverse hrvalid.2.1,
      e.reverseOn_apply x he.2.1]
  have hn : p.index < x.length := by simpa only [List.length_reverse] using p.source_bound
  have hn' : p.index < e.outputLength x.length := by simpa only [hlen] using p.target_bound
  have hyl : (e.apply x).length = e.outputLength x.length := e.apply_length x he.2.1
  refine ⟨⟨p.index, p.before, p.upper, hn, hn', ?_, ?_⟩⟩
  · intro i hi
    have hj : p.index - 1 - i < p.index := by omega
    have heq := p.agree (p.index - 1 - i) hj
    simp only [Nat.zero_add, hword] at heq
    rw [listLetters_reverse x (by omega), listLetters_reverse (e.apply x) (by omega)] at heq
    rw [hyl, e.listLetters_apply x he.2.1] at heq
    have hia : x.length - 1 - (p.index - 1 - i) = x.length - p.index + i := by omega
    have hib : e.outputLength x.length - 1 - (p.index - 1 - i) =
        e.outputLength x.length - p.index + i := by omega
    simpa only [hia, hib] using heq
  · have hneq := p.different
    rw [hword, listLetters_reverse x hn, listLetters_reverse (e.apply x) (by omega)] at hneq
    rw [hyl, e.listLetters_apply x he.2.1] at hneq
    simpa only [Nat.sub_sub, Nat.add_comm 1 p.index] using hneq

#print axioms exists_suffixBoundary

end DeletionCode.Burst
