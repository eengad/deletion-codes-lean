import DeletionCode.Burst.WordFacts
import DeletionCode.Burst.Rigidity

/-!
The first actual mismatch of a nontrivial bounded replacement lies less than
k+b letters after its start. For unequal block lengths, a longer agreement
would repeat a source k-gram at two distinct positions. Equal block lengths
are handled by the recorded inequality of the removed and replacement blocks.
-/
namespace DeletionCode.Burst

open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords

variable {α : Type*} [Inhabited α]

theorem not_long_common_prefix {k b : ℕ} (hk : 1 ≤ k) (e : Edit α) (x : Word α)
    (he : e.Valid b x) (hx : KUnique (listLetters x) x.length k)
    (hroom : e.pos + k + 2 * b ≤ x.length) :
    ¬ Agree (listLetters x) 0 (e.word (listLetters x)) 0 (e.pos + k + b) := by
  intro hag
  by_cases hlen : e.removed = e.replacement.length
  · apply he.2.2
    apply eq_of_listLetters ((e.sourceBlock_length x he.2.1).trans hlen)
    intro i hi
    have hiu : i < e.removed := by rw [e.sourceBlock_length x he.2.1] at hi; exact hi
    have hiv : i < e.replacement.length := by omega
    have heq := hag (e.pos + i) (by have hu := he.1.1; omega)
    simpa only [Nat.zero_add, e.sourceBlock_letters x hiu,
      e.word_replacement (listLetters x) hiv] using heq
  · let q := e.pos + max e.removed e.replacement.length
    let r := q + e.removed - e.replacement.length
    have hu := he.1.1
    have hv := he.1.2
    have hmax : max e.removed e.replacement.length ≤ b := max_le hu hv
    have hq : e.pos + e.replacement.length ≤ q := by dsimp [q]; omega
    have hqn : q + k ≤ x.length := by dsimp [q]; omega
    have hrn : r + k ≤ x.length := by dsimp [r, q]; omega
    have hqr : q ≠ r := by dsimp [r]; omega
    have heq : Agree (listLetters x) q (listLetters x) r k := by
      intro i hi
      have hag' := hag (q + i) (by dsimp [q]; omega)
      have hbefore : ¬ q + i < e.pos := by omega
      have hnew : ¬ q + i < e.pos + e.replacement.length := by omega
      have hind : q + i + e.removed - e.replacement.length = r + i := by
        dsimp [r]
        omega
      simpa only [Nat.zero_add, Edit.word, hbefore, hnew, ite_false, hind] using hag'
    exact hqr (hx q r hqn hrn heq)

structure PrefixBoundary {k b : ℕ} (e : Edit α) (x : Word α) where
  index : ℕ
  before : e.pos ≤ index
  upper : index < e.pos + k + b
  source_bound : index < x.length
  target_bound : index < e.outputLength x.length
  agree : Agree (listLetters x) 0 (e.word (listLetters x)) 0 index
  different : listLetters x index ≠ e.word (listLetters x) index

theorem exists_prefixBoundary {k b : ℕ} (hk : 1 ≤ k) (e : Edit α) (x : Word α)
    (he : e.Valid b x) (hx : KUnique (listLetters x) x.length k)
    (hroom : e.pos + k + 2 * b ≤ x.length) :
    Nonempty (PrefixBoundary (k := k) (b := b) e x) := by
  classical
  have hex : ∃ i, i < e.pos + k + b ∧ listLetters x i ≠ e.word (listLetters x) i := by
    by_contra hn
    apply not_long_common_prefix hk e x he hx hroom
    intro i hi
    simp only [Nat.zero_add]
    by_contra hneq
    exact hn ⟨i, hi, hneq⟩
  let ell := Nat.find hex
  have hspec := Nat.find_spec hex
  have hag : Agree (listLetters x) 0 (e.word (listLetters x)) 0 ell := by
    intro i hi
    simp only [Nat.zero_add]
    by_contra hneq
    exact Nat.find_min hex hi ⟨by dsimp [ell] at hi; omega, hneq⟩
  have hbefore : e.pos ≤ ell := by
    by_contra hn
    have hlt : ell < e.pos := by omega
    have hn' : listLetters x ell ≠ e.word (listLetters x) ell := hspec.2
    simp only [Edit.word, hlt, ite_true, ne_eq, not_true_eq_false] at hn'
  have hu := he.1.1
  refine ⟨⟨ell, hbefore, hspec.1, by omega, ?_, hag, hspec.2⟩⟩
  unfold Edit.outputLength
  omega

#print axioms not_long_common_prefix
#print axioms exists_prefixBoundary

end DeletionCode.Burst
