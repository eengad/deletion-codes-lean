import DeletionCode.SingleEditOrigins
import DeletionCode.TwoEditWindows
import DeletionCode.SpectrumPath

/-!
Shared source letters for two fixed edits of one k-unique word. A common
length-k block avoiding both edit positions is derived arithmetically. Its
source indices are consecutive in each word, and k-uniqueness identifies the
two source starting indices. Applying this to two windows in the same edited
word proves (L-1)-uniqueness without assuming simplicity of that edited word.
-/
namespace DeletionCode.EditRigidity

open Windows HeaderRecovery SingleEditOrigins

/-- The shared-source-letters assertion in manuscript lemma `lem:rigidity`.
The edits and all surviving source indices are actual data. Positivity of k
is explicit; the manuscript fixes k = 2*ceil(log₂ n)+2. -/
theorem shared_source_letters {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e f : Edit) (he : e.Valid n) (hf : f.Valid n)
    (a b : ℕ) (ha : a + (windowLength k - 1) ≤ e.outputLength n)
    (hb : b + (windowLength k - 1) ≤ f.outputLength n)
    (hag : Agree (e.word x) a (f.word x) b (windowLength k - 1)) :
    ∃ s r : ℕ, s + k ≤ windowLength k - 1 ∧ r + k ≤ n ∧
      ∀ i, i < k →
        e.origin (a + s + i) = some (r + i) ∧
        f.origin (b + s + i) = some (r + i) := by
  have hL : windowLength k - 1 = 3 * k + 2 := by unfold windowLength; omega
  obtain ⟨s, hsk, hea, hfb⟩ := TwoEditWindows.exists_clean_block k a b e.cut f.cut
  obtain ⟨r, hr⟩ := e.clean_block a s k hea
  obtain ⟨r', hr'⟩ := f.clean_block b s k hfb
  have hrlast := e.origin_lt he (i := a + s + (k - 1)) (by omega)
    (hr (k - 1) (by omega))
  have hr'last := f.origin_lt hf (i := b + s + (k - 1)) (by omega)
    (hr' (k - 1) (by omega))
  have hri : r + k ≤ n := by omega
  have hr'i : r' + k ≤ n := by omega
  have hsource : Agree x r x r' k := by
    intro i hi
    have heq := hag (s + i) (by omega)
    calc
      x (r + i) = e.word x (a + s + i) := (e.word_of_origin x (hr i hi)).symm
      _ = f.word x (b + s + i) := by simpa only [Nat.add_assoc] using heq
      _ = x (r' + i) := f.word_of_origin x (hr' i hi)
  have hrr := hx r r' hri hr'i hsource
  subst r'
  exact ⟨s, r, by omega, hri, fun i hi => ⟨hr i hi, hr' i hi⟩⟩

/-- No two distinct (L-1)-windows of a word one edit away from x coincide.
The injectivity of surviving source positions is proved from the edit. -/
theorem one_edit_unique {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e : Edit) (he : e.Valid n) :
    KUnique (e.word x) (e.outputLength n) (windowLength k - 1) := by
  intro a b ha hb hag
  obtain ⟨s, r, _, _, hsource⟩ := shared_source_letters hk x hx e e he he a b ha hb hag
  have h0 := hsource 0 (by omega)
  have hab := e.origin_injective h0.1 h0.2
  omega

/-- The integer L-spectrum remains Boolean after any one valid edit. -/
theorem one_edit_spectrum_boolean {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e : Edit) (he : e.Valid n) :
    ∀ g, SignedSupport.wordSpectrum (e.word x) (e.outputLength n) (windowLength k) g = 0 ∨
      SignedSupport.wordSpectrum (e.word x) (e.outputLength n) (windowLength k) g = 1 :=
  SpectrumPath.spectrum_boolean (e.word x) (e.outputLength n) (windowLength k)
    (one_edit_unique hk x hx e he)

#print axioms shared_source_letters
#print axioms one_edit_unique
#print axioms one_edit_spectrum_boolean

end DeletionCode.EditRigidity
