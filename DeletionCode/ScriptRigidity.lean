import DeletionCode.EditRigidity
import DeletionCode.SingleEditScripts

/-!
The shared-source and uniqueness lemma for genuine list edit scripts. Concrete
edits, output lengths, and their letter functions are derived from scripts of
cost at most one, so no origin labelling or unedited-block premise is supplied
by the caller. The explicit-edit theorem covers every fixed edit realization.
-/
namespace DeletionCode.ScriptRigidity

open Windows HeaderRecovery CatalogueWords EditAlignment SingleEditOrigins

/-- Equal long windows after genuine single edits have a common source block
at a common window offset. The edits and their source labellings are realized
from the original scripts. -/
theorem shared_source_letters {k : ℕ} (hk : 1 ≤ k) (x y z : List Bool)
    (hx : KUnique (listLetters x) x.length k)
    (hy : WithinEdits 1 x y) (hz : WithinEdits 1 x z) (a b : ℕ)
    (ha : a + (windowLength k - 1) ≤ y.length)
    (hb : b + (windowLength k - 1) ≤ z.length)
    (hag : Agree (listLetters y) a (listLetters z) b (windowLength k - 1)) :
    ∃ e f : Edit, e.Valid x.length ∧ f.Valid x.length ∧
      e.outputLength x.length = y.length ∧ f.outputLength x.length = z.length ∧
      e.word (listLetters x) = listLetters y ∧ f.word (listLetters x) = listLetters z ∧
      ∃ s r : ℕ, s + k ≤ windowLength k - 1 ∧ r + k ≤ x.length ∧
        ∀ i, i < k →
          e.origin (a + s + i) = some (r + i) ∧
          f.origin (b + s + i) = some (r + i) := by
  obtain ⟨e, he, hlen, hword⟩ := SingleEditScripts.within_one_realized hy
  obtain ⟨f, hf, hlen', hword'⟩ := SingleEditScripts.within_one_realized hz
  refine ⟨e, f, he, hf, hlen, hlen', hword, hword', ?_⟩
  apply EditRigidity.shared_source_letters hk (listLetters x) hx e f he hf a b
  · simpa only [hlen] using ha
  · simpa only [hlen'] using hb
  · simpa only [hword, hword'] using hag

/-- Every actual word within one edit of a k-unique word is (L-1)-unique. -/
theorem within_one_unique {k : ℕ} (hk : 1 ≤ k) (x y : List Bool)
    (hx : KUnique (listLetters x) x.length k) (hy : WithinEdits 1 x y) :
    KUnique (listLetters y) y.length (windowLength k - 1) := by
  obtain ⟨e, he, hlen, hword⟩ := SingleEditScripts.within_one_realized hy
  simpa only [hlen, hword] using EditRigidity.one_edit_unique hk (listLetters x) hx e he

theorem within_one_spectrum_boolean {k : ℕ} (hk : 1 ≤ k) (x y : List Bool)
    (hx : KUnique (listLetters x) x.length k) (hy : WithinEdits 1 x y) :
    ∀ g, SignedSupport.wordSpectrum (listLetters y) y.length (windowLength k) g = 0 ∨
      SignedSupport.wordSpectrum (listLetters y) y.length (windowLength k) g = 1 :=
  SpectrumPath.spectrum_boolean (listLetters y) y.length (windowLength k)
    (within_one_unique hk x y hx hy)

/-- The de Bruijn walk after one edit is simple, including its endpoint vertices. -/
theorem within_one_vertex_path_injective {k : ℕ} (hk : 1 ≤ k) (x y : List Bool)
    (hx : KUnique (listLetters x) x.length k) (hy : WithinEdits 1 x y)
    (hlen : windowLength k ≤ y.length) :
    Function.Injective (fun i : Fin (y.length - windowLength k + 2) =>
      SpectrumPath.vertexAt (listLetters y) (windowLength k) i.val) :=
  SpectrumPath.vertex_path_injective (listLetters y) y.length (windowLength k)
    (by unfold windowLength; omega) hlen (within_one_unique hk x y hx hy)

#print axioms shared_source_letters
#print axioms within_one_unique
#print axioms within_one_spectrum_boolean
#print axioms within_one_vertex_path_injective

end DeletionCode.ScriptRigidity
