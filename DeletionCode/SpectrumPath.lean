import DeletionCode.SignedSupport
import DeletionCode.WordPaths
import DeletionCode.HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
The manuscript lemma `lem:path`: a word with distinct (L-1)-grams has a
Boolean L-spectrum supported on its simple directed de Bruijn path, and that
spectrum determines the entire finite word. The competing word need not be
unique. Its windows are located from the actual spectrum counts, then the
overlap/contiguity theorem forces a single occurrence of the whole word.
-/

namespace DeletionCode.SpectrumPath

open Windows SignedSupport
open scoped BigOperators

/-- The actual (L-1)-gram vertex at a zero-based offset in a word. -/
def vertexAt (word : Letters) (L offset : ℕ) : SupportComponents.Vertex L :=
  fun i => word (offset + i.val)

theorem spectrum_at_occurrence_positive (word : Letters) (n L a : ℕ) (g : Gram L)
    (ha : a + L ≤ n) (hg : gram word L a = g) :
    0 < wordSpectrum word n L g := by
  classical
  let occurrence : Fin (n + 1) := ⟨a, by omega⟩
  have hsum :
      (if occurrence.val + L ≤ n ∧ gram word L occurrence.val = g then (1 : ℤ) else 0) ≤
      ∑ i : Fin (n + 1), if i.val + L ≤ n ∧ gram word L i.val = g then (1 : ℤ) else 0 := by
    apply Finset.single_le_sum (s := Finset.univ) (a := occurrence)
      (f := fun i : Fin (n + 1) =>
        if i.val + L ≤ n ∧ gram word L i.val = g then (1 : ℤ) else 0)
    · intro i hi
      split_ifs <;> omega
    · exact Finset.mem_univ occurrence
  have hone : (1 : ℤ) ≤ wordSpectrum word n L g := by
    simpa only [occurrence, ha, hg, and_self, ite_true, wordSpectrum] using hsum
  omega

theorem spectrum_nonzero_iff_occurs (word : Letters) (n L : ℕ) (g : Gram L) :
    wordSpectrum word n L g ≠ 0 ↔ ∃ a, a + L ≤ n ∧ gram word L a = g := by
  constructor
  · exact wordSpectrum_nonzero_occurs word n L g
  · rintro ⟨a, ha, hg⟩
    exact ne_of_gt (spectrum_at_occurrence_positive word n L a g ha hg)

/-- Equal valid L-grams begin at the same position in an (L-1)-unique word. -/
theorem gram_position_unique (word : Letters) (n L a b : ℕ)
    (hunique : KUnique word n (L - 1))
    (ha : a + L ≤ n) (hb : b + L ≤ n)
    (heq : gram word L a = gram word L b) : a = b := by
  apply hunique a b (by omega) (by omega)
  intro i hi
  exact congrFun heq ⟨i, by omega⟩

theorem spectrum_at_occurrence_one (word : Letters) (n L a : ℕ) (g : Gram L)
    (hunique : KUnique word n (L - 1))
    (ha : a + L ≤ n) (hg : gram word L a = g) :
    wordSpectrum word n L g = 1 := by
  classical
  let occurrence : Fin (n + 1) := ⟨a, by omega⟩
  unfold wordSpectrum
  have hsingle := Finset.sum_eq_single (s := Finset.univ)
    (f := fun i : Fin (n + 1) => if i.val + L ≤ n ∧ gram word L i.val = g then (1 : ℤ) else 0)
    occurrence
    (by
      intro i hi hne
      apply ite_eq_right
      rintro ⟨hibound, hgram⟩
      have hval := gram_position_unique word n L i.val a hunique hibound ha (hgram.trans hg.symm)
      exact hne (Fin.ext hval))
    (fun hnot => False.elim (hnot (Finset.mem_univ occurrence)))
  exact hsingle.trans (by simp [occurrence, ha, hg])

/-- Every actual integral spectrum coordinate is zero or one. -/
theorem spectrum_boolean (word : Letters) (n L : ℕ)
    (hunique : KUnique word n (L - 1)) :
    ∀ g, wordSpectrum word n L g = 0 ∨ wordSpectrum word n L g = 1 := by
  classical
  intro g
  by_cases hzero : wordSpectrum word n L g = 0
  · exact Or.inl hzero
  · obtain ⟨a, ha, hg⟩ := wordSpectrum_nonzero_occurs word n L g hzero
    exact Or.inr (spectrum_at_occurrence_one word n L a g hunique ha hg)

/-- All n-L+2 vertices, including the terminal vertex, are distinct. -/
theorem vertex_path_injective (word : Letters) (n L : ℕ)
    (hL : 1 ≤ L) (hn : L ≤ n) (hunique : KUnique word n (L - 1)) :
    Function.Injective (fun i : Fin (n - L + 2) => vertexAt word L i.val) := by
  intro a b heq
  apply Fin.ext
  apply hunique a.val b.val
  · have := a.isLt
    omega
  · have := b.isLt
    omega
  · intro i hi
    exact congrFun heq ⟨i, hi⟩

/-- These are exactly the n-L+1 edges carried by the spectrum. -/
theorem spectrum_support_path (word : Letters) (n L : ℕ) (hn : L ≤ n) (g : Gram L) :
    wordSpectrum word n L g ≠ 0 ↔ ∃ i : Fin (n - L + 1), gram word L i.val = g := by
  rw [spectrum_nonzero_iff_occurs]
  constructor
  · rintro ⟨a, ha, hg⟩
    exact ⟨⟨a, by omega⟩, hg⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.val, by have := i.isLt; omega, hi⟩

/-- Each supported gram is the directed edge between the displayed consecutive vertices. -/
theorem path_edge_endpoints (word : Letters) (L i : ℕ) :
    gramPrefix (gram word L i) = vertexAt word L i ∧
      gramSuffix (gram word L i) = vertexAt word L (i + 1) := by
  constructor
  · rfl
  · funext j
    change word (i + (j.val + 1)) = word (i + 1 + j.val)
    congr 1
    omega

/-- Equality of actual spectra recovers the finite word; no uniqueness of z is assumed. -/
theorem equal_spectrum_recovers_word (word z : Letters) (n L : ℕ)
    (hL : 1 ≤ L) (hn : L ≤ n) (hunique : KUnique word n (L - 1))
    (hspectrum : wordSpectrum z n L = wordSpectrum word n L) :
    Agree z 0 word 0 n := by
  have hwindows : ∀ i, i ≤ n - L → WordPaths.Occurs word n z i L := by
    intro i hi
    have hibound : i + L ≤ n := by omega
    have hz : wordSpectrum z n L (gram z L i) ≠ 0 :=
      ne_of_gt (spectrum_at_occurrence_positive z n L i (gram z L i) hibound rfl)
    have hy : wordSpectrum word n L (gram z L i) ≠ 0 := by
      rw [← hspectrum]
      exact hz
    obtain ⟨a, ha, hgram⟩ := wordSpectrum_nonzero_occurs word n L (gram z L i) hy
    exact ⟨a, ha, (gram_eq_iff_agree word z L a i).mp hgram⟩
  obtain ⟨a, ha, hagree⟩ := WordPaths.all_windows_occur_implies_subword
    word z n (L - 1) L (n - L) hunique (by omega) hwindows
  have hlength : L + (n - L) = n := by omega
  rw [hlength] at ha hagree
  have ha0 : a = 0 := by omega
  subst a
  intro i hi
  exact (hagree i hi).symm

/-- In the finite-word representation, equal spectra give literal word equality. -/
theorem equal_spectrum_eq_finite (word z : Letters) (n L : ℕ)
    (hL : 1 ≤ L) (hn : L ≤ n) (hunique : KUnique word n (L - 1))
    (hspectrum : wordSpectrum z n L = wordSpectrum word n L) :
    (fun i : Fin n => z i.val) = (fun i : Fin n => word i.val) := by
  funext i
  simpa only [Nat.zero_add] using
    equal_spectrum_recovers_word word z n L hL hn hunique hspectrum i.val i.isLt

/-- Manuscript Lemma `lem:path`, stated with actual counts, path vertices, and edge labels. -/
theorem spectrum_is_simple_path_and_determines_word (word : Letters) (n L : ℕ)
    (hL : 1 ≤ L) (hn : L ≤ n) (hunique : KUnique word n (L - 1)) :
    (∀ g, wordSpectrum word n L g = 0 ∨ wordSpectrum word n L g = 1) ∧
    Function.Injective (fun i : Fin (n - L + 2) => vertexAt word L i.val) ∧
    (∀ g, wordSpectrum word n L g ≠ 0 ↔ ∃ i : Fin (n - L + 1), gram word L i.val = g) ∧
    (∀ i : Fin (n - L + 1),
      gramPrefix (gram word L i.val) = vertexAt word L i.val ∧
      gramSuffix (gram word L i.val) = vertexAt word L (i.val + 1)) ∧
    (∀ z : Letters, wordSpectrum z n L = wordSpectrum word n L → Agree z 0 word 0 n) := by
  exact ⟨spectrum_boolean word n L hunique,
    vertex_path_injective word n L hL hn hunique,
    spectrum_support_path word n L hn,
    fun i => path_edge_endpoints word L i.val,
    fun z h => equal_spectrum_recovers_word word z n L hL hn hunique h⟩

/-- Uniqueness of shorter windows implies uniqueness of every longer window. -/
theorem kunique_mono (word : Letters) (n k m : ℕ)
    (hunique : KUnique word n k) (hkm : k ≤ m) : KUnique word n m := by
  intro a b ha hb hagree
  apply hunique a b (by omega) (by omega)
  intro i hi
  exact hagree i (by omega)

/-- The paper's k-uniqueness hypothesis suffices at its chosen L=3(k+1). -/
theorem catalogue_window_spectrum (word : Letters) (n k : ℕ)
    (hunique : KUnique word n k) (hn : HeaderRecovery.windowLength k ≤ n) :
    let L := HeaderRecovery.windowLength k
    (∀ g, wordSpectrum word n L g = 0 ∨ wordSpectrum word n L g = 1) ∧
    Function.Injective (fun i : Fin (n - L + 2) => vertexAt word L i.val) ∧
    (∀ g, wordSpectrum word n L g ≠ 0 ↔ ∃ i : Fin (n - L + 1), gram word L i.val = g) ∧
    (∀ i : Fin (n - L + 1),
      gramPrefix (gram word L i.val) = vertexAt word L i.val ∧
      gramSuffix (gram word L i.val) = vertexAt word L (i.val + 1)) ∧
    (∀ z : Letters, wordSpectrum z n L = wordSpectrum word n L → Agree z 0 word 0 n) := by
  have hlarge : k ≤ HeaderRecovery.windowLength k - 1 := by
    dsimp [HeaderRecovery.windowLength]
    omega
  exact spectrum_is_simple_path_and_determines_word word n (HeaderRecovery.windowLength k)
    (by dsimp [HeaderRecovery.windowLength]; omega) hn
    (kunique_mono word n k (HeaderRecovery.windowLength k - 1) hunique hlarge)

#print axioms spectrum_at_occurrence_positive
#print axioms spectrum_boolean
#print axioms vertex_path_injective
#print axioms spectrum_support_path
#print axioms equal_spectrum_recovers_word
#print axioms equal_spectrum_eq_finite
#print axioms spectrum_is_simple_path_and_determines_word
#print axioms kunique_mono
#print axioms catalogue_window_spectrum

end DeletionCode.SpectrumPath
