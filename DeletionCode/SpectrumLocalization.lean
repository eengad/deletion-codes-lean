import DeletionCode.CatalogueWords
import DeletionCode.SignedSupport
import Mathlib.Algebra.BigOperators.Fin

/-!
Locality of actual integer spectra. Windows in a word split into those
before a local substring, those inside it, and those starting in its final
L-1 letters. Equal boundary words make the two exterior sums cancel.
No uniqueness or bubble geometry is needed for this cancellation identity.
-/
namespace DeletionCode.SpectrumLocalization

open Windows SignedSupport CatalogueWords
open scoped BigOperators

noncomputable def windowSum (x : Letters) (L start count : ℕ) (g : Gram L) : ℤ := by
  classical
  exact ∑ i ∈ Finset.range count, if gram x L (start + i) = g then 1 else 0

/-- The guarded finite-word spectrum counts exactly the valid start positions. -/
theorem wordSpectrum_eq_windowSum (x : Letters) (n L : ℕ) (hL : L ≤ n + 1)
    (g : Gram L) : wordSpectrum x n L g = windowSum x L 0 (n + 1 - L) g := by
  classical
  unfold wordSpectrum windowSum
  rw [Fin.sum_univ_eq_sum_range
    (fun i => if i + L ≤ n ∧ gram x L i = g then (1 : ℤ) else 0) (n + 1)]
  have hsub : Finset.range (n + 1 - L) ⊆ Finset.range (n + 1) :=
    Finset.range_mono (by omega)
  rw [← Finset.sum_subset hsub (by
    intro i _ hi
    have hib : ¬ i < n + 1 - L := by simpa only [Finset.mem_range] using hi
    have hbad : ¬ i + L ≤ n := by omega
    simp only [hbad, false_and, ite_false])]
  apply Finset.sum_congr rfl
  intro i hi
  have hib := Finset.mem_range.mp hi
  have hgood : i + L ≤ n := by omega
  simp only [hgood, true_and, Nat.zero_add]

theorem windowSum_add (x : Letters) (L start a b : ℕ) (g : Gram L) :
    windowSum x L start (a + b) g =
      windowSum x L start a g + windowSum x L (start + a) b g := by
  classical
  unfold windowSum
  rw [Finset.sum_range_add]
  simp only [Nat.add_assoc]

theorem windowSum_shift (x : Letters) (L a count : ℕ) (g : Gram L) :
    windowSum x L a count g = windowSum (fun i => x (a + i)) L 0 count g := by
  classical
  unfold windowSum
  apply Finset.sum_congr rfl
  intro i _
  have hgram : gram x L (a + i) = gram (fun j => x (a + j)) L (0 + i) := by
    funext j
    simp only [SignedSupport.gram, Nat.zero_add, Nat.add_assoc]
  rw [hgram]

/-- All windows split at the two ends of the local path's edge interval. -/
theorem spectrum_split (x : Letters) (a p b L : ℕ) (hp : L ≤ p + 1) (g : Gram L) :
    wordSpectrum x (a + p + b) L g =
      windowSum x L 0 a g + wordSpectrum (fun i => x (a + i)) p L g +
        windowSum x L (a + (p + 1 - L)) b g := by
  rw [wordSpectrum_eq_windowSum x _ L (by omega),
    wordSpectrum_eq_windowSum _ p L hp]
  have hcount : a + p + b + 1 - L = (a + (p + 1 - L)) + b := by omega
  rw [hcount, windowSum_add, windowSum_add]
  simp only [Nat.zero_add, windowSum_shift x L a]

theorem windowSum_congr (x y : Letters) (L a b count : ℕ) (g : Gram L)
    (h : ∀ i, i < count → gram x L (a + i) = gram y L (b + i)) :
    windowSum x L a count g = windowSum y L b count g := by
  classical
  unfold windowSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (Finset.mem_range.mp hi)]

/-- A replacement with the same prefix and suffix of length L-1 has the
same spectrum change as its local words. Exterior lengths may be arbitrary. -/
theorem replacement (x y : Letters) (a p q b L : ℕ) (hL : 1 ≤ L)
    (hp : L ≤ p + 1) (hq : L ≤ q + 1)
    (hleft : Agree x 0 y 0 (a + (L - 1)))
    (hright : Agree x (a + (p + 1 - L)) y (a + (q + 1 - L)) (b + (L - 1)))
    (g : Gram L) :
    wordSpectrum y (a + q + b) L g - wordSpectrum x (a + p + b) L g =
      wordSpectrum (fun i => y (a + i)) q L g -
        wordSpectrum (fun i => x (a + i)) p L g := by
  have hbefore : windowSum x L 0 a g = windowSum y L 0 a g := by
    apply windowSum_congr
    intro i hi
    apply (gram_eq_iff_agree _ _ _ _ _).mpr
    intro j hj
    simpa only [Nat.zero_add] using hleft (i + j) (by omega)
  have hafter : windowSum x L (a + (p + 1 - L)) b g =
      windowSum y L (a + (q + 1 - L)) b g := by
    apply windowSum_congr
    intro i hi
    apply (gram_eq_iff_agree _ _ _ _ _).mpr
    intro j hj
    simpa only [Nat.add_assoc] using hright (i + j) (by omega)
  rw [spectrum_split x a p b L hp, spectrum_split y a q b L hq, hbefore, hafter]
  omega

theorem listLetters_append_left (x y : List Bool) (i : ℕ) (hi : i < x.length) :
    listLetters (x ++ y) i = listLetters x i := by
  simp only [listLetters, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hi]

theorem listLetters_append_right (x y : List Bool) (i : ℕ) :
    listLetters (x ++ y) (x.length + i) = listLetters y i := by
  simp only [listLetters, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem listLetters_middle (x p y : List Bool) (i : ℕ) (hi : i < p.length) :
    listLetters (x ++ (p ++ y)) (x.length + i) = listLetters p i := by
  rw [listLetters_append_right, listLetters_append_left p y i hi]

theorem listLetters_suffix (x p y : List Bool) (i : ℕ) :
    listLetters (x ++ (p ++ y)) (x.length + p.length + i) = listLetters y i := by
  rw [Nat.add_assoc, listLetters_append_right, listLetters_append_right]

theorem wordSpectrum_congr (x y : Letters) (n L : ℕ)
    (h : ∀ i, i < n → x i = y i) (g : Gram L) :
    wordSpectrum x n L g = wordSpectrum y n L g := by
  classical
  unfold wordSpectrum
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val + L ≤ n
  · have hgram : gram x L i.val = gram y L i.val := by
      funext j
      exact h (i.val + j.val) (by have := j.isLt; omega)
    rw [hgram]
  · simp only [hi, false_and, ite_false]

/-- Concrete unchanged exterior words cancel when the local words share
their first and last L-1 letters, exactly as in the coverage proof. -/
theorem context_replacement (x p q y : List Bool) (L : ℕ) (hL : 1 ≤ L)
    (hp : L ≤ p.length + 1) (hq : L ≤ q.length + 1)
    (hprefix : Agree (listLetters p) 0 (listLetters q) 0 (L - 1))
    (hsuffix : Agree (listLetters p) (p.length + 1 - L)
      (listLetters q) (q.length + 1 - L) (L - 1)) (g : Gram L) :
    wordSpectrum (listLetters (x ++ (q ++ y))) (x.length + q.length + y.length) L g -
      wordSpectrum (listLetters (x ++ (p ++ y))) (x.length + p.length + y.length) L g =
      wordSpectrum (listLetters q) q.length L g - wordSpectrum (listLetters p) p.length L g := by
  have hleft : Agree (listLetters (x ++ (p ++ y))) 0
      (listLetters (x ++ (q ++ y))) 0 (x.length + (L - 1)) := by
    intro i hi
    simp only [Nat.zero_add]
    by_cases hix : i < x.length
    · rw [listLetters_append_left x (p ++ y) i hix,
        listLetters_append_left x (q ++ y) i hix]
    · have heq : i = x.length + (i - x.length) := by omega
      rw [heq, listLetters_middle x p y _ (by omega),
        listLetters_middle x q y _ (by omega)]
      simpa only [Nat.zero_add] using hprefix (i - x.length) (by omega)
  have hright : Agree (listLetters (x ++ (p ++ y))) (x.length + (p.length + 1 - L))
      (listLetters (x ++ (q ++ y))) (x.length + (q.length + 1 - L))
      (y.length + (L - 1)) := by
    intro i hi
    by_cases hlocal : i < L - 1
    · rw [Nat.add_assoc, Nat.add_assoc,
        listLetters_middle x p y _ (by omega), listLetters_middle x q y _ (by omega)]
      exact hsuffix i hlocal
    · have hpindex : x.length + (p.length + 1 - L) + i =
          x.length + p.length + (i - (L - 1)) := by omega
      have hqindex : x.length + (q.length + 1 - L) + i =
          x.length + q.length + (i - (L - 1)) := by omega
      rw [hpindex, hqindex, listLetters_suffix, listLetters_suffix]
  have h := replacement (listLetters (x ++ (p ++ y))) (listLetters (x ++ (q ++ y)))
    x.length p.length q.length y.length L hL hp hq hleft hright g
  rw [wordSpectrum_congr _ (listLetters q) q.length L
      (fun i hi => listLetters_middle x q y i hi),
    wordSpectrum_congr _ (listLetters p) p.length L
      (fun i hi => listLetters_middle x p y i hi)] at h
  exact h

#print axioms wordSpectrum_eq_windowSum
#print axioms spectrum_split
#print axioms replacement
#print axioms context_replacement

end DeletionCode.SpectrumLocalization
