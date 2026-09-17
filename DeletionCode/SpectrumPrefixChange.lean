import DeletionCode.SpectrumLocalization

/-!
Changing a local word with an unchanged initial L-1 letters has a spectrum
increment independent of any earlier prefix. This one-sided cancellation
is the local identity used when telescoping an actual alignment trace.
-/
namespace DeletionCode.SpectrumPrefixChange

open Windows CatalogueWords SignedSupport SpectrumLocalization

noncomputable def spectrum (word : List Bool) (L : ℕ) : Gram L → ℤ :=
  wordSpectrum (listLetters word) word.length L

private theorem windowSum_zero (x : Letters) (L start : ℕ) (g : Gram L) :
    windowSum x L start 0 g = 0 := by simp [windowSum]

theorem spectrum_append (pre p : List Bool) (L : ℕ) (hp : L ≤ p.length + 1)
    (g : Gram L) :
    spectrum (pre ++ p) L g =
      windowSum (listLetters (pre ++ p)) L 0 pre.length g + spectrum p L g := by
  have h := spectrum_split (listLetters (pre ++ p)) pre.length p.length 0 L hp g
  rw [wordSpectrum_congr _ (listLetters p) p.length L
    (fun i _ => listLetters_append_right pre p i)] at h
  simpa only [spectrum, List.length_append, Nat.add_zero, windowSum_zero, add_zero] using h

/-- Only the first L-1 letters can affect windows starting before a local word. -/
theorem prefix_change (pre p q : List Bool) (L : ℕ) (hL : 1 ≤ L)
    (hp : L ≤ p.length + 1) (hq : L ≤ q.length + 1)
    (hprefix : Agree (listLetters p) 0 (listLetters q) 0 (L - 1)) (g : Gram L) :
    spectrum (pre ++ q) L g - spectrum (pre ++ p) L g =
      spectrum q L g - spectrum p L g := by
  have hbefore : windowSum (listLetters (pre ++ p)) L 0 pre.length g =
      windowSum (listLetters (pre ++ q)) L 0 pre.length g := by
    apply windowSum_congr
    intro i hi
    apply (gram_eq_iff_agree _ _ _ _ _).mpr
    intro j hj
    simp only [Nat.zero_add]
    by_cases hpre : i + j < pre.length
    · rw [listLetters_append_left pre p _ hpre, listLetters_append_left pre q _ hpre]
    · have hindex : i + j = pre.length + (i + j - pre.length) := by omega
      rw [hindex, listLetters_append_right, listLetters_append_right]
      simpa only [Nat.zero_add] using hprefix (i + j - pre.length) (by omega)
  rw [spectrum_append pre q L hq, spectrum_append pre p L hp, hbefore]
  omega

theorem common_prefix (common p q : List Bool) (L : ℕ)
    (hcommon : L - 1 ≤ common.length) :
    Agree (listLetters (common ++ p)) 0 (listLetters (common ++ q)) 0 (L - 1) := by
  intro i hi
  simp only [Nat.zero_add]
  rw [listLetters_append_left common p i (by omega),
    listLetters_append_left common q i (by omega)]

/-- An edit after a common long enough suffix has the same increment for
both earlier prefixes. No condition on the words following the edit is needed. -/
theorem common_suffix_change (a b common p q : List Bool) (L : ℕ) (hL : 1 ≤ L)
    (hcommon : L - 1 ≤ common.length) (g : Gram L) :
    spectrum ((b ++ common) ++ q) L g - spectrum ((b ++ common) ++ p) L g =
      spectrum ((a ++ common) ++ q) L g - spectrum ((a ++ common) ++ p) L g := by
  have hp : L ≤ (common ++ p).length + 1 := by
    simp only [List.length_append]
    omega
  have hq : L ≤ (common ++ q).length + 1 := by
    simp only [List.length_append]
    omega
  simp only [List.append_assoc]
  rw [prefix_change b _ _ L hL hp hq (common_prefix common p q L hcommon),
    prefix_change a _ _ L hL hp hq (common_prefix common p q L hcommon)]

#print axioms spectrum_append
#print axioms prefix_change
#print axioms common_suffix_change

end DeletionCode.SpectrumPrefixChange
