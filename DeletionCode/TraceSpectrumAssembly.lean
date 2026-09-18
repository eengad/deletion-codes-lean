import DeletionCode.TraceEditData
import DeletionCode.TraceMatchedSuffix
import DeletionCode.SpectrumPrefixChange

/-!
The spectrum change of an actual separated alignment is the sum of the
changes made by its edit columns individually on the original source.
The proof telescopes concrete hybrid words. Separation derives a common
matched suffix before each edit, so prefix cancellation identifies every
increment with the corresponding isolated original-source edit.
-/
namespace DeletionCode.TraceSpectrumAssembly

open AlignmentTrace FiniteConflictGraph TraceEditData SignedSupport
open SpectrumPrefixChange TraceMatchedSuffix
open scoped BigOperators

/-- The first j columns have been performed; the unprocessed suffix still
contributes its original source letters. -/
def hybrid (trace : Trace) (j : ℕ) : List Bool :=
  Trace.target (trace.take j) ++ Trace.source (trace.drop j)

theorem hybrid_zero (trace : Trace) : hybrid trace 0 = trace.source := by
  simp [hybrid, Trace.target]

theorem hybrid_end (trace : Trace) : hybrid trace trace.length = trace.target := by
  simp [hybrid, Trace.source]

theorem hybrid_before (trace : Trace) (i : Fin trace.length) :
    hybrid trace i.val = Trace.target (trace.take i.val) ++
      (Trace.source [trace.get i] ++ Trace.source (trace.drop (i.val + 1))) := by
  unfold hybrid
  have hdrop : trace.drop i.val = trace.get i :: trace.drop (i.val + 1) :=
    List.drop_eq_getElem_cons i.isLt
  rw [hdrop]
  congr 1
  exact Trace.source_append [trace.get i] (trace.drop (i.val + 1))

theorem hybrid_after (trace : Trace) (i : Fin trace.length) :
    hybrid trace (i.val + 1) =
      (Trace.target (trace.take i.val) ++ Trace.target [trace.get i]) ++
        Trace.source (trace.drop (i.val + 1)) := by
  unfold hybrid
  rw [List.take_succ_eq_append_getElem i.isLt, Trace.target_append]
  rfl

/-- Matched columns contribute zero, derived from their actual projections. -/
theorem hybrid_increment_of_not_edit (trace : Trace) (i : Fin trace.length)
    (hnot : ¬ EditIndex trace i) (L : ℕ) (g : Gram L) :
    spectrum (hybrid trace (i.val + 1)) L g - spectrum (hybrid trace i.val) L g = 0 := by
  cases hc : trace.get i with
  | matched bit =>
    rw [hybrid_after, hybrid_before, hc]
    simp only [Trace.source, Trace.target, List.append_assoc, List.singleton_append, sub_self]
  | deletion bit =>
    exact False.elim (hnot (by simp only [EditIndex, hc, Column.isEdit]))
  | insertion bit =>
    exact False.elim (hnot (by simp only [EditIndex, hc, Column.isEdit]))
  | substitution bit =>
    exact False.elim (hnot (by simp only [EditIndex, hc, Column.isEdit]))

/-- A separated edit's hybrid increment equals its actual isolated edit
on the original source. The common suffix is derived from the trace. -/
theorem hybrid_increment_of_edit {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (c : EditColumn trace) (g : Gram L) :
    spectrum (hybrid trace (c.val.val + 1)) L g - spectrum (hybrid trace c.val.val) L g =
      spectrum (oneEditTarget trace c) L g - spectrum trace.source L g := by
  obtain ⟨a, b, common, hs, ht, hcommon⟩ := common_suffix_before_edit hL hsep c.val c.property
  change sourcePrefix trace c = a ++ common at hs
  change targetPrefix trace c = b ++ common at ht
  rcases column_cases trace c with ⟨bit, hc⟩ | ⟨bit, hc⟩ | ⟨bit, hc⟩
  · have hc' : trace.get c.val = .deletion bit := hc
    have hbefore : hybrid trace c.val.val = targetPrefix trace c ++ bit :: sourceSuffix trace c := by
      simpa only [targetPrefix, sourceSuffix, hc', Trace.source, List.singleton_append] using
        hybrid_before trace c.val
    have hafter : hybrid trace (c.val.val + 1) = targetPrefix trace c ++ sourceSuffix trace c := by
      simpa only [targetPrefix, sourceSuffix, hc', Trace.target, List.append_nil] using
        hybrid_after trace c.val
    rw [hbefore, hafter, oneEditTarget_deletion_split trace c bit hc,
      source_split_of_deletion trace c bit hc, hs, ht]
    exact common_suffix_change a b common (bit :: sourceSuffix trace c)
      (sourceSuffix trace c) L hL hcommon g
  · have hc' : trace.get c.val = .insertion bit := hc
    have hbefore : hybrid trace c.val.val = targetPrefix trace c ++ sourceSuffix trace c := by
      simpa only [targetPrefix, sourceSuffix, hc', Trace.source, List.nil_append] using
        hybrid_before trace c.val
    have hafter : hybrid trace (c.val.val + 1) = targetPrefix trace c ++ bit :: sourceSuffix trace c := by
      simpa only [targetPrefix, sourceSuffix, hc', Trace.target, List.append_assoc,
        List.singleton_append] using hybrid_after trace c.val
    rw [hbefore, hafter, oneEditTarget_insertion_split trace c bit hc,
      source_split_of_insertion trace c bit hc, hs, ht]
    exact common_suffix_change a b common (sourceSuffix trace c)
      (bit :: sourceSuffix trace c) L hL hcommon g
  · have hc' : trace.get c.val = .substitution bit := hc
    have hbefore : hybrid trace c.val.val = targetPrefix trace c ++ bit :: sourceSuffix trace c := by
      simpa only [targetPrefix, sourceSuffix, hc', Trace.source, List.singleton_append] using
        hybrid_before trace c.val
    have hafter : hybrid trace (c.val.val + 1) =
        targetPrefix trace c ++ (!bit) :: sourceSuffix trace c := by
      simpa only [targetPrefix, sourceSuffix, hc', Trace.target, List.append_assoc,
        List.singleton_append] using hybrid_after trace c.val
    rw [hbefore, hafter, oneEditTarget_substitution_split trace c bit hc,
      source_split_of_substitution trace c bit hc, hs, ht]
    exact common_suffix_change a b common (bit :: sourceSuffix trace c)
      ((!bit) :: sourceSuffix trace c) L hL hcommon g

/-- Exact telescoping over every actual column; no separation is needed yet. -/
theorem hybrid_telescope (trace : Trace) (L : ℕ) (g : Gram L) :
    spectrum trace.target L g - spectrum trace.source L g =
      ∑ i : Fin trace.length,
        (spectrum (hybrid trace (i.val + 1)) L g - spectrum (hybrid trace i.val) L g) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun i => spectrum (hybrid trace (i + 1)) L g - spectrum (hybrid trace i) L g) trace.length]
  simpa only [hybrid_zero, hybrid_end] using
    (Finset.sum_range_sub (fun i => spectrum (hybrid trace i) L g) trace.length).symm

/-- The full trace's spectrum difference is the sum of isolated edit
differences, indexed by its actual deletion, insertion and substitution columns. -/
theorem spectrum_sum_apply {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (g : Gram L) :
    spectrum trace.target L g - spectrum trace.source L g =
      ∑ c : EditColumn trace,
        (spectrum (oneEditTarget trace c) L g - spectrum trace.source L g) := by
  classical
  let : Fintype {i : Fin trace.length // EditIndex trace i} := editColumnFintype trace
  let F : Fin trace.length → ℤ := fun i =>
    spectrum (hybrid trace (i.val + 1)) L g - spectrum (hybrid trace i.val) L g
  have hrestrict : (∑ i : Fin trace.length, F i) = ∑ c : EditColumn trace, F c.val := by
    change _ = ∑ c : {i : Fin trace.length // EditIndex trace i}, F c.val
    rw [← Finset.sum_subtype (Finset.univ.filter (fun i => EditIndex trace i)) (by simp) F]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hnot
    apply hybrid_increment_of_not_edit trace i _ L g
    intro hi
    exact hnot (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi)
  calc
    spectrum trace.target L g - spectrum trace.source L g = ∑ i : Fin trace.length, F i :=
      hybrid_telescope trace L g
    _ = ∑ c : EditColumn trace, F c.val := hrestrict
    _ = ∑ c : EditColumn trace,
        (spectrum (oneEditTarget trace c) L g - spectrum trace.source L g) := by
      apply Finset.sum_congr rfl
      intro c _
      exact hybrid_increment_of_edit hL hsep c g

/-- The actual signed integer vector identity used to assemble the
separated-edit catalogue. No uniqueness or spectrum-sum premise is required. -/
theorem spectrum_sum {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) :
    wordSpectrum (CatalogueWords.listLetters trace.target) trace.target.length L -
      wordSpectrum (CatalogueWords.listLetters trace.source) trace.source.length L =
      ∑ c : EditColumn trace,
        (wordSpectrum (CatalogueWords.listLetters (oneEditTarget trace c))
            (oneEditTarget trace c).length L -
          wordSpectrum (CatalogueWords.listLetters trace.source) trace.source.length L) := by
  funext g
  simp only [Pi.sub_apply, Finset.sum_apply]
  exact spectrum_sum_apply hL hsep g

#print axioms hybrid_increment_of_edit
#print axioms hybrid_telescope
#print axioms spectrum_sum_apply
#print axioms spectrum_sum

end DeletionCode.TraceSpectrumAssembly
