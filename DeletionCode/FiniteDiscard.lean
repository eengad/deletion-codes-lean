import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Finiteness

/-!
A finite averaging argument for discarding vertices. If each vertex has bad
event of probability at most one third, some outcome retains at least half
the vertices. The final theorem allows arbitrary events: measurable envelopes
have the same measure and can only decrease the retained set.
-/

namespace DeletionCode.FiniteDiscard

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {Ω V : Type*} [MeasurableSpace Ω] [DecidableEq V]

omit [DecidableEq V] in
/-- The averaging step for measurable bad events. -/
theorem exists_half_retained_of_measurable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset V) (E : V → Set Ω)
    (hmeas : ∀ v ∈ s, MeasurableSet (E v))
    (hE : ∀ v ∈ s, μ (E v) ≤ ENNReal.ofReal (1 / 3 : ℝ)) :
    ∃ ω, s.card ≤ 2 * (s.filter (fun v => ω ∉ E v)).card := by
  classical
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  by_cases hs : s.card = 0
  · exact ⟨ω₀, by simp only [hs, Nat.zero_le]⟩
  have hspos : 0 < s.card := Nat.pos_of_ne_zero hs
  let f : Ω → ℝ≥0∞ := fun ω => ∑ v ∈ s, (E v).indicator (fun _ => (1 : ℝ≥0∞)) ω
  have hcount (ω : Ω) : f ω = ((s.filter (fun v => ω ∈ E v)).card : ℝ≥0∞) := by
    simp [f, Set.indicator]
  have hupper : (∫⁻ ω, f ω ∂μ) ≤ (s.card : ℝ≥0∞) * ENNReal.ofReal (1 / 3 : ℝ) := by
    dsimp only [f]
    rw [lintegral_finsetSum s (fun v hv => measurable_const.indicator (hmeas v hv))]
    calc
      _ ≤ ∑ _v ∈ s, ENNReal.ofReal (1 / 3 : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        rw [lintegral_indicator_const (hmeas v hv), one_mul]
        exact hE v hv
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  by_contra hnone
  have hpoint (ω : Ω) : (s.card : ℝ≥0∞) ≤ 2 * f ω := by
    rw [hcount]
    have hgood : 2 * (s.filter (fun v => ω ∉ E v)).card < s.card :=
      Nat.lt_of_not_ge (fun h => hnone ⟨ω, h⟩)
    have hpartition := Finset.card_filter_add_card_filter_not (s := s) (fun v => ω ∈ E v)
    have hnat : s.card ≤ 2 * (s.filter (fun v => ω ∈ E v)).card := by omega
    exact_mod_cast hnat
  have hlower : (s.card : ℝ≥0∞) ≤ 2 * ∫⁻ ω, f ω ∂μ := by
    calc
      _ = ∫⁻ _ω, (s.card : ℝ≥0∞) ∂μ := by simp
      _ ≤ ∫⁻ ω, 2 * f ω ∂μ := lintegral_mono hpoint
      _ = _ := lintegral_const_mul' 2 f (by norm_num)
  have hfinal := hlower.trans (mul_le_mul' (show (2 : ℝ≥0∞) ≤ 2 from le_rfl) hupper)
  have hreal := ENNReal.toReal_mono (by finiteness) hfinal
  norm_num at hreal
  have hsreal : (0 : ℝ) < s.card := Nat.cast_pos.mpr hspos
  nlinarith

omit [DecidableEq V] in
/-- No measurability hypothesis is imposed on the bad events. A probability
space supplies an outcome even when the finite vertex set is empty. -/
theorem exists_half_retained (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset V) (E : V → Set Ω)
    (hE : ∀ v ∈ s, μ (E v) ≤ ENNReal.ofReal (1 / 3 : ℝ)) :
    ∃ ω, s.card ≤ 2 * (s.filter (fun v => ω ∉ E v)).card := by
  classical
  let T : V → Set Ω := fun v => toMeasurable μ (E v)
  have hT (v : V) (hv : v ∈ s) : μ (T v) ≤ ENNReal.ofReal (1 / 3 : ℝ) := by
    simpa only [T, measure_toMeasurable] using hE v hv
  obtain ⟨ω, hω⟩ := exists_half_retained_of_measurable μ s T
    (fun v _ => measurableSet_toMeasurable μ (E v)) hT
  refine ⟨ω, hω.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))⟩
  intro v hv
  obtain ⟨hvs, hnot⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hvs, fun hmem => hnot ((subset_toMeasurable μ (E v)) hmem)⟩

#print axioms exists_half_retained_of_measurable
#print axioms exists_half_retained

end

end DeletionCode.FiniteDiscard
