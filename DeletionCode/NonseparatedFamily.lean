import DeletionCode.ExceptionalPartnerCount

/-!
The full nonseparated-family lemma for the manuscript's actual exceptional
set and actual product of uniform real hash weights. Both the finite partner
count and the per-partner probability are proved from the concrete definitions.
-/
namespace DeletionCode.NonseparatedFamily

open MeasureTheory Windows HeaderRecovery SignedSupport CircleHash CircleUniform ConflictGraphWitness
open ExceptionalProbability ExceptionalPartnerCount ExceptionalCountArithmetic

theorem exceptional_measure_le {n : ℕ} (t k Q : ℕ) (x : Bits n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k ≤ n) (hQ : 2 ≤ Q) :
    realWeights (Gram (windowLength k)) (exceptionalEvent t k Q x) ≤
      (exceptionalConstant t * windowLength k * n ^ (2 * t - 1) : ℕ) *
        ENNReal.ofReal (2 / (Q : ℝ)) := by
  have hn' : 1 ≤ n := by unfold windowLength at hn; omega
  have hc : ((candidatePartners t k x).card : ENNReal) ≤
      (exceptionalConstant t * windowLength k * n ^ (2 * t - 1) : ℕ) := by
    exact_mod_cast candidatePartners_card_le t k x hn'
  exact (exceptional_probability_le t k Q x hx hn hQ).trans
    (mul_le_mul hc le_rfl (by positivity) (by positivity))

/-- Ordinary-real probability form, with an explicit constant depending only on t. -/
theorem exceptional_probability_bound {n : ℕ} (t k Q : ℕ) (x : Bits n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k ≤ n) (hQ : 2 ≤ Q) :
    (realWeights (Gram (windowLength k)) (exceptionalEvent t k Q x)).toReal ≤
      2 * (exceptionalConstant t : ℝ) * (n : ℝ) ^ (2 * t - 1) * (windowLength k : ℝ) / Q := by
  have h := exceptional_measure_le t k Q x hx hn hQ
  have hfinite :
      ((exceptionalConstant t * windowLength k * n ^ (2 * t - 1) : ℕ) : ENNReal) *
        ENNReal.ofReal (2 / (Q : ℝ)) ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono hfinite h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (div_nonneg (by norm_num) (Nat.cast_nonneg Q))] at hr
  convert hr using 1
  push_cast
  ring

/-- The manuscript's existence-of-a-constant formulation of `lem:nonsep`.
The global paper assumption n >= L is explicit, and target uniqueness is absent. -/
theorem nonseparated_family_thin (t : ℕ) (ht : 2 ≤ t) :
    ∃ c : ℕ, 0 < c ∧ ∀ (n k Q : ℕ) (x : Bits n),
      KUnique (padBits x) n k → windowLength k ≤ n → 2 ≤ Q →
        (realWeights (Gram (windowLength k))
          {weights | FiniteConflictGraph.Exceptional t k
            (wordLabel Q (realWeightedHash weights)) x}).toReal ≤
          2 * (c : ℝ) * (n : ℝ) ^ (2 * t - 1) * (windowLength k : ℝ) / Q := by
  refine ⟨exceptionalConstant t, exceptionalConstant_pos (by omega), ?_⟩
  intro n k Q x hx hn hQ
  exact exceptional_probability_bound t k Q x hx hn hQ

#print axioms exceptional_measure_le
#print axioms exceptional_probability_bound
#print axioms nonseparated_family_thin

end DeletionCode.NonseparatedFamily
