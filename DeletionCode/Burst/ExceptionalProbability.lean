import DeletionCode.Burst.WordHash
import DeletionCode.Burst.ExceptionalCountArithmetic
import DeletionCode.Qary.ExceptionalProbability

/-!
Exceptional partners are actual length-n words admitting short or
nonseparated chronological burst scripts. Their finite cover is independent
of the random weights; uniqueness is required only of the source word.
-/
namespace DeletionCode.Burst.ExceptionalProbability

open MeasureTheory DeletionCode.Qary.Windows DeletionCode.Qary.HeaderRecovery
open DeletionCode.Qary.SignedSupport DeletionCode.CircleHash DeletionCode.CircleUniform
open ConflictGraphWitness FiniteConflictGraph
open scoped BigOperators

variable {α : Type*} [Fintype α] [Inhabited α] {n : ℕ}

noncomputable def candidatePartners (b t k : ℕ) (x : Bits α n) : Finset (Bits α n) := by
  classical
  exact Finset.univ.filter (CandidatePartner b t k x)

@[simp] theorem mem_candidatePartners (b t k : ℕ) (x y : Bits α n) :
    y ∈ candidatePartners b t k x ↔ CandidatePartner b t k x y := by
  classical
  simp only [candidatePartners, Finset.mem_filter, Finset.mem_univ, true_and]

theorem candidatePartners_card_le (b t k : ℕ) (x : Bits α n) (hn : 1 ≤ n) :
    (candidatePartners b t k x).card ≤
      ExceptionalCountArithmetic.constant t b * Fintype.card α ^ (2 * b * t) *
        windowLength k b * n ^ (2 * t - 1) := by
  classical
  have hcover : (candidatePartners b t k x).card ≤
      (ExceptionalRecords.words b t n (8 * (windowLength k b + t * b)) (List.ofFn x)).card := by
    apply Finset.card_le_card_of_injOn List.ofFn
    · intro y hy
      exact ExceptionalRecords.mem_words (by simp)
        (by unfold windowLength; nlinarith) ((mem_candidatePartners b t k x y).mp hy).2
    · intro y hy z hz heq
      exact List.ofFn_injective heq
  exact hcover.trans (ExceptionalCountArithmetic.words_card_le n t b (windowLength k b)
    (List.ofFn x) Fintype.card_pos hn (by unfold windowLength; omega))

noncomputable def collisionEvent (b k Q : ℕ) (x y : Bits α n) :
    Set (Gram α (windowLength k b) → ℝ) :=
  {weights | wordLabel Q (realWeightedHash weights) x =
    wordLabel Q (realWeightedHash weights) y}

noncomputable def exceptionalEvent (b t k Q : ℕ) (x : Bits α n) :
    Set (Gram α (windowLength k b) → ℝ) :=
  {weights | FiniteConflictGraph.Exceptional b t k (wordLabel Q (realWeightedHash weights)) x}

theorem collision_probability_le (b k Q : ℕ) (x y : Bits α n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k b ≤ n)
    (hQ : 2 ≤ Q) (hxy : x ≠ y) :
    realWeights (Gram α (windowLength k b)) (collisionEvent b k Q x y) ≤
      ENNReal.ofReal (2 / (Q : ℝ)) := by
  exact Qary.ExceptionalProbability.collision_probability_le (k + b) Q x y
    (Qary.SpectrumPath.kunique_mono _ _ k (k + b) hx (by omega)) hn hQ hxy

theorem exceptionalEvent_eq_union (b t k Q : ℕ) (x : Bits α n) :
    exceptionalEvent b t k Q x =
      ⋃ y ∈ candidatePartners b t k x, collisionEvent b k Q x y := by
  ext weights
  simp only [exceptionalEvent, collisionEvent, FiniteConflictGraph.Exceptional, Set.mem_ofPred_eq,
    Set.mem_iUnion, mem_candidatePartners, exists_prop]

theorem exceptional_probability_le (b t k Q : ℕ) (x : Bits α n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k b ≤ n) (hQ : 2 ≤ Q) :
    realWeights (Gram α (windowLength k b)) (exceptionalEvent b t k Q x) ≤
      (candidatePartners b t k x).card * ENNReal.ofReal (2 / (Q : ℝ)) := by
  classical
  rw [exceptionalEvent_eq_union]
  calc
    _ ≤ ∑ y ∈ candidatePartners b t k x,
        realWeights (Gram α (windowLength k b)) (collisionEvent b k Q x y) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ candidatePartners b t k x, ENNReal.ofReal (2 / (Q : ℝ)) := by
      apply Finset.sum_le_sum
      intro y hy
      exact collision_probability_le b k Q x y hx hn hQ
        ((mem_candidatePartners b t k x y).mp hy).1
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem exceptional_measure_le (b t k Q : ℕ) (x : Bits α n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k b ≤ n) (hQ : 2 ≤ Q) :
    realWeights (Gram α (windowLength k b)) (exceptionalEvent b t k Q x) ≤
      (ExceptionalCountArithmetic.constant t b * Fintype.card α ^ (2 * b * t) *
        windowLength k b * n ^ (2 * t - 1) : ℕ) * ENNReal.ofReal (2 / (Q : ℝ)) := by
  have hn' : 1 ≤ n := by unfold windowLength at hn; omega
  have hc : ((candidatePartners b t k x).card : ENNReal) ≤
      (ExceptionalCountArithmetic.constant t b * Fintype.card α ^ (2 * b * t) *
        windowLength k b * n ^ (2 * t - 1) : ℕ) := by
    exact_mod_cast candidatePartners_card_le b t k x hn'
  exact (exceptional_probability_le b t k Q x hx hn hQ).trans
    (mul_le_mul hc le_rfl (by positivity) (by positivity))

theorem exceptional_probability_bound (b t k Q : ℕ) (x : Bits α n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k b ≤ n) (hQ : 2 ≤ Q) :
    (realWeights (Gram α (windowLength k b)) (exceptionalEvent b t k Q x)).toReal ≤
      2 * (ExceptionalCountArithmetic.constant t b : ℝ) *
        (Fintype.card α : ℝ) ^ (2 * b * t) * (n : ℝ) ^ (2 * t - 1) *
          (windowLength k b : ℝ) / Q := by
  have h := exceptional_measure_le b t k Q x hx hn hQ
  have hfinite :
      ((ExceptionalCountArithmetic.constant t b * Fintype.card α ^ (2 * b * t) *
        windowLength k b * n ^ (2 * t - 1) : ℕ) : ENNReal) *
          ENNReal.ofReal (2 / (Q : ℝ)) ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono hfinite h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (div_nonneg (by norm_num) (Nat.cast_nonneg Q))] at hr
  convert hr using 1
  push_cast
  ring

end DeletionCode.Burst.ExceptionalProbability
