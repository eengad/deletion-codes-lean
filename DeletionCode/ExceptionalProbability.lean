import DeletionCode.RandomHash
import DeletionCode.ConflictGraphWitness
import DeletionCode.SpectrumPath

/-!
The probability part of the manuscript's exceptional-word estimate. The
finite candidate set records actual short or nonseparated balanced traces,
independently of the random weights. Source uniqueness implies that every
distinct candidate has a nonzero spectrum difference, even when the candidate
is not unique. A finite union bound then charges at most 2/Q per candidate.
The combinatorial bound on the number of candidates is a separate result.
-/
namespace DeletionCode.ExceptionalProbability

open MeasureTheory Windows HeaderRecovery SignedSupport CircleHash CircleUniform
open ConflictGraphWitness
open scoped BigOperators

variable {n : ℕ}

/-- Exactly the partner and bad-trace conditions in the exceptional set,
with no hash-label condition and no uniqueness condition on the partner. -/
def CandidatePartner (t k : ℕ) (x y : Bits n) : Prop :=
  x ≠ y ∧ ∃ trace : AlignmentTrace.Trace,
    trace.source = List.ofFn x ∧ trace.target = List.ofFn y ∧
    trace.deletions = trace.insertions ∧
    (2 * trace.deletions + trace.substitutions < 2 * t ∨
      (2 * trace.deletions + trace.substitutions = 2 * t ∧
        ¬ FiniteConflictGraph.Separated (4 * windowLength k) trace))

/-- A fixed finite set of binary partners, independent of Q and the weights. -/
noncomputable def candidatePartners (t k : ℕ) (x : Bits n) : Finset (Bits n) := by
  classical
  exact Finset.univ.filter (CandidatePartner t k x)

@[simp] theorem mem_candidatePartners (t k : ℕ) (x y : Bits n) :
    y ∈ candidatePartners t k x ↔ CandidatePartner t k x y := by
  classical
  simp only [candidatePartners, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The original exceptional predicate is precisely a label collision with
one of these fixed partners, when its source uniqueness condition holds. -/
theorem exceptional_iff_candidate {H : Type*} (t k : ℕ) (label : Bits n → H)
    (x : Bits n) (hx : KUnique (padBits x) n k) :
    FiniteConflictGraph.Exceptional t k label x ↔
      ∃ y ∈ candidatePartners t k x, label x = label y := by
  constructor
  · rintro ⟨_, y, hxy, hlabel, htrace⟩
    exact ⟨y, (mem_candidatePartners t k x y).mpr ⟨hxy, htrace⟩, hlabel⟩
  · rintro ⟨y, hy, hlabel⟩
    obtain ⟨hxy, htrace⟩ := (mem_candidatePartners t k x y).mp hy
    exact ⟨hx, y, hxy, hlabel, htrace⟩

/-- Actual finite-word spectrum injectivity requires uniqueness only of x. -/
theorem spectrum_difference_ne_zero (k : ℕ) (x y : Bits n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k ≤ n) (hxy : x ≠ y) :
    spectrum k y - spectrum k x ≠ 0 := by
  intro hzero
  have hs : wordSpectrum (padBits y) n (windowLength k) =
      wordSpectrum (padBits x) n (windowLength k) := sub_eq_zero.mp hzero
  have hlarge : k ≤ windowLength k - 1 := by
    dsimp [windowLength]
    omega
  have hagree := SpectrumPath.equal_spectrum_recovers_word (padBits x) (padBits y)
    n (windowLength k) (by dsimp [windowLength]; omega) hn
    (SpectrumPath.kunique_mono (padBits x) n k (windowLength k - 1) hx hlarge) hs
  have hyx : y = x := by
    funext i
    simpa only [Nat.zero_add, padBits, dite_eq_left i.isLt] using hagree i.val i.isLt
  exact hxy hyx.symm

/-- Equality of the actual word labels, as an event on the paper's real weights. -/
noncomputable def collisionEvent (k Q : ℕ) (x y : Bits n) :
    Set (Gram (windowLength k) → ℝ) :=
  {weights | wordLabel Q (realWeightedHash weights) x =
    wordLabel Q (realWeightedHash weights) y}

/-- The actual exceptional-word event, on the same real-weight probability space. -/
noncomputable def exceptionalEvent (t k Q : ℕ) (x : Bits n) :
    Set (Gram (windowLength k) → ℝ) :=
  {weights | FiniteConflictGraph.Exceptional t k
    (wordLabel Q (realWeightedHash weights)) x}

/-- A label collision is contained in the strict norm test on a derived
nonzero spectrum difference, whose probability is exactly 2/Q. -/
theorem collision_probability_le (k Q : ℕ) (x y : Bits n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k ≤ n)
    (hQ : 2 ≤ Q) (hxy : x ≠ y) :
    realWeights (Gram (windowLength k)) (collisionEvent k Q x y) ≤
      ENNReal.ofReal (2 / (Q : ℝ)) := by
  have hsub : collisionEvent k Q x y ⊆
      {weights | ‖realWeightedHash weights (spectrum k y - spectrum k x)‖ < 1 / (Q : ℝ)} := by
    intro weights hlabel
    exact equal_hash_labels_norm_lt (realWeightedHash weights) Q hQ
      (spectrum k x) (spectrum k y) hlabel
  exact (measure_mono hsub).trans_eq
    (RandomHash.real_nonzero_test_probability (spectrum k y - spectrum k x)
      (spectrum_difference_ne_zero k x y hx hn hxy) Q hQ)

theorem exceptionalEvent_eq_union (t k Q : ℕ) (x : Bits n)
    (hx : KUnique (padBits x) n k) :
    exceptionalEvent t k Q x = ⋃ y ∈ candidatePartners t k x, collisionEvent k Q x y := by
  ext weights
  simp only [exceptionalEvent, collisionEvent, Set.mem_ofPred_eq, Set.mem_iUnion]
  simpa only [exists_prop] using
    exceptional_iff_candidate t k (wordLabel Q (realWeightedHash weights)) x hx

/-- Probability half of `lem:nonsep`, before its separate combinatorial
candidate-count estimate. Partners are actual finite words, not records,
and are not assumed unique. -/
theorem exceptional_probability_le (t k Q : ℕ) (x : Bits n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k ≤ n) (hQ : 2 ≤ Q) :
    realWeights (Gram (windowLength k))
        {weights | FiniteConflictGraph.Exceptional t k
          (wordLabel Q (realWeightedHash weights)) x} ≤
      (candidatePartners t k x).card * ENNReal.ofReal (2 / (Q : ℝ)) := by
  classical
  change realWeights (Gram (windowLength k)) (exceptionalEvent t k Q x) ≤ _
  rw [exceptionalEvent_eq_union t k Q x hx]
  calc
    _ ≤ ∑ y ∈ candidatePartners t k x,
        realWeights (Gram (windowLength k)) (collisionEvent k Q x y) :=
      measure_biUnion_finset_le (candidatePartners t k x) (collisionEvent k Q x)
    _ ≤ ∑ _y ∈ candidatePartners t k x, ENNReal.ofReal (2 / (Q : ℝ)) := by
      apply Finset.sum_le_sum
      intro y hy
      exact collision_probability_le k Q x y hx hn hQ
        ((mem_candidatePartners t k x y).mp hy).1
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

#print axioms exceptional_iff_candidate
#print axioms spectrum_difference_ne_zero
#print axioms collision_probability_le
#print axioms exceptional_probability_le

end DeletionCode.ExceptionalProbability
