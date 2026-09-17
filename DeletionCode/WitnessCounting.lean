import DeletionCode.ManuscriptCounting
import DeletionCode.WitnessCases
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Finite.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Count fixed candidate witness sets, independently of which rules survive a
random hash. The partition coordinate is the actual support-component count.
Each fibre is bounded by the established catalogue generating-set count.
-/
namespace DeletionCode.WitnessCounting

open Windows HeaderRecovery SignedRuleCount RuleSetGraph CountExponent
open ManuscriptCounting WitnessCases FiniteGenerating
open scoped BigOperators

/-- The counted objects are actual finite rule sets. Presentations are only
witnesses inside GeneratingSet, and survival is deliberately not part of this predicate. -/
structure Candidate (t : ℕ) (x : Letters) (n k R : ℕ) (U : RuleSet k) : Prop where
  generating : GeneratingSet t x n k R (componentCount U) U
  bounds : WitnessBounds t k U
  independent : Independent U

def AllowedComponents (t k R c : ℕ) : Prop :=
  c ≤ (2 * t - 1) * R + 1 ∧
    (R ≤ windowLength k → c ≤ (2 * t - 1) * R)

abbrev ComponentIndex (t k R : ℕ) :=
  {c : Fin (2 * t * R + 1) // AllowedComponents t k R c.val}

noncomputable instance componentIndexFintype (t k R : ℕ) :
    Fintype (ComponentIndex t k R) := by
  classical
  unfold ComponentIndex
  infer_instance

theorem componentIndex_card_le (t k R : ℕ) :
    Fintype.card (ComponentIndex t k R) ≤ 2 * t * R + 1 := by
  simpa only [Fintype.card_fin] using
    (Fintype.card_subtype_le (fun c : Fin (2 * t * R + 1) => AllowedComponents t k R c.val))

theorem allowed_of_bounds {t k R : ℕ} {U : RuleSet k}
    (hcard : U.card = R) (hb : WitnessBounds t k U) :
    AllowedComponents t k R (componentCount U) := by
  constructor
  · simpa only [hcard] using hb.components
  · intro hsmall
    have h := hb.small_components (by simpa only [hcard] using hsmall)
    simpa only [hcard] using h

theorem componentCount_lt_index_bound {t k R : ℕ} (ht : 1 ≤ t) (hR : 1 ≤ R)
    {U : RuleSet k} (hcard : U.card = R) (hb : WitnessBounds t k U) :
    componentCount U < 2 * t * R + 1 := by
  have hc := (allowed_of_bounds hcard hb).1
  have ht' : 1 ≤ 2 * t := by omega
  have hsplit : (2 * t - 1) * R + R = 2 * t * R := by
    calc
      _ = (2 * t - 1 + 1) * R := by ring
      _ = _ := by rw [Nat.sub_add_cancel ht']
  omega

noncomputable def actualComponentIndex {t k R : ℕ} (ht : 1 ≤ t) (hR : 1 ≤ R)
    (U : RuleSet k) (hcard : U.card = R) (hb : WitnessBounds t k U) :
    ComponentIndex t k R :=
  ⟨⟨componentCount U, componentCount_lt_index_bound ht hR hcard hb⟩,
    allowed_of_bounds hcard hb⟩

abbrev IndexedSets (t : ℕ) (x : Letters) (n k R : ℕ) :=
  Σ c : ComponentIndex t k R,
    {U : RuleSet k // GeneratingSet t x n k R c.val.val U}

/-- Partition by the intrinsic count, retaining the same underlying rule set. -/
noncomputable def partition (t : ℕ) (ht : 1 ≤ t) (x : Letters) (n k R : ℕ) (hR : 1 ≤ R) :
    {U : RuleSet k // Candidate t x n k R U} → IndexedSets t x n k R :=
  fun U => ⟨actualComponentIndex ht hR U.val U.property.generating.1 U.property.bounds,
    ⟨U.val, U.property.generating⟩⟩

theorem partition_injective (t : ℕ) (ht : 1 ≤ t) (x : Letters)
    (n k R : ℕ) (hR : 1 ≤ R) :
    Function.Injective (partition t ht x n k R hR) := by
  intro U V h
  apply Subtype.ext
  exact congrArg (fun z : IndexedSets t x n k R => z.2.val) h

theorem candidate_finite (t : ℕ) (ht : 1 ≤ t) (x : Letters)
    (n k R : ℕ) (hR : 1 ≤ R) (hx : KUnique x n k) :
    Finite {U : RuleSet k // Candidate t x n k R U} := by
  let : ∀ c : ComponentIndex t k R,
      Finite {U : RuleSet k // GeneratingSet t x n k R c.val.val U} :=
    fun c => generatingSet_finite t ht x n k R c.val.val hR hx
  let : Finite (IndexedSets t x n k R) := by unfold IndexedSets; infer_instance
  exact Finite.of_injective (partition t ht x n k R hR)
    (partition_injective t ht x n k R hR)

/-- The large-size arithmetic premise pays for the one extra allowed component. -/
theorem component_power_le (t n k R c : ℕ) (hn : 1 ≤ n)
    (hbonus : windowLength k < R → n ≤ 2 ^ R)
    (hc : AllowedComponents t k R c) :
    n ^ c ≤ 2 ^ R * n ^ ((2 * t - 1) * R) := by
  by_cases hsmall : R ≤ windowLength k
  · calc
      n ^ c ≤ n ^ ((2 * t - 1) * R) := Nat.pow_le_pow_right (by omega) (hc.2 hsmall)
      _ ≤ 2 ^ R * n ^ ((2 * t - 1) * R) := by
        have htwo : 1 ≤ 2 ^ R := one_le_pow₀ (by decide : (1 : ℕ) ≤ 2)
        simpa only [one_mul] using Nat.mul_le_mul_right (n ^ ((2 * t - 1) * R)) htwo
  · calc
      n ^ c ≤ n ^ ((2 * t - 1) * R + 1) := Nat.pow_le_pow_right (by omega) hc.1
      _ = n * n ^ ((2 * t - 1) * R) := by rw [pow_succ, Nat.mul_comm]
      _ ≤ 2 ^ R * n ^ ((2 * t - 1) * R) :=
        Nat.mul_le_mul_right _ (hbonus (by omega))

/-- The fixed-size witness-set count used before the random-hash union bound.
No ordering, catalogue presentation, or occurrence multiplicity is counted. -/
theorem candidate_card_bound (t : ℕ) (ht : 2 ≤ t) (x : Letters)
    (n k R : ℕ) (hR : 2 ≤ R) (hx : KUnique x n k) (hn : 1 ≤ n)
    (hbonus : windowLength k < R → n ≤ 2 ^ R) :
    Nat.card {U : RuleSet k // Candidate t x n k R U} ≤
      2 ^ R * (2 * t * R + 1) * n ^ ((2 * t - 1) * R) *
        (windowLength k * R) ^ (exponent t * R) := by
  classical
  have ht' : 1 ≤ t := by omega
  have hR' : 1 ≤ R := by omega
  let : ∀ c : ComponentIndex t k R,
      Finite {U : RuleSet k // GeneratingSet t x n k R c.val.val U} :=
    fun c => generatingSet_finite t ht' x n k R c.val.val hR' hx
  let : Finite (IndexedSets t x n k R) := by unfold IndexedSets; infer_instance
  calc
    Nat.card {U : RuleSet k // Candidate t x n k R U} ≤ Nat.card (IndexedSets t x n k R) :=
      Nat.card_le_card_of_injective (partition t ht' x n k R hR')
        (partition_injective t ht' x n k R hR')
    _ = ∑ c : ComponentIndex t k R,
        Nat.card {U : RuleSet k // GeneratingSet t x n k R c.val.val U} := Nat.card_sigma
    _ ≤ ∑ _c : ComponentIndex t k R,
        2 ^ R * n ^ ((2 * t - 1) * R) *
          (windowLength k * R) ^ (exponent t * R) := by
      apply Finset.sum_le_sum
      intro c _hc
      exact (ManuscriptCounting.card_bound t ht' x n k R c.val.val hR' hx).trans
        (Nat.mul_le_mul_right _ (component_power_le t n k R c.val.val hn hbonus c.property))
    _ = Fintype.card (ComponentIndex t k R) *
        (2 ^ R * n ^ ((2 * t - 1) * R) *
          (windowLength k * R) ^ (exponent t * R)) := by simp
    _ ≤ (2 * t * R + 1) *
        (2 ^ R * n ^ ((2 * t - 1) * R) *
          (windowLength k * R) ^ (exponent t * R)) :=
      Nat.mul_le_mul_right _ (componentIndex_card_le t k R)
    _ = _ := by ring

#print axioms partition_injective
#print axioms candidate_finite
#print axioms component_power_le
#print axioms candidate_card_bound

end DeletionCode.WitnessCounting
