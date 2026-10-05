import DeletionCode.Burst.CountingLemma
import DeletionCode.Qary.CanonicalIndex

/-!
The counting bound for underlying burst generating rule sets at the canonical
2tR bubble indexing. Actual catalogue presentations form a subclass; their
balance and local origin conditions can be imposed without increasing the bound.
-/
namespace DeletionCode.Burst.ManuscriptCounting

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]
open Qary.Windows
open Qary.SignedRuleCount (RuleSet)
open CountExponent

abbrev GeneratingSet (t : ℕ) (x : Letters α) (n k b R c : ℕ)
    (U : RuleSet α (k + b)) : Prop :=
  CountingLemma.GeneratingSet x n k b (2 * t * R) R c (Qary.CanonicalIndex.group t R) U

theorem generatingSet_finite (t : ℕ) (ht : 1 ≤ t) (x : Letters α)
    (n k b R c : ℕ) (hR : 1 ≤ R) (hx : KUnique x n k) :
    Finite {U : RuleSet α (k + b) // GeneratingSet t x n k b R c U} :=
  CountingLemma.generatingSet_finite x n k b (2 * t * R) R c (Qary.CanonicalIndex.group t R)
    (by nlinarith) hx

theorem card_bound (t : ℕ) (ht : 1 ≤ t) (x : Letters α)
    (n k b R c : ℕ) (hR : 1 ≤ R) (hx : KUnique x n k) :
    Nat.card {U : RuleSet α (k + b) // GeneratingSet t x n k b R c U} ≤
      n ^ c * (windowLength k b * R) ^ (exponent t * R) * Fintype.card α ^ (12 * b * t * R) :=
  CountingLemma.counting_generating_sets t ht x n k b R c hR hx (Qary.CanonicalIndex.group t R)

theorem filtered_card_bound (t : ℕ) (ht : 1 ≤ t) (x : Letters α)
    (n k b R c : ℕ) (hR : 1 ≤ R) (hx : KUnique x n k) (P : RuleSet α (k + b) → Prop) :
    Nat.card {U : RuleSet α (k + b) // GeneratingSet t x n k b R c U ∧ P U} ≤
      n ^ c * (windowLength k b * R) ^ (exponent t * R) * Fintype.card α ^ (12 * b * t * R) := by
  let : Finite {U : RuleSet α (k + b) // GeneratingSet t x n k b R c U} :=
    generatingSet_finite t ht x n k b R c hR hx
  let forget : {U : RuleSet α (k + b) // GeneratingSet t x n k b R c U ∧ P U} →
      {U : RuleSet α (k + b) // GeneratingSet t x n k b R c U} := fun U => ⟨U.val, U.property.1⟩
  have hinj : Function.Injective forget := by
    intro U V h
    exact Subtype.ext (congrArg
      (fun W : {U : RuleSet α (k + b) // GeneratingSet t x n k b R c U} => W.val) h)
  exact (Nat.card_le_card_of_injective forget hinj).trans (card_bound t ht x n k b R c hR hx)

#print axioms card_bound
#print axioms filtered_card_bound
end DeletionCode.Burst.ManuscriptCounting
