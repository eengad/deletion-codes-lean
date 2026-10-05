import DeletionCode.Qary.CountingLemma
import DeletionCode.Qary.CatalogueBridge
import DeletionCode.Qary.CanonicalIndex

/-!
The manuscript's generating-set counting bound, from concrete catalogue words.
Presentations use the paper's fixed labels (rule position, bubble position).
The counted object is only the underlying finite set of signed spectrum vectors.
The number c(G) is computed from its actual nonzero support union.

Linear independence and any restriction to surviving rules can further filter
this class. The same bound holds for every such subclass, as proved below.
This module does not assert the manuscript's final deletion-code theorem.
-/
namespace DeletionCode.Qary.ManuscriptCounting

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

open DeletionCode.Qary.Windows DeletionCode.Qary.HeaderRecovery DeletionCode.Qary.CatalogueWords DeletionCode.Qary.CatalogueBridge DeletionCode.Qary.SignedSupport
open DeletionCode.Qary.RuleReconstruction DeletionCode.Qary.RuleSetGraph DeletionCode.Qary.SignedRuleCount DeletionCode.CountExponent DeletionCode.Qary.CanonicalIndex

/-- Concrete balanced catalogue presentations of a signed generating set.
Existential presentations are witnesses, not objects being counted. -/
def GeneratingSet (t : ℕ) (x : Letters α) (n k R c : ℕ) (Q : RuleSet α k) : Prop :=
  Q.card = R ∧ componentCount Q = c ∧
    ∃ words : Fin R → Fin (2 * t) → BubbleWord α k,
      ValidCatalogue (flatten t R words) (group t R) ∧
      OrientationBalanced t (flatten t R words) (group t R) ∧
      SignedGenerating (flatFamily t R words).family x n (windowLength k) ∧
      rulesOfFamily (flatFamily t R words) (group t R) = Q

theorem generatingSet_included (t : ℕ) (x : Letters α) (n k R c : ℕ)
    (Q : RuleSet α k) (hQ : GeneratingSet t x n k R c Q) :
    CountingLemma.GeneratingSet x n k (2 * t * R) R c (group t R) Q := by
  obtain ⟨hcard, hc, words, hvalid, _, hgen, hrules⟩ := hQ
  exact ⟨hcard, hc, flatFamily t R words, fun _ => rfl,
    hvalid.geometry, hvalid.rank_disjoint, hgen, hrules⟩

def inclusion (t : ℕ) (x : Letters α) (n k R c : ℕ) :
    {Q : RuleSet α k // GeneratingSet t x n k R c Q} →
      {Q : RuleSet α k // CountingLemma.GeneratingSet x n k (2 * t * R) R c (group t R) Q} :=
  fun Q => ⟨Q.val, generatingSet_included t x n k R c Q.val Q.property⟩

theorem inclusion_injective (t : ℕ) (x : Letters α) (n k R c : ℕ) :
    Function.Injective (inclusion t x n k R c) := by
  intro Q₁ Q₂ h
  apply Subtype.ext
  exact congrArg (fun Q : {Q : RuleSet α k //
    CountingLemma.GeneratingSet x n k (2 * t * R) R c (group t R) Q} => Q.val) h

theorem generatingSet_finite (t : ℕ) (ht : 1 ≤ t) (x : Letters α)
    (n k R c : ℕ) (hR : 1 ≤ R) (hx : KUnique x n k) :
    Finite {Q : RuleSet α k // GeneratingSet t x n k R c Q} := by
  let : Finite {Q : RuleSet α k //
      CountingLemma.GeneratingSet x n k (2 * t * R) R c (group t R) Q} :=
    CountingLemma.generatingSet_finite x n k (2 * t * R) R c (group t R)
      (by nlinarith) hx
  exact Finite.of_injective (inclusion t x n k R c) (inclusion_injective t x n k R c)

/-- Explicit n^c (LR)^(a_t R) q^(12tR) bound for the underlying signed catalogue sets. -/
theorem card_bound (t : ℕ) (ht : 1 ≤ t) (x : Letters α)
    (n k R c : ℕ) (hR : 1 ≤ R) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet α k // GeneratingSet t x n k R c Q} ≤
      n ^ c * (windowLength k * R) ^ (exponent t * R) * Fintype.card α ^ (12 * t * R) := by
  let : Finite {Q : RuleSet α k //
      CountingLemma.GeneratingSet x n k (2 * t * R) R c (group t R) Q} :=
    CountingLemma.generatingSet_finite x n k (2 * t * R) R c (group t R)
      (by nlinarith) hx
  exact (Nat.card_le_card_of_injective (inclusion t x n k R c)
    (inclusion_injective t x n k R c)).trans
    (CountingLemma.counting_generating_sets t ht x n k R c hR hx (group t R))

/-- Any additional condition, including independence or survival, preserves the bound. -/
theorem filtered_card_bound (t : ℕ) (ht : 1 ≤ t) (x : Letters α)
    (n k R c : ℕ) (hR : 1 ≤ R) (hx : KUnique x n k) (P : RuleSet α k → Prop) :
    Nat.card {Q : RuleSet α k // GeneratingSet t x n k R c Q ∧ P Q} ≤
      n ^ c * (windowLength k * R) ^ (exponent t * R) * Fintype.card α ^ (12 * t * R) := by
  let : Finite {Q : RuleSet α k // GeneratingSet t x n k R c Q} :=
    generatingSet_finite t ht x n k R c hR hx
  let forget : {Q : RuleSet α k // GeneratingSet t x n k R c Q ∧ P Q} →
      {Q : RuleSet α k // GeneratingSet t x n k R c Q} := fun Q => ⟨Q.val, Q.property.1⟩
  have hinj : Function.Injective forget := by
    intro Q₁ Q₂ h
    apply Subtype.ext
    exact congrArg (fun Q : {Q : RuleSet α k // GeneratingSet t x n k R c Q} => Q.val) h
  exact (Nat.card_le_card_of_injective forget hinj).trans (card_bound t ht x n k R c hR hx)

/-- The existence-of-a-constant formulation of the manuscript's counting lemma. -/
theorem counting_generating_sets (t : ℕ) (ht : 1 ≤ t) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ (x : Letters α) (n k R c : ℕ),
      1 ≤ R → KUnique x n k →
        Nat.card {Q : RuleSet α k // GeneratingSet t x n k R c Q} ≤
          n ^ c * (windowLength k * R) ^ (a * R) * Fintype.card α ^ (12 * t * R) := by
  exact ⟨exponent t, exponent_pos t ht,
    fun x n k R c hR hx => card_bound t ht x n k R c hR hx⟩

#print axioms generatingSet_finite
#print axioms card_bound
#print axioms filtered_card_bound
#print axioms counting_generating_sets

end DeletionCode.Qary.ManuscriptCounting
