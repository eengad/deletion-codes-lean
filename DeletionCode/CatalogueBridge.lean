import DeletionCode.CatalogueWords
import DeletionCode.SignedRuleCount

/-!
The manuscript's local-word grammar and catalogue geometry imply the signed
rule-count hypotheses. The unequal path lengths are derived from the grammar's
header bounds; neither the edit identity nor support noncancellation is assumed.
The optional balanced class also requires t bubbles of each orientation per
rule and exactly R distinct resulting rules. Linear independence can further
restrict this class and is unnecessary for the bound proved here.
-/

namespace DeletionCode.CatalogueBridge

open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport
open RuleReconstruction SignedRuleCount DescriptionCount

def indexedFamily {k ν R : ℕ} (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R) :
    EditedFamily (Fin ν) k := editedFamily bubbles (fun b => (group b).val)

/-- Header lengths alone already imply that the two paths are not both single edges. -/
theorem notBothSingle {B : Type*} {k : ℕ} (E : EditedFamily B k) (b : B) :
    E.family.extra b false ≠ 0 ∨ E.family.extra b true ≠ 0 := by
  have hlo := E.rho_lower b
  have hhi := E.rho_upper b
  cases ho : (E.header b).orientation <;>
    simp only [EditedFamily.family, PathMemory.pathLength, Bool.false_eq_true,
      ite_false, ite_true, negativeLength, positiveLength, shortLength, longLength,
      windowLength, ho] <;> omega

/-- Exactly the local word-boundary and path restrictions used by the catalogue. -/
structure ValidCatalogue {k ν R : ℕ}
    (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R) : Prop where
  boundary : ∀ b, (bubbles b).orientation ≠ .substitution →
    (bubbles b).left.getLast? = some (!(bubbles b).bit) ∧
      (bubbles b).right.head? = some (!(bubbles b).bit)
  simple : ∀ b side, Function.Injective
    (fun i : Fin ((indexedFamily bubbles group).family.extra b side + 2) =>
      SupportComponents.vertex (indexedFamily bubbles group).family (windowLength k) b side i.val)
  endpoints : ∀ b i j,
    i ≤ (indexedFamily bubbles group).family.extra b false + 1 →
    j ≤ (indexedFamily bubbles group).family.extra b true + 1 →
    SupportComponents.vertex (indexedFamily bubbles group).family (windowLength k) b false i =
      SupportComponents.vertex (indexedFamily bubbles group).family (windowLength k) b true j →
    (i = 0 ∧ j = 0) ∨
      (i = (indexedFamily bubbles group).family.extra b false + 1 ∧
        j = (indexedFamily bubbles group).family.extra b true + 1)
  within_rule_disjoint : ∀ r : Fin R,
    VertexDisjointOn (indexedFamily bubbles group).family (windowLength k)
      (Finset.univ.filter (fun b => group b = r))

theorem ValidCatalogue.geometry {k ν R : ℕ}
    {bubbles : Fin ν → BubbleWord k} {group : Fin ν → Fin R}
    (h : ValidCatalogue bubbles group) :
    BubbleGeometry (indexedFamily bubbles group).family (windowLength k) :=
  ⟨h.simple, h.endpoints, notBothSingle (indexedFamily bubbles group)⟩

theorem ValidCatalogue.rank_disjoint {k ν R : ℕ}
    {bubbles : Fin ν → BubbleWord k} {group : Fin ν → Fin R}
    (h : ValidCatalogue bubbles group) :
    ∀ i, VertexDisjointOn (indexedFamily bubbles group).family (windowLength k)
      (ruleBubbles (indexedFamily bubbles group).family i) := by
  intro i a ha b hb hab sa sb j l hj hl
  have hra := (Finset.mem_filter.mp ha).2
  have hrb := (Finset.mem_filter.mp hb).2
  change (group a).val = i at hra
  change (group b).val = i at hrb
  have hgroup : group b = group a := Fin.ext (hrb.trans hra.symm)
  exact h.within_rule_disjoint (group a) a (by simp) b (by simp [hgroup]) hab sa sb j l hj hl

/-- Signed provenance supplies every actual negative L-window's source. -/
theorem word_generating {k ν R n : ℕ} {x : Letters}
    (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R)
    (hvalid : ValidCatalogue bubbles group)
    (hgen : SignedGenerating (indexedFamily bubbles group).family x n (windowLength k)) :
    (indexedFamily bubbles group).family.Generating x n (windowLength k) :=
  signed_generating_implies_generating (indexedFamily bubbles group).family x n
    (windowLength k) hvalid.geometry hvalid.rank_disjoint hgen

/-- The concrete catalogue conditions imply the entire signed counting interface. -/
theorem valid_generatingRuleSet {k ν R n c : ℕ} {x : Letters}
    (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R)
    (hvalid : ValidCatalogue bubbles group)
    (hgen : SignedGenerating (indexedFamily bubbles group).family x n (windowLength k))
    (hc : Fintype.card
      (SupportComponents.GraphComponents (indexedFamily bubbles group).family (windowLength k)) = c) :
    GeneratingRuleSet x n k ν R c group (rulesOfFamily (indexedFamily bubbles group) group) := by
  exact ⟨indexedFamily bubbles group, fun _ => rfl, hvalid.geometry,
    hvalid.rank_disjoint, hgen, hc, rfl⟩

/-- A rule contains d deletions, d insertions and s substitutions with 2d + s = 2t,
as in the edit version of the manuscript. -/
def OrientationBalanced {k ν R : ℕ} (t : ℕ)
    (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R) : Prop :=
  ∀ r : Fin R,
    (Finset.univ.filter (fun b => group b = r ∧ (bubbles b).orientation = .deletion)).card =
      (Finset.univ.filter (fun b => group b = r ∧ (bubbles b).orientation = .insertion)).card ∧
    2 * (Finset.univ.filter (fun b => group b = r ∧ (bubbles b).orientation = .deletion)).card +
      (Finset.univ.filter (fun b => group b = r ∧ (bubbles b).orientation = .substitution)).card =
        2 * t

/-- The grammar-defined, balanced catalogue class; independence may further restrict it. -/
def CatalogueGeneratingSet (x : Letters) (n k ν R t c : ℕ)
    (group : Fin ν → Fin R) (Q : RuleSet k) : Prop :=
  ∃ bubbles : Fin ν → BubbleWord k,
    ValidCatalogue bubbles group ∧ OrientationBalanced t bubbles group ∧
    SignedGenerating (indexedFamily bubbles group).family x n (windowLength k) ∧
    Fintype.card
      (SupportComponents.GraphComponents (indexedFamily bubbles group).family (windowLength k)) = c ∧
    rulesOfFamily (indexedFamily bubbles group) group = Q ∧ Q.card = R

theorem catalogueGeneratingSet_included (x : Letters) (n k ν R t c : ℕ)
    (group : Fin ν → Fin R) (Q : RuleSet k)
    (hQ : CatalogueGeneratingSet x n k ν R t c group Q) :
    GeneratingRuleSet x n k ν R c group Q := by
  obtain ⟨bubbles, hvalid, _, hgen, hc, rfl, _⟩ := hQ
  exact valid_generatingRuleSet bubbles group hvalid hgen hc

/-- The complete grammar-defined catalogue class inherits the finite-record count. -/
theorem catalogueGeneratingSet_card_bound (x : Letters) (n k ν R t c : ℕ)
    (group : Fin ν → Fin R) (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet k // CatalogueGeneratingSet x n k ν R t c group Q} ≤
      n ^ c * (fieldBound (windowLength k) ν) ^ (50 * ν) := by
  let : Finite {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} :=
    generatingRuleSet_finite x n k ν R c group hν hx
  let inclusion : {Q : RuleSet k // CatalogueGeneratingSet x n k ν R t c group Q} →
      {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} :=
    fun Q => ⟨Q.val, catalogueGeneratingSet_included x n k ν R t c group Q.val Q.property⟩
  have hinj : Function.Injective inclusion := by
    intro Q₁ Q₂ heq
    apply Subtype.ext
    exact congrArg (fun Q : {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} => Q.val) heq
  exact (Nat.card_le_card_of_injective inclusion hinj).trans
    (generatingRuleSet_card_bound x n k ν R c group hν hx)

#print axioms notBothSingle
#print axioms ValidCatalogue.geometry
#print axioms ValidCatalogue.rank_disjoint
#print axioms word_generating
#print axioms valid_generatingRuleSet
#print axioms catalogueGeneratingSet_card_bound

end DeletionCode.CatalogueBridge
