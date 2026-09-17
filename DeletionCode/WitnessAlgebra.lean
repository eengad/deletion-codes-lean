import DeletionCode.GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic

/-!
Algebraic steps used in extracting a witness. Supports of linear combinations
cannot acquire new coordinates. A step between Boolean spectra is generating
relative to any earlier span containing the current displacement. A nonzero
scalar multiple between signed unit vectors must have scalar 1 or -1.
-/

namespace DeletionCode.WitnessAlgebra

open scoped BigOperators

def BooleanVector {H : Type*} (v : H → ℚ) : Prop := ∀ h, v h = 0 ∨ v h = 1

def SignedUnitVector {H : Type*} (v : H → ℚ) : Prop :=
  ∀ h, v h = -1 ∨ v h = 0 ∨ v h = 1

/-- Catalogue geometry gives the signed-unit premise for actual rule spectra. -/
theorem ruleSpectrum_signed_unit {B : Type*} (F : RootSelection.Family B) (L : ℕ)
    (H : SignedSupport.BubbleGeometry F L) (S : Finset B)
    (hdis : SignedSupport.VertexDisjointOn F L S) :
    SignedUnitVector (fun g => (SignedSupport.ruleSpectrum F L S g : ℚ)) := by
  classical
  intro g
  by_cases hzero : SignedSupport.ruleSpectrum F L S g = 0
  · exact Or.inr (Or.inl (by simp [hzero]))
  · obtain ⟨b, hb, side, hwindow⟩ :=
      (SignedSupport.rule_support_iff F L H S hdis g).mp hzero
    have hvalue := SignedSupport.rule_value_at_gram F L H S hdis b hb g ⟨side, hwindow⟩
    cases side with
    | false =>
      left
      change (SignedSupport.ruleSpectrum F L S g : ℚ) = -1
      rw [hvalue, SignedSupport.bubble_negative_value F L H b g hwindow]
      norm_num
    | true =>
      right; right
      change (SignedSupport.ruleSpectrum F L S g : ℚ) = 1
      rw [hvalue, SignedSupport.bubble_positive_value F L H b g hwindow]
      norm_num

/-- Whole-block retention preserves independence as well as signed generation. -/
theorem independent_generating_blockHull {I : Type*} {L : ℕ}
    (v : SignedSupport.Gram L → ℤ) (G : I → SignedSupport.Gram L → ℤ)
    (rank : I → ℕ) (T : Set I) (hgen : GeneratingBlocks.Generating v G rank)
    (hind : LinearIndependent ℚ (fun i h => (G i h : ℚ))) :
    GeneratingBlocks.Generating v
      (fun i : GeneratingBlocks.blockHull G T => G i.val)
      (fun i : GeneratingBlocks.blockHull G T => rank i.val) ∧
    LinearIndependent ℚ
      (fun (i : GeneratingBlocks.blockHull G T) h => (G i.val h : ℚ)) := by
  exact ⟨GeneratingBlocks.generating_blockHull v G rank T hgen,
    hind.comp Subtype.val Subtype.val_injective⟩

theorem span_zero_at {H : Type*} (S : Set (H → ℚ)) (h : H)
    (hzero : ∀ w ∈ S, w h = 0) (u : H → ℚ) (hu : u ∈ Submodule.span ℚ S) :
    u h = 0 := by
  induction hu using Submodule.span_induction with
  | mem w hw => exact hzero w hw
  | zero => rfl
  | add x y hx hy hix hiy => simp [hix, hiy]
  | smul a x hx hix => simp [hix]

/-- A nonzero coordinate in the span occurs in some spanning vector. -/
theorem span_support {H : Type*} (S : Set (H → ℚ)) (u : H → ℚ)
    (hu : u ∈ Submodule.span ℚ S) (h : H) (hne : u h ≠ 0) :
    ∃ w ∈ S, w h ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  exact hne (span_zero_at S h hnone u hu)

/-- A negative step coordinate must be present at its Boolean starting point. -/
theorem negative_step_source {H : Type*} (p q : H → ℚ)
    (hp : BooleanVector p) (hq : BooleanVector q) (h : H)
    (hneg : (q - p) h = -1) : p h = 1 := by
  have hp' := hp h
  have hq' := hq h
  change q h - p h = -1 at hneg
  rcases hp' with hp' | hp'
  · rcases hq' with hq' | hq' <;> linarith
  · exact hp'

/-- The generating invariant at an append, as in the bounded-witness proof. -/
theorem generating_append {H : Type*} (v p q : H → ℚ) (S : Set (H → ℚ))
    (hp : BooleanVector p) (hq : BooleanVector q)
    (hspan : p - v ∈ Submodule.span ℚ S) (h : H)
    (hneg : (q - p) h = -1) : v h ≠ 0 ∨ ∃ w ∈ S, w h ≠ 0 := by
  classical
  by_cases hv : v h = 0
  · right
    apply span_support S (p - v) hspan h
    have hpone := negative_step_source p q hp hq h hneg
    simp [hpone, hv]
  · exact Or.inl hv

/-- Signed vectors cannot be distinct non-unit scalar multiples of each other. -/
theorem scalar_eq_one_or_neg_one {H : Type*} (g w : H → ℚ) (a : ℚ)
    (hg : SignedUnitVector g) (hw : SignedUnitVector w)
    (hg0 : g ≠ 0) (ha : a ≠ 0) (hrel : w = a • g) : a = 1 ∨ a = -1 := by
  classical
  have hex : ∃ h, g h ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hg0
    funext h
    exact hnone h
  obtain ⟨h, hh⟩ := hex
  have heq : w h = a * g h := congrFun hrel h
  rcases hg h with hgn | hgz | hgp
  · rcases hw h with hwn | hwz | hwp
    · left; nlinarith
    · exfalso; apply ha; nlinarith
    · right; nlinarith
  · exact False.elim (hh hgz)
  · rcases hw h with hwn | hwz | hwp
    · right; nlinarith
    · exfalso; apply ha; nlinarith
    · left; nlinarith

/-- A one-term nonzero relation is precisely a previously seen rule or its negative. -/
theorem scalar_multiple_eq_or_neg {H : Type*} (g w : H → ℚ) (a : ℚ)
    (hg : SignedUnitVector g) (hw : SignedUnitVector w)
    (hg0 : g ≠ 0) (ha : a ≠ 0) (hrel : w = a • g) : w = g ∨ w = -g := by
  rcases scalar_eq_one_or_neg_one g w a hg hw hg0 ha hrel with h | h
  · left; simpa [h] using hrel
  · right; simpa [h] using hrel

/-- A zero-sum sequence of signed independent vectors has even length.
This is the algebraic obstruction to traversing an odd closed walk using only ±G. -/
theorem signed_sum_even {I J V : Type*} [Fintype I] [Fintype J]
    [AddCommGroup V] [Module ℚ V] (G : I → V) (hG : LinearIndependent ℚ G)
    (label : J → I) (positive : J → Prop) [DecidablePred positive]
    (hsum : (∑ j, (if positive j then (1 : ℚ) else -1) • G (label j)) = 0) :
    Even (Fintype.card J) := by
  classical
  let a : J → ℚ := fun j => if positive j then 1 else -1
  let c : I → ℚ := fun i => ∑ j, if label j = i then a j else 0
  have hsumsmul (s : Finset J) (f : J → ℚ) (v : V) :
      (∑ j ∈ s, f j) • v = ∑ j ∈ s, f j • v := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih => simp [hj, add_smul, ih]
  have hgrouped : ∑ i, c i • G i = 0 := by
    calc
      ∑ i, c i • G i = ∑ j, ∑ i, (if label j = i then a j else 0) • G i := by
        simp only [c, hsumsmul]
        rw [Finset.sum_comm]
      _ = ∑ j, a j • G (label j) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [ite_smul, zero_smul]
        simp
      _ = 0 := hsum
  have hc : ∀ i, c i = 0 := fun i =>
    (linearIndependent_iff'.mp hG) Finset.univ c hgrouped i (Finset.mem_univ i)
  have htotal : ∑ j, a j = 0 := by
    calc
      ∑ j, a j = ∑ i, c i := by
        simp only [c]
        rw [Finset.sum_comm]
        simp
      _ = 0 := Finset.sum_eq_zero (fun i _ => hc i)
  have hcounts : ((Finset.univ.filter positive).card : ℚ) =
      ((Finset.univ.filter (fun j => ¬positive j)).card : ℚ) := by
    have hdiff := htotal
    simp only [a, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one,
      mul_neg, mul_one] at hdiff
    linarith
  have hnat : (Finset.univ.filter positive).card =
      (Finset.univ.filter (fun j => ¬positive j)).card := by exact_mod_cast hcounts
  have hpartition := Finset.card_filter_add_card_filter_not (s := Finset.univ) positive
  refine ⟨(Finset.univ.filter positive).card, ?_⟩
  simpa only [hnat, Finset.card_univ] using hpartition.symm

#print axioms span_support
#print axioms ruleSpectrum_signed_unit
#print axioms independent_generating_blockHull
#print axioms generating_append
#print axioms scalar_multiple_eq_or_neg
#print axioms signed_sum_even

end DeletionCode.WitnessAlgebra
