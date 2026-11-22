import DeletionCode.Explicit.ForestSpan

/-! Apply forest intersection to the recorded lifts and the borrowed catalogue. -/

namespace DeletionCode.Explicit.PatchSupport

open LetterSequence LetterGraphCuts ReplayEntry Borrowed RulePatch
open LiftDictionary (bubbleVector fieldSpectrum_zero lift_gram paddedLetters)
open Qary.SignedSupport Qary.Windows
open scoped BigOperators

variable {ℓ d s K b L Λ : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]
variable (data : Fin d × Fin s → LetterGraphCuts.GateData ℓ α)
variable (lifts : Fin d × Fin s → Completed ℓ α)
variable (x : Fin ℓ → α)

private noncomputable def gramSet (p : Fin (PatchTable.patchCount data)) : Finset (Gram α L) := by
  classical
  exact Finset.univ.filter (fun g : Gram α L => SupportsAt data lifts x g L 0 p)

omit [DecidableEq α] [Inhabited α] in
private theorem mem_gramSet (g : Gram α L) (p : Fin (PatchTable.patchCount data)) :
    g ∈ gramSet data lifts x p ↔ SupportsAt data lifts x g L 0 p := by
  classical
  simp [gramSet]

omit [DecidableEq α] [Inhabited α] in
private theorem gramSets_disjoint (hx : Strong x K Λ) (hfit : LiftsFit data lifts Λ)
    (hL : K+2*Λ ≤ L) :
    Pairwise (fun p p' => Disjoint (gramSet data lifts x (L := L) p) (gramSet data lifts x p')) := by
  intro p p' hne
  rw [Finset.disjoint_left]
  intro g hp hp'
  exact hne (gram_support_disjoint data lifts g hx hfit hL
    ((mem_gramSet data lifts x g p).mp hp) ((mem_gramSet data lifts x g p').mp hp'))

private theorem gram_support_of_recorded (e : Fin d × Fin s) (g : Gram α L)
    (hn : bubbleVector default x (lifts e) g ≠ 0) :
    g ∈ gramSet data lifts x (PatchTable.incidence data e) := by
  apply (mem_gramSet data lifts x g _).mpr
  by_contra hz
  have hs (side : Side) :
      fieldSpectrum (paddedLetters default (((lifts e).lift side).2.spelling x))
        ((lifts e).lift side).1 L g = 0 := by
    apply fieldSpectrum_zero
    intro a hb hga
    apply hz
    refine ⟨e,side,a.val,hb,rfl,by omega,?_⟩
    have hspell := (lift_gram default x ((lifts e).lift side) a.val hb).symm.trans hga
    intro i j hij
    have eq : i = j := Fin.ext (by simpa only [Nat.zero_add] using hij)
    subst j
    exact congrFun hspell i
  apply hn
  simpa [bubbleVector,Completed.lift] using sub_eq_zero.mpr ((hs .positive).trans (hs .negative).symm)

omit [DecidableEq α] in
private theorem supports_gram {n : ℕ} (word : Fin n → α) (a : ℕ) (ha : a+L ≤ n)
    (p : Fin (PatchTable.patchCount data)) (h : SupportsAt data lifts x word L a p) :
    gram (paddedLetters default word) L a ∈ gramSet data lifts x p := by
  obtain ⟨e,side,start,hs,hlabel,hspell⟩ := h
  obtain ⟨_,hw⟩ := hspell
  apply (mem_gramSet data lifts x _ p).mpr
  refine ⟨e,side,start,hs,hlabel,by omega,?_⟩
  intro i j hij
  have eq : i = j := Fin.ext (by simpa only [Nat.zero_add] using hij)
  subst j
  have hi : a+i.val < n := by omega
  have hpadded : gram (paddedLetters default word) L a i = word ⟨a+i.val,hi⟩ := by
    simp [gram,paddedLetters,hi]
  rw [hpadded]
  exact hw i ⟨a+i.val,hi⟩ rfl

/-- Every nonzero coefficient of a recorded rule occurs in one of its bubble patches. -/
theorem recorded_rule_occurrence (i : Fin d) (g : Gram α L)
    (hn : ruleVector lifts default x L i g ≠ 0) :
    ∃ j, SupportsAt data lifts x g L 0 (PatchTable.incidence data (i,j)) := by
  by_contra he
  apply hn
  apply Finset.sum_eq_zero
  intro j _
  by_contra hz
  exact he ⟨j,(mem_gramSet data lifts x g _).mp
    (gram_support_of_recorded data lifts x (i,j) g hz)⟩

/-- The actual catalogue-to-span implication in `d:forest-intersection`.
The recorded bubbles must have nonzero spectrum vectors. -/
theorem signed_catalogue_rule (hx : Strong x K Λ) (hfit : LiftsFit data lifts Λ)
    (hs : 3 ≤ s) (hL : K+2*Λ+1 ≤ L)
    (hforest : ∀ i : Fin d,
      (componentRules (PatchTable.incidence data) (.inl i)).card*s+1 =
        (componentRules (PatchTable.incidence data) (.inl i)).card+
          (componentPatches (PatchTable.incidence data) (.inl i)).card)
    (hn : ∀ e : Fin d × Fin s, ∃ g : Gram α L, bubbleVector default x (lifts e) g ≠ 0)
    (words : Fin s → BubbleWord α K b L)
    (hcat : Catalogue.ValidCatalogue words (fun _ => (0 : Fin 1)))
    {ρ : Gram α L → ZMod 3} (hne : ρ ≠ 0)
    (hρ : ρ ∈ Submodule.span (ZMod 3) (Set.range (ruleVector lifts default x L)))
    (hcast : ∀ g, ρ g =
      (ruleSpectrum (Catalogue.indexedFamily words (fun _ => (0 : Fin 1))) L Finset.univ g : ZMod 3)) :
    ∃ i, ρ = ruleVector lifts default x L i ∨ ρ = -ruleVector lifts default x L i := by
  classical
  let a := PatchTable.incidence data
  let support := gramSet data lifts x (L := L)
  let rows := ruleVector lifts default x L
  have hdis := gramSets_disjoint data lifts x hx hfit (show K+2*Λ ≤ L by omega)
  refine signed_rule_of_span a support rows hs hforest ?_ ?_ hne hρ ?_
  · intro e
    obtain ⟨g,hg⟩ := hn e
    have hm := gram_support_of_recorded data lifts x e g hg
    refine ⟨g,hm,?_⟩
    change (∑ j, bubbleVector default x (lifts (e.1,j)) g) ≠ 0
    rw [Finset.sum_eq_single_of_mem e.2 (Finset.mem_univ _) (fun j _ hj => ?_)]
    · simpa only [Prod.eta] using hg
    · by_contra h
      have hs' := gram_support_of_recorded data lifts x (e.1,j) g h
      have hne' : a (e.1,j) ≠ a e := fun he => hj
        (incidence_injective_of_forest a hforest e.1 (by simpa only [Prod.eta] using he))
      exact Finset.disjoint_left.mp (hdis hne') hs' hm
  · intro i p hnone g hg
    apply Finset.sum_eq_zero
    intro j _
    by_contra hnz
    exact Finset.disjoint_left.mp (hdis (hnone j))
      (gram_support_of_recorded data lifts x (i,j) g hnz) hg
  · let F := Catalogue.indexedFamily words (fun _ => (0 : Fin 1))
    have hc (j : Fin s) := catalogue_bubble_support data lifts words hcat hx hfit hL hρ hcast j
    choose patch hp using hc
    let bubble := fun (j : Fin s) (g : Gram α L) => (bubbleSpectrum F L j g : ZMod 3)
    have he : ρ = fun g => ∑ j, bubble j g := by
      funext g
      rw [hcast,ruleSpectrum,Int.cast_sum]
    rw [he]
    apply (Finset.card_le_card (occupied_le_card_image support patch bubble hdis ?_)).trans
    · simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin s))) (f := patch))
    · intro j g hgb
      have hb : bubbleSpectrum F L j g ≠ 0 := by
        intro hz
        apply hgb
        simp [bubble,hz]
      obtain ⟨side,i,hi⟩ := (bubble_support_iff F L hcat.geometry j g).mp hb
      let word := Catalogue.pathWord (words j) side
      have hlen : L ≤ word.length := hcat.length_lower j side
      have hstart : i.val+L ≤ word.length := by
        have hi' : i.val < word.length - L + 1 := i.isLt
        omega
      have eq : gram (paddedLetters default word.get) L i.val = g := by
        rw [← hi]
        funext k
        have hk : i.val+k.val < word.length := by omega
        simp [gram,paddedLetters,F,Catalogue.indexedFamily,Catalogue.family,
          Qary.CatalogueWords.listLetters,List.getD_eq_getElem?_getD,word,hk]
      rw [← eq]
      exact supports_gram data lifts x word.get i.val hstart (patch j) (hp j side i.val hstart)

#print axioms signed_catalogue_rule

end DeletionCode.Explicit.PatchSupport
