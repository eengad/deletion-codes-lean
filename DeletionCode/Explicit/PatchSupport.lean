import DeletionCode.Explicit.PatchTable
import DeletionCode.Explicit.Borrowed.Catalogue

/-! Equal windows and de Bruijn paths stay in one patch (`d:patch-support`). -/

namespace DeletionCode.Explicit.PatchSupport

open LetterSequence LetterGraphCuts LocalBudget ReplayEntry

variable {ℓ d s : ℕ} {α : Type*}
variable (data : Fin d × Fin s → GateData ℓ α) (lifts : Fin d × Fin s → Completed ℓ α)

/-- Both lifts of an added bubble are enclosed by its creation interval and
keep the budgets proved when that bubble was added. -/
def LiftsFit (Λ : ℕ) : Prop :=
  ∀ e side, let w := ((lifts e).lift side).2
    w.positions ⊆ Finset.Icc (data e).interval.first.val (data e).interval.last.val ∧
      w.freshOffsets.card ≤ Λ ∧ w.omissions.card ≤ Λ

private theorem positions_in_patch {Λ : ℕ} (h : LiftsFit data lifts Λ)
    (e : Fin d × Fin s) (side : Side) :
    ((lifts e).lift side).2.positions ⊆
      (PatchTable.patches data).positions (PatchTable.incidence data e) := by
  intro k hk
  obtain ⟨hl,hr⟩ := Finset.mem_Icc.mp ((h e side).1 hk)
  obtain ⟨hlo,hhi⟩ := PatchTable.incidence_contains data e
  exact Finset.mem_Icc.mpr ⟨hlo.trans hl,hr.trans hhi⟩

/-- Two equal windows from added lifts must have the same current patch.
The proof works with the budgets at creation even after a first event. -/
theorem equal_windows_same_patch {K Λ k a b : ℕ} {x : Fin ℓ → α}
    (hx : Strong x K Λ) (hfit : LiftsFit data lifts Λ) (hk : K+2*Λ ≤ k)
    (e f : Fin d × Fin s) (side₁ side₂ : Side)
    (ha : a+k ≤ ((lifts e).lift side₁).1) (hb : b+k ≤ ((lifts f).lift side₂).1)
    (hw : (((lifts e).lift side₁).2.window a k ha).spelling x =
      (((lifts f).lift side₂).2.window b k hb).spelling x) :
    PatchTable.incidence data e = PatchTable.incidence data f := by
  let P := PatchTable.patches data
  have he := hfit e side₁
  have hf := hfit f side₂
  have hi := creation_intersects hx ((lifts e).lift side₁).2 ((lifts f).lift side₂).2
    ha hb hk hw he.2.1 hf.2.1 he.2.2 hf.2.2
    (P.positions (PatchTable.incidence data e)) (P.positions (PatchTable.incidence data f))
    (positions_in_patch data lifts hfit e side₁) (positions_in_patch data lifts hfit f side₂)
  by_contra hne
  have hd := P.disjoint hne
  obtain ⟨z,hz⟩ := hi
  obtain ⟨hz₁,hz₂⟩ := Finset.mem_inter.mp hz
  exact Finset.disjoint_left.mp hd hz₁ hz₂

/-- The indicated gram occurs on an added lift in the specified patch. -/
def SupportsAt {n : ℕ} (x : Fin ℓ → α) (word : Fin n → α) (L a : ℕ)
    (p : Fin (PatchTable.patchCount data)) : Prop :=
  ∃ (e : Fin d × Fin s) (side : Side) (start : ℕ) (h : start+L ≤ ((lifts e).lift side).1),
    PatchTable.incidence data e = p ∧ SpellsAt (((lifts e).lift side).2.window start L h) x word a

theorem overlapping_support {K Λ k L δ₁ δ₂ a b n m : ℕ} {x : Fin ℓ → α}
    {word₁ : Fin n → α} {word₂ : Fin m → α}
    (hx : Strong x K Λ) (hfit : LiftsFit data lifts Λ) (hk : K+2*Λ ≤ k)
    (ha : a+L ≤ n) (hb : b+L ≤ m) (hδ₁ : δ₁+k ≤ L) (hδ₂ : δ₂+k ≤ L)
    (hw : ∀ i : Fin k, word₁ ⟨a+δ₁+i.val,by omega⟩ = word₂ ⟨b+δ₂+i.val,by omega⟩)
    {p q : Fin (PatchTable.patchCount data)}
    (hp : SupportsAt data lifts x word₁ L a p) (hq : SupportsAt data lifts x word₂ L b q) :
    p = q := by
  obtain ⟨e,side₁,start₁,hstart₁,hlabel₁,hspell₁⟩ := hp
  obtain ⟨f,side₂,start₂,hstart₂,hlabel₂,hspell₂⟩ := hq
  rw [← hlabel₁,← hlabel₂]
  apply equal_windows_same_patch data lifts hx hfit hk e f side₁ side₂
    (a := start₁+δ₁) (b := start₂+δ₂) (by omega) (by omega)
  funext i
  have hleft := hspell₁.2 ⟨δ₁+i.val,by omega⟩ ⟨a+δ₁+i.val,by omega⟩ (Nat.add_assoc a δ₁ i.val).symm
  have hright := hspell₂.2 ⟨δ₂+i.val,by omega⟩ ⟨b+δ₂+i.val,by omega⟩ (Nat.add_assoc b δ₂ i.val).symm
  simpa only [Lift.spelling,Lift.window,Nat.add_assoc] using (hleft.trans (hw i)).trans hright.symm

/-- A gram in two patch support sets identifies the same patch, giving (P1). -/
theorem gram_support_disjoint {K Λ L : ℕ} {x : Fin ℓ → α} (g : Fin L → α)
    (hx : Strong x K Λ) (hfit : LiftsFit data lifts Λ) (hk : K+2*Λ ≤ L)
    {p q : Fin (PatchTable.patchCount data)}
    (hp : SupportsAt data lifts x g L 0 p) (hq : SupportsAt data lifts x g L 0 q) :
    p = q :=
  overlapping_support data lifts hx hfit hk (by omega) (by omega)
    (δ₁ := 0) (δ₂ := 0) (by omega) (by omega) (fun _ => rfl) hp hq

/-- If each gram on a de Bruijn path has a patch occurrence, all grams of
the path have occurrences in a single patch. -/
theorem path_support {K Λ L n : ℕ} {x : Fin ℓ → α} (word : Fin n → α)
    (hx : Strong x K Λ) (hfit : LiftsFit data lifts Λ) (hk : K+2*Λ+1 ≤ L) (hn : L ≤ n)
    (hcovered : ∀ a, a+L ≤ n → ∃ p, SupportsAt data lifts x word L a p) :
    ∃ p, ∀ a, a+L ≤ n → SupportsAt data lifts x word L a p := by
  obtain ⟨p,hp⟩ := hcovered 0 (by omega)
  refine ⟨p,?_⟩
  intro a
  induction a with
  | zero => exact fun _ => hp
  | succ a ih =>
    intro ha
    obtain ⟨q,hq⟩ := hcovered (a+1) ha
    have hsame : p = q :=
      overlapping_support data lifts hx hfit (k := L-1) (by omega)
        (a := a) (b := a+1) (δ₁ := 1) (δ₂ := 0)
        (by omega) ha (by omega) (by omega) (fun _ => rfl) (ih (by omega)) hq
    exact hsame ▸ hq

/-- The common de Bruijn start vertex joins the two supported paths of a bubble. -/
theorem bubble_support {K Λ L n m : ℕ} {x : Fin ℓ → α}
    (neg : Fin n → α) (pos : Fin m → α) (hn : L ≤ n) (hm : L ≤ m)
    (hx : Strong x K Λ) (hfit : LiftsFit data lifts Λ) (hk : K+2*Λ+1 ≤ L)
    (hhead : ∀ i : Fin (L-1), neg ⟨i.val,by omega⟩ = pos ⟨i.val,by omega⟩)
    (hneg : ∀ a, a+L ≤ n → ∃ p, SupportsAt data lifts x neg L a p)
    (hpos : ∀ a, a+L ≤ m → ∃ p, SupportsAt data lifts x pos L a p) :
    ∃ p, (∀ a, a+L ≤ n → SupportsAt data lifts x neg L a p) ∧
      (∀ a, a+L ≤ m → SupportsAt data lifts x pos L a p) := by
  obtain ⟨p,hp⟩ := path_support data lifts neg hx hfit hk hn hneg
  obtain ⟨q,hq⟩ := path_support data lifts pos hx hfit hk hm hpos
  have hsame : p = q :=
    overlapping_support data lifts hx hfit (k := L-1) (by omega)
      (a := 0) (b := 0) (δ₁ := 0) (δ₂ := 0)
      (by omega) (by omega) (by omega) (by omega)
      (fun i => by simpa only [Nat.zero_add] using hhead i) (hp 0 (by omega)) (hq 0 (by omega))
  exact ⟨p,hp,hsame ▸ hq⟩

#print axioms gram_support_disjoint
#print axioms bubble_support

open Qary.SignedSupport LiftDictionary FieldHash

section SpanSupport
open scoped BigOperators

variable [DecidableEq α]

/-- The spectrum of a recorded rule is the sum of its lifted bubbles. -/
def ruleVector (pad : α) (x : Fin ℓ → α) (L : ℕ) (i : Fin d) : Gram α L → ZMod 3 :=
  fun g => ∑ j : Fin s, LiftDictionary.bubbleVector (L := L) pad x (lifts (i,j)) g

private theorem no_recorded_gram {L : ℕ} (pad : α) (x : Fin ℓ → α) (g : Gram α L)
    (h : ¬ ∃ p, SupportsAt data lifts x g L 0 p) (e : Fin d × Fin s) (side : Side) :
    fieldSpectrum (paddedLetters pad (((lifts e).lift side).2.spelling x))
      ((lifts e).lift side).1 L g = 0 := by
  apply LiftDictionary.fieldSpectrum_zero
  intro a ha he
  apply h
  refine ⟨PatchTable.incidence data e,e,side,a.val,ha,rfl,by omega,?_⟩
  have hspell := (LiftDictionary.lift_gram pad x ((lifts e).lift side) a.val ha).symm.trans he
  intro i j hij
  have heq : i = j := Fin.ext (by simpa only [Nat.zero_add] using hij)
  subst j
  exact congrFun hspell i

/-- A nonzero coordinate of any rule in the recorded span occurs on a
stored lift. Coefficients of different bubbles may cancel. -/
theorem gram_of_span {L : ℕ} (pad : α) (x : Fin ℓ → α) {ρ : Gram α L → ZMod 3}
    (hρ : ρ ∈ Submodule.span (ZMod 3) (Set.range (ruleVector lifts pad x L)))
    (g : Gram α L) (hρg : ρ g ≠ 0) : ∃ p, SupportsAt data lifts x g L 0 p := by
  by_contra h
  let ev : (Gram α L → ZMod 3) →ₗ[ZMod 3] ZMod 3 := LinearMap.proj g
  have hker : Submodule.span (ZMod 3) (Set.range (ruleVector lifts pad x L)) ≤ LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    apply LinearMap.mem_ker.mpr
    change ruleVector lifts pad x L i g = 0
    apply Finset.sum_eq_zero
    intro j _
    have hp := no_recorded_gram data lifts pad x g h (i,j) .positive
    have hn := no_recorded_gram data lifts pad x g h (i,j) .negative
    simp only [Completed.lift] at hp hn
    simp [LiftDictionary.bubbleVector,hp,hn]
  exact hρg (LinearMap.mem_ker.mp (hker hρ))

omit [DecidableEq α] in
private theorem support_at_word {L n a : ℕ} (pad : α) {x : Fin ℓ → α} (word : Fin n → α)
    (ha : a+L ≤ n) {p : Fin (PatchTable.patchCount data)}
    (h : SupportsAt data lifts x (gram (paddedLetters pad word) L a) L 0 p) :
    SupportsAt data lifts x word L a p := by
  obtain ⟨e,side,start,hstart,he,hsp⟩ := h
  refine ⟨e,side,start,hstart,he,ha,?_⟩
  intro i j hij
  have hs := hsp.2 i i (by simp)
  have hi : a+i.val < n := by omega
  have e' : (⟨a+i.val,hi⟩ : Fin n) = j := Fin.ext hij
  simpa only [gram,paddedLetters,dite_eq_left hi,e'] using hs

/-- The two paths of a bubble in an in-span rule lie in one patch once
each of their gram coordinates is nonzero in that rule. Catalogue
disjointness supplies those nonzero coordinates. -/
theorem bubble_support_of_span {K Λ L n m : ℕ} {x : Fin ℓ → α} (pad : α)
    (neg : Fin n → α) (pos : Fin m → α) (hn : L ≤ n) (hm : L ≤ m)
    (hx : Strong x K Λ) (hfit : LiftsFit data lifts Λ) (hk : K+2*Λ+1 ≤ L)
    (hhead : ∀ i : Fin (L-1), neg ⟨i.val,by omega⟩ = pos ⟨i.val,by omega⟩)
    {ρ : Gram α L → ZMod 3}
    (hρ : ρ ∈ Submodule.span (ZMod 3) (Set.range (ruleVector lifts pad x L)))
    (hneg : ∀ a, a+L ≤ n → ρ (gram (paddedLetters pad neg) L a) ≠ 0)
    (hpos : ∀ a, a+L ≤ m → ρ (gram (paddedLetters pad pos) L a) ≠ 0) :
    ∃ p, (∀ a, a+L ≤ n → SupportsAt data lifts x neg L a p) ∧
      (∀ a, a+L ≤ m → SupportsAt data lifts x pos L a p) := by
  apply bubble_support data lifts neg pos hn hm hx hfit hk hhead
  · intro a ha
    obtain ⟨p,hp⟩ := gram_of_span data lifts pad x hρ _ (hneg a ha)
    exact ⟨p,support_at_word data lifts pad neg ha hp⟩
  · intro a ha
    obtain ⟨p,hp⟩ := gram_of_span data lifts pad x hρ _ (hpos a ha)
    exact ⟨p,support_at_word data lifts pad pos ha hp⟩

#print axioms bubble_support_of_span

end SpanSupport

section CatalogueSupport

open Borrowed
open Qary.CatalogueWords (listLetters)
open Qary.SupportComponents (vertex)
open Qary.RuleReconstruction (groupBubbles)

variable [DecidableEq α] [Inhabited α]

/-- Every bubble of a catalogue rule in the span has both paths in a single
patch. The existing catalogue geometry proves that a bubble gram has
coefficient `1` or `-1`, so it stays nonzero after reduction modulo three. -/
theorem catalogue_bubble_support {K b L Λ ν : ℕ} {x : Fin ℓ → α}
    (words : Fin ν → BubbleWord α K b L)
    (hcat : Catalogue.ValidCatalogue words (fun _ => (0 : Fin 1)))
    (hx : Strong x K Λ) (hfit : LiftsFit data lifts Λ) (hk : K+2*Λ+1 ≤ L)
    {ρ : Gram α L → ZMod 3}
    (hρ : ρ ∈ Submodule.span (ZMod 3) (Set.range (ruleVector lifts default x L)))
    (hcast : ∀ g, ρ g =
      (ruleSpectrum (Catalogue.indexedFamily words (fun _ => (0 : Fin 1))) L Finset.univ g : ZMod 3))
    (i : Fin ν) :
    ∃ p, ∀ side a, a+L ≤ (Catalogue.pathWord (words i) side).length →
      SupportsAt data lifts x (Catalogue.pathWord (words i) side).get L a p := by
  let family := Catalogue.indexedFamily words (fun _ => (0 : Fin 1))
  have hdis : VertexDisjointOn family L Finset.univ := by
    have hgroup : groupBubbles (fun _ : Fin ν => (0 : Fin 1)) 0 = Finset.univ := by
      ext j
      exact iff_of_true (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩) (Finset.mem_univ _)
    have h := hcat.within_rule_disjoint (0 : Fin 1)
    rw [hgroup] at h
    exact h
  have hcoeff (side : Bool) (a : ℕ) (ha : a+L ≤ (Catalogue.pathWord (words i) side).length) :
      ρ (gram (paddedLetters default (Catalogue.pathWord (words i) side).get) L a) ≠ 0 := by
    have hm : a < family.extra i side + 1 := by
      change a < (Catalogue.pathWord (words i) side).length-L+1
      omega
    have hg : gram (family.path i side) L a ∈ windowSet (family.path i side) L
        (family.extra i side) := ⟨⟨a,hm⟩,rfl⟩
    have hword : gram (paddedLetters default (Catalogue.pathWord (words i) side).get) L a =
        gram (family.path i side) L a := by
      funext j
      have hj : a+j.val < (Catalogue.pathWord (words i) side).length := by omega
      simp [gram,paddedLetters,family,Catalogue.indexedFamily,Catalogue.family,listLetters,
        List.getD_eq_getElem?_getD,hj]
    rw [hword,hcast,rule_value_at_gram family L hcat.geometry Finset.univ hdis i
      (Finset.mem_univ _) _ ⟨side,hg⟩]
    cases side with
    | false =>
      rw [bubble_negative_value family L hcat.geometry i _ hg]
      exact (by decide : ((-1 : ℤ) : ZMod 3) ≠ 0)
    | true =>
      rw [bubble_positive_value family L hcat.geometry i _ hg]
      exact (by decide : ((1 : ℤ) : ZMod 3) ≠ 0)
  have hn := hcat.length_lower i false
  have hp := hcat.length_lower i true
  have hindex (len : ℕ) (h : L ≤ len) (j : Fin (L-1)) : j.val < len :=
    j.isLt.trans_le ((Nat.sub_le _ _).trans h)
  have hhead (j : Fin (L-1)) :
      (Catalogue.pathWord (words i) false).get ⟨j.val,hindex _ hn j⟩ =
        (Catalogue.pathWord (words i) true).get ⟨j.val,hindex _ hp j⟩ := by
    have he := congrFun (hcat.common_start i) j
    change listLetters (Catalogue.pathWord (words i) false) (0+j.val) =
      listLetters (Catalogue.pathWord (words i) true) (0+j.val) at he
    have hn' := hindex _ hn j
    have hp' := hindex _ hp j
    change (Catalogue.pathWord (words i) false)[j.val]'hn' =
      (Catalogue.pathWord (words i) true)[j.val]'hp'
    simpa only [Nat.zero_add,listLetters,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hn',List.getElem?_eq_getElem hp',Option.getD_some] using he
  obtain ⟨p,hneg,hpos⟩ := bubble_support_of_span data lifts default
    (Catalogue.pathWord (words i) false).get (Catalogue.pathWord (words i) true).get
    hn hp hx hfit hk hhead hρ (hcoeff false) (hcoeff true)
  refine ⟨p,?_⟩
  intro side
  cases side
  · exact hneg
  · exact hpos

#print axioms catalogue_bubble_support

end CatalogueSupport

end DeletionCode.Explicit.PatchSupport
