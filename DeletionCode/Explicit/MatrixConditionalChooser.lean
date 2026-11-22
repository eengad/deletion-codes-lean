import DeletionCode.Explicit.ConditionalChooser
import DeletionCode.Explicit.CoreWeight
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Uniform averages over row-major matrix completions and the three
bounds in `d:combined-CE` and `d:three-bounds`. -/
namespace DeletionCode.Explicit.ConditionalChooser

open FieldHash BucketBalance
open scoped BigOperators

variable {θ n : ℕ}
abbrev Cell (θ n : ℕ) := Fin θ × Fin n

def prefixHash (θ n : ℕ) (p : Prefix) : PartialHash θ n :=
  fun j i => p[(finProdFinEquiv (j, i) : Fin (θ * n)).val]?

def totalHash (θ n : ℕ) (p : Prefix) : TernaryMatrix θ n :=
  fun j i => (prefixHash θ n p j i).getD 0

private def fill (p : PartialHash θ n) (c : Cell θ n) (a : F₃) : PartialHash θ n :=
  fun j i => if (j, i) = c then some a else p j i

private def replace (H : TernaryMatrix θ n) (c : Cell θ n) (a : F₃) : TernaryMatrix θ n :=
  fun j i => if (j, i) = c then a else H j i

private theorem extends_fill_iff {p : PartialHash θ n} {c : Cell θ n}
    (hc : p c.1 c.2 = none) (a : F₃) (H : TernaryMatrix θ n) :
    Extends (fill p c a) H ↔ Extends p H ∧ H c.1 c.2 = a := by
  refine ⟨fun h => ⟨?_, h _ _ _ (by simp [fill])⟩, ?_⟩
  · intro j i b hb
    by_cases he : (j, i) = c
    · have hj : j = c.1 := congrArg Prod.fst he
      have hi : i = c.2 := congrArg Prod.snd he
      rw [hj, hi, hc] at hb
      contradiction
    · exact h j i b (by simpa [fill, he] using hb)
  · rintro ⟨hp, ha⟩ j i b hb
    by_cases he : (j, i) = c
    · have hj : j = c.1 := congrArg Prod.fst he
      have hi : i = c.2 := congrArg Prod.snd he
      have heq : a = b := by simpa [fill, he] using hb
      rw [hj, hi, ha, heq]
    · exact hp j i b (by simpa [fill, he] using hb)

private abbrev Completion (p : PartialHash θ n) := {H : Fin θ → Fin n → F₃ // Extends p H}

private def partition {p : PartialHash θ n} {c : Cell θ n} (hc : p c.1 c.2 = none) :
    Completion p ≃ (Σ a : F₃, Completion (fill p c a)) where
  toFun H := ⟨H.1 c.1 c.2, H.1, (extends_fill_iff hc _ _).mpr ⟨H.2, rfl⟩⟩
  invFun H := ⟨H.2.1, ((extends_fill_iff hc _ _).mp H.2.2).1⟩
  left_inv _ := rfl
  right_inv H := by
    obtain ⟨a, H, h⟩ := H
    have hh := ((extends_fill_iff hc _ _).mp h).2
    change H c.1 c.2 = a at hh
    subst a
    rfl

private theorem replace_extends {p : PartialHash θ n} {c : Cell θ n}
    (hc : p c.1 c.2 = none) {H : TernaryMatrix θ n} (hh : Extends p H) (a : F₃) :
    Extends (fill p c a) (replace H c a) := by
  apply (extends_fill_iff hc _ _).mpr
  refine ⟨?_, by simp [replace]⟩
  intro j i b hb
  by_cases he : (j, i) = c
  · have hj : j = c.1 := congrArg Prod.fst he
    have hi : i = c.2 := congrArg Prod.snd he
    rw [hj, hi, hc] at hb
    contradiction
  · simpa [replace, he] using hh j i b hb

private def changeCell {p : PartialHash θ n} {c : Cell θ n} (hc : p c.1 c.2 = none)
    (a b : F₃) : Completion (fill p c a) ≃ Completion (fill p c b) where
  toFun H := ⟨replace H.1 c b, replace_extends hc ((extends_fill_iff hc _ _).mp H.2).1 _⟩
  invFun H := ⟨replace H.1 c a, replace_extends hc ((extends_fill_iff hc _ _).mp H.2).1 _⟩
  left_inv H := by
    apply Subtype.ext
    funext j i
    have h := ((extends_fill_iff hc _ _).mp H.2).2
    by_cases he : (j, i) = c
    · have hj : j = c.1 := congrArg Prod.fst he
      have hi : i = c.2 := congrArg Prod.snd he
      simp [replace, he, hj, hi, h]
    · simp [replace, he]
  right_inv H := by
    apply Subtype.ext
    funext j i
    have h := ((extends_fill_iff hc _ _).mp H.2).2
    by_cases he : (j, i) = c
    · have hj : j = c.1 := congrArg Prod.fst he
      have hi : i = c.2 := congrArg Prod.snd he
      simp [replace, he, hj, hi, h]
    · simp [replace, he]

private theorem sum_trits (f : F₃ → ℚ) : (∑ a, f a) = f 0 + f 1 + f 2 := by
  have h : (Finset.univ : Finset F₃) = {0, 1, 2} := by decide
  rw [h, Finset.sum_insert (by decide : (0 : F₃) ∉ ({1, 2} : Finset F₃)),
    Finset.sum_insert (by decide : (1 : F₃) ∉ ({2} : Finset F₃)), Finset.sum_singleton]
  ring

private theorem mean_fill {p : PartialHash θ n} {c : Cell θ n} (hc : p c.1 c.2 = none)
    (f : TernaryMatrix θ n → ℚ) :
    (∑ a, completionMean (fill p c a) f) = 3 * completionMean p f := by
  classical
  let d := Fintype.card (Completion (fill p c 0))
  have hd (a : F₃) : Fintype.card (Completion (fill p c a)) = d :=
    Fintype.card_congr (changeCell hc a 0)
  have hp : Fintype.card (Completion p) = 3 * d := by
    rw [Fintype.card_congr (partition hc), Fintype.card_sigma]
    simp [hd]
  have hs : (∑ H : Completion p, f H.1) =
      ∑ a : F₃, ∑ H : Completion (fill p c a), f H.1 := by
    let g (x : Σ a : F₃, Completion (fill p c a)) : ℚ := f x.2.1
    exact (Fintype.sum_equiv (partition hc) (fun H => f H.1) g (fun _ => rfl)).trans
      (Fintype.sum_sigma g)
  have hne : (d : ℚ) ≠ 0 := by
    have h := extends_card_pos (fill p c 0)
    rw [Nat.card_eq_fintype_card] at h
    dsimp [d]
    exact_mod_cast h.ne'
  simp only [completionMean, Nat.card_eq_fintype_card, hd, hp, hs, Nat.cast_mul, Nat.cast_ofNat]
  rw [show (∑ a : F₃, (∑ H : Completion (fill p c a), f H.1) / (d : ℚ)) =
      (∑ a : F₃, ∑ H : Completion (fill p c a), f H.1) / (d : ℚ) by
    simp only [div_eq_mul_inv, Finset.sum_mul]]
  field_simp

private theorem prefixHash_append {p : Prefix} (hp : p.length < θ * n) (a : F₃) :
    prefixHash θ n (p ++ [a]) =
      fill (prefixHash θ n p) (finProdFinEquiv.symm ⟨p.length, hp⟩) a := by
  funext j i
  let c : Cell θ n := finProdFinEquiv.symm ⟨p.length, hp⟩
  let k := (finProdFinEquiv (j, i) : Fin (θ * n)).val
  have hidx : (finProdFinEquiv c : Fin (θ * n)).val = p.length :=
    congrArg Fin.val (finProdFinEquiv.apply_symm_apply (⟨p.length, hp⟩ : Fin (θ * n)))
  have he : (j, i) = c ↔ k = p.length := by
    constructor
    · intro h
      exact (congrArg (fun x : Cell θ n => (finProdFinEquiv x : Fin (θ * n)).val) h).trans hidx
    · intro h
      apply finProdFinEquiv.injective
      exact Fin.ext (h.trans hidx.symm)
  change (p ++ [a])[k]? = if (j, i) = c then some a else p[k]?
  rcases lt_trichotomy k p.length with h | h | h
  · rw [ite_eq_right (he.not.mpr h.ne), List.getElem?_append_left h]
  · rw [ite_eq_left (he.mpr h), h, List.getElem?_concat_length]
  · rw [ite_eq_right (he.not.mpr h.ne'), List.getElem?_eq_none (by simp; omega),
      List.getElem?_eq_none (by omega)]

theorem prefixMean_averages {p : Prefix} (hp : p.length < θ * n)
    (f : TernaryMatrix θ n → ℚ) :
    Averages (fun p => completionMean (prefixHash θ n p) f) p := by
  let c : Cell θ n := finProdFinEquiv.symm ⟨p.length, hp⟩
  have hc : prefixHash θ n p c.1 c.2 = none := by
    have hh : (finProdFinEquiv (c.1, c.2) : Fin (θ * n)).val = p.length :=
      congrArg Fin.val (finProdFinEquiv.apply_symm_apply (⟨p.length, hp⟩ : Fin (θ * n)))
    change p[(finProdFinEquiv (c.1, c.2) : Fin (θ * n)).val]? = none
    rw [hh, List.getElem?_eq_none le_rfl]
  rw [Averages, prefixHash_append hp, prefixHash_append hp, prefixHash_append hp]
  have hs := mean_fill hc f
  rw [sum_trits] at hs
  exact hs

theorem prefixMean_full {p : Prefix} (hp : p.length = θ * n)
    (f : TernaryMatrix θ n → ℚ) :
    completionMean (prefixHash θ n p) f = f (totalHash θ n p) := by
  classical
  have hh (H : Completion (prefixHash θ n p)) : H.1 = totalHash θ n p := by
    funext j i
    have hk : (finProdFinEquiv (j, i) : Fin (θ * n)).val < p.length :=
      hp.symm ▸ (finProdFinEquiv (j, i)).isLt
    have hget : prefixHash θ n p j i = some p[(finProdFinEquiv (j, i) : Fin (θ * n)).val] :=
      List.getElem?_eq_getElem hk
    rw [totalHash, hget]
    exact H.2 j i _ hget
  unfold completionMean
  simp only [hh, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hne : (Fintype.card (Completion (prefixHash θ n p)) : ℚ) ≠ 0 := by
    have h := extends_card_pos (prefixHash θ n p)
    rw [Nat.card_eq_fintype_card] at h
    exact_mod_cast h.ne'
  field_simp

theorem prefixHash_empty : prefixHash θ n [] = freeHash θ n := rfl

def chooseHash (θ n : ℕ) (E : Evaluator) (μ : Fin 3 → ℚ) : TernaryMatrix θ n :=
  totalHash θ n (choose (score E μ) (θ * n))

theorem chooseHash_bounds (E : Evaluator) (μ : Fin 3 → ℚ)
    (f : Fin 3 → TernaryMatrix θ n → ℚ)
    (hne : ∀ i H, 0 ≤ f i H)
    (hex : ∀ i p, p.length ≤ θ * n → E i p = completionMean (prefixHash θ n p) (f i))
    (hroot : ∀ i, completionMean (freeHash θ n) (f i) ≤ μ i) :
    ∀ i, f i (chooseHash θ n E μ) ≤ 3 * μ i := by
  have hb := choose_three_bounds E μ (θ * n)
    (fun i p hp => by
      rw [hex i p hp, completionMean]
      exact div_nonneg (Finset.sum_nonneg fun h _ => hne i h.1) (Nat.cast_nonneg _))
    (fun i => by simpa only [hex i [] (Nat.zero_le _), prefixHash_empty] using hroot i)
    (fun i p hp => by
      have ha (a : F₃) : (p ++ [a]).length ≤ θ * n := by simp; omega
      simpa only [Averages, hex i p hp.le, hex i _ (ha 0), hex i _ (ha 1), hex i _ (ha 2)]
        using prefixMean_averages hp (f i))
  intro i
  have hp := choose_length (score E μ) (θ * n)
  specialize hb i
  rw [hex i _ hp.le, prefixMean_full hp] at hb
  exact hb

theorem catalogue_root_nonneg {ℓ q : ℕ} {ι : Type*} [Fintype ι]
    (C : ι → CoreWeight.Object ℓ q n) (H : TernaryMatrix θ n) :
    0 ≤ CoreWeight.rootMass C H := by
  unfold CoreWeight.rootMass
  exact Finset.sum_nonneg fun i _ => div_nonneg (by split <;> norm_num) (by positivity)

private def combine {A : Type*} (a b c : A) : Fin 3 → A := ![a, b, c]

/-- The order is potential, exceptional mass, core mass. The selector's
normalization uses the root callback for the last two quantities and the
family count for the potential. -/
def catalogueBounds (J : ℕ) (E : Evaluator) : Fin 3 → ℚ :=
  combine (J : ℚ) (E 1 []) (E 2 [])

theorem chooseHash_three_bounds {ℓ q J : ℕ} {ε κ : Type*} [Fintype ε] [Fintype κ]
    (B : Fin J → Family n) (hne : ∀ j, (B j).Nonempty)
    (exc : ε → CoreWeight.Object ℓ q n) (core : κ → CoreWeight.Object ℓ q n)
    (E : Evaluator)
    (hpot : ∀ p, E 0 p = conditionalPotential B (prefixHash θ n p))
    (hexc : ∀ p, E 1 p = CoreWeight.conditionalMass exc (prefixHash θ n p))
    (hcore : ∀ p, E 2 p = CoreWeight.conditionalMass core (prefixHash θ n p)) :
    let H := chooseHash θ n E (catalogueBounds J E)
    potential B H ≤ 3 * J ∧
      CoreWeight.rootMass exc H ≤ 3 * completionMean (freeHash θ n) (CoreWeight.rootMass exc) ∧
      CoreWeight.rootMass core H ≤ 3 * completionMean (freeHash θ n) (CoreWeight.rootMass core) := by
  let f : Fin 3 → TernaryMatrix θ n → ℚ :=
    combine (potential B) (CoreWeight.rootMass exc) (CoreWeight.rootMass core)
  have h0 : completionMean (freeHash θ n) (potential B) ≤ J := by
    rw [uniform_mean B hne]
    have : 0 ≤ (J : ℚ) * (1 / (3 : ℚ)^θ) := by positivity
    linarith
  have h1 : E 1 [] = completionMean (freeHash θ n) (CoreWeight.rootMass exc) := by
    rw [hexc, CoreWeight.conditionalMass_eq_mean, prefixHash_empty]
  have h2 : E 2 [] = completionMean (freeHash θ n) (CoreWeight.rootMass core) := by
    rw [hcore, CoreWeight.conditionalMass_eq_mean, prefixHash_empty]
  have hn : ∀ i H, 0 ≤ f i H := by
    intro i H
    fin_cases i
    · exact potential_nonneg B H
    · exact catalogue_root_nonneg exc H
    · exact catalogue_root_nonneg core H
  have hex : ∀ i p, p.length ≤ θ * n → E i p = completionMean (prefixHash θ n p) (f i) := by
    intro i p _
    fin_cases i
    · exact (hpot p).trans (conditionalPotential_eq_mean B _)
    · exact (hexc p).trans (CoreWeight.conditionalMass_eq_mean exc _)
    · exact (hcore p).trans (CoreWeight.conditionalMass_eq_mean core _)
  have hr : ∀ i, completionMean (freeHash θ n) (f i) ≤ catalogueBounds J E i := by
    intro i
    fin_cases i
    · exact h0
    · exact h1.ge
    · exact h2.ge
  have hb := chooseHash_bounds E (catalogueBounds J E) f hn hex hr
  refine ⟨hb 0, ?_, ?_⟩
  · have he := hb 1
    change CoreWeight.rootMass exc _ ≤ 3 * E 1 [] at he
    rwa [h1] at he
  · have he := hb 2
    change CoreWeight.rootMass core _ ≤ 3 * E 2 [] at he
    rwa [h2] at he

#print axioms prefixMean_averages
#print axioms prefixMean_full
#print axioms chooseHash_bounds
#print axioms chooseHash_three_bounds

end DeletionCode.Explicit.ConditionalChooser
