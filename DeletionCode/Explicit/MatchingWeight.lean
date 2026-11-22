import DeletionCode.Explicit.LetterSequence
import DeletionCode.Qary.UniqueWordCount
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Hom.Set

/-! Strong words and matching-pattern weights, `d:strong-source`,
`d:self-matching`, and `d:match-weight`. -/
namespace DeletionCode.Explicit.MatchingWeight

open LetterSequence Qary.Windows
open scoped BigOperators

variable {α : Type*} {ℓ K Λ q : ℕ}

/-- Padding is irrelevant because every window in `KUnique` is in bounds. -/
def padded (pad : α) (x : Fin ℓ → α) (i : ℕ) : α :=
  if h : i < ℓ then x ⟨i, h⟩ else pad

theorem strong_kunique {x : Fin ℓ → α} (h : Strong x K Λ) (pad : α) :
    KUnique (padded pad x) ℓ K := by
  intro i j hi hj heq
  by_contra hij
  let f (a : Fin K) : Fin ℓ := ⟨i + a, by have := a.isLt; omega⟩
  let g (a : Fin K) : Fin ℓ := ⟨j + a, by have := a.isLt; omega⟩
  apply h f g
  · intro a b hab
    exact Nat.add_lt_add_left hab i
  · intro a b hab
    exact Nat.add_lt_add_left hab j
  · intro a b
    change i + b.val + 1 ≤ i + a.val + (K + 3 * Λ)
    have := b.isLt
    omega
  · intro a b
    change j + b.val + 1 ≤ j + a.val + (K + 3 * Λ)
    have := b.isLt
    omega
  · intro a ha
    exact hij (Nat.add_right_cancel (congrArg Fin.val ha))
  · intro a
    have ha := a.isLt
    simpa [padded, show i + a.val < ℓ by omega, show j + a.val < ℓ by omega, f, g]
      using heq a.val ha

abbrev Pattern (ℓ K : ℕ) := (Fin K → Fin ℓ) × (Fin K → Fin ℓ)

def Valid (Λ : ℕ) (p : Pattern ℓ K) : Prop :=
  StrictMono p.1 ∧ StrictMono p.2 ∧ ExtentLE p.1 (K + 3 * Λ) ∧
    ExtentLE p.2 (K + 3 * Λ) ∧ (∀ j, p.1 j ≠ p.2 j)

instance instDecidableValid (Λ : ℕ) (p : Pattern ℓ K) : Decidable (Valid Λ p) := by
  unfold Valid StrictMono ExtentLE
  infer_instance

def Satisfies (x : Fin ℓ → α) (p : Pattern ℓ K) : Prop :=
  ∀ j, x (p.1 j) = x (p.2 j)

instance instDecidableSatisfies [DecidableEq α] (x : Fin ℓ → α) (p : Pattern ℓ K) :
    Decidable (Satisfies x p) := by
  unfold Satisfies
  infer_instance

def patterns (ℓ K Λ : ℕ) : Finset (Pattern ℓ K) :=
  Finset.univ.filter (Valid Λ)

theorem mem_patterns {p : Pattern ℓ K} : p ∈ patterns ℓ K Λ ↔ Valid Λ p := by
  simp [patterns]

def weight [DecidableEq α] (x : Fin ℓ → α) (K Λ : ℕ) : ℕ :=
  ((patterns ℓ K Λ).filter (Satisfies x)).card

theorem weight_pos_iff_not_strong [DecidableEq α] (x : Fin ℓ → α) :
    0 < weight x K Λ ↔ ¬ Strong x K Λ := by
  classical
  rw [weight, Finset.card_pos]
  constructor
  · rintro ⟨⟨f, g⟩, hp⟩ hstrong
    obtain ⟨hp, hs⟩ := Finset.mem_filter.mp hp
    obtain ⟨hf, hg, ef, eg, hn⟩ := mem_patterns.mp hp
    exact hstrong f g hf hg ef eg hn hs
  · intro hn
    unfold Strong at hn
    push Not at hn
    obtain ⟨f, g, hf, hg, ef, eg, hn, hs⟩ := hn
    exact ⟨(f, g), Finset.mem_filter.mpr ⟨mem_patterns.mpr ⟨hf, hg, ef, eg, hn⟩, hs.1⟩⟩

/-- If a coordinate is free in the remaining conditions, imposing a single
equality on it removes exactly one free alphabet symbol. -/
private def equalityStep (P : (Fin ℓ → Fin q) → Prop) {a b : Fin ℓ} (hab : a ≠ b)
    (hP : ∀ x c, P (Function.update x a c) ↔ P x) :
    {x // P x} ≃ Fin q × {x // P x ∧ x a = x b} where
  toFun x :=
    ⟨x.1 a, Function.update x.1 a (x.1 b), (hP _ _).mpr x.2, by simp [hab.symm]⟩
  invFun xc := ⟨Function.update xc.2.1 a xc.1, (hP _ _).mpr xc.2.2.1⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i = a
    · subst i
      simp
    · simp [Function.update_of_ne hi]
  right_inv xc := by
    obtain ⟨c, x, hp, he⟩ := xc
    apply Prod.ext
    · simp
    · apply Subtype.ext
      funext i
      by_cases hi : i = a
      · subst i
        simpa [hab.symm] using he.symm
      · simp [Function.update_of_ne hi]

/-- In increasing lists with unequal heads, the smaller head cannot occur
in either tail. Remove that edge and recover the exact loss of one free
letter by `equalityStep`. This argument also covers overlapping lists. -/
theorem realizes_count_mul (p : Pattern ℓ K) (hf : StrictMono p.1) (hg : StrictMono p.2)
    (hne : ∀ i, p.1 i ≠ p.2 i) :
    q ^ K * Nat.card {x : Fin ℓ → Fin q // Satisfies x p} = q ^ ℓ := by
  induction K with
  | zero => simp [Satisfies, Nat.card_eq_fintype_card]
  | succ K ih =>
    let t : Pattern ℓ K := (fun i => p.1 i.succ, fun i => p.2 i.succ)
    have hmono : StrictMono (Fin.succ : Fin K → Fin (K + 1)) :=
      fun _ _ h => Nat.succ_lt_succ h
    have hpos (i : Fin K) : (0 : Fin (K + 1)) < i.succ := Nat.zero_lt_succ i.val
    have ht := ih t (hf.comp hmono) (hg.comp hmono) (fun i => hne i.succ)
    have hpart : q * Nat.card {x : Fin ℓ → Fin q // Satisfies x p} =
        Nat.card {x : Fin ℓ → Fin q // Satisfies x t} := by
      suffices ∀ {a b : Fin ℓ}, a ≠ b → (∀ i, a ≠ t.1 i ∧ a ≠ t.2 i) →
          (∀ x : Fin ℓ → Fin q, Satisfies x p ↔ Satisfies x t ∧ x a = x b) →
          q * Nat.card {x : Fin ℓ → Fin q // Satisfies x p} =
            Nat.card {x : Fin ℓ → Fin q // Satisfies x t} by
        rcases lt_or_gt_of_ne (hne 0) with hab | hba
        · apply this hab.ne (fun i => ⟨(hf (hpos i)).ne, (hab.trans (hg (hpos i))).ne⟩)
          intro x
          exact ⟨fun h => ⟨fun i => h i.succ, h 0⟩, fun h i => Fin.cases h.2 h.1 i⟩
        · apply this hba.ne (fun i => ⟨(hba.trans (hf (hpos i))).ne, (hg (hpos i)).ne⟩)
          intro x
          exact ⟨fun h => ⟨fun i => h i.succ, (h 0).symm⟩, fun h i => Fin.cases h.2.symm h.1 i⟩
      intro a b hab hfresh he
      have heq := equalityStep (q := q) (Satisfies (p := t) ·) hab (fun x c => by
        unfold Satisfies
        apply forall_congr'
        intro i
        rw [Function.update_of_ne (hfresh i).1.symm,
          Function.update_of_ne (hfresh i).2.symm])
      rw [Nat.card_congr heq, Nat.card_prod, Nat.card_fin,
        Nat.card_congr (Equiv.subtypeEquivRight he)]
    rw [pow_succ, mul_assoc, hpart, ht]

private def BoundedList (ℓ k B : ℕ) :=
  {f : Fin k → Fin ℓ // StrictMono f ∧ ExtentLE f B}

private instance boundedListFintype (ℓ k B : ℕ) : Fintype (BoundedList ℓ k B) := by
  unfold BoundedList ExtentLE StrictMono
  infer_instance

private theorem boundedList_card (B : ℕ) (hK : 0 < K) :
    Fintype.card (BoundedList ℓ K B) ≤ ℓ * B.choose K := by
  classical
  cases K with
  | zero => omega
  | succ k =>
    let P := (Finset.univ : Finset (Fin B)).powersetCard (k + 1)
    let offset (f : BoundedList ℓ (k + 1) B) (i : Fin (k + 1)) : Fin B :=
      ⟨(f.1 i).val - (f.1 0).val, by
        have := f.2.2 0 i
        have := f.2.1.monotone (Fin.zero_le i)
        change (f.1 0).val ≤ (f.1 i).val at this
        omega⟩
    have hoff (f : BoundedList ℓ (k + 1) B) : StrictMono (offset f) := by
      intro a b hab
      have h := f.2.1 hab
      have h' := f.2.1.monotone (Fin.zero_le a)
      change (f.1 a).val < (f.1 b).val at h
      change (f.1 0).val ≤ (f.1 a).val at h'
      change (f.1 a).val - (f.1 0).val < (f.1 b).val - (f.1 0).val
      omega
    let encode (f : BoundedList ℓ (k + 1) B) : Fin ℓ × P :=
      ⟨f.1 0, Finset.univ.image (offset f), by
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
          simp [Finset.card_image_of_injective _ (hoff f).injective]⟩⟩
    have hinj : Function.Injective encode := by
      intro f g he
      have hz : f.1 0 = g.1 0 := congrArg Prod.fst he
      have hs : Finset.univ.image (offset f) = Finset.univ.image (offset g) :=
        congrArg (fun p : Fin ℓ × P => p.2.val) he
      have hset : Set.range (offset f) = Set.range (offset g) := by
        ext i
        simpa using Finset.ext_iff.mp hs i
      have hall := (hoff f).eq_of_range_eq (hoff g) hset
      apply Subtype.ext
      funext i
      apply Fin.ext
      have h1 := f.2.1.monotone (Fin.zero_le i)
      have h2 := g.2.1.monotone (Fin.zero_le i)
      have ho : (f.1 i).val - (f.1 0).val = (g.1 i).val - (g.1 0).val :=
        congrArg Fin.val (congrFun hall i)
      have h0 := congrArg Fin.val hz
      change (f.1 0).val ≤ (f.1 i).val at h1
      change (g.1 0).val ≤ (g.1 i).val at h2
      omega
    simpa [P, Finset.card_powersetCard] using Fintype.card_le_of_injective encode hinj

theorem patterns_card_le (hK : 0 < K) :
    (patterns ℓ K Λ).card ≤ (ℓ * (K + 3 * Λ).choose K)^2 := by
  let pack (p : patterns ℓ K Λ) : BoundedList ℓ K (K + 3 * Λ) × BoundedList ℓ K (K + 3 * Λ) :=
    let hp := mem_patterns.mp p.2
    ⟨⟨p.1.1, hp.1, hp.2.2.1⟩, ⟨p.1.2, hp.2.1, hp.2.2.2.1⟩⟩
  have hinj : Function.Injective pack := by
    intro a b h
    exact Subtype.ext (congrArg (fun p : BoundedList ℓ K (K + 3 * Λ) ×
      BoundedList ℓ K (K + 3 * Λ) => (p.1.val, p.2.val)) h)
  have hc := Fintype.card_le_of_injective pack hinj
  simp only [Fintype.card_coe, Fintype.card_prod, ← pow_two] at hc
  exact hc.trans (Nat.pow_le_pow_left (boundedList_card _ hK) _)

open scoped BigOperators in
theorem weight_root_bound (hK : 0 < K) (hq : 0 < q) :
    (∑ x : Fin ℓ → Fin q, (weight x K Λ : ℚ)) / (q : ℚ)^ℓ ≤
      (ℓ : ℚ)^2 * ((K + 3 * Λ).choose K : ℚ)^2 / (q : ℚ)^K := by
  classical
  have hq' : 0 < (q : ℚ) := by exact_mod_cast hq
  have hpow : 0 < (q : ℚ)^K := pow_pos hq' _
  have hplen : 0 < (q : ℚ)^ℓ := pow_pos hq' _
  have hs (p : Pattern ℓ K) (hp : p ∈ patterns ℓ K Λ) :
      (∑ x : Fin ℓ → Fin q, if Satisfies x p then (1 : ℚ) else 0) =
        (q : ℚ)^ℓ / (q : ℚ)^K := by
    obtain ⟨hf, hg, _, _, hn⟩ := mem_patterns.mp hp
    have hc := realizes_count_mul (q := q) p hf hg hn
    rw [mul_comm] at hc
    apply (eq_div_iff hpow.ne').2
    have he : (∑ x : Fin ℓ → Fin q, if Satisfies x p then (1 : ℚ) else 0) =
        (Nat.card {x : Fin ℓ → Fin q // Satisfies x p} : ℚ) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]
    rw [he]
    exact_mod_cast hc
  have hsum (x : Fin ℓ → Fin q) : (weight x K Λ : ℚ) =
      ∑ p ∈ patterns ℓ K Λ, if Satisfies x p then (1 : ℚ) else 0 := by
    simp [weight, Finset.sum_boole]
  simp only [hsum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl hs, Finset.sum_const, nsmul_eq_mul]
  apply (le_div_iff₀ hpow).2
  have hcancel :
      (↑(patterns ℓ K Λ).card * ((q : ℚ)^ℓ / (q : ℚ)^K)) / (q : ℚ)^ℓ *
        (q : ℚ)^K = (↑(patterns ℓ K Λ).card : ℚ) := by
    field_simp
  rw [hcancel]
  simpa only [Nat.cast_pow, Nat.cast_mul, mul_pow] using
    (show (↑(patterns ℓ K Λ).card : ℚ) ≤ ↑((ℓ * (K + 3 * Λ).choose K)^2) by
      exact_mod_cast patterns_card_le (ℓ := ℓ) (Λ := Λ) hK)

/-- Finite reference prefix mass. The touched-component implementation
in the paper is required to replace the sum over all suffixes. -/
def prefixMass (K Λ : ℕ) {k : ℕ} (u : Fin k → Fin q) : ℕ :=
  ∑ x : Fin ℓ → Fin q, if ∀ i : Fin k, ∀ j : Fin ℓ, i.val = j.val → x j = u i
    then weight x K Λ else 0

theorem prefixMass_eq_sum {k : ℕ} (hk : k ≤ ℓ) (u : Fin k → Fin q) :
    prefixMass (ℓ := ℓ) K Λ u =
      ∑ x : Fin ℓ → Fin q, if ∀ i : Fin k, x (Fin.castLE hk i) = u i
        then weight x K Λ else 0 := by
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  exact propext ⟨fun h i => h i (Fin.castLE hk i) rfl, fun h i j hj => by
    have he : Fin.castLE hk i = j := Fin.ext hj
    simpa only [he] using h i⟩

#print axioms strong_kunique
#print axioms weight_pos_iff_not_strong
#print axioms realizes_count_mul
#print axioms patterns_card_le
#print axioms weight_root_bound
#print axioms prefixMass_eq_sum

end DeletionCode.Explicit.MatchingWeight
