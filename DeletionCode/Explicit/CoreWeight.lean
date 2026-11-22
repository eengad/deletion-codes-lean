import DeletionCode.Explicit.BucketBalance

/-! Exact word counts and hash averages for the finite enumeration in `d:core-weight`. -/

namespace DeletionCode.Explicit.CoreWeight

open FieldHash BucketBalance
variable {ℓ q n θ : ℕ} {ι : Type*} [Fintype ι]

/-- Letters prescribed at the active positions of an object. -/
structure Assignment (ℓ q : ℕ) where
  support : Finset (Fin ℓ)
  letter : (i : ↥support) → Fin q

abbrev Matches (a : Assignment ℓ q) (x : Fin ℓ → Fin q) : Prop :=
  ∀ i : ↥a.support, x i.val = a.letter i

private def freeEquiv (a : Assignment ℓ q) :
    {x : Fin ℓ → Fin q // Matches a x} ≃ ({i : Fin ℓ // i ∉ a.support} → Fin q) where
  toFun x i := x.val i.val
  invFun f := ⟨fun i => if h : i ∈ a.support then a.letter ⟨i,h⟩ else f ⟨i,h⟩,
    fun i => by simp [i.property]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases h : i ∈ a.support
    · simpa [h] using (x.property ⟨i,h⟩).symm
    · simp [h]
  right_inv f := by funext i; simp [i.property]

theorem matching_count (a : Assignment ℓ q) :
    (∑ x : Fin ℓ → Fin q, if Matches a x then 1 else 0) = q ^ (ℓ - a.support.card) := by
  classical
  have hc := Nat.card_congr (freeEquiv a)
  rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hc
  simpa [Finset.sum_boole, Fintype.card_subtype, Finset.filter_not,
    Finset.filter_mem_eq_inter, Finset.card_sdiff_of_subset (Finset.subset_univ _)] using hc

/-- A catalogue entry remembers its assignment and the matrix of its final rules.
Entries are indexed separately even if their assignments and matrices coincide. -/
structure Object (ℓ q n : ℕ) where
  assignment : Assignment ℓ q
  rows : ℕ
  rules : TernaryMatrix rows n

abbrev Kept (o : Object ℓ q n) (H : TernaryMatrix θ n) : Prop :=
  ∀ j, o.rules.mulVec (H j) = 0

def weight (C : ι → Object ℓ q n) (H : TernaryMatrix θ n) (x : Fin ℓ → Fin q) : ℕ :=
  ∑ i, if Kept (C i) H ∧ Matches (C i).assignment x then 1 else 0

theorem weight_pos_iff (C : ι → Object ℓ q n) (H : TernaryMatrix θ n) (x : Fin ℓ → Fin q) :
    0 < weight C H x ↔ ∃ i, Kept (C i) H ∧ Matches (C i).assignment x := by
  simp [weight, Finset.sum_boole, Finset.card_pos, Finset.Nonempty]

/-- Normalized root mass computed directly from the catalogue. -/
def rootMass (C : ι → Object ℓ q n) (H : TernaryMatrix θ n) : ℚ :=
  ∑ i, (if Kept (C i) H then (1 : ℚ) else 0) / (q : ℚ)^((C i).assignment.support.card)

theorem rootMass_eq_word_average (hq : 0 < q) (C : ι → Object ℓ q n) (H : TernaryMatrix θ n) :
    rootMass C H = (∑ x : Fin ℓ → Fin q, (weight C H x : ℚ)) / (q : ℚ)^ℓ := by
  classical
  simp only [rootMass, weight, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin ℓ → Fin q)))]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : Kept (C i) H
  · simp only [ite_eq_left h, and_iff_right h, one_mul]
    have hc : (∑ x : Fin ℓ → Fin q, if Matches (C i).assignment x then (1 : ℚ) else 0) =
        (q : ℚ) ^ (ℓ - (C i).assignment.support.card) := by
      exact_mod_cast matching_count (C i).assignment
    rw [← Finset.sum_mul, hc]
    have hsize : (C i).assignment.support.card ≤ ℓ := by
      simpa using (C i).assignment.support.card_le_univ
    have hp : (q : ℚ)^ℓ = (q : ℚ)^(ℓ - (C i).assignment.support.card) *
        (q : ℚ)^(C i).assignment.support.card := by rw [← pow_add, Nat.sub_add_cancel hsize]
    rw [hp]
    have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
  · simp only [iff_false_intro h, false_and, ↓reduceIte, zero_mul, Finset.sum_const_zero]

/-- Exact conditional mass for an arbitrary pattern of fixed hash entries. -/
def conditionalMass (C : ι → Object ℓ q n) (p : PartialHash θ n) : ℚ :=
  ∑ i, conditionalKernelProbability (C i).rules p / (q : ℚ)^(C i).assignment.support.card

theorem conditionalMass_eq_mean (C : ι → Object ℓ q n) (p : PartialHash θ n) :
    conditionalMass C p = completionMean p (rootMass C) := by
  classical
  unfold rootMass conditionalMass
  rw [mean_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mean_div, mean_kernel]

/-- The computed conditional mass is the mean of the normalized word weight
from the manuscript, with both the hash and word averages taken over their
actual finite spaces. -/
theorem conditionalMass_eq_word_mean (hq : 0 < q) (C : ι → Object ℓ q n)
    (p : PartialHash θ n) :
    conditionalMass C p = completionMean p (fun H =>
      (∑ x : Fin ℓ → Fin q, (weight C H x : ℚ)) / (q : ℚ)^ℓ) := by
  rw [conditionalMass_eq_mean]
  exact congrArg (completionMean p) (funext (rootMass_eq_word_average hq C))

/-- With no fixed entries the survival probability depends only on the row rank. -/
theorem uniform_mass (C : ι → Object ℓ q n) :
    completionMean (freeHash θ n) (rootMass C) =
      ∑ i, (1 / ((3 : ℚ)^θ)^(C i).rules.rank) / (q : ℚ)^(C i).assignment.support.card := by
  simp only [← conditionalMass_eq_mean, conditionalMass, free_kernel]

#print axioms rootMass_eq_word_average
#print axioms conditionalMass_eq_word_mean
#print axioms uniform_mass

/-- Two prescriptions are compatible when they agree on the overlap. -/
abbrev Compatible (a b : Assignment ℓ q) : Prop :=
  ∀ i : ↥a.support, ∀ h : i.val ∈ b.support, a.letter i = b.letter ⟨i.val,h⟩

private def joined (a b : Assignment ℓ q) : Assignment ℓ q where
  support := a.support ∪ b.support
  letter i := if h : i.val ∈ a.support then a.letter ⟨i.val,h⟩
    else b.letter ⟨i.val, (Finset.mem_union.mp i.property).resolve_left h⟩

private theorem matches_joined (a b : Assignment ℓ q) (h : Compatible a b) (x : Fin ℓ → Fin q) :
    Matches (joined a b) x ↔ Matches a x ∧ Matches b x := by
  constructor
  · intro hx
    constructor
    · intro i
      have he := hx ⟨i.val, Finset.mem_union_left _ i.property⟩
      simpa [joined, i.property] using he
    · intro i
      have he := hx ⟨i.val, Finset.mem_union_right _ i.property⟩
      by_cases hi : i.val ∈ a.support
      · simpa [joined, hi, h ⟨i.val,hi⟩ i.property] using he
      · simpa [joined, hi] using he
  · rintro ⟨ha,hb⟩ i
    by_cases hi : i.val ∈ a.support
    · simpa [joined, hi] using ha ⟨i.val,hi⟩
    · simpa [joined, hi] using hb ⟨i.val,(Finset.mem_union.mp i.property).resolve_left hi⟩

/-- Number of words satisfying the object and a second prescription, including
a prefix. The evaluator inspects the overlap and counts unconstrained positions. -/
def jointCount (a b : Assignment ℓ q) : ℕ :=
  if Compatible a b then q^(ℓ - (a.support ∪ b.support).card) else 0

theorem jointCount_eq_count (a b : Assignment ℓ q) :
    jointCount a b = ∑ x : Fin ℓ → Fin q, if Matches a x ∧ Matches b x then 1 else 0 := by
  classical
  by_cases h : Compatible a b
  · rw [jointCount, ite_eq_left h]
    change q ^ (ℓ - (joined a b).support.card) = _
    rw [← matching_count]
    simp only [matches_joined a b h]
  · have hx (x : Fin ℓ → Fin q) : ¬ (Matches a x ∧ Matches b x) := by
      rintro ⟨ha,hb⟩
      exact h (fun i hi => (ha i).symm.trans (hb ⟨i.val,hi⟩))
    simp only [jointCount, ite_eq_right h, ite_eq_right (hx _), Finset.sum_const_zero]

/-- Prescription of the first `k` letters in a word of length `ℓ`. -/
def initial {k : ℕ} (u : Fin k → Fin q) : Assignment ℓ q where
  support := Finset.univ.filter (fun i : Fin ℓ => i.val < k)
  letter i := u ⟨i.val.val, (Finset.mem_filter.mp i.property).2⟩

theorem matches_initial {k : ℕ} (hk : k ≤ ℓ) (u : Fin k → Fin q) (x : Fin ℓ → Fin q) :
    Matches (initial u) x ↔ ∀ i : Fin k, x (Fin.castLE hk i) = u i := by
  constructor
  · intro h i
    exact h ⟨Fin.castLE hk i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.isLt⟩⟩
  · intro h i
    exact h ⟨i.val.val,(Finset.mem_filter.mp i.property).2⟩

/-- Integer weight of all words extending the supplied prefix; the catalogue
algorithm enumerates objects and never enumerates the suffix letters. -/
def prefixMass {k : ℕ} (C : ι → Object ℓ q n) (H : TernaryMatrix θ n)
    (u : Fin k → Fin q) : ℕ :=
  if k ≤ ℓ then ∑ i, if Kept (C i) H then jointCount (C i).assignment (initial u) else 0 else 0

theorem prefixMass_eq_sum {k : ℕ} (hk : k ≤ ℓ) (C : ι → Object ℓ q n)
    (H : TernaryMatrix θ n) (u : Fin k → Fin q) :
    prefixMass C H u = ∑ x : Fin ℓ → Fin q,
      if ∀ i : Fin k, x (Fin.castLE hk i) = u i then weight C H x else 0 := by
  classical
  simp only [prefixMass, hk, ↓reduceIte, jointCount_eq_count, weight]
  have swap (x : Fin ℓ → Fin q) :
      (if ∀ i : Fin k, x (Fin.castLE hk i) = u i then
          ∑ i, if Kept (C i) H ∧ Matches (C i).assignment x then 1 else 0 else 0) =
        ∑ i, if Kept (C i) H ∧ Matches (C i).assignment x ∧ Matches (initial u) x then 1 else 0 := by
    by_cases hp : Matches (initial u) x
    · simp only [ite_eq_left ((matches_initial hk u x).mp hp), and_iff_left hp]
    · simp only [ite_eq_right ((matches_initial hk u x).not.mp hp), iff_false_intro hp, and_false, ↓reduceIte, Finset.sum_const_zero]
  simp_rw [swap]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin ℓ → Fin q)))]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : Kept (C i) H
  · simp only [ite_eq_left h, and_iff_right h]
  · simp only [iff_false_intro h, false_and, ↓reduceIte, Finset.sum_const_zero]

#print axioms prefixMass_eq_sum

/-- A slot encodes a rule count `r+1`, one of at most `Γ` descriptions and
one of at most `ℓ^(t*(r+1))` anchor choices. -/
abbrev Slot (ℓ t r₀ Γ : ℕ) :=
  (r : Fin r₀) × (Fin Γ × Fin (ℓ ^ (t * (r.val + 1))))

private def lettersEquiv (S : Finset (Fin ℓ)) :
    {a : Assignment ℓ q // a.support = S} ≃ (↥S → Fin q) where
  toFun a := a.property ▸ a.val.letter
  invFun f := ⟨⟨S,f⟩,rfl⟩
  left_inv := by rintro ⟨⟨_,f⟩,rfl⟩; rfl
  right_inv _ := rfl

/-- For one description and anchor choice, distinct assignments contribute at
most one unit of normalized word mass in total. -/
private theorem slot_card {κ : Type*} [DecidableEq κ]
    (C : ι → Object ℓ q n) (key : ι → κ) (S : κ → Finset (Fin ℓ))
    (hs : ∀ i, (C i).assignment.support = S (key i))
    (hu : ∀ i j, key i = key j → (C i).assignment = (C j).assignment → i = j) (k : κ) :
    (Finset.univ.filter fun i => key i = k).card ≤ q ^ (S k).card := by
  classical
  let fiber := Finset.univ.filter fun i => key i = k
  have hkey (i : ↥fiber) : key i.val = k := (Finset.mem_filter.mp i.property).2
  let assignment (i : ↥fiber) : {a : Assignment ℓ q // a.support = S k} :=
    ⟨(C i.val).assignment, (hs i.val).trans (congrArg S (hkey i))⟩
  have hinj : Function.Injective assignment := by
    intro i j he
    exact Subtype.ext (hu _ _ ((hkey i).trans (hkey j).symm) (congrArg Subtype.val he))
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin, fiber] using Fintype.card_le_of_injective ((lettersEquiv (S k)).toFun ∘ assignment)
    ((lettersEquiv (S k)).injective.comp hinj)

/-- Manuscript `d:core-mean` given the replay slots of the enumerated objects:
support depends only on the slot, each assignment occurs at most once in its
slot, and its final rule rows are independent. -/
theorem uniform_mass_le {t r₀ Γ : ℕ} (hq : 0 < q) (C : ι → Object ℓ q n)
    (key : ι → Slot ℓ t r₀ Γ) (S : Slot ℓ t r₀ Γ → Finset (Fin ℓ))
    (hs : ∀ i, (C i).assignment.support = S (key i))
    (hu : ∀ i j, key i = key j → (C i).assignment = (C j).assignment → i = j)
    (hr : ∀ i, (C i).rows = (key i).1.val + 1)
    (hind : ∀ i, LinearIndependent F₃ (C i).rules.row) :
    completionMean (freeHash θ n) (rootMass C) ≤
      (Γ : ℚ) * ∑ r : Fin r₀, (ℓ : ℚ)^(t * (r.val + 1)) / ((3 : ℚ)^θ)^(r.val+1) := by
  classical
  let prob (k : Slot ℓ t r₀ Γ) : ℚ := 1 / ((3 : ℚ)^θ)^(k.1.val+1)
  let mass (i : ι) := (1 / ((3 : ℚ)^θ)^(C i).rules.rank) / (q : ℚ)^(C i).assignment.support.card
  have hk (k : Slot ℓ t r₀ Γ) :
      (∑ i ∈ Finset.univ.filter (fun i => key i = k), mass i) ≤ prob k := by
    have each (i : ι) (hi : i ∈ Finset.univ.filter (fun i => key i = k)) :
        mass i = prob k / (q : ℚ)^(S k).card := by
      have e := (Finset.mem_filter.mp hi).2
      simp [mass, prob, (hind i).rank_matrix, hs i, hr i, e]
    rw [Finset.sum_congr rfl each, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ.filter fun i => key i = k).card : ℚ) ≤ (q : ℚ)^(S k).card := by
      exact_mod_cast slot_card C key S hs hu k
    have hpositive : (0 : ℚ) < (q : ℚ)^(S k).card := pow_pos (by exact_mod_cast hq) _
    have hp : 0 ≤ prob k := by dsimp [prob]; positivity
    calc
      _ ≤ (q : ℚ)^(S k).card * (prob k / (q : ℚ)^(S k).card) :=
        mul_le_mul_of_nonneg_right hcard (div_nonneg hp hpositive.le)
      _ = _ := by field_simp
  rw [uniform_mass]
  change ∑ i, mass i ≤ _
  rw [← Finset.sum_fiberwise Finset.univ key mass]
  refine (Finset.sum_le_sum (fun k _ => hk k)).trans_eq ?_
  simp only [Slot, Fintype.sum_sigma, Fintype.card_prod, prob, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

#print axioms uniform_mass_le

end DeletionCode.Explicit.CoreWeight
