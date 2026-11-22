import DeletionCode.Explicit.MatchingComponents
import Mathlib.Data.Fin.Tuple.Take

/-! Executable matching prefix mass and its exact weighted-address interface. -/
namespace DeletionCode.Explicit.MatchingEnumeration

open scoped BigOperators
variable {ℓ K Λ q k : ℕ}

def prefixMass (pad : Fin q) (ℓ K Λ : ℕ) (p : QWord q) : ℕ :=
  let pre := p.take ℓ
  ((patternList ℓ K Λ).map fun pat => completions pad ℓ pre (edges pat)).sum

private theorem prefixMass_of_admitted (pad : Fin q) (hk : k ≤ ℓ) (u : Fin k → Fin q) :
    prefixMass pad ℓ K Λ (List.ofFn u) = MatchingWeight.prefixMass (ℓ := ℓ) K Λ u := by
  classical
  have ht : (List.ofFn u).take ℓ = List.ofFn u := List.take_of_length_le (by simpa using hk)
  rw [prefixMass, ht, sum_patterns, MatchingWeight.prefixMass_eq_sum hk]
  simp_rw [pattern_completions_eq pad hk]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∀ i : Fin k, x (Fin.castLE hk i) = u i
  · simp [PrefixExtends, hx, MatchingWeight.weight, Finset.sum_boole]
  · simp [PrefixExtends, hx]

theorem prefixMass_eq (pad : Fin q) (u : Fin k → Fin q) :
    prefixMass pad ℓ K Λ (List.ofFn u) = MatchingWeight.prefixMass (ℓ := ℓ) K Λ u := by
  let m := min k ℓ
  have hm : m ≤ k := Nat.min_le_left ..
  have hl : m ≤ ℓ := Nat.min_le_right ..
  let v (j : Fin m) := u (Fin.castLE hm j)
  have ht : (List.ofFn u).take ℓ = List.ofFn v := by
    change _ = List.ofFn (Fin.take m hm u)
    rw [Fin.ofFn_take_eq_take_ofFn hm]
    by_cases hk : k ≤ ℓ
    · rw [List.take_of_length_le (by simpa using hk), List.take_of_length_le (by
        rw [List.length_ofFn]; exact (Nat.min_eq_left hk).ge)]
    · have he : min k ℓ = ℓ := Nat.min_eq_right (by omega)
      exact congrArg (fun n => (List.ofFn u).take n) he.symm
  have he : prefixMass pad ℓ K Λ (List.ofFn u) = prefixMass pad ℓ K Λ (List.ofFn v) := by
    simp only [prefixMass, ht, List.take_of_length_le (by simpa using hl : (List.ofFn v).length ≤ ℓ)]
  rw [he, prefixMass_of_admitted pad hl]
  unfold MatchingWeight.prefixMass
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply propext
  constructor
  · intro h i j hij
    have hi : i.val < m := Nat.lt_min.mpr ⟨i.isLt, by rw [hij]; exact j.isLt⟩
    exact h ⟨i.val,hi⟩ j hij
  · intro h i j hij
    exact h (Fin.castLE hm i) j hij

/-- The same matching weight on length-`ℓ` lists for weighted addressing. -/
def listWeight (ℓ K Λ : ℕ) (w : QWord q) : ℕ :=
  if h : w.length = ℓ then MatchingWeight.weight (fun i : Fin ℓ => w[i.val]'(h.symm ▸ i.isLt)) K Λ else 0

@[simp] theorem listWeight_ofFn (x : Fin ℓ → Fin q) :
    listWeight ℓ K Λ (List.ofFn x) = MatchingWeight.weight x K Λ := by
  simp only [listWeight, List.length_ofFn, List.getElem_ofFn]
  rfl

theorem sum_words (n : ℕ) (f : QWord q → ℕ) :
    ((wordsOfLength q n).map f).sum = ∑ x : Fin n → Fin q, f (List.ofFn x) := by
  classical
  have hset : (wordsOfLength q n).toFinset = (Finset.univ : Finset (Fin n → Fin q)).image List.ofFn := by
    ext w
    simp only [List.mem_toFinset, mem_wordsOfLength, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h
      subst n
      exact ⟨fun i => w[i], List.ofFn_get _⟩
    · rintro ⟨x,rfl⟩
      exact List.length_ofFn
  rw [sum_list _ (WeightedAddress.words_nodup q n), hset, Finset.sum_image]
  intro a _ b _ h
  exact List.ofFn_inj.mp h

theorem prefixFamily_sum (u : Fin k → Fin q) (n : ℕ) (f : (Fin (k+n) → Fin q) → ℕ) :
    (∑ x : Fin (k+n) → Fin q, if ∀ i : Fin k, x (Fin.castLE (Nat.le_add_right k n) i) = u i
      then f x else 0) = ∑ z : Fin n → Fin q, f (Fin.append u z) := by
  classical
  let P (x : Fin (k+n) → Fin q) := ∀ i : Fin k, x (Fin.castLE (Nat.le_add_right k n) i) = u i
  let good : Finset (Fin (k+n) → Fin q) := Finset.univ.filter P
  let extend (z : Fin n → Fin q) : ↥good := ⟨Fin.append u z,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => Fin.append_left' u z i⟩⟩
  have hbij : Function.Bijective extend := by
    constructor
    · intro a b he
      funext i
      have h := congrFun (congrArg Subtype.val he) (Fin.natAdd k i)
      simpa only [extend, Fin.append_right] using h
    · intro x
      have hx := (Finset.mem_filter.mp x.property).2
      refine ⟨fun i => x.val (Fin.natAdd k i), Subtype.ext ?_⟩
      funext i
      change Fin.append u (fun i => x.val (Fin.natAdd k i)) i = x.val i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]
        exact (hx j).symm
      · rw [Fin.append_right]
  rw [← Finset.sum_filter]
  change ∑ x ∈ good, f x = _
  rw [← Finset.sum_coe_sort]
  let g (x : ↥good) := f x.val
  exact (Fintype.sum_equiv (Equiv.ofBijective _ hbij) _ g (fun _ => rfl)).symm

theorem prefixMass_exact (pad : Fin q) (ℓ K Λ : ℕ) :
    WeightedAddress.Exact (listWeight (q := q) ℓ K Λ) (prefixMass pad ℓ K Λ) ℓ := by
  intro p n hp
  subst ℓ
  let u (i : Fin p.length) := p[i]
  have hu : List.ofFn u = p := List.ofFn_get p
  calc
    _ = MatchingWeight.prefixMass (ℓ := p.length+n) K Λ u := by
      conv_lhs => arg 5; rw [← hu]
      exact prefixMass_eq pad u
    _ = ∑ z : Fin n → Fin q, MatchingWeight.weight (Fin.append u z) K Λ := by
      rw [MatchingWeight.prefixMass_eq_sum (Nat.le_add_right p.length n), prefixFamily_sum]
    _ = _ := by
      rw [WeightedAddress.extensionMass, sum_words]
      apply Finset.sum_congr rfl
      intro z _
      have h : List.ofFn (Fin.append u z) = p ++ List.ofFn z := by
        rw [List.ofFn_add]
        simpa [Function.comp_def] using congrArg (· ++ List.ofFn z) hu
      rw [← h, listWeight_ofFn]

#print axioms prefixMass_eq
#print axioms prefixMass_exact

end DeletionCode.Explicit.MatchingEnumeration
