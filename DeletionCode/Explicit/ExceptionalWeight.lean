import DeletionCode.Burst.ChronologicalSeparation
import DeletionCode.Explicit.CoreWeight
import DeletionCode.Explicit.FieldPath

/-! The exceptional class and the singleton-rule specialization of the
catalogue weights, `d:exceptional`, `d:exceptions`, `d:exception-mean`. -/
namespace DeletionCode.Explicit.ExceptionalWeight

open FieldHash Qary.Windows Qary.SignedSupport Qary.SpectrumPath
open scoped BigOperators
variable {ℓ q L K n θ b t : ℕ}

/-- Index the grams by the columns of the provided hash. -/
def spectrum (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L) (x : List (Fin q)) :
    Fin n → F₃ :=
  fun j => listFieldSpectrum pad x L (cols j)

def delta (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L) (x z : List (Fin q)) :
    Fin n → F₃ :=
  spectrum pad cols z - spectrum pad cols x

/-- The witness uses the existing chronological-record predicate. Only the
source is required to have unique (K)-windows. -/
def Exceptional (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L)
    (H : TernaryMatrix θ n) (b t K : ℕ) (x : Fin ℓ → Fin q) : Prop :=
  let w := List.ofFn x
  KUnique (fun i => w.getD i pad) ℓ K ∧
    ∃ z : List (Fin q), z.length = ℓ ∧ z ≠ w ∧
      Burst.Exceptional b t ℓ (8 * (L + t * b)) w z ∧
      H.mulVec (spectrum pad cols z) = H.mulVec (spectrum pad cols w)

theorem delta_ne_zero (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L)
    {w z : List (Fin q)} (hlen : z.length = w.length)
    (hL : 1 ≤ L) (hw : L ≤ w.length) (hK : K < L)
    (hu : KUnique (fun i => w.getD i pad) w.length K) (hne : z ≠ w) :
    delta pad cols w z ≠ 0 := by
  intro he
  apply hne (field_path_list pad w z L hlen hL hw
    (kunique_mono _ _ _ _ hu (by omega)) ?_)
  have hs := sub_eq_zero.mp he
  funext g
  obtain ⟨j, rfl⟩ := cols.surjective g
  exact congrFun hs j

structure Entry (ℓ q n : ℕ) where
  assignment : CoreWeight.Assignment ℓ q
  changeVector : Fin n → F₃
  nonzero : changeVector ≠ 0

def Entry.object (a : Entry ℓ q n) : CoreWeight.Object ℓ q n :=
  ⟨a.assignment, 1, fun _ => a.changeVector⟩

theorem Entry.kept_iff (a : Entry ℓ q n) (H : TernaryMatrix θ n) :
    CoreWeight.Kept a.object H ↔ H.mulVec a.changeVector = 0 := by
  unfold CoreWeight.Kept Entry.object
  rw [funext_iff]
  constructor
  · intro h i
    have hi := congrFun (h i) (0 : Fin 1)
    change a.changeVector ⬝ᵥ H i = 0 at hi
    change H i ⬝ᵥ a.changeVector = 0
    rwa [dotProduct_comm]
  · intro h i
    funext j
    have hi := h i
    change H i ⬝ᵥ a.changeVector = 0 at hi
    change a.changeVector ⬝ᵥ H i = 0
    rwa [dotProduct_comm]

theorem Entry.rank (a : Entry ℓ q n) : a.object.rules.rank = 1 := by
  rw [Matrix.rank_eq_finrank_span_row]
  have h : Set.range a.object.rules.row = {a.changeVector} := by
    ext x
    simp [Entry.object, Matrix.row]
  rw [h, finrank_span_singleton a.nonzero]

variable {ι : Type*} [Fintype ι]

def weight (C : ι → Entry ℓ q n) (H : TernaryMatrix θ n) (x : Fin ℓ → Fin q) : ℕ :=
  CoreWeight.weight (fun i => (C i).object) H x

def rootMass (C : ι → Entry ℓ q n) (H : TernaryMatrix θ n) : ℚ :=
  CoreWeight.rootMass (fun i => (C i).object) H

def prefixMass (C : ι → Entry ℓ q n) (H : TernaryMatrix θ n) {k : ℕ}
    (u : Fin k → Fin q) : ℕ :=
  CoreWeight.prefixMass (fun i => (C i).object) H u

def conditionalMass (C : ι → Entry ℓ q n) (p : PartialHash θ n) : ℚ :=
  CoreWeight.conditionalMass (fun i => (C i).object) p

/-- The catalogue hypothesis concerns only coverage of chronological records.
The hash filter and the requirement that the difference be nonzero are
handled here. -/
theorem weight_pos_of_exceptional (C : ι → Entry ℓ q n) (pad : Fin q)
    (cols : Fin n ≃ Gram (Fin q) L) (H : TernaryMatrix θ n) (hL : L ≤ ℓ) (hK : K < L)
    (covers : ∀ (x : Fin ℓ → Fin q) z, z.length = ℓ →
      Burst.Exceptional b t ℓ (8 * (L + t * b)) (List.ofFn x) z →
      delta pad cols (List.ofFn x) z ≠ 0 →
      ∃ j, CoreWeight.Matches (C j).assignment x ∧
        (C j).changeVector = delta pad cols (List.ofFn x) z)
    {x : Fin ℓ → Fin q} (hx : Exceptional pad cols H b t K x) :
    0 < weight C H x := by
  obtain ⟨hu, z, hz, hn, hr, hhash⟩ := hx
  have hlen : z.length = (List.ofFn x).length := hz.trans (List.length_ofFn).symm
  have hu' : KUnique (fun i => (List.ofFn x).getD i pad) (List.ofFn x).length K := by
    rwa [List.length_ofFn]
  have hd := delta_ne_zero pad cols hlen (by omega) (by simpa) hK hu' hn
  obtain ⟨j, hj, hjd⟩ := covers x z hz hr hd
  apply (CoreWeight.weight_pos_iff _ _ _).2
  refine ⟨j, ((C j).kept_iff H).2 ?_, hj⟩
  rw [hjd, delta, Matrix.mulVec_sub, hhash, sub_self]

theorem prefixMass_eq_sum (C : ι → Entry ℓ q n) (H : TernaryMatrix θ n)
    {k : ℕ} (hk : k ≤ ℓ) (u : Fin k → Fin q) :
    prefixMass C H u = ∑ x : Fin ℓ → Fin q,
      if ∀ i : Fin k, x (Fin.castLE hk i) = u i then weight C H x else 0 := by
  apply CoreWeight.prefixMass_eq_sum hk

theorem conditionalMass_eq_word_mean (hq : 0 < q) (C : ι → Entry ℓ q n)
    (p : PartialHash θ n) :
    conditionalMass C p = BucketBalance.completionMean p (fun H =>
      (∑ x : Fin ℓ → Fin q, (weight C H x : ℚ)) / (q : ℚ)^ℓ) :=
  CoreWeight.conditionalMass_eq_word_mean hq _ p

/-- The explicit coefficient in `d:exception-constant`. -/
def recordConstant (b s t : ℕ) : ℕ :=
  2 ^ (s - 1) * (2 * (b + 1)) ^ s *
    ((s - 1) + 8 * s * (s + 1) * (1 + t * b) + s * (s * b + 1))

theorem uniform_mean (C : ι → Entry ℓ q n) :
    BucketBalance.completionMean (BucketBalance.freeHash θ n) (rootMass C) =
      (∑ j, (1 : ℚ) / (q : ℚ)^((C j).assignment.support.card)) / (3 : ℚ)^θ := by
  unfold rootMass
  rw [CoreWeight.uniform_mass]
  simp only [Entry.rank, pow_one]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  change _ * ((q : ℚ)^((C j).assignment.support.card))⁻¹ = _
  ring

/-- The assignment-mass bound is the remaining catalogue-counting premise
of `d:exception-mean`. Each retained difference contributes one kernel
constraint, regardless of how many positions its assignment prescribes. -/
theorem uniform_mean_le (C : ι → Entry ℓ q n)
    (hcount : (∑ j, (1 : ℚ) / (q : ℚ)^((C j).assignment.support.card)) ≤
      (recordConstant b (2 * t) t : ℚ) * (q : ℚ)^(b * (2 * t)) * L * (ℓ : ℚ)^(2 * t - 1)) :
    BucketBalance.completionMean (BucketBalance.freeHash θ n) (rootMass C) ≤
      (recordConstant b (2 * t) t : ℚ) * (q : ℚ)^(b * (2 * t)) * L *
        (ℓ : ℚ)^(2 * t - 1) / (3 : ℚ)^θ := by
  rw [uniform_mean]
  exact div_le_div_of_nonneg_right hcount (by positivity)

#print axioms delta_ne_zero
#print axioms weight_pos_of_exceptional
#print axioms prefixMass_eq_sum
#print axioms conditionalMass_eq_word_mean
#print axioms uniform_mean
#print axioms uniform_mean_le

end DeletionCode.Explicit.ExceptionalWeight
