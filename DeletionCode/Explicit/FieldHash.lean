import CslibFrontier.Foundations.LinearAlgebra.Matrix.GaussJordan
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Tactic.FieldSimp

/-! One-coordinate affine probabilities for manuscript `d:field-hash`. -/

namespace DeletionCode.Explicit.FieldHash

abbrev F₃ := ZMod 3
abbrev TernaryMatrix (m n : ℕ) := Matrix (Fin m) (Fin n) F₃

variable {m n : ℕ}

private abbrev Table (m n : ℕ) := Vector (Vector F₃ n) m

/-- Store the actual rows between elimination stages. -/
private def tabulate (A : TernaryMatrix m n) : Table m n :=
  Vector.ofFn (fun i => Vector.ofFn (A i))

private def asMatrix (rows : Table m n) : TernaryMatrix m n :=
  fun i j => (rows.get i).get j

private theorem asMatrix_tabulate (A : TernaryMatrix m n) : asMatrix (tabulate A) = A := by
  funext i j
  simp [asMatrix, tabulate, Vector.get]
  rfl

private def reducedTable (A : TernaryMatrix m n) : ℕ → Table m n
  | 0 => tabulate A
  | k + 1 =>
    let old := reducedTable A k
    if hk : k < n then tabulate (Matrix.GaussJordan.stage (asMatrix old) ⟨k, hk⟩) else old

private theorem reducedTable_eq (A : TernaryMatrix m n) (k : ℕ) :
    asMatrix (reducedTable A k) = Matrix.GaussJordan.reduceUpTo A k := by
  induction k with
  | zero => simp [reducedTable, asMatrix_tabulate, Matrix.GaussJordan.reduceUpTo_zero]
  | succ k ih =>
    by_cases hk : k < n
    · simp [reducedTable, hk, ih, asMatrix_tabulate, Matrix.GaussJordan.reduceUpTo_succ_of_lt A hk]
    · simp [reducedTable, hk, ih, Matrix.GaussJordan.reduceUpTo_succ_of_le A (Nat.le_of_not_gt hk)]

/-- Compute rank by counting the nonzero rows of the reduced matrix. -/
def ternaryRank (A : TernaryMatrix m n) : ℕ :=
  let rows := reducedTable A n
  (Finset.univ.filter fun i => (asMatrix rows).row i ≠ 0).card

theorem ternaryRank_eq (A : TernaryMatrix m n) : ternaryRank A = A.rank := by
  simp only [ternaryRank, reducedTable_eq]
  exact (Matrix.GaussJordan.rank_eq_card_reduce_ne_zero A).symm

/-- The right-hand side is the extra (first) column. -/
def augment (A : TernaryMatrix m n) (y : Fin m → F₃) : TernaryMatrix m (n + 1) :=
  fun i => Fin.cons (y i) (A i)

private theorem augmented_range (A : TernaryMatrix m n) (y : Fin m → F₃) :
    LinearMap.range A.mulVecLin ≤ LinearMap.range (augment A y).mulVecLin := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨j.succ, by funext i; simp [Matrix.col, augment]⟩

theorem consistent_iff (A : TernaryMatrix m n) (y : Fin m → F₃) :
    ternaryRank (augment A y) = ternaryRank A ↔ ∃ x, A.mulVec x = y := by
  rw [ternaryRank_eq, ternaryRank_eq]
  have hle := augmented_range A y
  have hy : y ∈ LinearMap.range (augment A y).mulVecLin := by
    rw [Matrix.range_mulVecLin]
    apply Submodule.subset_span
    exact ⟨0, by funext i; simp [Matrix.col, augment]⟩
  constructor
  · intro h
    have he := Submodule.eq_of_le_of_finrank_eq hle h.symm
    rwa [← he] at hy
  · intro h
    change y ∈ LinearMap.range A.mulVecLin at h
    have rev : LinearMap.range (augment A y).mulVecLin ≤ LinearMap.range A.mulVecLin := by
      rw [Matrix.range_mulVecLin]
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) j
      · have hc : (augment A y).col 0 = y := by funext i; simp [Matrix.col, augment]
        rw [hc]
        exact h
      · rw [Matrix.range_mulVecLin]
        apply Submodule.subset_span
        exact ⟨i, by funext a; simp [Matrix.col, augment]⟩
    unfold Matrix.rank
    rw [le_antisymm rev hle]

/-- Exact probability of `A x = y` when the `n` free entries of one
output coordinate are independent uniform trits. -/
def affineProbability (A : TernaryMatrix m n) (y : Fin m → F₃) : ℚ :=
  let r := ternaryRank A
  if ternaryRank (augment A y) = r then 1 / (3 : ℚ) ^ r else 0

private theorem rank_nullity (A : TernaryMatrix m n) :
    A.rank + Module.finrank F₃ (LinearMap.ker A.mulVecLin) = n := by
  simpa [Matrix.rank, Module.finrank_fintype_fun_eq_card] using A.mulVecLin.finrank_range_add_finrank_ker

private theorem fiber_count (A : TernaryMatrix m n) (x₀ : Fin n → F₃) :
    Nat.card {x : Fin n → F₃ // A.mulVec x = A.mulVec x₀} = 3 ^ (n - A.rank) := by
  let e : {x : Fin n → F₃ // A.mulVec x = A.mulVec x₀} ≃ LinearMap.ker A.mulVecLin :=
    A.mulVecLin.toAddMonoidHom.fiberEquivKer x₀
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := F₃)]
  have hd := rank_nullity A
  rw [show Module.finrank F₃ (LinearMap.ker A.mulVecLin) = n - A.rank by omega]
  simp [F₃]

/-- The computed rational is the fraction of all assignments in the affine
fiber, including inconsistent systems and systems with zero free entries. -/
theorem affineProbability_eq_fraction (A : TernaryMatrix m n) (y : Fin m → F₃) :
    affineProbability A y = (Nat.card {x : Fin n → F₃ // A.mulVec x = y} : ℚ) / (3 : ℚ) ^ n := by
  by_cases h : ∃ x, A.mulVec x = y
  · obtain ⟨x₀, rfl⟩ := h
    have hc := (consistent_iff A _).mpr ⟨x₀, rfl⟩
    simp only [affineProbability, hc, ↓reduceIte, ternaryRank_eq, fiber_count, Nat.cast_pow, Nat.cast_ofNat]
    have hd := rank_nullity A
    have he : (3 : ℚ) ^ n = (3 : ℚ) ^ (n - A.rank) * 3 ^ A.rank := by
      rw [← pow_add, Nat.sub_add_cancel (by omega : A.rank ≤ n)]
    rw [he]
    field_simp
  · have hc := (consistent_iff A y).not.mpr h
    have : IsEmpty {x : Fin n → F₃ // A.mulVec x = y} :=
      ⟨fun x => h ⟨x.val, x.property⟩⟩
    simp [affineProbability, hc]

/-- Different output coordinates can have different numbers of free entries. -/
def independentProbability {θ : ℕ} {d : Fin θ → ℕ}
    (A : (j : Fin θ) → TernaryMatrix m (d j)) (y : Fin θ → Fin m → F₃) : ℚ :=
  ∏ j, affineProbability (A j) (y j)

private def coordinateFibers {θ : ℕ} {d : Fin θ → ℕ}
    (A : (j : Fin θ) → TernaryMatrix m (d j)) (y : Fin θ → Fin m → F₃) :
    {v : (j : Fin θ) → Fin (d j) → F₃ // ∀ j, (A j).mulVec (v j) = y j} ≃
      ((j : Fin θ) → {x : Fin (d j) → F₃ // (A j).mulVec x = y j}) where
  toFun v j := ⟨v.val j, v.property j⟩
  invFun v := ⟨fun j => (v j).val, fun j => (v j).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The product computes the fraction over the full space of independent
free entries. No consistency or full-rank hypothesis is needed. -/
theorem independentProbability_eq_fraction {θ : ℕ} {d : Fin θ → ℕ}
    (A : (j : Fin θ) → TernaryMatrix m (d j)) (y : Fin θ → Fin m → F₃) :
    independentProbability A y =
      (Nat.card {v : (j : Fin θ) → Fin (d j) → F₃ // ∀ j, (A j).mulVec (v j) = y j} : ℚ) /
      (Nat.card ((j : Fin θ) → Fin (d j) → F₃) : ℚ) := by
  rw [Nat.card_congr (coordinateFibers A y), Nat.card_pi, Nat.card_pi]
  simp only [independentProbability, affineProbability_eq_fraction, Finset.prod_div_distrib,
    Nat.cast_prod, Nat.card_fun, Nat.card_fin, Nat.cast_pow]
  simp [F₃]

/-- With no entries fixed every output coordinate imposes the same homogeneous
rank-`r` system. For `P = 3^θ` this is the paper's `P^(-r)`. -/
theorem uniform_kernel_probability (A : TernaryMatrix m n) (θ : ℕ) :
    independentProbability (fun _ : Fin θ => A) (fun _ => 0) =
      1 / ((3 : ℚ) ^ θ) ^ A.rank := by
  have hc := (consistent_iff A 0).mpr ⟨0, Matrix.mulVec_zero A⟩
  simp [independentProbability, affineProbability, hc, ternaryRank_eq,
    ← pow_mul, Nat.mul_comm A.rank θ]

/-- A partial hash records a fixed trit or a free entry at each position.
The first index is the output coordinate. -/
abbrev PartialHash (θ n : ℕ) := Fin θ → Fin n → Option F₃

def Extends {θ : ℕ} (p : PartialHash θ n) (H : Fin θ → Fin n → F₃) : Prop :=
  ∀ j i a, p j i = some a → H j i = a

def fixedMatrix (p : Fin n → Option F₃) : TernaryMatrix n n :=
  Matrix.diagonal (fun i => if (p i).isSome then 1 else 0)

def fixedTarget (p : Fin n → Option F₃) : Fin n → F₃ :=
  fun i => (p i).getD 0

private theorem fixed_iff (p : Fin n → Option F₃) (x : Fin n → F₃) :
    (fixedMatrix p).mulVec x = fixedTarget p ↔ ∀ i a, p i = some a → x i = a := by
  constructor
  · intro h i a hi
    have he := congrFun h i
    simpa [fixedMatrix, fixedTarget, Matrix.mulVec_diagonal, hi] using he
  · intro h
    funext i
    cases hi : p i with
    | none => simp [fixedMatrix, fixedTarget, Matrix.mulVec_diagonal, hi]
    | some a => simpa [fixedMatrix, fixedTarget, Matrix.mulVec_diagonal, hi] using h i a hi

/-- Stack the kernel equations and the equations for fixed entries. A free
entry contributes a zero row and zero right-hand side. -/
def jointMatrix (A : TernaryMatrix m n) (p : Fin n → Option F₃) : TernaryMatrix (m + n) n :=
  Fin.append A (fixedMatrix p)

def jointTarget (p : Fin n → Option F₃) : Fin (m + n) → F₃ :=
  Fin.append (fun _ => 0) (fixedTarget p)

theorem joint_affine_iff (A : TernaryMatrix m n) (y : Fin m → F₃)
    (p : Fin n → Option F₃) (x : Fin n → F₃) :
    (jointMatrix A p).mulVec x = Fin.append y (fixedTarget p) ↔
      A.mulVec x = y ∧ ∀ i a, p i = some a → x i = a := by
  rw [← fixed_iff]
  have left (i : Fin m) : (jointMatrix A p).mulVec x (Fin.castAdd n i) = A.mulVec x i :=
    congrArg (fun row => dotProduct row x) (Fin.append_left A (fixedMatrix p) i)
  have right (i : Fin n) : (jointMatrix A p).mulVec x (Fin.natAdd m i) = (fixedMatrix p).mulVec x i :=
    congrArg (fun row => dotProduct row x) (Fin.append_right A (fixedMatrix p) i)
  constructor
  · intro h
    exact ⟨funext (fun i => by
      simpa only [left, right, Fin.append_left, Fin.append_right] using congrFun h (Fin.castAdd n i)),
      funext (fun i => by
        simpa only [left, right, Fin.append_left, Fin.append_right] using congrFun h (Fin.natAdd m i))⟩
  · rintro ⟨hA, hp⟩
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [left, right, Fin.append_left, Fin.append_right] using congrFun hA i
    · simpa only [left, right, Fin.append_left, Fin.append_right] using congrFun hp i

private theorem joint_iff (A : TernaryMatrix m n) (p : Fin n → Option F₃) (x : Fin n → F₃) :
    (jointMatrix A p).mulVec x = jointTarget p ↔
      A.mulVec x = 0 ∧ ∀ i a, p i = some a → x i = a :=
  joint_affine_iff A 0 p x

/-- Conditional probability that every row of `A` hashes to zero, given
any partial hash assignment. The numerator imposes the fixed entries and
the kernel equations, and the denominator imposes just the fixed entries. -/
def conditionalKernelProbability {θ : ℕ} (A : TernaryMatrix m n) (p : PartialHash θ n) : ℚ :=
  independentProbability (fun j => jointMatrix A (p j)) (fun j => jointTarget (p j)) /
    independentProbability (fun j => fixedMatrix (p j)) (fun j => fixedTarget (p j))

theorem extends_card_pos {θ : ℕ} (p : PartialHash θ n) :
    0 < Nat.card {H : Fin θ → Fin n → F₃ // Extends p H} := by
  have : Nonempty {H : Fin θ → Fin n → F₃ // Extends p H} :=
    ⟨⟨fun j i => (p j i).getD 0, fun j i a h => by simp [h]⟩⟩
  exact Nat.card_pos

/-- The returned rational is the fraction of the compatible completions that
kill all rows, for arbitrary patterns of fixed entries in each coordinate. -/
theorem conditionalKernelProbability_eq_fraction {θ : ℕ} (A : TernaryMatrix m n)
    (p : PartialHash θ n) :
    conditionalKernelProbability A p =
      (Nat.card {H : Fin θ → Fin n → F₃ // Extends p H ∧ ∀ j, A.mulVec (H j) = 0} : ℚ) /
      (Nat.card {H : Fin θ → Fin n → F₃ // Extends p H} : ℚ) := by
  have num (H : Fin θ → Fin n → F₃) :
      (∀ j, (jointMatrix A (p j)).mulVec (H j) = jointTarget (p j)) ↔
        Extends p H ∧ ∀ j, A.mulVec (H j) = 0 := by
    simp only [joint_iff]
    exact ⟨fun h => ⟨fun j => (h j).2, fun j => (h j).1⟩, fun h j => ⟨h.2 j, h.1 j⟩⟩
  have den (H : Fin θ → Fin n → F₃) :
      (∀ j, (fixedMatrix (p j)).mulVec (H j) = fixedTarget (p j)) ↔ Extends p H := by
    simp only [fixed_iff, Extends]
  unfold conditionalKernelProbability
  rw [independentProbability_eq_fraction, independentProbability_eq_fraction,
    Nat.card_congr (Equiv.subtypeEquivRight num), Nat.card_congr (Equiv.subtypeEquivRight den)]
  have hfull : (Nat.card (Fin θ → Fin n → F₃) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.card_pos : 0 < Nat.card (Fin θ → Fin n → F₃)))
  field_simp [hfull]

#print axioms conditionalKernelProbability_eq_fraction

#print axioms independentProbability_eq_fraction
#print axioms uniform_kernel_probability

#print axioms ternaryRank_eq
#print axioms consistent_iff
#print axioms affineProbability_eq_fraction

end DeletionCode.Explicit.FieldHash
