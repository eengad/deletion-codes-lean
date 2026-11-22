import DeletionCode.Explicit.FamilyBuckets
import DeletionCode.Explicit.MixedRadix

/-! The width of a pivot digit is fixed by its family, before the inverse
computes the hash value of its bucket. -/

namespace DeletionCode.Explicit.BubbleFamilies

open FieldHash

def pivotRadix (M P : ℕ) : ℕ := (2*M+(P-1))/P

theorem le_pivotRadix {ν M P : ℕ} (hP : 0 < P) (hν : ν*P ≤ 2*M) :
    ν ≤ pivotRadix M P := by
  apply (Nat.le_div_iff_mul_le hP).mpr
  exact hν.trans (Nat.le_add_right _ _)

theorem pivotRadix_mul_le {M P : ℕ} (h : P ≤ M) : pivotRadix M P * P ≤ 3*M := by
  unfold pivotRadix
  have hdiv := Nat.div_mul_le_self (2*M+(P-1)) P
  omega

/-- The concrete bucket list fits the pivot radix assigned by the balance
bound. The radix depends only on the number of members of the family. -/
theorem bucket_fits_pivotRadix
    {q K b L Λ θ J : ℕ} (pad : Fin q) (hL : 1 ≤ L)
    (B : Fin J → BucketBalance.Family (q^L)) (H : TernaryMatrix θ (q^L))
    (hΦ : BucketBalance.potential B H ≤ 3*J) (j : Fin J)
    (s : Shape q) (he : B j = s.vectors K b L Λ pad)
    (hlarge : 12*J*(3^θ)^2 ≤ (B j).card) (z : Fin θ → F₃) :
    (bucket s K b L Λ pad H z).length ≤ pivotRadix (s.members K b L Λ pad).length (3^θ) := by
  rw [bucket_length s K b L Λ pad hL H z,← vectors_card s K b L Λ pad hL,← he]
  have hh := BucketBalance.large_bucket_bounds B H hΦ j z hlarge
  dsimp only at hh
  have hp : (0 : ℝ) < 3^θ := by positivity
  have hr := (le_div_iff₀ hp).mp (hh.1.trans (hh.2.1.trans hh.2.2))
  apply le_pivotRadix (by positivity)
  exact_mod_cast hr

/-- One family with a active letters reserves at most 3*q^a/P
indices, represented without division in the inequality. -/
theorem pivotRadix_capacity {q K b L Λ P : ℕ} (pad : Fin q) (hL : 1 ≤ L) (s : Shape q)
    (hM : P ≤ (s.members K b L Λ pad).length) :
    pivotRadix (s.members K b L Λ pad).length P * P ≤ 3*q^s.originalCount := by
  apply (pivotRadix_mul_le hM).trans
  apply Nat.mul_le_mul_left
  rw [← vectors_card s K b L Λ pad hL]
  exact vectors_card_le s K b L Λ pad

/-- The literal and pivot digits are packed together. Each pair is a
pivot's number of active letters and its family-dependent radix. -/
theorem payload_capacity (q P : ℕ) (digits : List (ℕ × ℕ))
    (h : ∀ p ∈ digits, p.2*P ≤ 3*q^p.1) :
    (digits.map Prod.snd).prod * P^digits.length ≤
      3^digits.length * q^((digits.map Prod.fst).sum) := by
  induction digits with
  | nil => simp
  | cons p tail ih =>
    have hhead := h p (by simp)
    have htail := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [List.map_cons,List.prod_cons,List.sum_cons,List.length_cons,Nat.pow_succ,Nat.pow_add]
    calc
      _ = (p.2*P)*((tail.map Prod.snd).prod * P^tail.length) := by ring
      _ ≤ (3*q^p.1)*(3^tail.length*q^((tail.map Prod.fst).sum)) :=
        Nat.mul_le_mul hhead htail
      _ = _ := by ring

#print axioms bucket_fits_pivotRadix
#print axioms pivotRadix_capacity
#print axioms payload_capacity

end DeletionCode.Explicit.BubbleFamilies
