import DeletionCode.Windows

/-!
Constant-run bounds from actual substring uniqueness. A source run longer
than k would give two equal overlapping k-windows. An insertion can increase
the length of a constant substring by at most one, as follows by removing the
inserted position when the substring crosses it. No positivity of k is assumed.
-/

namespace DeletionCode.UniqueRuns

open Windows

def ConstantOn (x : Letters) (start len : ℕ) (bit : Bool) : Prop :=
  ∀ i, i < len → x (start + i) = bit

/-- Every in-bounds constant substring of a k-unique source has length at most k. -/
theorem constant_length_le (k n : ℕ) (x : Letters) (hx : KUnique x n k)
    (a len : ℕ) (bit : Bool) (hbound : a + len ≤ n)
    (hconstant : ConstantOn x a len bit) : len ≤ k := by
  by_contra hnot
  have hlong : k < len := by omega
  have heq : a = a + 1 := hx a (a + 1) (by omega) (by omega) (by
    intro i hi
    have hfirst := hconstant i (by omega)
    have hsecond := hconstant (i + 1) (by omega)
    have hindex : (a + 1) + i = a + (i + 1) := by omega
    rw [hindex]
    exact hfirst.trans hsecond.symm)
  omega

/-- In particular there is no in-bounds constant window of length k+1. -/
theorem no_constant_succ_window (k n : ℕ) (x : Letters) (hx : KUnique x n k)
    (a : ℕ) (bit : Bool) (hbound : a + (k + 1) ≤ n) :
    ¬ ConstantOn x a (k + 1) bit := by
  intro hconstant
  have h := constant_length_le k n x hx a (k + 1) bit hbound hconstant
  omega

/-- A constant substring after a valid insertion has length at most k+1.
The inserted bit and the constant substring's bit need not be supplied as equal. -/
theorem insert_constant_length_le (k n : ℕ) (x : Letters) (hx : KUnique x n k)
    (pos : ℕ) (insertedBit : Bool) (hpos : pos ≤ n)
    (a len : ℕ) (bit : Bool) (hbound : a + len ≤ n + 1)
    (hconstant : ConstantOn (insertAt x pos insertedBit) a len bit) : len ≤ k + 1 := by
  by_cases hbefore : a + len ≤ pos
  · have hsource : ConstantOn x a len bit := by
      intro i hi
      have hcut : a + i < pos := by omega
      simpa only [insertAt, ite_eq_left hcut] using hconstant i hi
    have h := constant_length_le k n x hx a len bit (by omega) hsource
    omega
  · by_cases hafter : pos < a
    · have hsource : ConstantOn x (a - 1) len bit := by
        intro i hi
        have hcut : ¬ a + i < pos := by omega
        have hne : a + i ≠ pos := by omega
        have hindex : a + i - 1 = a - 1 + i := by omega
        simpa only [insertAt, ite_eq_right hcut, ite_eq_right hne, hindex]
          using hconstant i hi
      have h := constant_length_le k n x hx (a - 1) len bit (by omega) hsource
      omega
    · have hsource : ConstantOn x a (len - 1) bit := by
        intro i hi
        by_cases hcut : a + i < pos
        · simpa only [insertAt, ite_eq_left hcut] using hconstant i (by omega)
        · have hcutNext : ¬ a + (i + 1) < pos := by omega
          have hne : a + (i + 1) ≠ pos := by omega
          have hindex : a + (i + 1) - 1 = a + i := by omega
          simpa only [insertAt, ite_eq_right hcutNext, ite_eq_right hne, hindex]
            using hconstant (i + 1) (by omega)
      have h := constant_length_le k n x hx a (len - 1) bit (by omega) hsource
      omega

#print axioms constant_length_le
#print axioms no_constant_succ_window
#print axioms insert_constant_length_le

end DeletionCode.UniqueRuns
