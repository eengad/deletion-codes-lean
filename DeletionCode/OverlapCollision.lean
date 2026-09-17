import DeletionCode.HeaderRecovery
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega

/-!
Equal substrings, including overlapping substrings, cost at least k bits.
The encoding deletes the later substring. Its missing bits are determined in
increasing order, since each missing bit equals a strictly earlier bit.
-/
namespace DeletionCode.OverlapCollision

open Windows HeaderRecovery

/-- Actual length-n binary words whose indicated length-k windows agree. -/
abbrev Collision (n k a b : ℕ) :=
  {x : Bits n // Agree (padBits x) a (padBits x) b k}

noncomputable instance collisionFintype (n k a b : ℕ) :
    Fintype (Collision n k a b) := by
  classical
  unfold Collision
  infer_instance

/-- Indices outside the later interval `[b,b+k)`, in their original order. -/
def keptIndex (n k b : ℕ) (hb : b + k ≤ n) (i : Fin (n - k)) : Fin n :=
  if h : i.val < b then ⟨i.val, by omega⟩
  else ⟨i.val + k, by omega⟩

/-- Remove exactly the later substring; retain n-k actual bits. -/
def encode (n k b : ℕ) (hb : b + k ≤ n) (x : Bits n) : Bits (n - k) :=
  fun i => x (keptIndex n k b hb i)

/-- Equality of encodings preserves each bit outside the removed interval. -/
theorem encode_eq_at (n k b : ℕ) (hb : b + k ≤ n)
    (x y : Bits n) (heq : encode n k b hb x = encode n k b hb y)
    (j : ℕ) (hj : j < n) (hout : j < b ∨ b + k ≤ j) :
    padBits x j = padBits y j := by
  rcases hout with hbefore | hafter
  · have hj' : j < n - k := by omega
    have hh := congrFun heq (⟨j, hj'⟩ : Fin (n - k))
    simpa only [encode, keptIndex, dite_eq_left hbefore, padBits, dite_eq_left hj] using hh
  · have hj' : j - k < n - k := by omega
    have hbefore : ¬j - k < b := by omega
    have hrestore : j - k + k = j := by omega
    have hh := congrFun heq (⟨j - k, hj'⟩ : Fin (n - k))
    simpa only [encode, keptIndex, dite_eq_right hbefore, hrestore,
      padBits, dite_eq_left hj] using hh

/-- A collision reconstructs each deleted bit from a strictly earlier bit.
No disjointness of the two windows is used. -/
theorem encode_injective_of_agree (n k a b : ℕ) (hab : a < b)
    (hb : b + k ≤ n) (x y : Bits n)
    (hx : Agree (padBits x) a (padBits x) b k)
    (hy : Agree (padBits y) a (padBits y) b k)
    (heq : encode n k b hb x = encode n k b hb y) : x = y := by
  have hall : ∀ j, j < n → padBits x j = padBits y j := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      by_cases hbefore : j < b
      · exact encode_eq_at n k b hb x y heq j hj (Or.inl hbefore)
      by_cases hafter : b + k ≤ j
      · exact encode_eq_at n k b hb x y heq j hj (Or.inr hafter)
      have hoffset : j - b < k := by omega
      have hearlier : a + (j - b) < j := by omega
      have hearlier_bound : a + (j - b) < n := by omega
      have hrestore : b + (j - b) = j := by omega
      have hxcopy := hx (j - b) hoffset
      have hycopy := hy (j - b) hoffset
      rw [hrestore] at hxcopy hycopy
      exact hxcopy.symm.trans ((ih (a + (j - b)) hearlier hearlier_bound).trans hycopy)
  funext j
  simpa only [padBits, dite_eq_left j.isLt] using hall j.val j.isLt

def collisionEncode (n k a b : ℕ) (hb : b + k ≤ n) :
    Collision n k a b → Bits (n - k) :=
  fun x => encode n k b hb x.val

theorem collisionEncode_injective (n k a b : ℕ) (hab : a < b)
    (hb : b + k ≤ n) : Function.Injective (collisionEncode n k a b hb) := by
  intro x y heq
  apply Subtype.ext
  exact encode_injective_of_agree n k a b hab hb x.val y.val x.property y.property heq

/-- The concrete collision set has at most 2^(n-k) members, even when the
windows overlap. The earlier window bound follows already from a<b and hb. -/
theorem collision_card_le (n k a b : ℕ) (hab : a < b)
    (_ha : a + k ≤ n) (hb : b + k ≤ n) :
    Fintype.card (Collision n k a b) ≤ 2 ^ (n - k) := by
  calc
    Fintype.card (Collision n k a b) ≤ Fintype.card (Bits (n - k)) :=
      Fintype.card_le_of_injective (collisionEncode n k a b hb)
        (collisionEncode_injective n k a b hab hb)
    _ = 2 ^ (n - k) := by simp [Bits]

#print axioms encode_injective_of_agree
#print axioms collisionEncode_injective
#print axioms collision_card_le

end DeletionCode.OverlapCollision
