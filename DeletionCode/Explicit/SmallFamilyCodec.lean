import DeletionCode.Explicit.FamilyInjective
import Mathlib.Data.Nat.Log

/-! One mixed-radix payload for the literal letters and the member of a small family. -/

namespace DeletionCode.Explicit.SmallFamilyCodec

variable {q ℓ : ℕ}

/-- Read the positions in a set in their original order. -/
def select (S : Finset (Fin ℓ)) (x : Fin ℓ → Fin q) : Fin S.card → Fin q :=
  fun i => x ((S.orderIsoOfFin rfl) i).val

/-- Combine the selected letters with the literal letters of the complement. -/
def assemble (S : Finset (Fin ℓ)) (active : Fin S.card → Fin q)
    (literal : Fin Sᶜ.card → Fin q) : Fin ℓ → Fin q :=
  fun i => if h : i ∈ S then active ((S.orderIsoOfFin rfl).symm ⟨i,h⟩)
    else literal ((Sᶜ.orderIsoOfFin rfl).symm ⟨i,Finset.mem_compl.mpr h⟩)

@[simp] theorem assemble_select (S : Finset (Fin ℓ)) (x : Fin ℓ → Fin q) :
    assemble S (select S x) (select Sᶜ x) = x := by
  funext i
  by_cases h : i ∈ S <;> simp [assemble,select,h]

/-- The family member is the lower digit, with a radix independent of
the source letters or the literal word. -/
def rank (S : Finset (Fin ℓ)) (members : List (Fin S.card → Fin q)) (x : Fin ℓ → Fin q) :
    Option (Fin (q^Sᶜ.card*members.length)) :=
  let i := members.idxOf (select S x)
  if h : i < members.length then
    some (finProdFinEquiv (finFunctionFinEquiv (select Sᶜ x),⟨i,h⟩))
  else none

def unrank (S : Finset (Fin ℓ)) (members : List (Fin S.card → Fin q))
    (k : Fin (q^Sᶜ.card*members.length)) : Fin ℓ → Fin q :=
  let (lit,i) := finProdFinEquiv.symm k
  assemble S (members.get i) (finFunctionFinEquiv.symm lit)

def payloadLength (S : Finset (Fin ℓ)) (members : List (Fin S.card → Fin q)) : ℕ :=
  Nat.clog q (q^Sᶜ.card*members.length)

def encode (hq : 1 < q) (S : Finset (Fin ℓ)) (members : List (Fin S.card → Fin q))
    (x : Fin ℓ → Fin q) : Option (Fin (payloadLength S members) → Fin q) :=
  (rank S members x).map fun k =>
    finFunctionFinEquiv.symm (Fin.castLE (Nat.le_pow_clog hq _) k)

def decode (S : Finset (Fin ℓ)) (members : List (Fin S.card → Fin q))
    (payload : Fin (payloadLength S members) → Fin q) : Option (Fin ℓ → Fin q) :=
  let k := (finFunctionFinEquiv payload).val
  if h : k < q^Sᶜ.card*members.length then some (unrank S members ⟨k,h⟩) else none

theorem rank_roundtrip (S : Finset (Fin ℓ)) (members : List (Fin S.card → Fin q))
    (x : Fin ℓ → Fin q) (hm : select S x ∈ members) :
    ∃ k, rank S members x = some k ∧ unrank S members k = x := by
  have hi : members.idxOf (select S x) < members.length := List.idxOf_lt_length_iff.mpr hm
  refine ⟨finProdFinEquiv (finFunctionFinEquiv (select Sᶜ x),⟨_,hi⟩),?_,?_⟩
  · simp [rank,hi]
  · rw [unrank,Equiv.symm_apply_apply]
    simp

theorem encode_roundtrip (hq : 1 < q) (S : Finset (Fin ℓ))
    (members : List (Fin S.card → Fin q)) (x : Fin ℓ → Fin q) (hm : select S x ∈ members) :
    ∃ packed, encode hq S members x = some packed ∧ decode S members packed = some x := by
  obtain ⟨k,hr,hu⟩ := rank_roundtrip S members x hm
  refine ⟨finFunctionFinEquiv.symm (Fin.castLE (Nat.le_pow_clog hq _) k),?_,?_⟩
  · simp [encode,hr]
  · unfold decode
    rw [Equiv.apply_symm_apply]
    change (if h : k.val < q^Sᶜ.card*members.length then some (unrank S members ⟨k.val,h⟩)
      else none) = some x
    rw [dite_eq_left k.isLt]
    exact congrArg some hu

theorem payloadLength_le (hq : 1 < q) (S : Finset (Fin ℓ))
    (members : List (Fin S.card → Fin q)) :
    payloadLength S members ≤ ℓ-S.card+Nat.clog q members.length := by
  have hc : Sᶜ.card = ℓ-S.card := by simp [Finset.card_compl]
  rw [payloadLength, Nat.clog_le_iff_le_pow hq, ← hc, Nat.pow_add]
  exact Nat.mul_le_mul_left _ (Nat.le_pow_clog hq _)

/-- Rank-ready assignments in the same order as the shape's enumeration. -/
def shapeAssignments (s : BubbleFamilies.Shape q) (K b L Λ : ℕ) (pad : Fin q) :
    List (Fin s.originalCount → Fin q) :=
  (s.members K b L Λ pad).filterMap fun (w,_) =>
    if h : w.length = s.originalCount then some (fun i => w.get (Fin.cast h.symm i)) else none

theorem mem_shapeAssignments (s : BubbleFamilies.Shape q) (K b L Λ : ℕ) (pad : Fin q)
    (values : Fin s.originalCount → Fin q) {w : Borrowed.BubbleWord (Fin q) K b L}
    (hm : s.member K b L Λ pad (List.ofFn values) = some w) :
    values ∈ shapeAssignments s K b L Λ pad := by
  have hpair : (List.ofFn values,w) ∈ s.members K b L Λ pad :=
    (BubbleFamilies.mem_members s K b L Λ pad _ _).mpr ⟨by simp,hm⟩
  apply List.mem_filterMap.mpr
  refine ⟨(List.ofFn values,w),hpair,?_⟩
  simp

#print axioms encode_roundtrip
#print axioms payloadLength_le
#print axioms mem_shapeAssignments

end DeletionCode.Explicit.SmallFamilyCodec
