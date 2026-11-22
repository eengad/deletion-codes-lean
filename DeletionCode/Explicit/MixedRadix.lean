import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Log

/-! A single q-ary rounding for a list of fields of different radices. -/

namespace DeletionCode.Explicit.MixedRadix

def rank : (radices values : List ℕ) → Option (Fin radices.prod)
  | [], [] => some ⟨0,by simp⟩
  | [], _ :: _ => none
  | _ :: _, [] => none
  | r :: rs, v :: vs =>
    if h : v < r then
      (rank rs vs).map (fun k => finProdFinEquiv (⟨v,h⟩,k))
    else none

def unrank : (radices : List ℕ) → Fin radices.prod → List ℕ
  | [], _ => []
  | _ :: rs, k =>
    let (v,tail) := finProdFinEquiv.symm k
    v.val :: unrank rs tail

/-- The digits must have exactly the requested widths. -/
def Fits : List ℕ → List ℕ → Prop := List.Forall₂ (fun radix value => value < radix)

theorem rank_roundtrip {radices values : List ℕ} (hf : Fits radices values) :
    ∃ k, rank radices values = some k ∧ unrank radices k = values := by
  induction hf with
  | nil => exact ⟨⟨0,by simp⟩,rfl,rfl⟩
  | @cons r v rs vs h _ ih =>
    obtain ⟨k,hr,hu⟩ := ih
    let digit : Fin r := ⟨v,h⟩
    refine ⟨finProdFinEquiv (digit,k),?_,?_⟩
    · simp only [rank,dite_eq_left h,hr]
      rfl
    · let f := finProdFinEquiv (m := r) (n := rs.prod)
      change (f.symm (f (digit,k))).1.val :: unrank rs (f.symm (f (digit,k))).2 = v :: vs
      rw [Equiv.symm_apply_apply,hu]

def width (q : ℕ) (radices : List ℕ) : ℕ :=
  Nat.clog q radices.prod

def encode {q : ℕ} (hq : 1 < q) (radices values : List ℕ) :
    Option (Fin (width q radices) → Fin q) :=
  (rank radices values).map (fun k => finFunctionFinEquiv.symm (Fin.castLE (Nat.le_pow_clog hq _) k))

def decode {q : ℕ} (radices : List ℕ) (payload : Fin (width q radices) → Fin q) :
    Option (List ℕ) :=
  let k := (finFunctionFinEquiv payload).val
  if h : k < radices.prod then some (unrank radices ⟨k,h⟩) else none

theorem encode_roundtrip {q : ℕ} (hq : 1 < q) {radices values : List ℕ}
    (h : Fits radices values) :
    ∃ payload, encode hq radices values = some payload ∧ decode radices payload = some values := by
  obtain ⟨k,hr,hu⟩ := rank_roundtrip h
  refine ⟨finFunctionFinEquiv.symm (Fin.castLE (Nat.le_pow_clog hq _) k),by simp [encode,hr],?_⟩
  unfold decode
  rw [Equiv.apply_symm_apply]
  change (if h : k.val < radices.prod then some (unrank radices ⟨k.val,h⟩) else none) = some values
  rw [dite_eq_left k.isLt]
  exact congrArg some hu

theorem width_le {q limit : ℕ} (hq : 1 < q) (radices : List ℕ)
    (h : radices.prod ≤ q^limit) : width q radices ≤ limit :=
  (Nat.clog_le_iff_le_pow hq).mpr h

#print axioms encode_roundtrip
#print axioms width_le

end DeletionCode.Explicit.MixedRadix
