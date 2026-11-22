import DeletionCode.Explicit.Machine.TernaryRank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Rank test for the independent adjunctions of `d:closure-exists`. -/
namespace DeletionCode.Explicit.Machine.Ternary

open FieldHash
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

abbrev Adjunction := MatrixInput × Row

abbrev adjunctionEncoding := encPair matrixEncoding rowEncoding

/-- Test whether prepending a candidate row increases the span. -/
def independentAdjunction (p : Adjunction) : Bool :=
  !(rank (p.1.1, p.2 :: p.1.2) == rank p.1)

theorem independentAdjunction_polyTime :
    ComputableInPolyTime independentAdjunction adjunctionEncoding encBool := by
  have hi := fst matrixEncoding rowEncoding
  have hn := (fst encUnary rowsEncoding).comp hi
  have hr := (snd encUnary rowsEncoding).comp hi
  have ha := snd matrixEncoding rowEncoding
  have hnew := rank_polyTime.comp (hn.prod (cons' ha hr))
  have hold := rank_polyTime.comp hi
  exact bool_not.comp (unary_beq hnew hold)

def vector (n : ℕ) (r : Row) : Fin n → F₃ :=
  fun j => r.getD j.val 0

private theorem range_cons_row (n : ℕ) (r : Row) (xs : Rows) :
    Set.range (matrixOf (n, r :: xs)).row =
      insert (vector n r) (Set.range (matrixOf (n, xs)).row) := by
  ext v
  simp only [Set.mem_range, Set.mem_insert_iff]
  constructor
  · rintro ⟨i, rfl⟩
    cases i using Fin.cases with
    | zero => exact Or.inl rfl
    | succ i => exact Or.inr ⟨i, rfl⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨i.succ, rfl⟩

theorem independentAdjunction_eq_true (p : Adjunction) :
    independentAdjunction p = true ↔
      vector p.1.1 p.2 ∉ Submodule.span F₃ (Set.range (matrixOf p.1).row) := by
  classical
  rcases p with ⟨⟨n, xs⟩, r⟩
  let W := Submodule.span F₃ (Set.range (matrixOf (n, xs)).row)
  let U := Submodule.span F₃ (Set.range (matrixOf (n, r :: xs)).row)
  have hU : U = W ⊔ Submodule.span F₃ {vector n r} := by
    change Submodule.span F₃ (Set.range (matrixOf (n, r :: xs)).row) = _
    rw [range_cons_row, Submodule.span_insert, sup_comm]
  have hle : W ≤ U := hU ▸ le_sup_left
  have hspan : U = W ↔ vector n r ∈ W := by
    rw [hU]
    constructor
    · intro h
      have hh : Submodule.span F₃ {vector n r} ≤ W ⊔ Submodule.span F₃ {vector n r} :=
        le_sup_right
      exact h ▸ hh (Submodule.mem_span_singleton_self _)
    · intro h
      exact sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr h)
  have hdim : Module.finrank F₃ U = Module.finrank F₃ W ↔ U = W := by
    constructor
    · intro he
      exact (Submodule.eq_of_le_of_finrank_le hle he.le).symm
    · intro he
      rw [he]
  simp only [independentAdjunction, Bool.not_eq_true', beq_eq_false_iff_ne, rank_eq,
    ternaryRank_eq, Matrix.rank_eq_finrank_span_row]
  change (Module.finrank F₃ U ≠ Module.finrank F₃ W) ↔ _
  exact not_congr (hdim.trans hspan)

#print axioms independentAdjunction_polyTime
#print axioms independentAdjunction_eq_true

end DeletionCode.Explicit.Machine.Ternary
