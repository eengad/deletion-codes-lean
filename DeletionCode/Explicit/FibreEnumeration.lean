import DeletionCode.Explicit.CanonicalColour
import DeletionCode.Explicit.EditBallCount

/-! Enumerate a local zero-one fibre by testing just the binary assignments
on separating columns of its spanning matrix. -/

namespace DeletionCode.Explicit.FibreEnumeration

open FieldHash CanonicalColour

variable {n : ℕ}

abbrev IsBoolean (v : Row n) : Prop := ∀ j, v j = 0 ∨ v j = 1

def check (v : Row n) : Bool :=
  (List.finRange n).all (fun j => v j == 0 || v j == 1)

theorem check_iff (v : Row n) : check v = true ↔ IsBoolean v := by
  simp [check,List.all_eq_true]

def column (rows : List (Row n)) (j : Fin n) : Row rows.length :=
  fun i => rows.get i j

def image (rows : List (Row n)) (a : Row rows.length) : Row n :=
  fun j => dotProduct (column rows j) a

private def columns (rows : List (Row n)) : List (Row rows.length) :=
  (List.finRange n).map (column rows)

private def chosen (rows : List (Row n)) : List (Row rows.length) :=
  basisRows (columns rows) (columns rows)

def separating (rows : List (Row n)) : List (Fin n) :=
  (chosen rows).filterMap fun col =>
    let j := (columns rows).idxOf col
    if hj : j < n then some ⟨j,hj⟩ else none

private theorem column_mem (rows : List (Row n)) (j : Fin n) : column rows j ∈ columns rows :=
  List.mem_map.mpr ⟨j,by simp,rfl⟩

private theorem exists_separating (rows : List (Row n)) {v : Row rows.length}
    (hv : v ∈ chosen rows) : ∃ j ∈ separating rows, column rows j = v := by
  have hm := (mem_basisRows (columns rows) (columns rows) hv).1
  have hlt : (columns rows).idxOf v < (columns rows).length := List.idxOf_lt_length_iff.mpr hm
  have hlt' : (columns rows).idxOf v < n := by simpa [columns] using hlt
  let j : Fin n := ⟨(columns rows).idxOf v,hlt'⟩
  refine ⟨j,List.mem_filterMap.mpr ⟨v,hv,by simp [hlt',j]⟩,?_⟩
  have he := List.getElem_idxOf hlt
  simp only [columns,List.getElem_map,List.getElem_finRange] at he
  exact he

theorem image_eq_of_agree (rows : List (Row n)) {a b : Row rows.length}
    (h : ∀ j ∈ separating rows, image rows a j = image rows b j) : image rows a = image rows b := by
  funext j
  have hs := basisRows_span (columns rows) (columns rows) (fun _ hx => hx)
  have hmem : column rows j ∈ span (chosen rows) := by
    change column rows j ∈ span (basisRows (columns rows) (columns rows))
    rw [hs]
    exact Submodule.subset_span (column_mem rows j)
  have he (col : Row rows.length) (hc : col ∈ span (chosen rows)) :
      dotProduct col a = dotProduct col b := by
    induction hc using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨p,hp,rfl⟩ := exists_separating rows hv
      exact h p hp
    | zero => simp
    | add x y _ _ h₁ h₂ => rw [add_dotProduct,add_dotProduct,h₁,h₂]
    | smul r x _ hx => rw [smul_dotProduct,smul_dotProduct,hx]
  exact he (column rows j) hmem

theorem separating_length (rows : List (Row n)) : (separating rows).length ≤ rows.length := by
  apply (List.length_filterMap_le _ _).trans
  have h := basisRows_independent (columns rows) (columns rows)
  simpa [chosen,Module.finrank_fintype_fun_eq_card] using h.fintype_card_le_finrank

private def restrictedMatrix (rows : List (Row n)) :
    TernaryMatrix (separating rows).length rows.length :=
  fun i => column rows ((separating rows).get i)

private def bitsOf (rows : List (Row n)) (v : Row n) : QWord 2 :=
  List.ofFn (fun i : Fin (separating rows).length =>
    if v ((separating rows).get i) = 0 then 0 else 1)

private def target (rows : List (Row n)) (v : Row n) (bits : QWord 2) :
    Fin (separating rows).length → F₃ :=
  fun i => ((bits.getD i.val 0).val : F₃) - v ((separating rows).get i)

/-- Solving on the selected columns is sufficient even before knowing
whether the reconstructed full vector has only zero and one entries. -/
def enumerate (rows : List (Row n)) (v : Row n) : List (Row n) :=
  (wordsOfLength 2 (separating rows).length).filterMap fun bits => do
    let a ← solveAffine (restrictedMatrix rows) (target rows v bits)
    let u := v + image rows a
    if check u then some u else none

theorem enumerate_length (rows : List (Row n)) (v : Row n) :
    (enumerate rows v).length ≤ 2^rows.length := by
  apply (List.length_filterMap_le _ _).trans
  rw [length_wordsOfLength]
  exact Nat.pow_le_pow_right (by decide) (separating_length rows)

theorem mem_enumerate (rows : List (Row n)) (v u : Row n) :
    u ∈ enumerate rows v ↔ IsBoolean u ∧ ∃ a, u = v+image rows a := by
  constructor
  · intro h
    obtain ⟨bits,_,he⟩ := List.mem_filterMap.mp h
    cases ha : solveAffine (restrictedMatrix rows) (target rows v bits) with
    | none => simp [ha] at he
    | some a =>
      by_cases hc : check (v+image rows a) = true
      · have hu : v+image rows a = u := by simpa [ha,hc] using he
        exact ⟨hu ▸ (check_iff _).mp hc,⟨a,hu.symm⟩⟩
      · simp [ha,hc] at he
  · rintro ⟨hu,a,he⟩
    have hrhs : (restrictedMatrix rows).mulVec a = target rows v (bitsOf rows u) := by
      funext i
      let j := (separating rows).get i
      have hj := congrFun he j
      change u j = v j + image rows a j at hj
      have hbit : (( ((bitsOf rows u).getD i.val 0).val : ℕ) : F₃) = u j := by
        simp only [bitsOf,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
          dite_eq_left i.isLt,Option.getD_some]
        change ((if u j = 0 then (0 : Fin 2) else 1).val : F₃) = u j
        rcases hu j with hz | ho
        · simp [hz]
        · simp [ho]
      change image rows a j = (( ((bitsOf rows u).getD i.val 0).val : ℕ) : F₃) - v j
      rw [hbit,hj]
      abel
    obtain ⟨b,hb,hsol⟩ := solveAffine_exists _ _ ⟨a,hrhs⟩
    have him : image rows b = image rows a := by
      apply image_eq_of_agree
      intro j hj
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hj
      exact hi ▸ congrFun (hsol.trans hrhs.symm) i
    refine List.mem_filterMap.mpr ⟨bitsOf rows u, mem_wordsOfLength.mpr (by simp [bitsOf]),?_⟩
    have hh := (check_iff u).mpr hu
    simp [hb,him,← he,hh]

#print axioms enumerate_length
#print axioms mem_enumerate

end DeletionCode.Explicit.FibreEnumeration
