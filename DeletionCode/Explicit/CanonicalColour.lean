import DeletionCode.Explicit.AffineSolution
import DeletionCode.Explicit.ForestSpan

/-! Canonical colour equations obtained by scanning the catalogue in order. -/

namespace DeletionCode.Explicit.CanonicalColour

open FieldHash

variable {n : ℕ}

abbrev Row (n : ℕ) := Fin n → F₃

def matrix (rows : List (Row n)) : TernaryMatrix rows.length n :=
  fun i => rows.get i

abbrev span (rows : List (Row n)) : Submodule F₃ (Row n) :=
  Submodule.span F₃ {v | v ∈ rows}

theorem range_matrix_row (rows : List (Row n)) :
    Set.range (matrix rows).row = {v | v ∈ rows} := by
  ext v
  exact List.mem_iff_get.symm

def inSpan (rows : List (Row n)) (v : Row n) : Bool :=
  let A := (Matrix.transpose (matrix rows))
  ternaryRank (augment A v) == ternaryRank A

theorem inSpan_iff (rows : List (Row n)) (v : Row n) :
    inSpan rows v = true ↔ v ∈ span rows := by
  rw [inSpan,beq_iff_eq,consistent_iff]
  change v ∈ LinearMap.range ((Matrix.transpose (matrix rows))).mulVecLin ↔ _
  rw [Matrix.range_mulVecLin]
  change v ∈ Submodule.span F₃ (Set.range (matrix rows).row) ↔ _
  rw [range_matrix_row]

private def collect : List (Row n) → List (Row n) → List (Row n)
  | [], old => old
  | v :: next, old =>
    collect next (if inSpan old v then old else v :: old)

private theorem collect_span (next old : List (Row n)) :
    span (collect next old) = span (next ++ old) := by
  induction next generalizing old with
  | nil => rfl
  | cons v next ih =>
    rw [collect,ih]
    have hadd : span (next ++ v :: old) = span ((v :: next) ++ old) := by
      apply congrArg (Submodule.span F₃)
      ext x
      change x ∈ next ++ v :: old ↔ x ∈ (v :: next) ++ old
      simp only [List.mem_append,List.mem_cons]
      tauto
    by_cases hv : inSpan old v = true
    · rw [ite_eq_left hv,← hadd]
      apply le_antisymm
      · apply Submodule.span_mono
        intro x hx
        exact List.mem_append.mpr ((List.mem_append.mp hx).imp_right (List.mem_cons_of_mem _))
      · apply Submodule.span_le.mpr
        intro x hx
        change x ∈ next ++ v :: old at hx
        simp only [List.mem_append,List.mem_cons] at hx
        rcases hx with hn | heq | ho
        · exact Submodule.subset_span (List.mem_append_left _ hn)
        · rw [heq]
          have hold : span old ≤ span (next ++ old) :=
            Submodule.span_mono (fun _ ho => List.mem_append_right _ ho)
          exact hold ((inSpan_iff old v).mp hv)
        · exact Submodule.subset_span (List.mem_append_right _ ho)
    · rw [ite_eq_right hv,hadd]

private theorem collect_independent (next old : List (Row n))
    (h : LinearIndependent F₃ (matrix old).row) :
    LinearIndependent F₃ (matrix (collect next old)).row := by
  induction next generalizing old with
  | nil => exact h
  | cons v next ih =>
    rw [collect]
    by_cases hv : inSpan old v = true
    · exact (ite_eq_left hv) ▸ ih old h
    · rw [ite_eq_right hv]
      apply ih
      apply linearIndependent_finSucc.mpr
      change LinearIndependent F₃ (matrix old).row ∧ v ∉ Submodule.span F₃ (Set.range (matrix old).row)
      rw [range_matrix_row]
      exact ⟨h,fun hm => hv ((inSpan_iff old v).mpr hm)⟩

private theorem mem_of_mem_collect (next old : List (Row n)) {v : Row n}
    (h : v ∈ collect next old) : v ∈ next ++ old := by
  induction next generalizing old with
  | nil => exact h
  | cons r next ih =>
    simp only [collect] at h
    split at h
    · exact List.mem_append.mpr ((List.mem_append.mp (ih old h)).imp_left (List.mem_cons_of_mem _))
    · simpa [List.mem_append,or_comm,or_left_comm] using ih (r :: old) h

/-- The selected catalogue rows, stored in reverse order for a linear scan. -/
def basisRows (catalogue old : List (Row n)) : List (Row n) :=
  collect (catalogue.filter (inSpan old)) []

theorem basisRows_independent (catalogue old : List (Row n)) :
    LinearIndependent F₃ (matrix (basisRows catalogue old)).row :=
  collect_independent _ _ (linearIndependent_empty_type (ι := Fin 0))

theorem basisRows_span (catalogue old : List (Row n))
    (hc : ∀ v ∈ old, v ∈ catalogue) :
    span (basisRows catalogue old) = span old := by
  unfold basisRows
  rw [collect_span,List.append_nil]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv
    exact (inSpan_iff old v).mp (List.mem_filter.mp hv).2
  · apply Submodule.span_mono
    intro v hv
    exact List.mem_filter.mpr ⟨hc v hv,(inSpan_iff old v).mpr (Submodule.subset_span hv)⟩

theorem mem_basisRows (catalogue old : List (Row n)) {v : Row n}
    (h : v ∈ basisRows catalogue old) : v ∈ catalogue ∧ v ∈ span old := by
  have hm : v ∈ catalogue.filter (inSpan old) := by simpa using mem_of_mem_collect _ [] h
  exact ⟨(List.mem_filter.mp hm).1,(inSpan_iff old v).mp (List.mem_filter.mp hm).2⟩

theorem basisRows_congr (catalogue : List (Row n)) {old new : List (Row n)} (h : span old = span new) :
    basisRows catalogue old = basisRows catalogue new := by
  have he : inSpan old = inSpan new := by
    funext v
    apply Bool.eq_iff_iff.mpr
    rw [inSpan_iff,inSpan_iff,h]
  simp [basisRows,he]

private def solveRows (rows : List (Row n)) : Option (Row n) :=
  solveAffine (matrix rows) (fun _ => 1)

def alpha (catalogue old : List (Row n)) : Option (Row n) :=
  solveRows (basisRows catalogue old)

theorem alpha_congr (catalogue : List (Row n)) {old new : List (Row n)} (h : span old = span new) :
    alpha catalogue old = alpha catalogue new :=
  congrArg solveRows (basisRows_congr catalogue h)

theorem alpha_exists (catalogue old : List (Row n)) :
    ∃ a, alpha catalogue old = some a := by
  let rs := basisRows catalogue old
  let A := matrix rs
  have hind := basisRows_independent catalogue old
  have hdim : A.rank = rs.length := by
    rw [Matrix.rank_eq_finrank_span_row,finrank_span_eq_card hind,Fintype.card_fin]
  have htop : LinearMap.range A.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank,Module.finrank_fintype_fun_eq_card] using hdim
  have hone : (fun _ : Fin rs.length => (1 : F₃)) ∈ LinearMap.range A.mulVecLin := by
    rw [htop]
    trivial
  obtain ⟨a,ha,-⟩ := solveAffine_exists A _ hone
  exact ⟨a,ha⟩

theorem innerProduct_one (catalogue old : List (Row n)) {a r : Row n}
    (ha : alpha catalogue old = some a) (hr : r ∈ basisRows catalogue old) :
    dotProduct r a = 1 := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hr
  have he := congrFun (solveAffine_sound (matrix (basisRows catalogue old)) (fun _ => 1) ha) i
  change dotProduct ((basisRows catalogue old).get i) a = 1 at he
  rwa [hi] at he

#print axioms alpha_congr
#print axioms alpha_exists
#print axioms innerProduct_one

end DeletionCode.Explicit.CanonicalColour
