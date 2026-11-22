import DeletionCode.Explicit.FieldHash

/-! Canonical affine solving by repeated Gaussian consistency tests. -/

namespace DeletionCode.Explicit.FieldHash

variable {m n : ℕ}

private def feasible (A : TernaryMatrix m n) (y : Fin m → F₃) (p : Fin n → Option F₃) : Bool :=
  let B := jointMatrix A p
  let target := Fin.append y (fixedTarget p)
  ternaryRank (augment B target) == ternaryRank B

private theorem feasible_iff (A : TernaryMatrix m n) (y : Fin m → F₃) (p : Fin n → Option F₃) :
    feasible A y p = true ↔
      ∃ x, A.mulVec x = y ∧ ∀ i a, p i = some a → x i = a := by
  simp only [feasible,beq_iff_eq,consistent_iff,joint_affine_iff]

private def choices : List F₃ := [0,1,-1]

private theorem mem_choices (a : F₃) : a ∈ choices := by
  have h : ∀ v : F₃, v ∈ choices := by decide
  exact h a

private def assign (A : TernaryMatrix m n) (y : Fin m → F₃) :
    List (Fin n) → (Fin n → Option F₃) → Option (Fin n → Option F₃)
  | [], p => some p
  | i :: is, p => do
    let a ← choices.find? (fun a => feasible A y (Function.update p i (some a)))
    assign A y is (Function.update p i (some a))

private theorem assign_exists (A : TernaryMatrix m n) (y : Fin m → F₃) (is : List (Fin n))
    (p : Fin n → Option F₃) (hp : feasible A y p = true) :
    ∃ r, assign A y is p = some r ∧ feasible A y r = true ∧
      ∀ i, (p i).isSome ∨ i ∈ is → (r i).isSome := by
  induction is generalizing p with
  | nil => exact ⟨p,rfl,hp,by simp⟩
  | cons i is ih =>
    let candidate := fun a => feasible A y (Function.update p i (some a))
    have hfind : ∃ a, choices.find? candidate = some a := by
      obtain ⟨x,hx,hfix⟩ := (feasible_iff A y p).mp hp
      have hchoice : candidate (x i) = true := by
        apply (feasible_iff A y _).mpr
        refine ⟨x,hx,?_⟩
        intro j a ha
        by_cases h : j = i
        · subst j
          simpa using ha
        · exact hfix j a (by simpa [Function.update_of_ne h] using ha)
      cases he : choices.find? candidate with
      | none =>
        have h := List.find?_eq_none.mp he (x i) (mem_choices _)
        simp [hchoice] at h
      | some a => exact ⟨a,rfl⟩
    obtain ⟨a,ha⟩ := hfind
    have hc : candidate a = true := List.find?_some ha
    obtain ⟨r,hr,hgood,hset⟩ := ih (Function.update p i (some a)) hc
    have hstep : assign A y (i :: is) p = some r := by
      change (choices.find? candidate).bind (fun a => assign A y is (Function.update p i (some a))) = some r
      rw [ha]
      exact hr
    refine ⟨r,hstep,hgood,?_⟩
    intro j hj
    apply hset
    rcases hj with hj | hj
    · by_cases hji : j = i
      · subst j
        simp
      · exact Or.inl (by simpa [Function.update_of_ne hji] using hj)
    · rcases List.mem_cons.mp hj with rfl | ht
      · simp
      · exact Or.inr ht

/-- Fix trits from the last coordinate to the first. At each coordinate
keep the first value that leaves the remaining system consistent. -/
def solveAffine (A : TernaryMatrix m n) (y : Fin m → F₃) : Option (Fin n → F₃) :=
  let p : Fin n → Option F₃ := fun _ => none
  if feasible A y p then
    (assign A y (List.finRange n).reverse p).map (fun r i => (r i).getD 0)
  else none

theorem solveAffine_exists (A : TernaryMatrix m n) (y : Fin m → F₃)
    (h : ∃ x, A.mulVec x = y) :
    ∃ x, solveAffine A y = some x ∧ A.mulVec x = y := by
  obtain ⟨x,hx⟩ := h
  let p : Fin n → Option F₃ := fun _ => none
  have hp : feasible A y p = true := (feasible_iff A y p).mpr ⟨x,hx,by simp [p]⟩
  obtain ⟨r,hr,hrf,hset⟩ := assign_exists A y (List.finRange n).reverse p hp
  obtain ⟨out,hout,hfix⟩ := (feasible_iff A y r).mp hrf
  have he : (fun i => (r i).getD 0) = out := by
    funext i
    have hs := hset i (Or.inr (by simp))
    cases hv : r i with
    | none => simp [hv] at hs
    | some a => simpa only [hv,Option.getD_some] using (hfix i a hv).symm
  refine ⟨out,?_,hout⟩
  change (if feasible A y p then (assign A y (List.finRange n).reverse p).map
    (fun r i => (r i).getD 0) else none) = some out
  rw [ite_eq_left hp,hr]
  exact congrArg some he

theorem solveAffine_sound (A : TernaryMatrix m n) (y : Fin m → F₃) {x : Fin n → F₃}
    (h : solveAffine A y = some x) : A.mulVec x = y := by
  have hf : feasible A y (fun _ => none) = true := by
    by_contra hn
    simp [solveAffine,hn] at h
  obtain ⟨w,hw,-⟩ := (feasible_iff A y _).mp hf
  obtain ⟨out,hout,he⟩ := solveAffine_exists A y ⟨w,hw⟩
  rw [h] at hout
  rwa [Option.some.inj hout]

#print axioms solveAffine_exists
#print axioms solveAffine_sound

end DeletionCode.Explicit.FieldHash
