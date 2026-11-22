import DeletionCode.Explicit.FibreEnumeration

/-! Test exposure on the executable local fibres of disjoint components. -/

namespace DeletionCode.Explicit.ComponentExposure

open FieldHash CanonicalColour FibreEnumeration
open scoped BigOperators

variable {n m : ℕ}

def occupies (rows : List (Row n)) (g : Fin n) : Bool :=
  rows.any (fun row => row g != 0)

private def allowed (z : F₃) : Bool := z == 0 || z == 1

private theorem allowed_iff (z : F₃) : allowed z = true ↔ z = 0 ∨ z = 1 := by
  simp [allowed]

theorem occupies_iff (rows : List (Row n)) (g : Fin n) :
    occupies rows g = true ↔ ∃ row ∈ rows, row g ≠ 0 := by
  simp [occupies,List.any_eq_true]

private theorem image_zero (rows : List (Row n)) (a : Row rows.length) {g : Fin n}
    (h : occupies rows g ≠ true) : image rows a g = 0 := by
  have hz : column rows g = 0 := by
    funext i
    change rows[i.val] g = 0
    by_contra hn
    exact h ((occupies_iff rows g).mpr ⟨_,List.get_mem ..,hn⟩)
  simp [image,hz]

def check (parts : Fin m → List (Row n)) (v ρ : Row n) : Bool :=
  (List.finRange n).all (fun g =>
    (List.finRange m).any (fun i => occupies (parts i) g) || allowed (v g + ρ g)) &&
  (List.finRange m).all (fun i =>
    (enumerate (parts i) v).any (fun u =>
      (List.finRange n).all (fun g => !occupies (parts i) g || allowed (u g + ρ g))))

private def total (parts : Fin m → List (Row n)) (v : Row n)
    (a : (i : Fin m) → Row (parts i).length) : Row n :=
  fun g => v g + ∑ i, image (parts i) (a i) g

private theorem total_at (parts : Fin m → List (Row n)) (v : Row n)
    (a : (i : Fin m) → Row (parts i).length)
    (hp : ∀ {i j : Fin m}, i ≠ j → ∀ g, occupies (parts i) g = true → occupies (parts j) g ≠ true)
    (i : Fin m) (g : Fin n) (hi : occupies (parts i) g = true) :
    total parts v a g = (v + image (parts i) (a i)) g := by
  unfold total
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun j _ hj =>
    image_zero _ _ (hp hj.symm g hi))]
  rfl

private theorem total_off (parts : Fin m → List (Row n)) (v : Row n)
    (a : (i : Fin m) → Row (parts i).length) (g : Fin n)
    (h : ¬ ∃ i, occupies (parts i) g = true) :
    total parts v a g = v g := by
  unfold total
  rw [Finset.sum_eq_zero,add_zero]
  intro i _
  exact image_zero _ _ (fun hi => h ⟨i,hi⟩)

/-- Given disjoint component supports, testing all factors separately is
equivalent to finding one global zero-one pseudostate witnessing exposure. -/
theorem check_iff (parts : Fin m → List (Row n)) (v ρ : Row n) (hv : IsBoolean v)
    (hp : ∀ {i j : Fin m}, i ≠ j → ∀ g, occupies (parts i) g = true → occupies (parts j) g ≠ true) :
    check parts v ρ = true ↔ ∃ a : (i : Fin m) → Row (parts i).length,
      IsBoolean (total parts v a) ∧ IsBoolean (total parts v a+ρ) := by
  classical
  have hout : (List.finRange n).all (fun g =>
      (List.finRange m).any (fun i => occupies (parts i) g) || allowed (v g + ρ g)) = true ↔
      ∀ g, (¬ ∃ i, occupies (parts i) g = true) → allowed (v g + ρ g) = true := by
    simp only [List.all_eq_true,List.mem_finRange,true_implies,Bool.or_eq_true_iff,
      List.any_eq_true,true_and]
    constructor
    · intro h g hn
      exact (h g).resolve_left hn
    · intro h g
      by_cases hg : ∃ i, occupies (parts i) g = true
      · exact Or.inl hg
      · exact Or.inr (h g hg)
  have hlocal (i : Fin m) (u : Row n) :
      (List.finRange n).all (fun g => !occupies (parts i) g || allowed (u g+ρ g)) = true ↔
      ∀ g, occupies (parts i) g = true → allowed (u g+ρ g) = true := by
    simp only [List.all_eq_true,List.mem_finRange,true_implies,Bool.or_eq_true_iff]
    constructor
    · intro h g hg
      exact (h g).resolve_left (by simp [hg])
    · intro h g
      by_cases hg : occupies (parts i) g = true
      · exact Or.inr (h g hg)
      · exact Or.inl (by simpa using hg)
  unfold check
  rw [Bool.and_eq_true_iff,hout]
  constructor
  · rintro ⟨hoff,hall⟩
    have hcomponent (i : Fin m) :
        ∃ a : Row (parts i).length, IsBoolean (v+image (parts i) a) ∧
          ∀ g, occupies (parts i) g = true → allowed ((v+image (parts i) a) g+ρ g) = true := by
      obtain ⟨u,hu,hreq⟩ := List.any_eq_true.mp (List.all_eq_true.mp hall i (by simp))
      obtain ⟨hb,a,rfl⟩ := (mem_enumerate (parts i) v u).mp hu
      exact ⟨a,hb,(hlocal i _).mp hreq⟩
    choose a hbool hreq using hcomponent
    refine ⟨a,?_,?_⟩
    · intro g
      by_cases h : ∃ i, occupies (parts i) g = true
      · obtain ⟨i,hi⟩ := h
        rw [total_at parts v a hp i g hi]
        exact hbool i g
      · rw [total_off parts v a g h]
        exact hv g
    · intro g
      apply (allowed_iff _).mp
      change allowed (total parts v a g+ρ g) = true
      by_cases h : ∃ i, occupies (parts i) g = true
      · obtain ⟨i,hi⟩ := h
        rw [total_at parts v a hp i g hi]
        exact hreq i g hi
      · rw [total_off parts v a g h]
        exact hoff g h
  · rintro ⟨a,hu,hru⟩
    refine ⟨?_,List.all_eq_true.mpr ?_⟩
    · intro g hg
      apply (allowed_iff _).mpr
      simpa only [Pi.add_apply,total_off parts v a g hg] using hru g
    · intro i _
      let u := v+image (parts i) (a i)
      apply List.any_eq_true.mpr
      refine ⟨u,(mem_enumerate _ _ _).mpr ⟨?_,⟨a i,rfl⟩⟩,(hlocal i u).mpr ?_⟩
      · intro g
        by_cases hg : occupies (parts i) g = true
        · simpa only [total_at parts v a hp i g hg] using hu g
        · simpa [u,Pi.add_apply,image_zero (parts i) (a i) hg] using hv g
      · intro g hg
        apply (allowed_iff _).mpr
        simpa only [u,Pi.add_apply,total_at parts v a hp i g hg] using hru g

private theorem image_eq_mulVec (rows : List (Row n)) (a : Row rows.length) :
    image rows a = (Matrix.transpose (matrix rows)).mulVec a := by
  funext g
  rfl

private theorem range_transpose (rows : List (Row n)) :
    LinearMap.range (Matrix.transpose (matrix rows)).mulVecLin = span rows := by
  rw [Matrix.range_mulVecLin]
  change Submodule.span F₃ (Set.range (matrix rows).row) = Submodule.span F₃ {v | v ∈ rows}
  rw [range_matrix_row]

theorem image_mem_span (rows : List (Row n)) (a : Row rows.length) :
    image rows a ∈ span rows := by
  rw [← range_transpose, image_eq_mulVec]
  exact ⟨a,rfl⟩

private theorem image_zero_coeff (rows : List (Row n)) : image rows 0 = 0 := by
  rw [image_eq_mulVec,Matrix.mulVec_zero]

private theorem image_add (rows : List (Row n)) (a b : Row rows.length) :
    image rows (a+b) = image rows a+image rows b := by
  funext g
  exact dotProduct_add _ _ _

private theorem image_smul (rows : List (Row n)) (r : F₃) (a : Row rows.length) :
    image rows (r • a) = r • image rows a := by
  funext g
  exact dotProduct_smul _ _ _

def flatRows (parts : Fin m → List (Row n)) : List (Row n) :=
  (List.finRange m).flatMap parts

private theorem mem_flatRows {parts : Fin m → List (Row n)} {row : Row n} :
    row ∈ flatRows parts ↔ ∃ i, row ∈ parts i := by
  simp [flatRows,List.mem_flatMap]

private theorem mem_span_parts (parts : Fin m → List (Row n)) (w : Row n) :
    w ∈ span (flatRows parts) ↔
    ∃ a : (i : Fin m) → Row (parts i).length, (∑ i, image (parts i) (a i)) = w := by
  classical
  constructor
  · intro hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i,hi⟩ := mem_flatRows.mp hx
      let M := Matrix.transpose (matrix (parts i))
      have hspan : span (parts i) = LinearMap.range M.mulVecLin := (range_transpose _).symm
      have hc : x ∈ LinearMap.range M.mulVecLin := hspan ▸ Submodule.subset_span hi
      obtain ⟨a,ha⟩ := hc
      refine ⟨fun j => if h : j = i then h.symm ▸ a else 0,?_⟩
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun j _ hj => ?_)]
      · have he : image (parts i) a = x := (image_eq_mulVec _ _).trans ha
        simpa using he
      · simp only [dite_eq_right hj,image_zero_coeff]
    | zero =>
      exact ⟨fun _ => 0,by simp only [image_zero_coeff,Finset.sum_const_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a,ha⟩ := hx
      obtain ⟨b,hb⟩ := hy
      exact ⟨fun i => a i+b i,by simp_rw [image_add,Finset.sum_add_distrib,ha,hb]⟩
    | smul r x _ hx =>
      obtain ⟨a,ha⟩ := hx
      exact ⟨fun i => r • a i,by simp_rw [image_smul,← Finset.smul_sum,ha]⟩
  · rintro ⟨a,rfl⟩
    apply Submodule.sum_mem
    intro i _
    have hle : span (parts i) ≤ span (flatRows parts) :=
      Submodule.span_mono (fun _ hz => mem_flatRows.mpr ⟨i,hz⟩)
    exact hle (image_mem_span _ _)

/-- The test decides exposure over the span of all the component rows. -/
theorem check_span (parts : Fin m → List (Row n)) (v ρ : Row n) (hv : IsBoolean v)
    (hp : ∀ {i j : Fin m}, i ≠ j → ∀ g, occupies (parts i) g = true → occupies (parts j) g ≠ true) :
    check parts v ρ = true ↔ ∃ w ∈ span (flatRows parts), IsBoolean (v+w) ∧ IsBoolean (v+w+ρ) := by
  rw [check_iff parts v ρ hv hp]
  have htotal (a : (i : Fin m) → Row (parts i).length) :
      total parts v a = v + ∑ i, image (parts i) (a i) := by
    funext g
    simp [total,Finset.sum_apply]
  constructor
  · rintro ⟨a,h₁,h₂⟩
    rw [htotal] at h₁ h₂
    exact ⟨_,(mem_span_parts parts _).mpr ⟨a,rfl⟩,h₁,h₂⟩
  · rintro ⟨w,hw,h₁,h₂⟩
    obtain ⟨a,rfl⟩ := (mem_span_parts parts w).mp hw
    exact ⟨a,htotal a ▸ h₁,htotal a ▸ h₂⟩

#print axioms check_span

end DeletionCode.Explicit.ComponentExposure
