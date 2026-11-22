import DeletionCode.Explicit.CanonicalColour

/-! A signed basis representative changes the colour even when its hash is zero. -/

namespace DeletionCode.Explicit.CanonicalColour

open FieldHash

variable {n d θ : ℕ}

/-- If the intersection consists of signed independent generators, the
canonical basis has one of the signs of every generator. -/
theorem basisRows_contains_signed (catalogue old : List (Row n)) (source : Fin d → Row n)
    (hspan : span old = Submodule.span F₃ (Set.range source))
    (hind : LinearIndependent F₃ source) (hc : ∀ v ∈ old, v ∈ catalogue)
    (hinter : ∀ v ∈ catalogue, v ∈ span old → ∃ i, v = source i ∨ v = -source i)
    (i : Fin d) :
    source i ∈ basisRows catalogue old ∨ -source i ∈ basisRows catalogue old := by
  classical
  by_contra hn
  let other := Submodule.span F₃ (source '' (Set.univ \ {i}))
  have hle : span (basisRows catalogue old) ≤ other := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨hm,hs⟩ := mem_basisRows catalogue old hv
    obtain ⟨j,hj⟩ := hinter v hm hs
    have hji : j ≠ i := by
      intro he
      subst j
      rcases hj with h | h
      · exact hn (Or.inl (h ▸ hv))
      · exact hn (Or.inr (h ▸ hv))
    have hbase : source j ∈ other :=
      Submodule.subset_span ⟨j,⟨Set.mem_univ _,hji⟩,rfl⟩
    rcases hj with h | h
    · exact h.symm ▸ hbase
    · exact h.symm ▸ other.neg_mem hbase
  rw [basisRows_span catalogue old hc,hspan] at hle
  exact (linearIndependent_iff_notMem_span.mp hind i) (hle (Submodule.subset_span ⟨i,rfl⟩))

theorem innerProduct_nonzero (catalogue old : List (Row n)) (source : Fin d → Row n)
    (hspan : span old = Submodule.span F₃ (Set.range source))
    (hind : LinearIndependent F₃ source) (hc : ∀ v ∈ old, v ∈ catalogue)
    (hinter : ∀ v ∈ catalogue, v ∈ span old → ∃ i, v = source i ∨ v = -source i)
    {a ρ : Row n} (ha : alpha catalogue old = some a)
    (hrc : ρ ∈ catalogue) (hr : ρ ∈ span old) :
    dotProduct ρ a ≠ 0 := by
  obtain ⟨i,hi⟩ := hinter ρ hrc hr
  have he : dotProduct (source i) a ≠ 0 := by
    rcases basisRows_contains_signed catalogue old source hspan hind hc hinter i with hb | hb
    · rw [innerProduct_one catalogue old ha hb]
      exact one_ne_zero
    · have h := innerProduct_one catalogue old ha hb
      rw [neg_dotProduct] at h
      intro hz
      simp [hz] at h
  rcases hi with rfl | rfl
  · exact he
  · simpa [neg_dotProduct] using he

def labelPair (H : TernaryMatrix θ n) (catalogue old : List (Row n)) (v : Row n) :
    Option (Row θ × F₃) :=
  (alpha catalogue old).map fun a => (H.mulVec v, dotProduct v a)

theorem labelPair_separates (H : TernaryMatrix θ n) (catalogue old new : List (Row n))
    (source : Fin d → Row n) (hspan : span old = Submodule.span F₃ (Set.range source))
    (hind : LinearIndependent F₃ source) (hc : ∀ v ∈ old, v ∈ catalogue)
    (hinter : ∀ v ∈ catalogue, v ∈ span old → ∃ i, v = source i ∨ v = -source i)
    (hcl : span old = span new) {v ρ : Row n}
    (hrc : ρ ∈ catalogue) (hr : ρ ∈ span old) :
    labelPair H catalogue old v ≠ labelPair H catalogue new (v+ρ) := by
  obtain ⟨a,ha⟩ := alpha_exists catalogue old
  have ha' := (alpha_congr catalogue hcl).symm.trans ha
  have hn := innerProduct_nonzero catalogue old source hspan hind hc hinter ha hrc hr
  unfold labelPair
  rw [ha,ha']
  intro he
  have hs := congrArg Prod.snd (Option.some.inj he)
  change dotProduct v a = dotProduct (v+ρ) a at hs
  rw [add_dotProduct] at hs
  exact hn (add_left_cancel ((add_zero (dotProduct v a)).trans hs).symm)

private def trit (a : F₃) : Fin 3 := ⟨a.val,ZMod.val_lt a⟩

private theorem trit_injective : Function.Injective trit :=
  fun _ _ h => ZMod.val_injective 3 (congrArg Fin.val h)

def packLabel (z : Row θ × F₃) : Fin (3^θ*3) :=
  finProdFinEquiv (finFunctionFinEquiv (fun i => trit (z.1 i)), trit z.2)

theorem packLabel_injective : Function.Injective (packLabel (θ := θ)) := by
  intro x y h
  obtain ⟨h₁,h₂⟩ := Prod.mk.inj (finProdFinEquiv.injective h)
  refine Prod.ext (funext fun i => trit_injective (congrFun (finFunctionFinEquiv.injective h₁) i)) ?_
  exact trit_injective h₂

theorem packLabel_bound (z : Row θ × F₃) : (packLabel z).val < 3*(3^θ) := by
  exact (packLabel z).isLt.trans_le (le_of_eq (Nat.mul_comm _ _))

#print axioms labelPair_separates
#print axioms packLabel_injective

end DeletionCode.Explicit.CanonicalColour
