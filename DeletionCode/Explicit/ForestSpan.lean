import DeletionCode.Explicit.ForestSelection

/-! The intersection of a catalogue and the span before a first event. -/

namespace DeletionCode.Explicit.RulePatch

open FieldHash
open scoped BigOperators

variable {d s c : ℕ} {γ : Type*}

/-- Every rule meets a given patch in at most one bubble in a forest. -/
theorem incidence_injective_of_forest (a : Incidence d s c)
    (hforest : ∀ i : Fin d, (componentRules a (.inl i)).card*s+1 =
      (componentRules a (.inl i)).card+(componentPatches a (.inl i)).card)
    (i : Fin d) : Function.Injective (fun j : Fin s => a (i,j)) := by
  let f := fun j : Fin s => a (i,j)
  have he : patches a {i} = Finset.univ.image f := by
    ext p
    constructor
    · intro hp
      obtain ⟨⟨k,j⟩,he,heq⟩ := Finset.mem_image.mp hp
      have eq : k = i := Finset.mem_singleton.mp (Finset.mem_product.mp he).1
      subst k
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,heq⟩
    · intro hp
      obtain ⟨j,_,he⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_product.mpr
        ⟨Finset.mem_singleton_self _,Finset.mem_univ _⟩,he⟩
  have h := selected_forest_count a hforest {i} (Finset.singleton_nonempty i)
  rw [he,Finset.card_singleton,Nat.one_mul] at h
  have hlo : (Finset.univ : Finset (Fin s)).card ≤ (Finset.univ.image f).card := by
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  have hcard := Nat.le_antisymm Finset.card_image_le hlo
  exact fun x y hxy => (Finset.card_image_iff.mp hcard) (Finset.mem_univ x) (Finset.mem_univ y) hxy

/-- A vector written as a sum of bubbles, each supported in its designated
patch, occupies at most one patch per bubble. -/
theorem occupied_le_card_image {ι : Type*} [Fintype ι]
    (support : Fin c → Finset γ) (label : ι → Fin c) (bubble : ι → γ → F₃)
    (hdis : Pairwise (fun p p' => Disjoint (support p) (support p')))
    (hfit : ∀ j g, bubble j g ≠ 0 → g ∈ support (label j)) :
    occupied support (fun g => ∑ j, bubble j g) ⊆ Finset.univ.image label := by
  intro p hp
  obtain ⟨g,hg⟩ := (Finset.mem_filter.mp hp).2
  obtain ⟨hgs,hgn⟩ := Finset.mem_filter.mp hg
  by_contra hn
  apply hgn
  apply Finset.sum_eq_zero
  intro j _
  by_contra hne
  have hp' := hfit j g hne
  have hpe : label j ≠ p := fun he => hn (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,he⟩)
  exact Finset.disjoint_left.mp (hdis hpe) hp' hgs

/-- In the span of a patch forest, every nonzero vector occupying at most
`s` patches equals one of the signed original rules. -/
theorem signed_rule_of_span (a : Incidence d s c) (support : Fin c → Finset γ)
    (rows : Fin d → γ → F₃) (hs : 3 ≤ s)
    (hforest : ∀ i : Fin d, (componentRules a (.inl i)).card*s+1 =
      (componentRules a (.inl i)).card+(componentPatches a (.inl i)).card)
    (hnonzero : ∀ e : Fin d × Fin s, ∃ g ∈ support (a e), rows e.1 g ≠ 0)
    (hvanish : ∀ i p, (∀ j, a (i,j) ≠ p) → ∀ g ∈ support p, rows i g = 0)
    {ρ : γ → F₃} (hρ : ρ ≠ 0) (hmem : ρ ∈ Submodule.span F₃ (Set.range rows))
    (hbound : (occupied support ρ).card ≤ s) :
    ∃ i, ρ = rows i ∨ ρ = -rows i := by
  obtain ⟨coeff,hcoeff⟩ := (Submodule.mem_span_range_iff_exists_fun F₃).mp hmem
  let I := Finset.univ.filter (fun i => coeff i ≠ 0)
  have he : (fun g => ∑ i ∈ I, coeff i*rows i g) = ρ := by
    funext g
    have hc := congrFun hcoeff g
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hc
    apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).trans hc
    intro i _ hi
    have hz : coeff i = 0 := by
      by_contra h
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    rw [hz,zero_mul]
  have hne : I.Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [hz] at he
    apply hρ
    change ρ = fun _ => 0
    simpa using he.symm
  have hc := one_rule_of_patch_bound a support rows I coeff hs (selected_forest_count a hforest I hne)
    (fun _ hi => (Finset.mem_filter.mp hi).2) hnonzero hvanish (by rw [he]; exact hbound)
  have card : I.card = 1 := Nat.le_antisymm hc hne.card_pos
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp card
  have him : i ∈ I := by rw [hi]; simp
  have hci := (Finset.mem_filter.mp him).2
  have all : ∀ z : F₃, z = 0 ∨ z = 1 ∨ z = -1 := by decide
  refine ⟨i,?_⟩
  rcases (all (coeff i)).resolve_left hci with hv | hv <;>
    rw [hi] at he <;> simp only [Finset.sum_singleton,hv] at he
  · exact Or.inl (by simpa using he.symm)
  · right
    change ρ = fun g => -rows i g
    simpa using he.symm

#print axioms incidence_injective_of_forest
#print axioms signed_rule_of_span

end DeletionCode.Explicit.RulePatch
