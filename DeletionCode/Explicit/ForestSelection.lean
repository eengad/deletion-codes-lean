import DeletionCode.Explicit.ForestIntersection

/-! Counting the selected forest inside the executable incidence components. -/

namespace DeletionCode.Explicit.RulePatch

variable {d s c : ℕ}

private theorem originalRule_val_injective (a : Incidence d s c) (root : Fin d ⊕ Fin c) :
    Function.Injective (fun i => (originalRule a root i).val) := by
  intro i j h
  exact (componentRules a root).orderIsoOfFin rfl |>.injective (Subtype.ext h)

private theorem originalPatch_val_injective (a : Incidence d s c) (root : Fin d ⊕ Fin c) :
    Function.Injective (fun p => (originalPatch a root p).val) := by
  intro p q h
  exact (componentPatches a root).orderIsoOfFin rfl |>.injective (Subtype.ext h)

private theorem selected_count_in_component (a : Incidence d s c) (i : Fin d)
    (T : Finset (Fin d)) (hne : T.Nonempty) (hsub : T ⊆ componentRules a (.inl i))
    (hforest : (componentRules a (.inl i)).card*s+1 =
      (componentRules a (.inl i)).card+(componentPatches a (.inl i)).card) :
    T.card*s+1 ≤ T.card+(patches a T).card := by
  let root : Fin d ⊕ Fin c := .inl i
  let ix := componentIncidence a root
  let T' : Finset (Fin (componentRules a root).card) :=
    Finset.univ.filter (fun k => (originalRule a root k).val ∈ T)
  have hT' : T'.image (fun k => (originalRule a root k).val) = T := by
    ext k
    constructor
    · intro hk
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
      exact (Finset.mem_filter.mp hj).2
    · intro hk
      let j := ((componentRules a root).orderIsoOfFin rfl).symm ⟨k,hsub hk⟩
      have hj : (originalRule a root j).val = k := by simp [j,originalRule]
      exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj.symm ▸ hk⟩,hj⟩
  have hP' : (patches ix T').image (fun p => (originalPatch a root p).val) = patches a T := by
    ext p
    constructor
    · intro hp
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨⟨k,j⟩,he,rfl⟩ := Finset.mem_image.mp hu
      have hk := (Finset.mem_filter.mp (Finset.mem_product.mp he).1).2
      exact Finset.mem_image.mpr ⟨((originalRule a root k).val,j),
        Finset.mem_product.mpr ⟨hk,Finset.mem_univ _⟩,(componentIncidence_original a root k j).symm⟩
    · intro hp
      obtain ⟨⟨k,j⟩,he,rfl⟩ := Finset.mem_image.mp hp
      have hk := (Finset.mem_product.mp he).1
      rw [← hT'] at hk
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_image.mpr ⟨ix (u,j),Finset.mem_image.mpr
        ⟨(u,j),Finset.mem_product.mpr ⟨hu,Finset.mem_univ _⟩,rfl⟩,
        componentIncidence_original a root u j⟩
  have hTc : T'.card = T.card := by
    rw [← hT',Finset.card_image_of_injective _ (originalRule_val_injective a root)]
  have hPc : (patches ix T').card = (patches a T).card := by
    rw [← hP',Finset.card_image_of_injective _ (originalPatch_val_injective a root)]
  have hne' : T'.Nonempty := Finset.card_pos.mp (hTc.symm ▸ hne.card_pos)
  have hv := vertices_le ix (componentIncidence_connected a root) T' hne'
  change (componentRules a root).card+(componentPatches a root).card+T'.card*s ≤
    T'.card+(patches ix T').card+(componentRules a root).card*s at hv
  rw [← hforest,hTc,hPc] at hv
  dsimp only [root] at hv
  omega

private theorem patches_union (a : Incidence d s c) (S T : Finset (Fin d)) :
    patches a (S∪T) = patches a S ∪ patches a T := by
  simp [patches,edges,Finset.union_product,Finset.image_union]

private theorem patches_disjoint_component (a : Incidence d s c) (i : Fin d)
    (T U : Finset (Fin d)) (ht : T ⊆ componentRules a (.inl i))
    (hu : ∀ k ∈ U, k ∉ componentRules a (.inl i)) :
    Disjoint (patches a T) (patches a U) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain ⟨⟨j,u⟩,hj,hej⟩ := Finset.mem_image.mp hp
  obtain ⟨⟨k,v⟩,hk,hek⟩ := Finset.mem_image.mp hq
  have hrj := (mem_componentRules a (.inl i) j).mp (ht (Finset.mem_product.mp hj).1)
  have hp' : (graph a).Reachable (.inl i) (.inr p) := by
    rw [← hej]
    exact hrj.trans (bubble_reaches a j u)
  have hrk : (graph a).Reachable (.inl i) (.inl k) := by
    rw [← hek] at hp'
    exact hp'.trans (bubble_reaches a k v).symm
  exact hu k (Finset.mem_product.mp hk).1 ((mem_componentRules a (.inl i) k).mpr hrk)

/-- A nonempty set of rules selected from forest components still has at least
one more vertex than edges, counting each selected bubble as an edge. -/
theorem selected_forest_count (a : Incidence d s c)
    (hforest : ∀ i : Fin d, (componentRules a (.inl i)).card*s+1 =
      (componentRules a (.inl i)).card+(componentPatches a (.inl i)).card)
    (S : Finset (Fin d)) (hne : S.Nonempty) :
    S.card*s+1 ≤ S.card+(patches a S).card := by
  revert hne
  refine Finset.strongInductionOn S ?_
  intro S ih hne
  obtain ⟨i,hi⟩ := hne
  let C := componentRules a (.inl i)
  let T := S ∩ C
  let U := S \ C
  have hiC : i ∈ C := (mem_componentRules a _ _).mpr SimpleGraph.Reachable.rfl
  have hiT : i ∈ T := Finset.mem_inter.mpr ⟨hi,hiC⟩
  have hparts : T ∪ U = S := by
    ext k
    simp only [T,U,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have hd : Disjoint T U := by
    exact Finset.disjoint_left.mpr fun k ht hu => (Finset.mem_sdiff.mp hu).2 (Finset.mem_inter.mp ht).2
  have hpd := patches_disjoint_component a i T U
    (fun _ ht => (Finset.mem_inter.mp ht).2) (fun _ hu => (Finset.mem_sdiff.mp hu).2)
  have hc := selected_count_in_component a i T ⟨i,hiT⟩ (fun _ ht => (Finset.mem_inter.mp ht).2) (hforest i)
  have htU : U ⊂ S := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.sdiff_subset,fun heq => (Finset.mem_sdiff.mp (heq ▸ hi)).2 hiC⟩
  have hU : U.card*s ≤ U.card+(patches a U).card := by
    by_cases h : U.Nonempty
    · exact (Nat.le_succ _).trans (ih U htU h)
    · rw [Finset.not_nonempty_iff_eq_empty.mp h]
      simp
  have hsc : S.card = T.card+U.card := by
    rw [← hparts,Finset.card_union_of_disjoint hd]
  have hpc : (patches a S).card = (patches a T).card+(patches a U).card := by
    rw [← hparts,patches_union,Finset.card_union_of_disjoint hpd]
  rw [hsc,hpc,Nat.add_mul]
  omega

#print axioms selected_forest_count

end DeletionCode.Explicit.RulePatch
