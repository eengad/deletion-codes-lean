import DeletionCode.Explicit.LabelRecognition
import DeletionCode.Explicit.ReplayFamilyMember
import DeletionCode.Explicit.RecognizerBirth

/-! The recognizer's retained batches carry their original catalogue decomposition. -/

namespace DeletionCode.Explicit.Recognizer

open FieldHash CanonicalColour LetterGraphCuts LetterSequence ReplayEntry LiftDictionary
open PatchSupport RulePatch FirstEvent
open Qary.SignedSupport
open scoped BigOperators

variable {ℓ q K b L Λ R s θ : ℕ}

theorem RecordedBatches.catalogue_rows {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q}
    {x : Fin ℓ → Fin q} {root : Fin ℓ} {hs : History ℓ q L s}
    (h : RecordedBatches P pad x root hs) :
    ∀ row ∈ oldRows hs, row ∈ catalogueRows q K b L s pad := by
  intro row hr
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hb
  obtain ⟨words,hwords,hrow,_⟩ := (h.batch_at i).fromCatalogue
  exact List.mem_map.mpr ⟨words,hwords,hrow.symm⟩

theorem RecordedBatches.nonzero_lifts
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {root : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x root hs) (e : Fin hs.length × Fin s) :
    ∃ g : Gram (Fin q) L, bubbleVector pad x (lifts hs e) g ≠ 0 := by
  classical
  let : Inhabited (Fin q) := ⟨pad⟩
  have hL : 0 < L := by have hb := P.window; omega
  obtain ⟨words,hwords,_,edges,hprep⟩ := (h.batch_at e.1).fromCatalogue
  let one := fun _ : Fin 1 => words e.2
  have hcat := BubbleFamilies.member_catalogue words ((CatalogueEnumeration.mem_rules_iff pad hL words).mp hwords) e.2
  have hn := CatalogueEnumeration.row_ne_zero pad one (by decide) hcat
  by_contra he
  apply hn
  funext col
  let g := finFunctionFinEquiv.symm col
  have hz : bubbleVector pad x (lifts hs e) g = 0 := not_ne_iff.mp (fun h => he ⟨g,h⟩)
  have hv := ((hprep e.2).2.vector_eq (pad := pad) g).symm.trans hz
  change (∑ i : Fin 1, BubbleFamilies.vector pad (one i) col) = 0
  have hg : finFunctionFinEquiv g = col := Equiv.apply_symm_apply _ _
  rw [hg] at hv
  simpa [one] using hv

theorem RecordedBatches.independent
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {root : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x root hs) :
    LinearIndependent F₃ (fun i : Fin hs.length => (hs.get i).row) := by
  apply independent_of_chronology
  intro i hi
  apply (h.batch_at i).outside
  apply Submodule.span_mono _ hi
  rintro _ ⟨j,hij,rfl⟩
  have hlt : j.val < (hs.take i.val).length := by
    have hle := i.isLt
    simp [List.length_take]
    exact hij
  let k : Fin (hs.take i.val).length := ⟨j.val,hlt⟩
  have hk : (hs.take i.val).get k = hs.get j := by
    change (hs.take i.val)[j.val]'hlt = hs[j.val]
    rw [List.getElem_take]
  exact List.mem_map.mpr ⟨hs.get j,hk ▸ List.get_mem (hs.take i.val) k,rfl⟩

/-- For a completed history, the concrete patch supports imply that every
catalogue rule in the computed span is one of the signed recorded rules. -/
theorem RecordedBatches.signed_intersection
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {root : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x root hs)
    {E : Letter ℓ (Fin q) → Letter ℓ (Fin q) → Prop} {marks : Finset (Fin ℓ)}
    (hv : GraphValid pad x b Λ hs E marks) (hx : Strong x K Λ) (hbefore : BeforeEvent hs R)
    (hsiz : 3 ≤ s) (hL : K+2*Λ+1 ≤ L) :
    ∀ v ∈ catalogueRows q K b L s pad, v ∈ span (oldRows hs) →
      ∃ i : Fin hs.length, v = (hs.get i).row ∨ v = -(hs.get i).row := by
  let : Inhabited (Fin q) := ⟨pad⟩
  let a := PatchTable.incidence (gates hs)
  have hforest (i : Fin hs.length) :
      (componentRules a (.inl i)).card*s+1 =
        (componentRules a (.inl i)).card+(componentPatches a (.inl i)).card := by
    have hn := ((componentEvent_eq_false a R i).mp (hbefore i)).2
    have hp : (componentRules a (.inl i)).card+(componentPatches a (.inl i)).card ≤
        (componentRules a (.inl i)).card*s+1 := component_vertices_le a (.inl i)
    omega
  intro v hm hspan
  obtain ⟨words,hmem,rfl⟩ := List.mem_map.mp hm
  have hvalid := (CatalogueEnumeration.mem_rules_iff pad (show 0 < L by omega) words).mp hmem
  let ρ := gramEquiv (q := q) (L := L) (CatalogueEnumeration.row pad words)
  have hn : ρ ≠ 0 := by
    intro hz
    have hp := CatalogueEnumeration.row_ne_zero pad words (show 0 < s by omega) hvalid
    apply hp
    apply (gramEquiv (q := q) (L := L)).injective
    simpa [ρ] using hz
  have hmap : ρ ∈ Submodule.span F₃ (Set.range (ruleVector (lifts hs) pad x L)) := by
    have hw : ρ ∈ historySpace hs := Submodule.mem_map_of_mem hspan
    unfold historySpace at hw
    rw [Submodule.map_span] at hw
    apply Submodule.span_mono _ hw
    rintro _ ⟨u,hu,rfl⟩
    obtain ⟨batch,hb,rfl⟩ := List.mem_map.mp hu
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hb
    refine ⟨i,?_⟩
    rw [← hi]
    exact (funext (hv.vectors i)).symm
  obtain ⟨i,he⟩ := signed_catalogue_rule (gates hs) (lifts hs) x hx hv.fit hsiz hL
    hforest (h.nonzero_lifts) words hvalid hn hmap (CatalogueEnumeration.row_eq_spectrum pad words hvalid)
  have hv' : gramEquiv (q := q) (L := L) (hs.get i).row =
      ruleVector (lifts hs) pad x L i := funext (hv.vectors i)
  refine ⟨i,?_⟩
  rcases he with he | he
  · exact Or.inl ((gramEquiv (q := q) (L := L)).injective (he.trans hv'.symm))
  · right
    apply (gramEquiv (q := q) (L := L)).injective
    rw [map_neg,hv']
    exact he

#print axioms RecordedBatches.independent
#print axioms RecordedBatches.signed_intersection
#print axioms RecordedBatches.nonzero_lifts

end DeletionCode.Explicit.Recognizer
