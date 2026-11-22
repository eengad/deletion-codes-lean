import DeletionCode.Explicit.RecognizerState
import DeletionCode.Explicit.CompactReplay
import DeletionCode.Explicit.ReplayGrammar

/-! Chronological gate indices and patch anchors of a retained witness. -/

namespace DeletionCode.Explicit.Recognizer

open LetterGraphCuts RulePatch ReplayEntry ReplayGrammar

variable {ℓ q L s : ℕ}

abbrev RuleVertex (hs : History ℓ q L s) :=
  Fin hs.length ⊕ Fin (PatchTable.patchCount (gates hs))

def retainedEntries (hs : History ℓ q L s) (root : RuleVertex hs) : Finset (Fin (hs.length*s)) :=
  Finset.univ.filter fun j =>
    (finProdFinEquiv.symm j).1 ∈ componentRules (PatchTable.incidence (gates hs)) root

theorem retainedEntries_card (hs : History ℓ q L s) (root : RuleVertex hs) :
    (retainedEntries hs root).card = (componentRules (PatchTable.incidence (gates hs)) root).card*s := by
  let a := PatchTable.incidence (gates hs)
  let S := componentRules a root
  have he : (edges (s := s) S).image finProdFinEquiv = retainedEntries hs root := by
    ext j
    constructor
    · intro hj
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
        rw [Equiv.symm_apply_apply]
        exact (Finset.mem_product.mp he).1⟩
    · intro hj
      exact Finset.mem_image.mpr ⟨finProdFinEquiv.symm j,
        Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hj).2,Finset.mem_univ _⟩,
        Equiv.apply_symm_apply _ _⟩
  rw [← he,Finset.card_image_of_injective _ finProdFinEquiv.injective,edges,Finset.card_product]
  simp [S,a]

def patchAnchor (hs : History ℓ q L s) (p : Fin (PatchTable.patchCount (gates hs))) : Fin ℓ :=
  ((CreationInterval.coalesce (PatchTable.intervals (gates hs))).get p).first

def witnessPatchNumber (hs : History ℓ q L s) (root : RuleVertex hs)
    (p : Fin (PatchTable.patchCount (gates hs))) : ℕ :=
  compactIndex (componentPatches (PatchTable.incidence (gates hs)) root) p.val

def witnessRuleNumber (hs : History ℓ q L s) (root : RuleVertex hs) : ℕ → ℕ :=
  compactIndex (componentRules (PatchTable.incidence (gates hs)) root)

def witnessAnchor (hs : History ℓ q L s) (root : RuleVertex hs) (p : ℕ) : Option (Fin ℓ) :=
  let a := PatchTable.incidence (gates hs)
  if hp : p < (componentPatches a root).card then
    some (patchAnchor hs (originalPatch a root ⟨p,hp⟩).val)
  else none

private theorem witness_number (T : Finset (Fin N)) (i : Fin N) (hi : i ∈ T) :
    compactIndex T i.val = (BackwardSlice.number T ⟨i,hi⟩).val := by
  unfold compactIndex
  rw [dite_eq_left i.isLt,dite_eq_left hi]

theorem witnessAnchor_at (hs : History ℓ q L s) (root : RuleVertex hs)
    (p : Fin (PatchTable.patchCount (gates hs)))
    (hp : p ∈ componentPatches (PatchTable.incidence (gates hs)) root) :
    witnessAnchor hs root (witnessPatchNumber hs root p) = some (patchAnchor hs p) := by
  let a := PatchTable.incidence (gates hs)
  let ix := (componentPatches a root).orderIsoOfFin rfl
  have hnum : witnessPatchNumber hs root p = (ix.symm ⟨p,hp⟩).val := witness_number _ p hp
  unfold witnessAnchor
  rw [hnum,dite_eq_left (ix.symm ⟨p,hp⟩).isLt]
  have h : (originalPatch a root (ix.symm ⟨p,hp⟩)).val = p :=
    congrArg Subtype.val (ix.apply_symm_apply ⟨p,hp⟩)
  change some (patchAnchor hs (originalPatch a root (ix.symm ⟨p,hp⟩)).val) = _
  rw [h]

/-- A gate's patch is retained whenever its rule is retained. -/
theorem witnessEntry_patch (hs : History ℓ q L s) (root : RuleVertex hs)
    (e : Fin hs.length × Fin s) (he : e.1 ∈ componentRules (PatchTable.incidence (gates hs)) root) :
    (PatchTable.incidence (gates hs)) e ∈ componentPatches (PatchTable.incidence (gates hs)) root :=
  (mem_componentPatches _ _ _).mpr (((mem_componentRules ..).mp he).trans (bubble_reaches _ e.1 e.2))

/-- Convert one complete gate record to the new patch labels. The stored
supplier entry numbers are translated only after taking the desired slice. -/
def witnessEntry (hs : History ℓ q L s) (root : RuleVertex hs) (x : Fin ℓ → Fin q)
    (j : Fin (hs.length*s)) : Entry (Fin q) :=
  let e := finProdFinEquiv.symm j
  let p := PatchTable.incidence (gates hs) e
  ((hs.get e.1).bubbles e.2).replayEntry x (witnessPatchNumber hs root p) (patchAnchor hs p)

def witnessLifts (hs : History ℓ q L s) (j : Fin (hs.length*s)) : Completed ℓ (Fin q) :=
  lifts hs (finProdFinEquiv.symm j)

/-- Form the encoded description in chronological slice order, retaining
the designated final-bubble and final-rule markers. -/
def descriptions (hs : History ℓ q L s) (root : RuleVertex hs) (x : Fin ℓ → Fin q)
    (slice : Finset (Fin (hs.length*s))) (inner outer : Fin (hs.length*s) → Bool) :
    List (DecodedEntry q) :=
  List.ofFn fun i : Fin slice.card =>
    let j := BackwardSlice.original slice i
    ⟨(witnessEntry hs root x j).relabel (compactIndex slice) (witnessRuleNumber hs root),
      inner j,outer j⟩

#print axioms retainedEntries_card
#print axioms witnessAnchor_at

end DeletionCode.Explicit.Recognizer
