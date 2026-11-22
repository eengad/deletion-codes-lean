import DeletionCode.Explicit.RecognizerWitness
import DeletionCode.Explicit.WitnessMarks

/-! Recover peeler rule and patch indices after restricting to a witness. -/

namespace DeletionCode.Explicit.RulePatch

variable {d s c c' : ℕ}

theorem atPatch_embed (a : Incidence d s c) (f : Fin c → Fin c') (hf : Function.Injective f)
    (S : Finset (Fin d)) (p : Fin c) :
    atPatch (f ∘ a) S (f p) = atPatch a S p := by
  ext e
  simp [atPatch,Function.comp_def,hf.eq_iff]

private theorem pivot_embed (a : Incidence d s c) (f : Fin c → Fin c') (hf : Function.Injective f)
    (S : Finset (Fin d)) : pivot (f ∘ a) S = pivot a S := by
  unfold pivot
  have H (e : Fin d × Fin s) : atPatch (f ∘ a) S ((f ∘ a) e) = atPatch a S (a e) :=
    atPatch_embed a f hf S (a e)
  simp only [H]

theorem peel_embed (a : Incidence d s c) (f : Fin c → Fin c') (hf : Function.Injective f)
    (S : Finset (Fin d)) : peel (f ∘ a) S = peel a S := by
  rw [peel,peel,pivot_embed a f hf]
  split
  next => rfl
  next e he =>
    rw [peel_embed a f hf (S.erase e.1)]
termination_by S.card
decreasing_by exact Finset.card_erase_lt_of_mem (pivot_spec ‹pivot a S = some _›).1

theorem patches_original (a : Incidence d s c) (root : Fin d ⊕ Fin c)
    (S : Finset (Fin (componentRules a root).card)) :
    patches a (S.image (fun i => (originalRule a root i).val)) =
      (patches (componentIncidence a root) S).image (fun p => (originalPatch a root p).val) := by
  ext p
  simp only [patches,Finset.mem_image,edges,Finset.mem_product,Finset.mem_univ,and_true]
  constructor
  · rintro ⟨⟨i,j⟩,⟨r,hr,hri⟩,he⟩
    change (originalRule a root r).val = i at hri
    subst i
    exact ⟨componentIncidence a root (r,j),⟨(r,j),hr,rfl⟩,
      (componentIncidence_original a root r j).trans he⟩
  · rintro ⟨p',⟨⟨i,j⟩,hi,rfl⟩,h⟩
    exact ⟨((originalRule a root i).val,j),⟨i,hi,rfl⟩,
      (componentIncidence_original a root i j).symm.trans h⟩

end DeletionCode.Explicit.RulePatch

namespace DeletionCode.Explicit.Recognizer

open LetterGraphCuts RulePatch

variable {ℓ q L s : ℕ}

/-- The chronological numbering of the retained gates is the Cartesian
order of the retained rules and the original bubbles of each rule. -/
theorem original_entry (hs : History ℓ q L s) (root : RuleVertex hs)
    (r : Fin (componentRules (PatchTable.incidence (gates hs)) root).card) (j : Fin s) :
    let a := PatchTable.incidence (gates hs)
    let n := (componentRules a root).card
    let e : Fin ((retainedEntries hs root).card) :=
      Fin.cast (retainedEntries_card hs root).symm (finProdFinEquiv (r,j) : Fin (n*s))
    BackwardSlice.original (retainedEntries hs root) e =
      finProdFinEquiv ((originalRule a root r).val,j) := by
  dsimp only
  let a := PatchTable.incidence (gates hs)
  let T := retainedEntries hs root
  let U := componentRules a root
  let g (k : Fin (U.card*s)) : Fin (hs.length*s) :=
    let e := finProdFinEquiv.symm k
    finProdFinEquiv ((originalRule a root e.1).val,e.2)
  have lex {n : ℕ} (u v : Fin n × Fin s) :
      (finProdFinEquiv u : Fin (n*s)) < finProdFinEquiv v ↔
        u.1 < v.1 ∨ u.1 = v.1 ∧ u.2 < v.2 := by
    change u.2.val+s*u.1.val < v.2.val+s*v.1.val ↔
      u.1.val < v.1.val ∨ u.1 = v.1 ∧ u.2.val < v.2.val
    rcases lt_trichotomy u.1 v.1 with h | h | h
    · have hl := Nat.mul_le_mul_left s (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at hl
      have hu := u.2.isLt
      exact ⟨fun _ => Or.inl h,fun _ => by omega⟩
    · have hv : u.1.val = v.1.val := congrArg Fin.val h
      rw [hv]
      constructor
      · intro h'
        exact Or.inr ⟨h,by omega⟩
      · rintro (h' | ⟨_,h'⟩) <;> omega
    · have hl := Nat.mul_le_mul_left s (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at hl
      have hv := v.2.isLt
      constructor
      · intro h'
        omega
      · rintro (h' | ⟨h',_⟩)
        · exact (lt_asymm h h').elim
        · exact (ne_of_lt h h'.symm).elim
  have hmono : StrictMono g := by
    intro i k h
    have hi : finProdFinEquiv (finProdFinEquiv.symm i) = i := Equiv.apply_symm_apply _ _
    have hk : finProdFinEquiv (finProdFinEquiv.symm k) = k := Equiv.apply_symm_apply _ _
    rw [← hi,← hk] at h
    rcases (lex _ _).mp h with h' | ⟨he,h'⟩
    · exact (lex _ _).mpr (Or.inl ((U.orderEmbOfFin rfl).strictMono h'))
    · exact (lex _ _).mpr (Or.inr ⟨congrArg (fun p => (originalRule a root p).val) he,h'⟩)
  have hG (k : Fin (U.card*s)) : g k ∈ T := by
    change g k ∈ retainedEntries hs root
    simp only [g,retainedEntries,Finset.mem_filter,Finset.mem_univ,true_and,Equiv.symm_apply_apply]
    exact (originalRule a root (finProdFinEquiv.symm k).1).property
  have he := Finset.orderEmbOfFin_unique (retainedEntries_card hs root) hG hmono
  have hh := congrFun he (finProdFinEquiv (r,j))
  simp only [g,Equiv.symm_apply_apply] at hh
  apply Eq.trans _ hh.symm
  simp only [BackwardSlice.original,Finset.orderEmbOfFin_apply]
  rfl


#print axioms original_entry

end DeletionCode.Explicit.Recognizer
