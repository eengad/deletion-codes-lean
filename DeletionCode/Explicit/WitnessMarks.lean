import DeletionCode.Explicit.WitnessAnchors

/-! Rule marks identify exactly the final rule and bubble sets of a slice. -/

namespace DeletionCode.Explicit.Recognizer

open LetterGraphCuts RulePatch ReplayEntry ReplayGrammar CoreWeight

variable {ℓ q L s E : ℕ}

def ruleEntries {d : ℕ} (S : Finset (Fin d)) (s : ℕ) : Finset (Fin (d*s)) :=
  (edges (s := s) S).image finProdFinEquiv

@[simp] theorem mem_ruleEntries {d : ℕ} (S : Finset (Fin d)) (j : Fin (d*s)) :
    j ∈ ruleEntries S s ↔ (finProdFinEquiv.symm j).1 ∈ S := by
  constructor
  · intro hj
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
    simpa only [Equiv.symm_apply_apply] using (Finset.mem_product.mp he).1
  · intro hj
    exact Finset.mem_image.mpr ⟨finProdFinEquiv.symm j,
      Finset.mem_product.mpr ⟨hj,Finset.mem_univ _⟩,Equiv.apply_symm_apply _ _⟩

theorem ruleEntries_patches (hs : History ℓ q L s) (S : Finset (Fin hs.length)) :
    ((ruleEntries S s).image (fun j => PatchTable.incidence (gates hs) (finProdFinEquiv.symm j))) =
      patches (PatchTable.incidence (gates hs)) S := by
  unfold ruleEntries patches
  rw [Finset.image_image]
  simp only [Function.comp_def,Equiv.symm_apply_apply]

theorem compactIndex_inj {N : ℕ} {T : Finset (Fin N)} {i j : Fin N}
    (hi : i ∈ T) (hj : j ∈ T) (h : compactIndex T i.val = compactIndex T j.val) : i = j := by
  unfold compactIndex at h
  rw [dite_eq_left i.isLt,dite_eq_left hi,dite_eq_left j.isLt,dite_eq_left hj] at h
  have he := (T.orderIsoOfFin rfl).symm.injective (Fin.ext h)
  exact congrArg Subtype.val he

theorem ofFn_original {N : ℕ} (T : Finset (Fin N)) :
    List.ofFn (BackwardSlice.original T) = T.sort := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn,BackwardSlice.original,Finset.orderEmbOfFin_apply]
    rfl

theorem descriptions_eq_sorted (hs : History ℓ q L s) (root : RuleVertex hs) (x : Fin ℓ → Fin q)
    (T : Finset (Fin (hs.length*s))) (inner outer : Fin (hs.length*s) → Bool) :
    descriptions hs root x T inner outer = T.sort.map (fun j =>
      ⟨(witnessEntry hs root x j).relabel (compactIndex T) (witnessRuleNumber hs root),
        inner j,outer j⟩) := by
  rw [← ofFn_original,List.map_ofFn]
  rfl

theorem finalKeys_iff {ds : List (DecodedEntry q)} (p : Fin E) :
    p ∈ finalRuleKeys E ds ↔ ∃ d ∈ ds, d.finalRule = true ∧ d.entry.rule = p.val := by
  simp [finalRuleKeys,List.any_eq_true,Bool.and_eq_true_iff,beq_iff_eq]

/-- The rule-marked keys are exactly the chosen historical rules in compact
chronological numbering. -/
theorem marked_keys (hs : History ℓ q L s) (root : RuleVertex hs) (x : Fin ℓ → Fin q)
    (hc : Chronological hs) (S : Finset (Fin hs.length)) (hspos : 0 < s)
    (T : Finset (Fin (hs.length*s))) (hends : ruleEntries S s ⊆ T)
    (hfit : ∀ d ∈ descriptions hs root x T (fun j => decide ((finProdFinEquiv.symm j).1 ∈ S))
      (fun j => decide ((finProdFinEquiv.symm j).1 ∈ S)), d.entry.rule < E) :
    let mark j := decide ((finProdFinEquiv.symm j).1 ∈ S)
    let ds := descriptions hs root x T mark mark
    (finalRuleKeys E ds).image Fin.val = S.image (fun i => witnessRuleNumber hs root i.val) := by
  dsimp only
  let mark (j : Fin (hs.length*s)) := decide ((finProdFinEquiv.symm j).1 ∈ S)
  let ds := descriptions hs root x T mark mark
  ext p
  constructor
  · intro hp
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨d,hd,hmark,hval⟩ := (finalKeys_iff r).mp hr
    rw [descriptions_eq_sorted] at hd
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hd
    have hm : (finProdFinEquiv.symm j).1 ∈ S := of_decide_eq_true hmark
    refine Finset.mem_image.mpr ⟨_,hm,?_⟩
    exact (congrArg (witnessRuleNumber hs root) (witnessEntry_rule hs hc root x j)).symm.trans hval
  · intro hp
    obtain ⟨r,hr,hval⟩ := Finset.mem_image.mp hp
    let j := finProdFinEquiv (r,⟨0,hspos⟩)
    have hj' : (finProdFinEquiv.symm j).1 = r := by simp [j]
    have hmem : j ∈ T := hends ((mem_ruleEntries S j).mpr (hj'.symm ▸ hr))
    let d : DecodedEntry q := ⟨(witnessEntry hs root x j).relabel (compactIndex T)
      (witnessRuleNumber hs root),mark j,mark j⟩
    have hd : d ∈ ds := by
      unfold ds
      rw [descriptions_eq_sorted]
      exact List.mem_map.mpr ⟨j,(Finset.mem_sort _).mpr hmem,rfl⟩
    have hmark : d.finalRule = true := by
      change decide ((finProdFinEquiv.symm j).1 ∈ S) = true
      exact decide_eq_true (hj'.symm ▸ hr)
    have he : d.entry.rule = p := by
      change witnessRuleNumber hs root (witnessEntry hs root x j).rule = p
      rw [witnessEntry_rule hs hc,hj']
      exact hval
    let id : Fin E := ⟨d.entry.rule,hfit d hd⟩
    exact Finset.mem_image.mpr ⟨id,(finalKeys_iff id).mpr ⟨d,hd,hmark,rfl⟩,he⟩

/-- Sorting and filtering the chosen gates of one rule preserves its
bubble order from the original catalogue tuple. -/
theorem sorted_one_rule {d : ℕ} (T : Finset (Fin (d*s))) (i : Fin d)
    (hi : ∀ j : Fin s, finProdFinEquiv (i,j) ∈ T) :
    (T.sort.filter fun j => decide ((finProdFinEquiv.symm j).1 = i)) =
      List.ofFn fun j : Fin s => finProdFinEquiv (i,j) := by
  let a := T.sort.filter fun j => decide ((finProdFinEquiv.symm j).1 = i)
  let b := List.ofFn fun j : Fin s => finProdFinEquiv (i,j)
  let rel (u v : Fin (d*s)) := u < v
  have hir : Std.Irrefl rel := ⟨fun _ => lt_irrefl _⟩
  have han : Std.Antisymm rel := ⟨fun _ _ h h' => False.elim (lt_asymm h h')⟩
  have ha : a.Pairwise rel := (T.sortedLT_sort).pairwise.filter _
  have hb : b.Pairwise rel := by
    apply List.pairwise_iff_getElem.mpr
    intro j k hj hk hlt
    simp only [b,List.getElem_ofFn]
    change j+s*i.val < k+s*i.val
    omega
  refine @List.Subset.antisymm_of_pairwise _ rel han hir _ _ ha hb ?_ ?_
  · intro j hj
    have h := of_decide_eq_true (List.mem_filter.mp hj).2
    apply List.mem_ofFn.mpr
    refine ⟨(finProdFinEquiv.symm j).2,?_⟩
    exact (congrArg (fun r => finProdFinEquiv (r,(finProdFinEquiv.symm j).2)) h).symm.trans
      (Equiv.apply_symm_apply _ _)
  · intro j hj
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hj
    exact List.mem_filter.mpr ⟨(Finset.mem_sort _).mpr (hi k),by simp⟩

#print axioms marked_keys
#print axioms sorted_one_rule

end DeletionCode.Explicit.Recognizer
