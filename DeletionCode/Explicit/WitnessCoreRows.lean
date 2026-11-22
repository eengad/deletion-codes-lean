import DeletionCode.Explicit.WitnessFamilies
import DeletionCode.Explicit.WitnessMarks

/-! A core slot replays each selected rule in its original bubble order. -/

namespace DeletionCode.Explicit.Recognizer

open LetterGraphCuts RulePatch ReplayEntry ReplayGrammar CoreWeight FieldHash
open PeelingBuckets
open scoped BigOperators

variable {ℓ q L s E K b Λ R : ℕ}

def markRule {d : ℕ} (S : Finset (Fin d)) (j : Fin (d*s)) : Bool :=
  decide ((finProdFinEquiv.symm j).1 ∈ S)

def replayedPairs (hs : History ℓ q L s) (root : RuleVertex hs) (x : Fin ℓ → Fin q)
    (T : Finset (Fin (hs.length*s))) (S : Finset (Fin hs.length)) :
    List (DecodedEntry q × Completed ℓ (Fin q)) :=
  T.sort.map fun j =>
    let p := sliceRecord hs root x T j
    (⟨p.1,markRule S j,markRule S j⟩,p.2)

theorem zip_slice (hs : History ℓ q L s) (root : RuleVertex hs) (x : Fin ℓ → Fin q)
    (T : Finset (Fin (hs.length*s))) (S : Finset (Fin hs.length)) :
    (descriptions hs root x T (markRule S) (markRule S)).zip
      (List.ofFn fun i => (sliceRecord hs root x T (BackwardSlice.original T i)).2) =
      replayedPairs hs root x T S := by
  have he : (List.ofFn fun i => (sliceRecord hs root x T (BackwardSlice.original T i)).2) =
      T.sort.map (fun j => (sliceRecord hs root x T j).2) := by
    rw [← ofFn_original T,List.map_ofFn]
    rfl
  rw [descriptions_eq_sorted,he,List.zip_map']
  rfl

theorem filter_replayedPairs (hs : History ℓ q L s) (root : RuleVertex hs) (x : Fin ℓ → Fin q)
    (hc : Chronological hs) (T : Finset (Fin (hs.length*s))) (S : Finset (Fin hs.length))
    (hends : ruleEntries S s ⊆ T) (hsub : T ⊆ retainedEntries hs root)
    (r : Fin hs.length) (hr : r ∈ S)
    (id : ℕ) (hid : witnessRuleNumber hs root r.val = id) (hspos : 0 < s) :
    (replayedPairs hs root x T S).filter (fun p => p.1.finalBubble && p.1.entry.rule == id) =
      List.ofFn (fun j : Fin s =>
        let p := sliceRecord hs root x T (finProdFinEquiv (r,j))
        (⟨p.1,true,true⟩,p.2)) := by
  let f (j : Fin (hs.length*s)) :=
    let p := sliceRecord hs root x T j
    ((⟨p.1,markRule S j,markRule S j⟩ : DecodedEntry q),p.2)
  have hmem (j : Fin s) : finProdFinEquiv (r,j) ∈ T :=
    hends ((mem_ruleEntries S _).mpr (by simpa only [Equiv.symm_apply_apply] using hr))
  have hret : r ∈ componentRules (PatchTable.incidence (gates hs)) root := by
    have h := (Finset.mem_filter.mp (hsub (hmem ⟨0,hspos⟩))).2
    simpa only [Equiv.symm_apply_apply] using h
  have hpred : (T.sort.filter (fun j =>
      (f j).1.finalBubble && (f j).1.entry.rule == id)) =
      T.sort.filter (fun j => decide ((finProdFinEquiv.symm j).1 = r)) := by
    apply List.filter_congr
    intro j hj
    have hjT := (Finset.mem_sort _).mp hj
    let rule := (finProdFinEquiv.symm j).1
    have hmemRule : rule ∈ componentRules (PatchTable.incidence (gates hs)) root :=
      (Finset.mem_filter.mp (hsub hjT)).2
    have hnum : (f j).1.entry.rule = witnessRuleNumber hs root rule.val := by
      change witnessRuleNumber hs root (witnessEntry hs root x j).rule = _
      rw [witnessEntry_rule hs hc]
    change ((f j).1.finalBubble && ((f j).1.entry.rule == id)) = decide (rule = r)
    by_cases eq : rule = r
    · have hmark : (f j).1.finalBubble = true := by
        change decide (rule ∈ S) = true
        rw [eq]
        exact decide_eq_true hr
      rw [hmark,hnum,eq,hid]
      simp
    · have hne : witnessRuleNumber hs root rule.val ≠ id := by
        rw [← hid]
        exact fun h => eq (compactIndex_inj hmemRule hret h)
      rw [hnum,beq_eq_false_iff_ne.mpr hne,Bool.and_false]
      exact (decide_eq_false eq).symm
  unfold replayedPairs
  change ((T.sort.map f).filter (fun p => p.1.finalBubble && p.1.entry.rule == id)) = _
  rw [List.filter_map]
  change List.map f (T.sort.filter (fun j => (f j).1.finalBubble && (f j).1.entry.rule == id)) = _
  rw [hpred,sorted_one_rule T r hmem,List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  have hm : markRule S (finProdFinEquiv (r,j)) = true := by
    change decide ((finProdFinEquiv.symm (finProdFinEquiv (r,j))).1 ∈ S) = true
    rwa [Equiv.symm_apply_apply,decide_eq_true_eq]
  simp only [f,Function.comp_apply,hm]

private theorem mapM_ofFn_some {A B : Type*} {n : ℕ} (f : A → Option B)
    (u : Fin n → A) (v : Fin n → B) (h : ∀ j, f (u j) = some (v j)) :
    (List.ofFn u).mapM f = some (List.ofFn v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,List.mapM_cons,h,ih _ _ (fun j => h j.succ)]
    rfl

/-- Matching a marked key to a history row supplies its validated catalogue
tuple and its vector in the replayed word. -/
theorem replayed_rule
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs) (hc : Chronological hs)
    (root : RuleVertex hs) (T : Finset (Fin (hs.length*s))) (S : Finset (Fin hs.length))
    (hends : ruleEntries S s ⊆ T) (hsub : T ⊆ retainedEntries hs root)
    (r : Fin hs.length) (hr : r ∈ S)
    (id : ℕ) (hid : witnessRuleNumber hs root r.val = id) (hspos : 0 < s) :
    let selected := (replayedPairs hs root x T S).filter (fun p => p.1.finalBubble && p.1.entry.rule == id)
    (∃ words : Fin s → Borrowed.BubbleWord (Fin q) K b L,
      @Borrowed.Catalogue.ValidCatalogue _ ⟨pad⟩ K b L s 1 words (fun _ => 0) ∧
      selected.mapM (recoveredBubble K b L Λ x) = some (List.ofFn words)) ∧
    ∀ col : Fin (q^L),
      (selected.map (fun p => LiftDictionary.bubbleVector (L := L) pad x p.2 (finFunctionFinEquiv.symm col))).sum =
        (hs.get r).row col := by
  dsimp only
  have hordered := filter_replayedPairs hs root x hc T S hends hsub r hr id hid hspos
  rw [hordered]
  obtain ⟨words,hcat,hrow,hfamily⟩ := slice_rule_families h root T r
  constructor
  · refine ⟨words,hcat,?_⟩
    apply mapM_ofFn_some
    intro j
    exact (hfamily j).2.2 true true
  · intro col
    rw [List.map_ofFn,List.sum_ofFn,hrow]
    simp only [CatalogueEnumeration.row]
    apply Finset.sum_congr rfl
    intro j _
    exact congrFun (hfamily j).2.1.symm col

#print axioms filter_replayedPairs
#print axioms replayed_rule

end DeletionCode.Explicit.Recognizer
