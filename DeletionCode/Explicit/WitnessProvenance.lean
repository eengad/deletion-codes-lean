import DeletionCode.Explicit.RecognizerBirth
import DeletionCode.Explicit.WitnessTables
import DeletionCode.Explicit.ReplayPresence

/-! Each witness entry replays from the same older rules as its prepared gate. -/

namespace DeletionCode.Explicit.Recognizer

open LetterGraphCuts LetterSequence RulePatch ReplayEntry ReplayGrammar LiftDictionary Borrowed
open Qary.SignedSupport

variable {ℓ q K b L Λ R s : ℕ}

theorem completed_take_older (hs : History ℓ q L s) (h : Chronological hs) (i : Fin hs.length) :
    ∀ j : Fin (completed (hs.take i.val)).size, (completed (hs.take i.val))[j].rule < i.val := by
  have hlen : (hs.take i.val).length = i.val := by simp [List.length_take,Nat.min_eq_left i.isLt.le]
  have hchron : Chronological (hs.take i.val) := by
    intro r k
    have hr : r.val < hs.length := r.isLt.trans_le (hlen.le.trans i.isLt.le)
    change (((hs.take i.val)[r.val]).bubbles k).gate.entry = _ ∧
        (((hs.take i.val)[r.val]).bubbles k).rule = _
    rw [List.getElem_take]
    exact h ⟨r.val,hr⟩ k
  intro j
  exact (rules_increasing (hs.take i.val) hchron j).trans_le hlen.le

theorem witnessEntry_rule (hs : History ℓ q L s) (hc : Chronological hs)
    (root : RuleVertex hs) (x : Fin ℓ → Fin q) (j : Fin (hs.length*s)) :
    (witnessEntry hs root x j).rule = (finProdFinEquiv.symm j).1.val :=
  (hc (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2).2

theorem witnessLifts_rule (hs : History ℓ q L s) (hc : Chronological hs) (j : Fin (hs.length*s)) :
    (witnessLifts hs j).rule = (finProdFinEquiv.symm j).1.val :=
  (hc (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2).2

/-- Evaluate one retained gate in the dictionary that existed at its
birth, with its source references rebased to the final patch. -/
theorem witnessEntry_evaluates
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs) (hc : Chronological hs)
    (root : RuleVertex hs) (j : Fin (hs.length*s)) (hj : j ∈ retainedEntries hs root) :
    evaluate L j.val (witnessAnchor hs root) (prior (witnessLifts hs) j.val) (witnessEntry hs root x j) =
      some (witnessLifts hs j) := by
  let e := finProdFinEquiv.symm j
  let old := hs.take e.1.val
  let p := PatchTable.incidence (gates hs) e
  have hp : p ∈ componentPatches (PatchTable.incidence (gates hs)) root :=
    witnessEntry_patch hs root e (Finset.mem_filter.mp hj).2
  have hanchor := witnessAnchor_at hs root p hp
  obtain ⟨words,hcat,_,edges,hprep⟩ := (h.batch_at e.1).fromCatalogue
  have heval := prepareBubble_replay pad x (completed old) (words e.2) origin (patchAnchor hs p)
    ((completed old).size+e.2.val) old.length (witnessPatchNumber hs root p)
    (RuleAddition.left_pos P _) (RuleAddition.right_pos P _) (Nat.le_add_right _ _)
    (by
      have hn := completed_take_older hs hc e.1
      simpa [old,List.length_take,Nat.min_eq_left e.1.isLt.le] using hn)
    (hprep e.2).1 (hprep e.2).2.spelling (witnessAnchor hs root) hanchor
  have hn : (completed old).size = e.1.val*s := by
    simp [old,List.length_take,Nat.min_eq_left e.1.isLt.le]
  have hnum : e.1.val*s+e.2.val = j.val := by
    have he : finProdFinEquiv e = j := Equiv.apply_symm_apply _ _
    have hf := congrArg Fin.val he
    change e.2.val+s*e.1.val = j.val at hf
    simpa only [Nat.mul_comm,Nat.add_comm] using hf
  rw [hn,hnum] at heval
  have heval' :
      evaluate L j.val (witnessAnchor hs root) (fun k => (completed old)[k]?) (witnessEntry hs root x j) =
        some (witnessLifts hs j) := heval
  apply Eq.trans _ heval'
  apply evaluate_congr
  intro k hk
  have hsupply := evaluate_suppliers heval' hk
  obtain ⟨o,ho,_⟩ := hsupply.2
  have hprior := completed_take_get hs e.1 k
  change (completed old)[k]? = prior (witnessLifts hs) (e.1.val*s) k at hprior
  have hlt : k < e.1.val*s := by
    by_contra h'
    rw [ho,prior,dite_eq_right (show ¬ (k < hs.length*s ∧ k < e.1.val*s) from fun h => h' h.2)] at hprior
    contradiction
  have hfull : k < hs.length*s := hlt.trans_le (Nat.mul_le_mul_right _ e.1.isLt.le)
  have hcurr := hsupply.1
  rw [hprior,prior,dite_eq_left ⟨hfull,hcurr⟩,prior,dite_eq_left ⟨hfull,hlt⟩]

#print axioms witnessEntry_evaluates

end DeletionCode.Explicit.Recognizer
