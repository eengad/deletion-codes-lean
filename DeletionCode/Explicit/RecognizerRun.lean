import DeletionCode.Explicit.RecognizerGeometry
import DeletionCode.Explicit.RecognizerClosure
import DeletionCode.Explicit.RecognizerBirth

/-! A strong source reaches closure or its first rule-patch event. -/

namespace DeletionCode.Explicit.Recognizer

open FieldHash LetterSequence LetterGraphCuts BooleanClosure LiftDictionary FirstEvent
open RulePatch ReplayEntry

variable {ℓ q K b L Λ s R θ : ℕ}

abbrev BeforeEvent (hs : History ℓ q L s) (R : ℕ) : Prop :=
  ∀ i, componentEvent (PatchTable.incidence (gates hs)) R i = false

def ResultValid (H : TernaryMatrix θ (q^L)) (pad : Fin q) (x : Fin ℓ → Fin q)
    (K b Λ R : ℕ) : Result ℓ q L s → Prop
  | .complete hs =>
    ∃ edges marks, GraphValid pad x b Λ hs edges marks ∧ BeforeEvent hs R ∧
      historySpace hs = closure (kernelRules (K := K) (b := b) (s := s) H pad)
        (fieldSpectrum (paddedLetters pad x) ℓ L)
  | .firstEvent hs i =>
    ∃ edges marks, GraphValid pad x b Λ hs edges marks ∧
      componentEvent (PatchTable.incidence (gates hs)) R i = true ∧
      ∃ old p, BeforeEvent old R ∧ hs = old ++ [p] ∧ i.val = old.length

set_option maxHeartbeats 1000000 in
theorem run_verified (P : RuleAddition.Bounds K b L Λ s R) (H : TernaryMatrix θ (q^L))
    (pad : Fin q) (x : Fin ℓ → Fin q) (root : Fin ℓ) (hx : Strong x K Λ)
    (hL : K+2*Λ+1 ≤ L) (fuel : ℕ)
    (hs : History ℓ q L s) (edges : Letter ℓ (Fin q) → Letter ℓ (Fin q) → Prop) (marks : Finset (Fin ℓ))
    (hv : GraphValid pad x b Λ hs edges marks) (hbefore : BeforeEvent hs R)
    (hgreedy : Greedy (kernelRules (K := K) (b := b) (s := s) H pad)
      (fieldSpectrum (paddedLetters pad x) ℓ L) hs.length (historySpace hs))
    (hrecords : RecordedBatches P pad x root hs)
    (hfuel : q^L < hs.length+fuel) :
    ∃ out, run H pad x root R (CatalogueEnumeration.rules q K b L s pad) fuel hs = some out ∧
      ResultValid H pad x K b Λ R out ∧
      (match out with
       | .complete history => RecordedBatches P pad x root history
       | .firstEvent history _ => RecordedBatches P pad x root history) := by
  induction fuel generalizing hs edges marks with
  | zero =>
    have hbound : hs.length ≤ q^L := by simpa using hgreedy.steps_le_ambient
    omega
  | succ fuel ih =>
    let catalogue := CatalogueEnumeration.rules q K b L s pad
    cases hfind : nextRule H pad x hs catalogue with
    | none =>
      refine ⟨.complete hs,?_,⟨edges,marks,hv,hbefore,?_⟩,hrecords⟩
      · simp [run,catalogue,hfind]
      · exact hgreedy.eq_closure (nextRule_none_closed H pad hv hx hL hfind)
    | some words =>
      have hmem := List.mem_of_find?_eq_some hfind
      let : Inhabited (Fin q) := ⟨pad⟩
      have hcat := (CatalogueEnumeration.mem_rules_iff pad (show 0 < L by omega) words).mp hmem
      have hOK := List.find?_some hfind
      have hex := candidate_dictionary_exposure H pad hv hx hL words hOK
      have hcutoff (p : Fin (PatchTable.patchCount (gates hs))) :
          (componentRules (PatchTable.incidence (gates hs)) (.inr p)).card ≤ R :=
        (preEvent_patch_components _ R (PatchTable.incidence_surjective (gates hs)) hbefore p).1
      have hout := (nextRule_selected H pad x hs catalogue hfind).2.2
      obtain ⟨p,hadd,hbatch,E',marks',hw⟩ := appendRule_correct P pad root hv hx hcutoff words hcat hmem hout hex
      let hs' := hs ++ [p]
      have he : hs' = hs++[p] := rfl
      have hstep := nextRule_greedy_step H pad hv hx hL root hgreedy hfind hadd
      have hrecords' : RecordedBatches P pad x root hs' := .append hrecords hbatch
      have hlen : hs'.length = hs.length+1 := by simp [hs']
      have hlt : hs.length < hs'.length := by omega
      let last : Fin hs'.length := ⟨hs.length,hlt⟩
      cases event : componentEvent (PatchTable.incidence (gates hs')) R last with
      | false =>
        have hquiet : BeforeEvent hs' R := by
          exact beforeEvent_append hs p R hbefore event
        obtain ⟨out,hrun,hvalid,hrecorded⟩ := ih hs' E' marks' hw hquiet hstep hrecords' (by omega)
        refine ⟨out,?_,hvalid,hrecorded⟩
        have hsame : componentEvent (PatchTable.incidence (gates (hs++[p]))) R
            ⟨hs.length, by simp⟩ = false := event
        simpa [run,catalogue,hfind,hadd,hsame,hs'] using hrun
      | true =>
        refine ⟨.firstEvent hs' last,?_,⟨E',marks',hw,event,hs,p,hbefore,he,rfl⟩,hrecords'⟩
        have hsame : componentEvent (PatchTable.incidence (gates (hs++[p]))) R
            ⟨hs.length, by simp⟩ = true := event
        simp [run,catalogue,hfind,hadd,hsame,last,hs']

/-- The executable recognizer finishes on every strong source of positive
length satisfying the local proof's parameter inequalities. -/
theorem recognize_verified (P : RuleAddition.Bounds K b L Λ s R) (H : TernaryMatrix θ (q^L))
    (pad : Fin q) (x : Fin ℓ → Fin q) (hx : Strong x K Λ)
    (hL : K+2*Λ+1 ≤ L) (hℓ : 0 < ℓ) :
    ∃ out, recognize (K := K) (b := b) (s := s) H pad x R = some out ∧
      ResultValid H pad x K b Λ R out ∧
      (match out with
       | .complete history => RecordedBatches P pad x ⟨0,hℓ⟩ history
       | .firstEvent history _ => RecordedBatches P pad x ⟨0,hℓ⟩ history) := by
  have hw : GraphValid (L := L) (s := s) pad x b Λ [] originalEdges ∅ := graph_initial pad x
  have hgreedy : Greedy (kernelRules (K := K) (b := b) (s := s) H pad)
      (fieldSpectrum (paddedLetters pad x) ℓ L) ([] : History ℓ q L s).length (historySpace ([] : History ℓ q L s)) := by
    rw [historySpace_nil]
    exact .start
  obtain ⟨out,he,hvalid,hr⟩ := run_verified P H pad x ⟨0,hℓ⟩ hx hL (q^L+1) [] originalEdges ∅
    hw (fun i => i.elim0) hgreedy .empty (by simp)
  exact ⟨out,by simpa [recognize,hℓ] using he,hvalid,hr⟩

#print axioms recognize_verified

end DeletionCode.Explicit.Recognizer
