import DeletionCode.Explicit.RecognizerProof
import DeletionCode.Explicit.RuleAddition
import DeletionCode.Explicit.MatchingWeight
import DeletionCode.Explicit.CompactReplay

/-! Chronological indices and graph invariants of the executable recognizer. -/

namespace DeletionCode.Explicit.Recognizer

open FieldHash CanonicalColour RulePatch LetterSequence LetterGraphCuts ReplayEntry LiftDictionary PatchSupport
open Qary.SignedSupport
open scoped BigOperators

variable {ℓ q K b L Λ R s : ℕ}

@[simp] theorem completed_size (hs : History ℓ q L s) : (completed hs).size = hs.length*s := by
  simp [completed]

def completedIndex (hs : History ℓ q L s) :
    Fin hs.length × Fin s ≃ Fin (completed hs).size :=
  finProdFinEquiv.trans (finCongr (completed_size hs).symm)

theorem completedIndex_val (hs : History ℓ q L s) (e : Fin hs.length × Fin s) :
    (completedIndex hs e).val = (finProdFinEquiv e).val := rfl

def entryAt {A : Type*} (a : Array A) (i : Fin a.size) : A := a[i.val]'i.isLt

theorem completed_get (hs : History ℓ q L s) (e : Fin hs.length × Fin s) :
    entryAt (completed hs) (completedIndex hs e) = lifts hs e := by
  unfold entryAt
  simp only [completed,Array.getElem_ofFn]
  change ((hs.get (finProdFinEquiv.symm (finProdFinEquiv e)).1).bubbles
    (finProdFinEquiv.symm (finProdFinEquiv e)).2).completed = lifts hs e
  rw [Equiv.symm_apply_apply]
  rfl

def Chronological (hs : History ℓ q L s) : Prop :=
  ∀ (i : Fin hs.length) (j : Fin s),
    ((hs.get i).bubbles j).gate.entry = i.val*s+j.val ∧ ((hs.get i).bubbles j).rule = i.val

theorem rules_increasing (hs : History ℓ q L s) (h : Chronological hs) :
    ∀ i : Fin (completed hs).size, (completed hs)[i].rule < hs.length := by
  intro i
  let e := (completedIndex hs).symm i
  have hi : i = completedIndex hs e := ((completedIndex hs).apply_symm_apply i).symm
  have he := (congrArg (entryAt (completed hs)) hi).trans (completed_get hs e)
  have hr : (completed hs)[i].rule = ((hs.get e.1).bubbles e.2).rule :=
    congrArg Completed.rule he
  rw [hr,(h e.1 e.2).2]
  exact e.1.isLt

theorem ids_below (hs : History ℓ q L s) (h : Chronological hs) (e : Fin hs.length × Fin s) :
    (gates hs e).id < (completed hs).size := by
  let i := finProdFinEquiv e
  have he : (gates hs e).id = i.val := by
    change ((hs.get e.1).bubbles e.2).gate.entry = e.2.val+s*e.1.val
    rw [(h e.1 e.2).1]
    ac_rfl
  rw [completed_size,he]
  exact i.isLt

theorem ids_injective (hs : History ℓ q L s) (h : Chronological hs) :
    Function.Injective (fun e => (gates hs e).id) := by
  intro e f he
  apply finProdFinEquiv.injective
  apply Fin.ext
  change e.2.val+s*e.1.val = f.2.val+s*f.1.val
  rw [Nat.mul_comm s e.1.val,Nat.mul_comm s f.1.val,Nat.add_comm e.2.val,Nat.add_comm f.2.val]
  change ((hs.get e.1).bubbles e.2).gate.entry = ((hs.get f.1).bubbles f.2).gate.entry at he
  simpa only [(h e.1 e.2).1,(h f.1 f.2).1] using he

structure GraphValid (pad : Fin q) (x : Fin ℓ → Fin q) (b Λ : ℕ) (hs : History ℓ q L s)
    (edges : Letter ℓ (Fin q) → Letter ℓ (Fin q) → Prop) (marked : Finset (Fin ℓ)) : Prop where
  chronology : Chronological hs
  graph : LetterGraphCuts.History ℓ (Fin q) edges marked
  records : PatchTable.RecordsGraph (gates hs) edges marked
  follows : ∀ e side, ((lifts hs e).lift side).2.Follows edges
  fit : LiftsFit (gates hs) (lifts hs) Λ
  lowWidth : ∀ e, L ≤ 2*((gates hs e).interval.last.val+1-(gates hs e).interval.first.val)
  highWidth : ∀ e, (gates hs e).interval.last.val+1-(gates hs e).interval.first.val ≤ 3*L
  marks : ∀ e, (gates hs e).marks.card ≤ b
  stock : ∀ e, (gates hs e).inserted.card ≤ b
  vectors : RowsMatch pad x hs

theorem graph_initial (pad : Fin q) (x : Fin ℓ → Fin q) :
    GraphValid (L := L) (s := s) pad x b Λ [] originalEdges ∅ := by
  refine ⟨?_,LetterGraphCuts.History.initial,PatchTable.initial_records _,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact i.elim0
  · intro e
    exact e.1.elim0
  · intro e
    exact e.1.elim0
  · intro e
    exact e.1.elim0
  · intro e
    exact e.1.elim0
  · intro e
    exact e.1.elim0
  · intro e
    exact e.1.elim0
  · intro i
    exact i.elim0

theorem get?_completed (hs : History ℓ q L s) {j : ℕ} {out : Completed ℓ (Fin q)}
    (h : (completed hs)[j]? = some out) :
    ∃ e, lifts hs e = out := by
  by_cases hj : j < (completed hs).size
  · let i : Fin (completed hs).size := ⟨j,hj⟩
    let e := (completedIndex hs).symm i
    have hi : i = completedIndex hs e := ((completedIndex hs).apply_symm_apply i).symm
    refine ⟨e,(completed_get hs e).symm.trans ?_⟩
    apply (congrArg (entryAt (completed hs)) hi).symm.trans
    exact Option.some.inj ((Array.getElem?_eq_getElem hj).symm.trans h)
  · have hh : (completed hs)[j]? = none := Array.getElem?_eq_none (Nat.le_of_not_gt hj)
    rw [hh] at h
    contradiction

/-- The dictionary's grouped arrays and the recognizer's rows have the
same kernel and exposure coordinates when read in chronological order. -/
theorem liftedRule_eq (pad : Fin q) (x : Fin ℓ → Fin q) (hs : History ℓ q L s)
    (h : Chronological hs) (r : ℕ) (g : Gram (Fin q) L) :
    liftedRule (L := L) pad x (completed hs) r g =
      ∑ i : Fin hs.length, if i.val = r then ruleVector (lifts hs) pad x L i g else 0 := by
  let f := completedIndex hs
  unfold liftedRule
  rw [← Equiv.sum_comp f]
  have he (e : Fin hs.length × Fin s) :
      (completed hs)[f e] = lifts hs e := completed_get hs e
  simp only [he]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  have hg (j : Fin s) : (lifts hs (i,j)).rule = i.val := (h i j).2
  simp only [hg]
  by_cases hi : i.val = r <;> simp [hi,ruleVector]

abbrev gramEquiv : Row (q^L) ≃ₗ[F₃] (Gram (Fin q) L → F₃) :=
  LinearEquiv.funCongrLeft F₃ F₃ finFunctionFinEquiv

theorem spectrum_isBoolean (pad : Fin q) (x : Fin ℓ → Fin q) (hx : Strong x K Λ)
    (hL : K ≤ L-1) : FibreEnumeration.IsBoolean (spectrum pad x L) := by
  have hu := MatchingWeight.strong_kunique hx pad
  have hu' : Qary.Windows.KUnique (paddedLetters pad x) ℓ (L-1) := by
    intro i j hi hj he
    exact hu i j (by omega) (by omega) (fun z hz => he z (hz.trans_le hL))
  intro g
  unfold spectrum
  rw [fieldSpectrum_eq_cast]
  rcases Qary.SpectrumPath.spectrum_boolean _ _ _ hu' (finFunctionFinEquiv.symm g) with hz | ho
  · left
    simp [hz]
  · right
    simp [ho]

theorem history_span (pad : Fin q) (x : Fin ℓ → Fin q) (hs : History ℓ q L s)
    (hc : Chronological hs) (hm : RowsMatch pad x hs) :
    (span (oldRows hs)).map (gramEquiv (q := q) (L := L)).toLinearMap =
      Submodule.span F₃ (Set.range (liftedRule (L := L) pad x (completed hs))) := by
  classical
  have he (i : Fin hs.length) :
      liftedRule (L := L) pad x (completed hs) i.val = gramEquiv (q := q) (L := L) (hs.get i).row := by
    funext g
    rw [liftedRule_eq pad x hs hc]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun j _ hj => ?_)]
    · rw [ite_eq_left rfl]
      exact (hm i g).symm
    · simp [show j.val ≠ i.val from fun ht => hj (Fin.ext ht)]
  rw [Submodule.map_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨v,hv,rfl⟩
    obtain ⟨batch,hm,hv⟩ := List.mem_map.mp hv
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hm
    change gramEquiv v ∈ _
    rw [← hv,← hi,← he i]
    exact Submodule.subset_span ⟨i.val,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨r,rfl⟩
    by_cases h : r < hs.length
    · rw [he ⟨r,h⟩]
      exact Submodule.subset_span ⟨(hs.get ⟨r,h⟩).row,List.mem_map_of_mem (List.get_mem ..),rfl⟩
    · have hz : liftedRule (L := L) pad x (completed hs) r = 0 := by
        funext g
        rw [liftedRule_eq pad x hs hc]
        apply Finset.sum_eq_zero
        intro i _
        rw [ite_eq_right (show i.val ≠ r by intro e; exact h (e ▸ i.isLt))]
      rw [hz]
      exact Submodule.zero_mem _

/-- The array available to rule `i` is the prefix of the full bubble table
ending immediately before rule `i`. Later bubbles are invisible. -/
theorem completed_take_get (hs : History ℓ q L s) (i : Fin hs.length) (j : ℕ) :
    (completed (hs.take i.val))[j]? = prior (fun k : Fin (hs.length*s) =>
      lifts hs (finProdFinEquiv.symm k)) (i.val*s) j := by
  have hlen : (hs.take i.val).length = i.val := by simp [List.length_take]
  by_cases h : j < i.val*s
  · have hk : j < hs.length*s := h.trans_le (Nat.mul_le_mul_right s i.isLt.le)
    have hj : j < (completed (hs.take i.val)).size := by simpa [completed_size,hlen] using h
    let k : Fin (hs.length*s) := ⟨j,hk⟩
    let f := finProdFinEquiv.symm (⟨j,by simpa [hlen] using h⟩ :
      Fin ((hs.take i.val).length*s))
    have hidx : (completedIndex (hs.take i.val) f).val = j := by
      rw [completedIndex_val]
      exact congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv _)
    have he : (completed (hs.take i.val))[j]'hj = lifts (hs.take i.val) f := by
      change entryAt (completed (hs.take i.val)) ⟨j,hj⟩ = _
      have h : completedIndex (hs.take i.val) f = ⟨j,hj⟩ := Fin.ext hidx
      rw [← h]
      exact completed_get _ _
    rw [Array.getElem?_eq_getElem hj,he,prior,dite_eq_left ⟨hk,h⟩]
    congr 1
    let e := finProdFinEquiv.symm k
    have hleft : f.1.val = e.1.val := rfl
    have hright : f.2 = e.2 := by apply Fin.ext; rfl
    change (((hs.take i.val).get f.1).bubbles f.2).completed = ((hs.get e.1).bubbles e.2).completed
    rw [hright]
    congr 2
    have hget : (hs.take i.val).get f.1 = hs.get e.1 := by
      change (hs.take i.val)[f.1.val] = hs[e.1.val]
      rw [List.getElem_take]
      exact congrArg (fun j : Fin hs.length => hs.get j) (Fin.ext hleft)
    rw [hget]
  · have hj : (completed (hs.take i.val)).size ≤ j := by rw [completed_size,hlen]; omega
    rw [Array.getElem?_eq_none hj,prior,dite_eq_right (show ¬ (j < hs.length*s ∧ j < i.val*s) from fun he => h he.2)]

#print axioms completed_take_get
#print axioms history_span
#print axioms liftedRule_eq

end DeletionCode.Explicit.Recognizer
