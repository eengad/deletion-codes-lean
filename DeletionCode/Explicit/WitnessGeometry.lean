import DeletionCode.Explicit.WitnessProvenance
import DeletionCode.Explicit.SupplierRetention

/-! Saved windows keep their suppliers in the witness and bound their references. -/

namespace DeletionCode.Explicit.Recognizer

open LetterGraphCuts LetterSequence RulePatch ReplayEntry ReplayGrammar LiftDictionary Borrowed PatchSupport
open Qary.SignedSupport

variable {ℓ q K b L Λ R s : ℕ}

theorem saved_read
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs) (hc : Chronological hs)
    (root : RuleVertex hs) (j : Fin (hs.length*s)) (hj : j ∈ retainedEntries hs root)
    (o : Occurrence ℓ L (Fin q)) (ho : o ∈ ((hs.get (finProdFinEquiv.symm j).1).bubbles (finProdFinEquiv.symm j).2).windows) :
    ∃ a, ∃ ha : a+L ≤ (witnessLifts hs j).negative.1,
      o.lift.spelling x = ((witnessLifts hs j).negative.2.window a L ha).spelling x ∧
      Reads L j.val (witnessEntry hs root x j).rule
        (witnessAnchor hs root (witnessEntry hs root x j).patch) (prior (witnessLifts hs) j.val)
        (o.location.reference (patchAnchor hs (PatchTable.incidence (gates hs) (finProdFinEquiv.symm j)))) o.lift := by
  let e := finProdFinEquiv.symm j
  let p := PatchTable.incidence (gates hs) e
  let prepared := (hs.get e.1).bubbles e.2
  let old := hs.take e.1.val
  let rootPos := patchAnchor hs p
  obtain ⟨words,hw,_,E,hprep⟩ := (h.batch_at e.1).fromCatalogue
  let : Inhabited (Fin q) := ⟨pad⟩
  have hL : 0 < L := by have h := P.window; omega
  have hcat := (CatalogueEnumeration.mem_rules_iff pad hL words).mp hw
  have hOld := completed_take_older hs hc e.1
  have hOlder : ∀ i : Fin (completed old).size, (completed old)[i].rule < old.length := by
    simpa [old,List.length_take] using hOld
  obtain ⟨a,ha,hspell,hread⟩ := prepareBubble_saved_window pad x (completed old) (words e.2) origin rootPos
    ((completed old).size+e.2.val) old.length (RuleAddition.left_pos P _) (RuleAddition.right_pos P _)
    (hprep e.2).1 (hprep e.2).2.spelling (hcat.length_lower e.2 false) (Nat.le_add_right _ _) hOlder ho
  have hn : (completed old).size = e.1.val*s := by simp [old,List.length_take]
  have hnum : e.1.val*s+e.2.val = j.val := by
    have he : finProdFinEquiv e = j := Equiv.apply_symm_apply _ _
    have hh := congrArg Fin.val he
    change e.2.val+s*e.1.val = j.val at hh
    simpa only [Nat.mul_comm,Nat.add_comm] using hh
  have hlen : old.length = e.1.val := by simp [old,List.length_take]
  rw [hn,hnum,hlen] at hread
  have hanchor : witnessAnchor hs root (witnessEntry hs root x j).patch = some rootPos :=
    witnessAnchor_at hs root p (witnessEntry_patch hs root e (Finset.mem_filter.mp hj).2)
  have heval := reads_of_read hread
  refine ⟨a,ha,hspell,?_⟩
  rw [hanchor,witnessEntry_rule hs hc]
  generalize lift_eq : o.lift = u at heval ⊢
  cases heq : o.location with
  | source start =>
    have h : Reads L j.val e.1.val (some rootPos)
          (fun k => (completed old)[k]?) (.source ((start : ℤ)-rootPos.val)) u := by
      simpa only [heq,Location.reference] using heval
    cases h with
    | source root delta ha hs hb => exact .source root _ ha hs hb
  | supplier k side offset =>
    have h : Reads L j.val e.1.val (some rootPos)
          (fun k => (completed old)[k]?) (.supplier k side offset) u := by
      simpa only [heq,Location.reference] using heval
    simp only [Location.reference]
    cases h with
    | supplier _ _ _ supplier hlt' hget hOlderRule hWidth =>
      refine .supplier k side offset supplier hlt' ?_ hOlderRule hWidth
      have hpref := completed_take_get hs e.1 k
      change (completed old)[k]? = prior (witnessLifts hs) (e.1.val*s) k at hpref
      have hlt : k < e.1.val*s := by
        by_contra h'
        rw [hget,prior,dite_eq_right (show ¬ (k < hs.length*s ∧ k < e.1.val*s) from fun h => h' h.2)] at hpref
        contradiction
      have hfull : k < hs.length*s := hlt.trans_le (Nat.mul_le_mul_right _ e.1.isLt.le)
      rw [hget,prior,dite_eq_left ⟨hfull,hlt⟩] at hpref
      rw [prior,dite_eq_left ⟨hfull,hlt'⟩,← hpref]

/-- A saved supplier belongs to the same final patch as the consumer. -/
theorem witness_supplier_patch
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs) (hc : Chronological hs)
    (hx : Strong x K Λ) (hf : LiftsFit (gates hs) (lifts hs) Λ) (hL : K+2*Λ ≤ L)
    (root : RuleVertex hs) (j : Fin (hs.length*s)) (hj : j ∈ retainedEntries hs root)
    (k : ℕ) (hk : k ∈ (witnessEntry hs root x j).suppliers) :
    ∃ z : Fin (hs.length*s), z.val = k ∧ z < j ∧
      PatchTable.incidence (gates hs) (finProdFinEquiv.symm z) =
        PatchTable.incidence (gates hs) (finProdFinEquiv.symm j) := by
  simp only [Entry.suppliers,List.mem_toFinset,List.mem_filterMap] at hk
  obtain ⟨ref,href,hk⟩ := hk
  cases ref with
  | source => contradiction
  | supplier k' side a =>
    have eq : k' = k := Option.some.inj hk
    subst k'
    obtain ⟨o,ho,he⟩ := List.mem_map.mp href
    obtain ⟨offset,hoff,hspell,hr⟩ := saved_read h hc root j hj o ho
    rw [he] at hr
    generalize hu : o.lift = u at hspell hr
    cases hr with
    | supplier _ _ _ supplier hlt hget hRule hWidth =>
      have hbound : k < hs.length*s := hlt.trans j.isLt
      let z : Fin (hs.length*s) := ⟨k,hbound⟩
      have hLifts : witnessLifts hs z = supplier := Option.some.inj
        ((dite_eq_left (t := fun h => some (witnessLifts hs ⟨k,h.1⟩))
          (e := fun _ => none) ⟨hbound,hlt⟩).symm.trans hget)
      subst supplier
      refine ⟨z,rfl,hlt,?_⟩
      exact supplier_same_patch (gates hs) (lifts hs) hx hf hL
        (finProdFinEquiv.symm j) (finProdFinEquiv.symm z) side hoff hWidth hspell.symm

theorem witness_suppliers_retained
    {P : RuleAddition.Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs) (hc : Chronological hs)
    (hx : Strong x K Λ) (hf : LiftsFit (gates hs) (lifts hs) Λ) (hL : K+2*Λ ≤ L)
    (root : RuleVertex hs) (j : Fin (hs.length*s)) (hj : j ∈ retainedEntries hs root)
    (k : ℕ) (hk : k ∈ (witnessEntry hs root x j).suppliers) :
    ∃ z ∈ retainedEntries hs root, z.val = k ∧ z < j := by
  obtain ⟨z,hz,hzj,hp⟩ := witness_supplier_patch h hc hx hf hL root j hj k hk
  refine ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hz,hzj⟩
  exact component_keeps_supplier (gates hs) hp.symm (Finset.mem_filter.mp hj).2

#print axioms witness_supplier_patch
#print axioms witness_suppliers_retained

end DeletionCode.Explicit.Recognizer
