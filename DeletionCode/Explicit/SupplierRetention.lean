import DeletionCode.Explicit.PatchSupport
import DeletionCode.Explicit.FirstEventGeometry
import DeletionCode.Explicit.ReplayRelabel

/-! Supplier retention across final patch labels (`d:supplier-retention`). -/

namespace DeletionCode.Explicit.PatchSupport

open LetterSequence LetterGraphCuts RulePatch ReplayEntry

variable {ℓ d s : ℕ} {α : Type*}
variable (data : Fin d × Fin s → GateData ℓ α) (lifts : Fin d × Fin s → Completed ℓ α)

/-- A selected occurrence on the consumer's final negative lift identifies
the same patch as the matching occurrence on its named supplier. -/
theorem supplier_same_patch {K Λ L a b : ℕ} {x : Fin ℓ → α}
    (hx : Strong x K Λ) (hfit : LiftsFit data lifts Λ) (hk : K+2*Λ ≤ L)
    (consumer supplier : Fin d × Fin s) (side : Side)
    (ha : a+L ≤ (lifts consumer).negative.1)
    (hb : b+L ≤ ((lifts supplier).lift side).1)
    (hspell : ((lifts consumer).negative.2.window a L ha).spelling x =
      (((lifts supplier).lift side).2.window b L hb).spelling x) :
    PatchTable.incidence data supplier = PatchTable.incidence data consumer :=
  (equal_windows_same_patch data lifts hx hfit hk consumer supplier .negative side ha hb hspell).symm

/-- Components keep every supplier of their rules, and thus keep the entire
backward closure under supplier edges with the same-patch property. -/
theorem component_keeps_supplier {e f : Fin d × Fin s}
    {root : Fin d ⊕ Fin (PatchTable.patchCount data)}
    (h : PatchTable.incidence data e = PatchTable.incidence data f)
    (he : e.1 ∈ componentRules (PatchTable.incidence data) root) :
    f.1 ∈ componentRules (PatchTable.incidence data) root := by
  let a := PatchTable.incidence data
  have hc := (mem_componentRules a root _).mp he
  have he' := bubble_reaches a e.1 e.2
  have hf' := (bubble_reaches a f.1 f.2).symm
  have hh : a (e.1,e.2) = a (f.1,f.2) := h
  rw [← hh] at hf'
  exact (mem_componentRules a root _).mpr (hc.trans (he'.trans hf'))

#print axioms supplier_same_patch
#print axioms component_keeps_supplier

section Independence

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

/-- A chronological list of rows is independent when each new row lies
outside the span of those already present. -/
theorem independent_of_chronology {n : ℕ} (rows : Fin n → M)
    (hrows : ∀ i, rows i ∉ Submodule.span F (rows '' Set.Iio i)) :
    LinearIndependent F rows := by
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n ih =>
    apply linearIndependent_finSucc'.mpr
    constructor
    · apply ih
      intro i hi
      apply hrows i.castSucc
      apply Submodule.span_mono _ hi
      rintro _ ⟨j,hj,rfl⟩
      exact ⟨j.castSucc,hj,rfl⟩
    · intro hi
      apply hrows (Fin.last n)
      apply Submodule.span_mono _ hi
      rintro _ ⟨j,rfl⟩
      exact ⟨j.castSucc,Fin.castSucc_lt_last _,rfl⟩

/-- In particular, a first-event component inherits independent rows in
the same order as the source history. -/
theorem component_rows_independent {c : ℕ} (a : Incidence d s c)
    (root : Fin d ⊕ Fin c) (rows : Fin d → M)
    (hrows : ∀ i, rows i ∉ Submodule.span F (rows '' Set.Iio i)) :
    LinearIndependent F (fun i : Fin (componentRules a root).card => rows (originalRule a root i).val) :=
  (independent_of_chronology rows hrows).comp _
    (Subtype.val_injective.comp ((componentRules a root).orderIsoOfFin rfl).injective)

#print axioms component_rows_independent

end Independence

end DeletionCode.Explicit.PatchSupport
