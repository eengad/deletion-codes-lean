import DeletionCode.Burst.GeneratingModel
import DeletionCode.Burst.ConcreteRecovery
import DeletionCode.Qary.SupportComponents

/-!
End-to-end bounded decoding for generating families of actual edited words.
The number of root positions is proved to equal the number of connected
components of the actual consecutive-window support graph. SignedSupport and
RuleSetGraph identify signed rule components; RecordSerialization encodes the record.
-/
namespace DeletionCode.Burst.GeneratingRecovery

variable {α : Type*} [DecidableEq α] [Inhabited α]

open DeletionCode.Qary.Windows DeletionCode.Burst.HeaderRecovery DeletionCode.Burst.GeneratingModel DeletionCode.Burst.ConcreteDecoder

variable {B : Type*} {k d : ℕ}

theorem initial_vertices_agree (E : EditedFamily α B k d) (b : B) :
    Qary.SupportComponents.vertex E.family (windowLength k d) b false 0 =
      Qary.SupportComponents.vertex E.family (windowLength k d) b true 0 := by
  apply (Qary.SupportComponents.vertex_eq_iff_agree E.family (windowLength k d)
    b b false true 0 0).mpr
  exact E.initial_agreement b

/-- Actual edited-word components and supported de Bruijn graph components coincide. -/
noncomputable def componentGraphEquiv (E : EditedFamily α B k d) :
    GeneratingModel.Components E ≃ Qary.SupportComponents.GraphComponents E.family (windowLength k d) :=
  Qary.SupportComponents.componentEquiv E.family (windowLength k d)
    (by unfold windowLength; omega) (initial_vertices_agree E)

noncomputable instance componentsFintype [Fintype B] (E : EditedFamily α B k d) :
    Fintype (GeneratingModel.Components E) := Fintype.ofFinite _

noncomputable instance graphComponentsFintype [Fintype B] (E : EditedFamily α B k d) :
    Fintype (Qary.SupportComponents.GraphComponents E.family (windowLength k d)) :=
  Fintype.ofEquiv (GeneratingModel.Components E) (componentGraphEquiv E)

/-- Selecting one actual root per component is a bijection onto the marked roots. -/
noncomputable def rootEquiv (E : EditedFamily α B k d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k d)) :
    GeneratingModel.Components E ≃ {b // (model E x n hx hg).schedule.root b} where
  toFun C := ⟨selectedRoot E x n hx hg C, C, rfl⟩
  invFun b := Quotient.mk (GeneratingModel.componentSetoid E.family (windowLength k d)) b.val
  left_inv C := (selectedRoot_spec E x n hx hg C).1
  right_inv b := by
    apply Subtype.ext
    obtain ⟨C, hC⟩ := b.property
    change selectedRoot E x n hx hg
      (Quotient.mk (GeneratingModel.componentSetoid E.family (windowLength k d)) b.val) = b.val
    rw [← hC, (selectedRoot_spec E x n hx hg C).1]

theorem rootCount_eq_components [Fintype B]
    (E : EditedFamily α B k d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k d)) :
    ConcreteInitialization.rootCount (model E x n hx hg) =
      Fintype.card (GeneratingModel.Components E) := by
  classical
  unfold ConcreteInitialization.rootCount
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr (rootEquiv E x n hx hg)).symm

theorem rootCount_eq_graph_components [Fintype B]
    (E : EditedFamily α B k d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k d)) :
    ConcreteInitialization.rootCount (model E x n hx hg) =
      Fintype.card (Qary.SupportComponents.GraphComponents E.family (windowLength k d)) := by
  rw [rootCount_eq_components E x n hx hg]
  exact Fintype.card_congr (componentGraphEquiv E)

/-- Every generating edited family has a bounded successful concrete decoding record. -/
theorem generating_decode_exists [Fintype B] [DecidableEq B]
    (E : EditedFamily α B k d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k d)) :
    ∃ roots instructions,
      roots.length = Fintype.card (Qary.SupportComponents.GraphComponents E.family (windowLength k d)) ∧
      instructions.length ≤ 4 * Fintype.card B ∧
      decode x n k d E.header roots instructions =
        some (fun b i => negativePath (E.header b) (E.long b) i.val) := by
  obtain ⟨roots, instructions, hroots, hcost, hdecode⟩ :=
    ConcreteRecovery.decode_exists (model E x n hx hg) hx
  exact ⟨roots, instructions,
    hroots.trans (rootCount_eq_graph_components E x n hx hg), hcost, hdecode⟩

#print axioms componentGraphEquiv
#print axioms rootEquiv
#print axioms rootCount_eq_components
#print axioms rootCount_eq_graph_components
#print axioms generating_decode_exists

end DeletionCode.Burst.GeneratingRecovery
