import DeletionCode.GeneratingModel
import DeletionCode.ConcreteRecovery
import DeletionCode.SupportComponents

/-!
End-to-end bounded decoding for generating families of actual edited words.
The number of root positions is proved to equal the number of connected
components of the actual consecutive-window support graph. SignedSupport and
RuleSetGraph identify signed rule components; RecordSerialization encodes the record.
-/
namespace DeletionCode.GeneratingRecovery

open Windows HeaderRecovery GeneratingModel ConcreteDecoder

variable {B : Type*} {k : ℕ}

theorem initial_vertices_agree (E : EditedFamily B k) (b : B) :
    SupportComponents.vertex E.family (windowLength k) b false 0 =
      SupportComponents.vertex E.family (windowLength k) b true 0 := by
  apply (SupportComponents.vertex_eq_iff_agree E.family (windowLength k)
    b b false true 0 0).mpr
  exact PathMemory.pathInitialAgreement k (E.header b) (E.long b)

/-- Actual edited-word components and supported de Bruijn graph components coincide. -/
noncomputable def componentGraphEquiv (E : EditedFamily B k) :
    GeneratingModel.Components E ≃ SupportComponents.GraphComponents E.family (windowLength k) :=
  SupportComponents.componentEquiv E.family (windowLength k)
    (by unfold windowLength; omega) (initial_vertices_agree E)

noncomputable instance componentsFintype [Fintype B] (E : EditedFamily B k) :
    Fintype (GeneratingModel.Components E) := Fintype.ofFinite _

noncomputable instance graphComponentsFintype [Fintype B] (E : EditedFamily B k) :
    Fintype (SupportComponents.GraphComponents E.family (windowLength k)) :=
  Fintype.ofEquiv (GeneratingModel.Components E) (componentGraphEquiv E)

/-- Selecting one actual root per component is a bijection onto the marked roots. -/
noncomputable def rootEquiv (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k)) :
    GeneratingModel.Components E ≃ {b // (model E x n hx hg).schedule.root b} where
  toFun C := ⟨selectedRoot E x n hx hg C, C, rfl⟩
  invFun b := Quotient.mk (GeneratingModel.componentSetoid E.family (windowLength k)) b.val
  left_inv C := (selectedRoot_spec E x n hx hg C).1
  right_inv b := by
    apply Subtype.ext
    obtain ⟨C, hC⟩ := b.property
    change selectedRoot E x n hx hg
      (Quotient.mk (GeneratingModel.componentSetoid E.family (windowLength k)) b.val) = b.val
    rw [← hC, (selectedRoot_spec E x n hx hg C).1]

theorem rootCount_eq_components [Fintype B]
    (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k)) :
    ConcreteInitialization.rootCount (model E x n hx hg) =
      Fintype.card (GeneratingModel.Components E) := by
  classical
  unfold ConcreteInitialization.rootCount
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr (rootEquiv E x n hx hg)).symm

theorem rootCount_eq_graph_components [Fintype B]
    (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k)) :
    ConcreteInitialization.rootCount (model E x n hx hg) =
      Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) := by
  rw [rootCount_eq_components E x n hx hg]
  exact Fintype.card_congr (componentGraphEquiv E)

/-- Every generating edited family has a bounded successful concrete decoding record. -/
theorem generating_decode_exists [Fintype B] [DecidableEq B]
    (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k)) :
    ∃ roots instructions,
      roots.length = Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) ∧
      instructions.length ≤ 4 * Fintype.card B ∧
      decode x n k E.header roots instructions =
        some (fun b i => negativePath k (E.header b) (E.long b) i.val) := by
  obtain ⟨roots, instructions, hroots, hcost, hdecode⟩ :=
    ConcreteRecovery.decode_exists (model E x n hx hg) hx
  exact ⟨roots, instructions,
    hroots.trans (rootCount_eq_graph_components E x n hx hg), hcost, hdecode⟩

#print axioms componentGraphEquiv
#print axioms rootEquiv
#print axioms rootCount_eq_components
#print axioms rootCount_eq_graph_components
#print axioms generating_decode_exists

end DeletionCode.GeneratingRecovery
