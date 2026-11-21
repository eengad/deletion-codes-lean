import DeletionCode.Burst.RecordSerialization
import Mathlib.SetTheory.Cardinal.Finite

/-!
Counting all finite recovered data represented by generating edited families.
Ranks and unused infinite word tails are omitted from the counted objects.
Finiteness and the cardinal bound follow from the proved finite-record decoder
coverage; neither an injective encoding nor finiteness is assumed as a premise.
-/
namespace DeletionCode.Burst.GeneratingCount

variable {α : Type*} [DecidableEq α] [Inhabited α] [Fintype α]

open DeletionCode.Qary.Windows DeletionCode.Burst.HeaderRecovery DeletionCode.Burst.GeneratingModel DeletionCode.Burst.GeneratingRecovery DeletionCode.Burst.RecordSerialization DeletionCode.Burst.DescriptionCount

/-- Finite headers and finite negative words admitting a generating-family witness. -/
def GeneratingData (x : Letters α) (n k d ν c : ℕ) (data : RecoveredData α ν) : Prop :=
  ∃ E : EditedFamily α (Fin ν) k d,
    E.family.Generating x n (windowLength k d) ∧
    Fintype.card (Qary.SupportComponents.GraphComponents E.family (windowLength k d)) = c ∧
    dataOfFamily E = data

theorem generatingData_record_exists (x : Letters α) (n k d ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k)
    (data : {data : RecoveredData α ν // GeneratingData x n k d ν c data}) :
    ∃ record : Description α d n (windowLength k d) ν c,
      decodeDescription x n k d ν c hν record = some data.val := by
  obtain ⟨E, hg, hc, hdata⟩ := data.property
  obtain ⟨record, hd⟩ := serialized_generating_coverage E x n c hν hx hg hc
  exact ⟨record, by simpa only [hdata] using hd⟩

/-- Choose a successful finite record, justified by the concrete coverage theorem. -/
noncomputable def encodeGeneratingData (x : Letters α) (n k d ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k)
    (data : {data : RecoveredData α ν // GeneratingData x n k d ν c data}) :
    Description α d n (windowLength k d) ν c :=
  Classical.choose (generatingData_record_exists x n k d ν c hν hx data)

theorem decode_encodeGeneratingData (x : Letters α) (n k d ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k)
    (data : {data : RecoveredData α ν // GeneratingData x n k d ν c data}) :
    decodeDescription x n k d ν c hν (encodeGeneratingData x n k d ν c hν hx data) = some data.val :=
  Classical.choose_spec (generatingData_record_exists x n k d ν c hν hx data)

theorem encodeGeneratingData_injective (x : Letters α) (n k d ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Function.Injective (encodeGeneratingData x n k d ν c hν hx) := by
  intro a b hab
  have ha := decode_encodeGeneratingData x n k d ν c hν hx a
  have hb := decode_encodeGeneratingData x n k d ν c hν hx b
  rw [hab] at ha
  exact Subtype.ext (Option.some.inj (ha.symm.trans hb))

/-- The entire class of generating finite data is finite, without a Fintype premise. -/
theorem generatingData_finite (x : Letters α) (n k d ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Finite {data : RecoveredData α ν // GeneratingData x n k d ν c data} :=
  Finite.of_injective (encodeGeneratingData x n k d ν c hν hx)
    (encodeGeneratingData_injective x n k d ν c hν hx)

theorem generatingData_card_le_description (x : Letters α) (n k d ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {data : RecoveredData α ν // GeneratingData x n k d ν c data} ≤
      Fintype.card (Description α d n (windowLength k d) ν c) := by
  simpa only [Nat.card_eq_fintype_card] using
    Nat.card_le_card_of_injective (encodeGeneratingData x n k d ν c hν hx)
      (encodeGeneratingData_injective x n k d ν c hν hx)

/-- There cannot be more supported graph components than indexed bubbles. -/
theorem editedFamily_component_count_le {ν k d : ℕ} (E : EditedFamily α (Fin ν) k d) :
    Fintype.card (Qary.SupportComponents.GraphComponents E.family (windowLength k d)) ≤ ν := by
  classical
  rw [← Fintype.card_congr (componentGraphEquiv E)]
  let : Fintype (GeneratingModel.Components E) := componentsFintype E
  let f : Fin ν → GeneratingModel.Components E :=
    Quotient.mk (GeneratingModel.componentSetoid E.family (windowLength k d))
  have hsurj : Function.Surjective f := by
    intro C
    induction C using Quotient.inductionOn with
    | _ b => exact ⟨b, rfl⟩
  have hcard := Fintype.card_le_of_surjective f hsurj
  simpa only [Fintype.card_fin] using hcard

theorem generatingData_components_le (x : Letters α) (n k d ν c : ℕ)
    (data : RecoveredData α ν) (hdata : GeneratingData x n k d ν c data) : c ≤ ν := by
  obtain ⟨E, _, hc, _⟩ := hdata
  rw [← hc]
  exact editedFamily_component_count_le E

theorem generatingData_card_bound_of_le (x : Letters α) (n k d ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) (hc : c ≤ ν) :
    Nat.card {data : RecoveredData α ν // GeneratingData x n k d ν c data} ≤
      n ^ c * (fieldBound (windowLength k d) ν) ^ (53 * ν) * Fintype.card α ^ (6 * d * ν) := by
  exact (generatingData_card_le_description x n k d ν c hν hx).trans
    (description_bound α d n (windowLength k d) ν c (by unfold windowLength; omega) hν hc)

/-- The complete class of generating finite path data obeys the description bound. -/
theorem generatingData_card_bound (x : Letters α) (n k d ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {data : RecoveredData α ν // GeneratingData x n k d ν c data} ≤
      n ^ c * (fieldBound (windowLength k d) ν) ^ (53 * ν) * Fintype.card α ^ (6 * d * ν) := by
  by_cases hc : c ≤ ν
  · exact generatingData_card_bound_of_le x n k d ν c hν hx hc
  · let : IsEmpty {data : RecoveredData α ν // GeneratingData x n k d ν c data} :=
      ⟨fun data => hc (generatingData_components_le x n k d ν c data.val data.property)⟩
    simp

#print axioms generatingData_record_exists
#print axioms encodeGeneratingData_injective
#print axioms generatingData_finite
#print axioms generatingData_card_le_description
#print axioms editedFamily_component_count_le
#print axioms generatingData_card_bound

end DeletionCode.Burst.GeneratingCount
