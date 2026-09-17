import DeletionCode.RecordSerialization
import Mathlib.SetTheory.Cardinal.Finite

/-!
Counting all finite recovered data represented by generating edited families.
Ranks and unused infinite word tails are omitted from the counted objects.
Finiteness and the cardinal bound follow from the proved finite-record decoder
coverage; neither an injective encoding nor finiteness is assumed as a premise.
-/
namespace DeletionCode.GeneratingCount

open Windows HeaderRecovery GeneratingModel GeneratingRecovery RecordSerialization DescriptionCount

/-- Finite headers and finite negative words admitting a generating-family witness. -/
def GeneratingData (x : Letters) (n k ν c : ℕ) (data : RecoveredData ν) : Prop :=
  ∃ E : EditedFamily (Fin ν) k,
    E.family.Generating x n (windowLength k) ∧
    Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) = c ∧
    dataOfFamily E = data

theorem generatingData_record_exists (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k)
    (data : {data : RecoveredData ν // GeneratingData x n k ν c data}) :
    ∃ d : Description n (windowLength k) ν c,
      decodeDescription x n k ν c hν d = some data.val := by
  obtain ⟨E, hg, hc, hdata⟩ := data.property
  obtain ⟨d, hd⟩ := serialized_generating_coverage E x n c hν hx hg hc
  exact ⟨d, by simpa only [hdata] using hd⟩

/-- Choose a successful finite record, justified by the concrete coverage theorem. -/
noncomputable def encodeGeneratingData (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k)
    (data : {data : RecoveredData ν // GeneratingData x n k ν c data}) :
    Description n (windowLength k) ν c :=
  Classical.choose (generatingData_record_exists x n k ν c hν hx data)

theorem decode_encodeGeneratingData (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k)
    (data : {data : RecoveredData ν // GeneratingData x n k ν c data}) :
    decodeDescription x n k ν c hν (encodeGeneratingData x n k ν c hν hx data) = some data.val :=
  Classical.choose_spec (generatingData_record_exists x n k ν c hν hx data)

theorem encodeGeneratingData_injective (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Function.Injective (encodeGeneratingData x n k ν c hν hx) := by
  intro a b hab
  have ha := decode_encodeGeneratingData x n k ν c hν hx a
  have hb := decode_encodeGeneratingData x n k ν c hν hx b
  rw [hab] at ha
  exact Subtype.ext (Option.some.inj (ha.symm.trans hb))

/-- The entire class of generating finite data is finite, without a Fintype premise. -/
theorem generatingData_finite (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Finite {data : RecoveredData ν // GeneratingData x n k ν c data} :=
  Finite.of_injective (encodeGeneratingData x n k ν c hν hx)
    (encodeGeneratingData_injective x n k ν c hν hx)

theorem generatingData_card_le_description (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {data : RecoveredData ν // GeneratingData x n k ν c data} ≤
      Fintype.card (Description n (windowLength k) ν c) := by
  simpa only [Nat.card_eq_fintype_card] using
    Nat.card_le_card_of_injective (encodeGeneratingData x n k ν c hν hx)
      (encodeGeneratingData_injective x n k ν c hν hx)

/-- There cannot be more supported graph components than indexed bubbles. -/
theorem editedFamily_component_count_le {ν k : ℕ} (E : EditedFamily (Fin ν) k) :
    Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) ≤ ν := by
  classical
  rw [← Fintype.card_congr (componentGraphEquiv E)]
  let : Fintype (GeneratingModel.Components E) := componentsFintype E
  let f : Fin ν → GeneratingModel.Components E :=
    Quotient.mk (GeneratingModel.componentSetoid E.family (windowLength k))
  have hsurj : Function.Surjective f := by
    intro C
    induction C using Quotient.inductionOn with
    | _ b => exact ⟨b, rfl⟩
  have hcard := Fintype.card_le_of_surjective f hsurj
  simpa only [Fintype.card_fin] using hcard

theorem generatingData_components_le (x : Letters) (n k ν c : ℕ)
    (data : RecoveredData ν) (hdata : GeneratingData x n k ν c data) : c ≤ ν := by
  obtain ⟨E, _, hc, _⟩ := hdata
  rw [← hc]
  exact editedFamily_component_count_le E

theorem generatingData_card_bound_of_le (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) (hc : c ≤ ν) :
    Nat.card {data : RecoveredData ν // GeneratingData x n k ν c data} ≤
      n ^ c * (fieldBound (windowLength k) ν) ^ (50 * ν) := by
  exact (generatingData_card_le_description x n k ν c hν hx).trans
    (description_bound n (windowLength k) ν c (by unfold windowLength; omega) hν hc)

/-- The complete class of generating finite path data obeys the description bound. -/
theorem generatingData_card_bound (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {data : RecoveredData ν // GeneratingData x n k ν c data} ≤
      n ^ c * (fieldBound (windowLength k) ν) ^ (50 * ν) := by
  by_cases hc : c ≤ ν
  · exact generatingData_card_bound_of_le x n k ν c hν hx hc
  · let : IsEmpty {data : RecoveredData ν // GeneratingData x n k ν c data} :=
      ⟨fun data => hc (generatingData_components_le x n k ν c data.val data.property)⟩
    simp

#print axioms generatingData_record_exists
#print axioms encodeGeneratingData_injective
#print axioms generatingData_finite
#print axioms generatingData_card_le_description
#print axioms editedFamily_component_count_le
#print axioms generatingData_card_bound

end DeletionCode.GeneratingCount
