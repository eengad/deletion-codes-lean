import DeletionCode.BipartiteSelection
import DeletionCode.Qary.WordHash

/-!
The deterministic code selection for the actual finite conflict graph.
A derived independent set in its bipartite components is restricted to a
single actual hash label, then transported from graph vertices to finite
alphabet words. The resulting code has disjoint radius-t edit-output sets.
No independent set, coloring, or large label fiber is supplied as a premise.
-/
namespace DeletionCode.Qary.CodeSelection

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

open DeletionCode.Qary.HeaderRecovery DeletionCode.Qary.ConflictGraphWitness DeletionCode.BipartiteSelection

variable {n k : ℕ}

noncomputable instance vertexFintype {A : Type*} (t k : ℕ) (label : Bits α n → A) :
    Fintype (FiniteConflictGraph.Vertex t k label) := Fintype.ofFinite _

/-- The actual edit-correction condition: distinct codewords have no common
output obtainable with at most t edits from each word. -/
def Corrects (t : ℕ) (C : Finset (Bits α n)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ¬ FiniteConflictGraph.Confusable t x y

omit [Fintype α] [Inhabited α] in
/-- Thus any shared output uniquely determines a codeword, with the edit
relation exactly the one used by the manuscript's conflict graph. -/
theorem Corrects.eq_of_common_output {t : ℕ} {C : Finset (Bits α n)} (hC : Corrects t C)
    {x y : Bits α n} (hx : x ∈ C) (hy : y ∈ C) (output : List α)
    (hxo : EditAlignment.WithinEdits t (List.ofFn x) output)
    (hyo : EditAlignment.WithinEdits t (List.ofFn y) output) : x = y := by
  by_contra hxy
  exact hC x hx y hy hxy ⟨output, hxo, hyo⟩

/-- Convert the actual integer hash label to its proved finite range. -/
noncomputable def wordLabelFin (Q : ℕ) (hQ : 2 ≤ Q)
    (H : Spectrum α k →+ UnitAddCircle) (x : Bits α n) : Fin Q :=
  ⟨(wordLabel Q H x).toNat, by
    have hr := CircleHash.label_range Q hQ (H (spectrum k x))
    change 0 ≤ wordLabel Q H x ∧ wordLabel Q H x < (Q : ℤ) at hr
    omega⟩

omit [Fintype α] [DecidableEq α] in
theorem wordLabelFin_eq_iff (Q : ℕ) (hQ : 2 ≤ Q)
    (H : Spectrum α k →+ UnitAddCircle) (x y : Bits α n) :
    wordLabelFin Q hQ H x = wordLabelFin Q hQ H y ↔ wordLabel Q H x = wordLabel Q H y := by
  constructor
  · intro h
    have heq : (wordLabel Q H x).toNat = (wordLabel Q H y).toNat := congrArg Fin.val h
    have hx := (CircleHash.label_range Q hQ (H (spectrum k x))).1
    have hy := (CircleHash.label_range Q hQ (H (spectrum k y))).1
    change 0 ≤ wordLabel Q H x at hx
    change 0 ≤ wordLabel Q H y at hy
    omega
  · intro h
    apply Fin.ext
    exact congrArg Int.toNat h

/-- From the actual graph and hash alone, retain at least one word for each
2Q good vertices, in multiplication form. No probability estimate enters
this deterministic selection step. -/
theorem exists_correcting_code (t Q : ℕ) (hQ : 2 ≤ Q)
    (H : Spectrum α k →+ UnitAddCircle) :
    ∃ C : Finset (Bits α n),
      (goodVertices (graph (n := n) t Q H)).card ≤ 2 * Q * C.card ∧ Corrects t C := by
  classical
  let V := Vertex (n := n) t Q H
  let G : SimpleGraph V := graph t Q H
  obtain ⟨I, _hgood, hind, hhalf⟩ := exists_independent_good G
  let label : V → Fin Q := fun v => wordLabelFin Q hQ H v.val
  obtain ⟨a, hlabelcard⟩ := exists_large_label_fiber I label (by omega)
  let J : Finset V := I.filter (fun v => label v = a)
  let C : Finset (Bits α n) := J.image Subtype.val
  have hcard : C.card = J.card := Finset.card_image_of_injective J Subtype.val_injective
  refine ⟨C, ?_, ?_⟩
  · calc
      (goodVertices (graph (n := n) t Q H)).card ≤ 2 * I.card := hhalf
      _ ≤ 2 * (Q * J.card) := Nat.mul_le_mul_left 2 hlabelcard
      _ = 2 * Q * C.card := by rw [hcard, Nat.mul_assoc]
  · intro x hx y hy hxy hconf
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    have hv' := Finset.mem_filter.mp hv
    have hw' := Finset.mem_filter.mp hw
    have hne : v ≠ w := fun heq => hxy (congrArg Subtype.val heq)
    have hlabel : wordLabel Q H v.val = wordLabel Q H w.val :=
      (wordLabelFin_eq_iff Q hQ H v.val w.val).mp (hv'.2.trans hw'.2.symm)
    have hnot : ¬ G.Adj v w := hind hv'.1 hw'.1 hne
    exact hnot ⟨hxy, hconf, hlabel⟩

#print axioms Corrects.eq_of_common_output
#print axioms wordLabelFin_eq_iff
#print axioms exists_correcting_code

end DeletionCode.Qary.CodeSelection
