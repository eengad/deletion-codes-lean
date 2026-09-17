import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Lean.Elab.Tactic.Omega

/-!
Finite connected sets can be built from one member by repeatedly adding a
member adjacent to the current set. The growth order is proved to exist from
induced connectedness; no enumeration or spanning tree is assumed.
-/

namespace DeletionCode.FiniteConnectedGrowth

variable {α : Type*} [DecidableEq α]

/-- Edges are restricted to the chosen finite vertex set. -/
def Induced (B : Finset α) (r : α → α → Prop) (u v : α) : Prop :=
  u ∈ B ∧ v ∈ B ∧ r u v

/-- Every nonempty proper subset of a connected finite set has an outgoing edge. -/
theorem frontier (B S : Finset α) (r : α → α → Prop)
    (hconnected : ∀ a ∈ B, ∀ b ∈ B, Relation.EqvGen (Induced B r) a b)
    (hsub : S ⊆ B) (hS : S.Nonempty) (hproper : S ≠ B) :
    ∃ w ∈ B, w ∉ S ∧ ∃ u ∈ S, r w u ∨ r u w := by
  classical
  by_contra hnone
  have preserve : ∀ a b, Relation.EqvGen (Induced B r) a b → (a ∈ S ↔ b ∈ S) := by
    intro a b hpath
    induction hpath with
    | rel a b hedge =>
      obtain ⟨haB, hbB, hr⟩ := hedge
      constructor
      · intro haS
        by_contra hbS
        exact hnone ⟨b, hbB, hbS, a, haS, Or.inr hr⟩
      · intro hbS
        by_contra haS
        exact hnone ⟨a, haB, haS, b, hbS, Or.inl hr⟩
    | refl a => exact Iff.rfl
    | symm a b h ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  obtain ⟨a, haS⟩ := hS
  have hback : B ⊆ S := by
    intro b hbB
    exact (preserve a b (hconnected a (hsub haS) b hbB)).mp haS
  exact hproper (Finset.Subset.antisymm hsub hback)

/-- Induction by adjoining adjacent members of a nonempty induced connected set. -/
theorem connected_induction (B : Finset α) (r : α → α → Prop)
    (hB : B.Nonempty)
    (hconnected : ∀ a ∈ B, ∀ b ∈ B, Relation.EqvGen (Induced B r) a b)
    (P : Finset α → Prop)
    (hsingleton : ∀ a ∈ B, P {a})
    (hgrowth : ∀ U : Finset α, U ⊆ B → ∀ w ∈ B, w ∉ U →
      (∃ u ∈ U, r w u ∨ r u w) → P U → P (insert w U)) : P B := by
  have aux : ∀ d : ℕ, ∀ U : Finset α, U ⊆ B → U.Nonempty →
      P U → B.card - U.card = d → P B := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro U hsub hU hP hdiff
      by_cases heq : U = B
      · simpa only [heq] using hP
      · obtain ⟨w, hwB, hwU, hadj⟩ := frontier B U r hconnected hsub hU heq
        have hsub' : insert w U ⊆ B := Finset.insert_subset_iff.mpr ⟨hwB, hsub⟩
        have hP' : P (insert w U) := hgrowth U hsub w hwB hwU hadj hP
        have hcard : (insert w U).card = U.card + 1 := Finset.card_insert_of_notMem hwU
        have hbound : (insert w U).card ≤ B.card := Finset.card_le_card hsub'
        have hsmaller : B.card - (insert w U).card < d := by omega
        exact ih (B.card - (insert w U).card) hsmaller (insert w U) hsub'
          ⟨w, Finset.mem_insert_self w U⟩ hP' rfl
  obtain ⟨a, ha⟩ := hB
  exact aux (B.card - ({a} : Finset α).card) {a}
    (Finset.singleton_subset_iff.mpr ha) ⟨a, Finset.mem_singleton_self a⟩
    (hsingleton a ha) rfl

/-- One saved unit at every connected addition gives the usual (d-1)|B|+1 bound. -/
theorem connected_count_bound (B : Finset α) (r : α → α → Prop)
    (hB : B.Nonempty)
    (hconnected : ∀ a ∈ B, ∀ b ∈ B, Relation.EqvGen (Induced B r) a b)
    (f : Finset α → ℕ) (d : ℕ) (hd : 1 ≤ d)
    (hsingleton : ∀ a ∈ B, f {a} ≤ d)
    (hgrowth : ∀ U : Finset α, U ⊆ B → ∀ w ∈ B, w ∉ U →
      (∃ u ∈ U, r w u ∨ r u w) → f (insert w U) + 1 ≤ f U + d) :
    f B ≤ (d - 1) * B.card + 1 := by
  apply connected_induction B r hB hconnected (fun U => f U ≤ (d - 1) * U.card + 1)
  · intro a ha
    have hbase := hsingleton a ha
    simp only [Finset.card_singleton, Nat.mul_one]
    omega
  · intro U hsub w hwB hwU hadj hbound
    have hstep := hgrowth U hsub w hwB hwU hadj
    rw [Finset.card_insert_of_notMem hwU, Nat.mul_add, Nat.mul_one]
    omega

#print axioms frontier
#print axioms connected_induction
#print axioms connected_count_bound

end DeletionCode.FiniteConnectedGrowth
