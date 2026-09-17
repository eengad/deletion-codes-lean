import DeletionCode.RuleSetGraph

/-!
Supplier retention for the actual signed rules of the manuscript.

Rule adjacency means intersection of incident vertices in the de Bruijn support
graph. A supplier shares the actual negative gram, hence is in the same rule
block. Restricting a generating family to any union of whole blocks therefore
preserves generation. Independence is irrelevant to this step.
-/

namespace DeletionCode.GeneratingBlocks

open SignedSupport RuleSetGraph

/-- The manuscript's negative-coordinate condition, with the original order. -/
def Generating {I : Type*} {L : ℕ} (v : Gram L → ℤ)
    (G : I → Gram L → ℤ) (rank : I → ℕ) : Prop :=
  ∀ i g, G i g = -1 → v g ≠ 0 ∨ ∃ j, rank j < rank i ∧ G j g ≠ 0

/-- Two rules share an actual incident support vertex. -/
def Adjacent {I : Type*} {L : ℕ} (G : I → Gram L → ℤ) (i j : I) : Prop :=
  ∃ u, Incident {G i} u ∧ Incident {G j} u

def Connected {I : Type*} {L : ℕ} (G : I → Gram L → ℤ) : I → I → Prop :=
  Relation.EqvGen (Adjacent G)

/-- Membership is constant on rule blocks; this permits any union of blocks. -/
def BlockClosed {I : Type*} {L : ℕ} (G : I → Gram L → ℤ) (S : Set I) : Prop :=
  ∀ i ∈ S, ∀ j, Connected G i j → j ∈ S

theorem nonzero_incident {L : ℕ} (w : Gram L → ℤ) (g : Gram L) (hg : w g ≠ 0) :
    Incident {w} (gramPrefix g) := by
  classical
  exact ⟨gramSuffix g, Or.inl ⟨w, by simp, g, hg, rfl, rfl⟩⟩

theorem common_gram_adjacent {I : Type*} {L : ℕ} (G : I → Gram L → ℤ)
    (i j : I) (g : Gram L) (hi : G i g ≠ 0) (hj : G j g ≠ 0) :
    Adjacent G i j :=
  ⟨gramPrefix g, nonzero_incident (G i) g hi, nonzero_incident (G j) g hj⟩

/-- A supplying rule is in the same block, derived from the shared gram. -/
theorem supplier_connected {I : Type*} {L : ℕ} (G : I → Gram L → ℤ)
    (i j : I) (g : Gram L) (hi : G i g = -1) (hj : G j g ≠ 0) :
    Connected G i j := by
  apply Relation.EqvGen.rel
  exact common_gram_adjacent G i j g (by omega) hj

/-- Keeping whole blocks retains every required earlier supplier. -/
theorem generating_restrict {I : Type*} {L : ℕ} (v : Gram L → ℤ)
    (G : I → Gram L → ℤ) (rank : I → ℕ) (S : Set I)
    (hgen : Generating v G rank) (hclosed : BlockClosed G S) :
    Generating v (fun i : S => G i.val) (fun i : S => rank i.val) := by
  intro i g hneg
  rcases hgen i.val g hneg with hsource | ⟨j, hlt, hj⟩
  · exact Or.inl hsource
  · exact Or.inr ⟨⟨j, hclosed i.val i.property j
      (supplier_connected G i.val j g hneg hj)⟩, hlt, hj⟩

/-- The union of all blocks meeting an arbitrary set of selected rules. -/
def blockHull {I : Type*} {L : ℕ} (G : I → Gram L → ℤ) (T : Set I) : Set I :=
  {j | ∃ i ∈ T, Connected G i j}

theorem subset_blockHull {I : Type*} {L : ℕ} (G : I → Gram L → ℤ) (T : Set I) :
    T ⊆ blockHull G T := by
  intro i hi
  exact ⟨i, hi, Relation.EqvGen.refl i⟩

theorem blockHull_closed {I : Type*} {L : ℕ} (G : I → Gram L → ℤ) (T : Set I) :
    BlockClosed G (blockHull G T) := by
  rintro i ⟨a, ha, hai⟩ j hij
  exact ⟨a, ha, Relation.EqvGen.trans a i j hai hij⟩

/-- The precise whole-block restriction used in the relation case of the witness proof. -/
theorem generating_blockHull {I : Type*} {L : ℕ} (v : Gram L → ℤ)
    (G : I → Gram L → ℤ) (rank : I → ℕ) (T : Set I)
    (hgen : Generating v G rank) :
    Generating v (fun i : blockHull G T => G i.val)
      (fun i : blockHull G T => rank i.val) :=
  generating_restrict v G rank (blockHull G T) hgen (blockHull_closed G T)

/-- Restriction to a single block is the large-block case of the same argument. -/
theorem generating_single_block {I : Type*} {L : ℕ} (v : Gram L → ℤ)
    (G : I → Gram L → ℤ) (rank : I → ℕ) (a : I)
    (hgen : Generating v G rank) :
    Generating v (fun i : {i // Connected G a i} => G i.val)
      (fun i : {i // Connected G a i} => rank i.val) := by
  apply generating_restrict v G rank {i | Connected G a i} hgen
  intro i hi j hij
  exact Relation.EqvGen.trans a i j hi hij

/-- Existing concrete-family signed generation is exactly this ordered condition. -/
theorem signedGenerating_iff {B : Type*} [Fintype B] (F : RootSelection.Family B)
    (x : Windows.Letters) (n L : ℕ) :
    SignedGenerating F x n L ↔
      Generating (wordSpectrum x n L)
        (fun i : ℕ => ruleSpectrum F L (ruleBubbles F i)) id := Iff.rfl

#print axioms common_gram_adjacent
#print axioms generating_restrict
#print axioms generating_blockHull
#print axioms generating_single_block
#print axioms signedGenerating_iff

end DeletionCode.GeneratingBlocks
