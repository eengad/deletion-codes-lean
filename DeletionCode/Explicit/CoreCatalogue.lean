import DeletionCode.Explicit.CoreWeight

/-! Enumeration from replay descriptions, anchors, and the letters on their
active positions, as used in manuscript `d:core-weight`. -/

namespace DeletionCode.Explicit.CoreWeight

open FieldHash BucketBalance

/-- A replay slot fixes the active positions before reading any letters.
For an assignment on those positions, return the matrix of the final rules
if the replay, family membership, and catalogue membership checks succeed.
Row independence is checked separately by the enumerator. -/
structure ReplayData (ℓ q n t r₀ Γ : ℕ) where
  support : Slot ℓ t r₀ Γ → Finset (Fin ℓ)
  rules : (k : Slot ℓ t r₀ Γ) → (↥(support k) → Fin q) →
    Option (TernaryMatrix (k.1.val + 1) n)

namespace ReplayData

variable {ℓ q n t r₀ Γ θ : ℕ} (D : ReplayData ℓ q n t r₀ Γ)

abbrev Candidate := (k : Slot ℓ t r₀ Γ) × (↥(D.support k) → Fin q)

def admissible (c : D.Candidate) : Bool :=
  (D.rules c.1 c.2).any (fun A => decide (ternaryRank A = c.1.1.val + 1))

abbrev Index := {c : D.Candidate // D.admissible c = true}

/-- Finite enumeration over slots and assignments, filtered by the replay
checks and the full-row-rank test. Each surviving index contributes once. -/
def object (i : D.Index) : Object ℓ q n where
  rows := i.val.1.1.val + 1
  assignment := ⟨D.support i.val.1, i.val.2⟩
  rules := (D.rules i.val.1 i.val.2).getD 0

private theorem object_rank (i : D.Index) : (D.object i).rules.rank = (D.object i).rows := by
  have h := i.property
  cases he : D.rules i.val.1 i.val.2 with
  | none => simp [admissible, he] at h
  | some A => simpa [admissible, object, he, ternaryRank_eq] using h

private theorem independent (i : D.Index) : LinearIndependent F₃ (D.object i).rules.row := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  simpa [Set.finrank, Matrix.rank_eq_finrank_span_row] using (D.object_rank i).symm

private theorem distinct {i j : D.Index} (hk : i.val.1 = j.val.1)
    (ha : (D.object i).assignment = (D.object j).assignment) : i = j := by
  rcases i with ⟨⟨k,f⟩,hi⟩
  rcases j with ⟨⟨k',g⟩,hj⟩
  change k = k' at hk
  subst k'
  change (⟨D.support k,f⟩ : Assignment ℓ q) = ⟨D.support k,g⟩ at ha
  have he : f = g := eq_of_heq (Assignment.mk.inj ha).2
  subst g
  rfl

/-- Every decoded full-rank object whose rules lie in the kernel contributes
to the weight of its source word, with the assignment read from that word. -/
theorem weight_pos_of_replay (H : TernaryMatrix θ n) (x : Fin ℓ → Fin q)
    (k : Slot ℓ t r₀ Γ) (A : TernaryMatrix (k.1.val+1) n)
    (hdecode : D.rules k (fun i => x i.val) = some A)
    (hind : LinearIndependent F₃ A.row) (hker : ∀ j, A.mulVec (H j) = 0) :
    0 < weight D.object H x := by
  let c : D.Candidate := ⟨k,fun i => x i.val⟩
  have hr : ternaryRank A = k.1.val+1 := by simpa [ternaryRank_eq] using hind.rank_matrix
  have hc : D.admissible c = true := by simp [admissible, c, hdecode, hr]
  apply (weight_pos_iff _ _ _).mpr
  refine ⟨⟨c,hc⟩,?_,fun _ => rfl⟩
  change ∀ j, ((D.rules k (fun i => x i.val)).getD 0).mulVec (H j) = 0
  rw [hdecode]
  exact hker

/-- The catalogue produced by the enumerator satisfies `d:core-mean` for
every replay table, including tables with empty slots or dependent outputs. -/
theorem mean_bound (hq : 0 < q) :
    completionMean (freeHash θ n) (rootMass D.object) ≤
      (Γ : ℚ) * ∑ r : Fin r₀, (ℓ : ℚ)^(t*(r.val+1)) / ((3 : ℚ)^θ)^(r.val+1) :=
  uniform_mass_le hq D.object (fun i => i.val.1) D.support (fun _ => rfl)
    (fun _ _ hk ha => D.distinct hk ha) (fun _ => rfl) D.independent

#print axioms weight_pos_of_replay
#print axioms mean_bound

end ReplayData
end DeletionCode.Explicit.CoreWeight
