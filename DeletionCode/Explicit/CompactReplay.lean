import DeletionCode.Explicit.ReplayRelabel
import DeletionCode.Explicit.BackwardSlice

/-! Replay a chronological subset in its compact numbering. -/

namespace DeletionCode.Explicit.ReplayEntry

open BackwardSlice

variable {ℓ N : ℕ} {α : Type*}

/-- A read from a verified table is visible only after its entry was processed. -/
def prior (out : Fin N → Completed ℓ α) (k j : ℕ) : Option (Completed ℓ α) :=
  if h : j < N ∧ j < k then some (out ⟨j,h.1⟩) else none

private theorem take_array_get (out : Fin N → Completed ℓ α) (k j : ℕ) :
    ((List.ofFn out).take k).toArray[j]? = prior out k j := by
  simp only [List.getElem?_toArray,List.getElem?_take,List.getElem?_ofFn,prior]
  by_cases h : j < k <;> by_cases h' : j < N <;> simp [h,h']

/-- A row-by-row successful evaluation produces exactly the recorded array. -/
theorem replay_of_table (L : ℕ) (anchors : ℕ → Option (Fin ℓ))
    (entries : Fin N → Entry α) (out : Fin N → Completed ℓ α)
    (h : ∀ i : Fin N, evaluate L i.val anchors (prior out i.val) (entries i) = some (out i)) :
    replay L anchors (List.ofFn entries) = some (List.ofFn out).toArray := by
  suffices hp : ∀ k ≤ N, replay L anchors ((List.ofFn entries).take k) =
      some ((List.ofFn out).take k).toArray by
    have hr := hp N le_rfl
    rw [List.take_of_length_le (show (List.ofFn entries).length ≤ N by simp),
      List.take_of_length_le (show (List.ofFn out).length ≤ N by simp)] at hr
    exact hr
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hlt : k < N := hk
    have he : k < (List.ofFn entries).length := by simpa using hlt
    have hout : k < (List.ofFn out).length := by simpa using hlt
    have ih' := ih hlt.le
    rw [List.take_succ_eq_append_getElem he,List.take_succ_eq_append_getElem hout]
    unfold replay at *
    rw [List.foldlM_append,ih']
    have hsize : ((List.ofFn out).take k).toArray.size = k := by
      change ((List.ofFn out).take k).length = k
      simp [List.length_take, Nat.min_eq_left hlt.le]
    have hs : (fun j => ((List.ofFn out).take k).toArray[j]?) = prior out k :=
      funext (take_array_get out k)
    simp only [List.foldlM_cons,List.foldlM_nil,List.getElem_ofFn,
      Option.pure_def,Option.bind_eq_bind,Option.bind_some]
    have hrow : evaluate L k anchors (prior out k) (entries ⟨k,hlt⟩) = some (out ⟨k,hlt⟩) :=
      h ⟨k,hlt⟩
    rw [hsize,hs,hrow]
    simp

/-- The compact index of a retained row. Indices outside the slice are
unused by a valid compact program. -/
def compactIndex (T : Finset (Fin N)) (j : ℕ) : ℕ :=
  if h : j < N then
    if ht : (⟨j,h⟩ : Fin N) ∈ T then (number T ⟨⟨j,h⟩,ht⟩).val else 0
  else 0

theorem compactIndex_original (T : Finset (Fin N)) (i : Fin T.card) :
    compactIndex T (original T i).val = i.val := by
  let a := T.orderIsoOfFin rfl
  change compactIndex T (a i).val.val = _
  unfold compactIndex
  rw [dite_eq_left (a i).val.isLt,dite_eq_left (a i).property]
  exact congrArg Fin.val (a.symm_apply_apply i)

/-- Restrict a verified table to a supplier-closed slice. The result retains
exact spelling and original positions up to renaming the fresh identifiers.
The rule map must preserve chronology comparisons with suppliers. -/
theorem replay_compact (L : ℕ) (anchors : ℕ → Option (Fin ℓ))
    (entries : Fin N → Entry α) (out : Fin N → Completed ℓ α)
    (T : Finset (Fin N)) (g : ℕ → ℕ)
    (h : ∀ i ∈ T, evaluate L i.val anchors (prior out i.val) (entries i) = some (out i))
    (hsub : ∀ i ∈ T, ∀ j ∈ (entries i).suppliers,
      ∃ k ∈ T, k.val = j ∧ k < i)
    (hrule : ∀ i ∈ T, ∀ j ∈ T,
      (out j).rule < (entries i).rule ↔ g (out j).rule < g (entries i).rule) :
    replay L anchors (List.ofFn fun i => (entries (original T i)).relabel (compactIndex T) g) =
      some (List.ofFn fun i => (out (original T i)).relabel (compactIndex T) g).toArray := by
  apply replay_of_table
  intro i
  let originalOut := fun i : Fin T.card => (out (original T i)).relabel (compactIndex T) g
  let f := compactIndex T
  have hiT : original T i ∈ T := (T.orderIsoOfFin rfl i).property
  have hi : f (original T i).val = i.val := compactIndex_original T i
  have hlocal := evaluate_relabel anchors (prior out (original T i).val) (prior originalOut i.val)
    f g (entries (original T i)) (h (original T i) hiT) ?_
  · simpa only [hi] using hlocal
  · intro j hj
    obtain ⟨k,hk,rfl,hklt⟩ := hsub (original T i) hiT j hj
    let kk : Fin T.card := number T ⟨k,hk⟩
    have hkk : original T kk = k :=
      congrArg Subtype.val ((T.orderIsoOfFin rfl).apply_symm_apply ⟨k,hk⟩)
    have hf : f k.val = kk.val := by rw [← compactIndex_original T kk,hkk]
    have hlt : kk < i := (T.orderEmbOfFin rfl).lt_iff_lt.mp (hkk ▸ hklt)
    refine ⟨⟨fun _ => by rw [hf,hi]; exact hlt,fun _ => hklt⟩,?_,?_⟩
    · have h₁ : k.val < N ∧ k.val < (original T i).val := ⟨k.isLt,hklt⟩
      have h₂ : kk.val < T.card ∧ kk.val < i.val := ⟨kk.isLt,hlt⟩
      rw [hf,prior,dite_eq_left h₂,prior,dite_eq_left h₁]
      simp [originalOut,hkk,f]
    · intro u hu
      have h₁ : k.val < N ∧ k.val < (original T i).val := ⟨k.isLt,hklt⟩
      have he : out k = u := by simpa [prior,h₁] using hu
      rw [← he]
      exact hrule (original T i) hiT k hk

#print axioms replay_of_table
#print axioms replay_compact

end DeletionCode.Explicit.ReplayEntry
