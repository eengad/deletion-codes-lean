import DeletionCode.Explicit.ReplayGrammar

/-! Successful replay uses only the anchors named in the description. -/

namespace DeletionCode.Explicit.ReplayEntry

variable {ℓ L current : ℕ} {α : Type*}

theorem replay_anchor_congr (entries : List (Entry α)) (a b : ℕ → Option (Fin ℓ))
    (h : ∀ e ∈ entries, a e.patch = b e.patch) :
    replay L a entries = replay L b entries := by
  unfold replay
  generalize (#[] : Array (Completed ℓ α)) = done
  induction entries generalizing done with
  | nil => rfl
  | cons e rest ih =>
    have heval : evaluate L done.size a (fun j => done[j]?) e =
        evaluate L done.size b (fun j => done[j]?) e := by
      unfold evaluate
      rw [h e List.mem_cons_self]
    simp only [List.foldlM_cons,heval]
    cases he : evaluate L done.size b (fun j => done[j]?) e with
    | none => rfl
    | some u => exact ih (fun f hf => h f (List.mem_cons_of_mem _ hf)) (done.push u)

#print axioms replay_anchor_congr

end DeletionCode.Explicit.ReplayEntry
