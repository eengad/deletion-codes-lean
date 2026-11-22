import DeletionCode.Explicit.ReplayEntry

/-! A successful symbolic replay proves that every named supplier was read. -/

namespace DeletionCode.Explicit.ReplayEntry

open LetterSequence

variable {ℓ L current rule : ℕ} {α : Type*}

theorem WindowTrace.read_of_mem {read : Reference → Lift ℓ L α → Prop}
    {starts refs initial out} (h : WindowTrace read starts refs initial out)
    (ref : Reference) (href : ref ∈ refs) :
    ∃ lift, read ref lift := by
  induction h with
  | done => simp at href
  | step hread _ tail ih =>
    rcases List.mem_cons.mp href with rfl | hm
    · exact ⟨_,hread⟩
    · exact ih hm

theorem Recorded.read_of_mem {anchor : Option (Fin ℓ)} {get : ℕ → Option (Completed ℓ α)}
    {e : Entry α} {neg : Lift ℓ e.negativeLength α}
    (h : Recorded L current anchor get e neg) {ref : Reference} (href : ref ∈ e.references) :
    ∃ lift, Reads L current e.rule anchor get ref lift := by
  obtain ⟨_,starts,first,refs,initial,_,he,hfirst,htail⟩ := h
  rw [he] at href
  rcases List.mem_cons.mp href with rfl | hm
  · exact ⟨initial,hfirst⟩
  · exact htail.read_of_mem ref hm

theorem evaluate_reads {anchors : ℕ → Option (Fin ℓ)} {get : ℕ → Option (Completed ℓ α)}
    {e : Entry α} {out : Completed ℓ α} (h : evaluate L current anchors get e = some out)
    {ref : Reference} (hm : ref ∈ e.references) :
    ∃ lift, Reads L current e.rule (anchors e.patch) get ref lift := by
  cases he : negativeLift L current e (anchors e.patch) get with
  | none => simp [evaluate,he] at h
  | some neg => exact (recorded_of_negativeLift he).read_of_mem hm

theorem evaluate_suppliers {anchors : ℕ → Option (Fin ℓ)} {get : ℕ → Option (Completed ℓ α)}
    {e : Entry α} {out : Completed ℓ α} (h : evaluate L current anchors get e = some out)
    {j : ℕ} (hj : j ∈ e.suppliers) :
    j < current ∧ ∃ supplier, get j = some supplier ∧ supplier.rule < e.rule := by
  simp only [Entry.suppliers,List.mem_toFinset,List.mem_filterMap] at hj
  obtain ⟨ref,hm,he⟩ := hj
  cases ref with
  | source => contradiction
  | supplier k side a =>
    have eq : k = j := Option.some.inj he
    subst k
    obtain ⟨lift,hread⟩ := evaluate_reads h hm
    cases hread with
    | supplier j side a e hj he hr _ => exact ⟨hj,e,he,hr⟩

#print axioms evaluate_suppliers

end DeletionCode.Explicit.ReplayEntry
