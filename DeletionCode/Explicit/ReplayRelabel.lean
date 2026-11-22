import DeletionCode.Explicit.ReplayEntry

/-! Replay is equivariant under chronological renumbering of a supplier slice. -/

namespace DeletionCode.Explicit.ReplayEntry

open LetterSequence

def renameRef (f : ℕ → ℕ) : Reference → Reference
  | .source delta => .source delta
  | .supplier j side a => .supplier (f j) side a

/-- Renumber a completed bubble after a chronological slice. -/
def Completed.relabel {ℓ : ℕ} {α : Type*} (e : Completed ℓ α) (f g : ℕ → ℕ) : Completed ℓ α :=
  ⟨g e.rule,⟨e.negative.1,e.negative.2.renameEntries f⟩,
    ⟨e.positive.1,e.positive.2.renameEntries f⟩⟩

@[simp] theorem Completed.relabel_lift {ℓ : ℕ} {α : Type*} (e : Completed ℓ α)
    (f g : ℕ → ℕ) (side : Side) :
    ((e.relabel f g).lift side).1 = (e.lift side).1 := by cases side <;> rfl

private theorem Completed.relabel_window {ℓ : ℕ} {α : Type*} (e : Completed ℓ α)
    (f g : ℕ → ℕ) (side : Side) (a L : ℕ) (h : a+L ≤ (e.lift side).1) :
    ((e.relabel f g).lift side).2.window a L (by simpa only [Completed.relabel_lift] using h) =
      ((e.lift side).2.window a L h).renameEntries f := by cases side <;> rfl

/-- Renumber the entry and rule indices of one recorded bubble. The source
reference stays relative to the same patch anchor. -/
def Entry.relabel {α : Type*} (e : Entry α) (f g : ℕ → ℕ) : Entry α :=
  { e with rule := g e.rule, references := e.references.map (renameRef f) }

private theorem read_relabel {ℓ : ℕ} {α : Type*} {L current rule : ℕ}
    (anchor : Option (Fin ℓ)) (get get' : ℕ → Option (Completed ℓ α))
    (f g : ℕ → ℕ) (ref : Reference)
    (hkeep : ∀ j side a, ref = .supplier j side a →
      (j < current ↔ f j < f current) ∧
      get' (f j) = (get j).map (fun e => e.relabel f g) ∧
      ∀ out, get j = some out → (out.rule < rule ↔ g out.rule < g rule)) :
    readReference L (f current) (g rule) anchor get' (renameRef f ref) =
      (readReference L current rule anchor get ref).map (fun w => w.renameEntries f) := by
  cases ref with
  | source delta =>
    cases anchor with
    | none => rfl
    | some p =>
      simp only [renameRef,readReference]
      split
      · split
        · simp
        · rfl
      · rfl
  | supplier j side a =>
    obtain ⟨horder,hget,hrule⟩ := hkeep j side a rfl
    by_cases hc : j < current
    · have hnc := Nat.not_le_of_gt hc
      have hnc' := Nat.not_le_of_gt (horder.mp hc)
      cases hg : get j with
      | none =>
        have hget' : get' (f j) = none := by simpa [hg] using hget
        simp [renameRef,readReference,hnc,hnc',hg,hget']
      | some e =>
        have hget' : get' (f j) = some (e.relabel f g) := by simpa [hg] using hget
        have hr := hrule e hg
        by_cases he : e.rule < rule
        · have hnrule := Nat.not_le_of_gt he
          have hnrule' : ¬ g rule ≤ (e.relabel f g).rule := Nat.not_le_of_gt (hr.mp he)
          by_cases hw : a+L ≤ (e.lift side).1
          · simp [renameRef,readReference,hnc,hnc',hg,hget',hnrule,hnrule',hw,
              Completed.relabel_window e f g side a L hw]
          · simp [renameRef,readReference,hnc,hnc',hg,hget',hnrule,hnrule',hw]
        · have hnr := Nat.le_of_not_gt he
          have hnr' : g rule ≤ (e.relabel f g).rule := Nat.le_of_not_gt (mt hr.mpr he)
          simp [renameRef,readReference,hnc,hnc',hg,hget',hnr,hnr']
    · have hnc := Nat.le_of_not_gt hc
      have hnc' := Nat.le_of_not_gt (mt horder.mpr hc)
      simp [renameRef,readReference,hnc,hnc']

/-- The recorded evaluator produces the same two lifts after consistently
renumbering the retained suppliers, rules, and fresh identifiers. -/
theorem evaluate_relabel {ℓ : ℕ} {α : Type*} {L current : ℕ}
    (anchors : ℕ → Option (Fin ℓ)) (get get' : ℕ → Option (Completed ℓ α))
    (f g : ℕ → ℕ) (e : Entry α) {out : Completed ℓ α}
    (h : evaluate L current anchors get e = some out)
    (hkeep : ∀ j ∈ e.suppliers,
      (j < current ↔ f j < f current) ∧
      get' (f j) = (get j).map (fun e => e.relabel f g) ∧
      ∀ out, get j = some out → (out.rule < e.rule ↔ g out.rule < g e.rule)) :
    evaluate L (f current) anchors get' (e.relabel f g) = some (out.relabel f g) := by
  unfold evaluate at h
  cases hn : negativeLift L current e (anchors e.patch) get with
  | none => simp [hn] at h
  | some w =>
    have eq : completedOf current e w = out := by simpa [hn] using h
    subst out
    have hr : List.Forall₂ (fun r r' =>
      readReference L (f current) (g e.rule) (anchors e.patch) get' r' =
        (readReference L current e.rule (anchors e.patch) get r).map (fun w => w.renameEntries f))
        e.references (e.references.map (renameRef f)) := by
      apply List.forall₂_map_right_iff.mpr
      apply List.forall₂_same.mpr
      intro ref hm
      apply read_relabel
      intro j side a he
      apply hkeep j
      simp only [Entry.suppliers,List.mem_toFinset,List.mem_filterMap]
      exact ⟨ref,hm,by simp [he]⟩
    have hn' := negativeLift_renameEntries e _ (g e.rule) (anchors e.patch) get get' f hn hr
    have hp : completedOf (f current) (e.relabel f g) (w.renameEntries f) =
        (completedOf current e w).relabel f g := by
      have hi := Lift.installGate_renameEntries w current (fun i : Fin e.replacement.length =>
        e.replacement[i]) f
      exact congrArg (fun pos : Lift ℓ e.positiveLength α =>
        (⟨g e.rule,⟨e.negativeLength,w.renameEntries f⟩,⟨e.positiveLength,pos⟩⟩ : Completed ℓ α)) hi
    unfold evaluate
    have hh : negativeLift L (f current) (e.relabel f g) (anchors (e.relabel f g).patch) get' =
        some (w.renameEntries f) := hn'
    rw [hh]
    exact congrArg some hp

#print axioms evaluate_relabel

end DeletionCode.Explicit.ReplayEntry
