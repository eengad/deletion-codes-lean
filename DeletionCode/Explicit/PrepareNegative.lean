import DeletionCode.Explicit.PatchTable
import DeletionCode.Explicit.RulePatchComponents

/-! The frozen dictionary and computed patch table used to prepare one
exposed bubble before installing any gates of its rule. -/

namespace DeletionCode.Explicit.LetterGraphCuts

open LetterSequence LocalBudget RulePatch ReplayEntry LiftDictionary SelectedReplay
open Qary.SignedSupport FieldHash

variable {ℓ d s : ℕ} {α : Type*} [DecidableEq α]

/-- Choose the dictionary windows and assemble the negative lift. Source
references use position zero temporarily, so they encode absolute starts.
The caller stores the occurrences so they can later be encoded relative
to the computed patch anchor. -/
def prepareNegative (pad : α) (x : Fin ℓ → α) (history : Array (Completed ℓ α))
    (L current rule : ℕ) (root : Fin ℓ) (left : ℕ) (removed replacement : List α) (right : ℕ)
    (word : Fin (left+removed.length+right) → α) :
    Option (List (Occurrence ℓ L α) × Lift ℓ (left+removed.length+right) α) := do
  let os ← select pad x history L word
  let entry : Entry α := ⟨rule,0,left,removed,replacement,right,
    os.map (fun o => o.location.reference root)⟩
  let w ← negativeLift L current entry (some root) (fun j => history[j]?)
  pure (os,w)

theorem prepareNegative_correct (pad : α) (x : Fin ℓ → α) (history : Array (Completed ℓ α))
    (data : Fin d × Fin s → GateData ℓ α)
    {E : Letter ℓ α → Letter ℓ α → Prop} {marked : Finset (Fin ℓ)}
    (H : History ℓ α E marked) (hrecords : PatchTable.RecordsGraph data E marked)
    (hid : Function.Injective (fun e => (data e).id))
    {K Λ L b R current rule : ℕ} (hx : Strong x K Λ) (hL : 2 ≤ L)
    (hroomCap : 4*(s*b*R) ≤ L) (hΛ : 14*(s*b*R) ≤ Λ)
    (hwidth : ∀ e, L ≤ 2 * ((data e).interval.last.val+1-(data e).interval.first.val))
    (hmark : ∀ e, (data e).marks.card ≤ b) (hstock : ∀ e, (data e).inserted.card ≤ b)
    (hcutoff : ∀ p, (componentRules (PatchTable.incidence data) (.inr p)).card ≤ R)
    (hc : history.size ≤ current) (hr : ∀ j : Fin history.size, history[j].rule < rule)
    (hold : ∀ (j : ℕ) (out : Completed ℓ α), history[j]? = some out → ∀ side, (out.lift side).2.Follows E)
    (root : Fin ℓ) (left : ℕ) (removed replacement : List α) (right : ℕ)
    (word : Fin (left+removed.length+right) → α)
    {ρ : Gram α L → ZMod 3}
    (hexposed : Exposed (fieldSpectrum (paddedLetters pad x) ℓ L)
      (Submodule.span (ZMod 3) (Set.range (liftedRule pad x history))) ρ)
    (hneg : ∀ a, a+L ≤ left+removed.length+right →
      ρ (gram (paddedLetters pad word) L a) = -1)
    (hlen : L ≤ left+removed.length+right) (hshort : left+removed.length+right ≤ 3*L)
    (hoverlap : (left+removed.length+right-L+1)/2 + (K+2*Λ) ≤ L) :
    ∃ os w, prepareNegative pad x history L current rule root left removed replacement right word =
      some (os,w) ∧ SpellsAt w x word 0 ∧ w.Follows E ∧
      w.freshOffsets.card ≤ 14*(s*b*R) ∧ w.omissions.card ≤ 14*(s*b*R) := by
  obtain ⟨os,hselect,hoccurs⟩ := select_spec pad x history hexposed word hlen hneg root hc hr
  let entry : Entry α := ⟨rule,0,left,removed,replacement,right,
    os.map (fun o => o.location.reference root)⟩
  have hstarts : ∀ a ∈ selectedStarts L entry.negativeLength, a+L ≤ entry.negativeLength := by
    intro a ha
    have hm := selectedStarts_mem.mp ha
    change L ≤ entry.negativeLength at hlen
    rcases hm with rfl | rfl | rfl <;> omega
  have hreads := dictionary_reads pad x (current := current) (rule := rule) word root
    (fun j => history[j]?) hstarts hoccurs
  have caps (p : Fin (PatchTable.patchCount data)) :
      ((PatchTable.patches data).marks p).card ≤ s*b*R ∧
      (PatchTable.stock data p).card ≤ s*b*R := by
    obtain ⟨rules,hr,hp⟩ := component_rule_sets_of_cutoff _ R hcutoff p
    exact PatchTable.capacity data hmark hstock p rules hr hp
  obtain ⟨w,hw,hsp,hpath⟩ := negativeLift_of_history H (PatchTable.patches data)
    (PatchTable.owner data) (PatchTable.stock data) hx hL (PatchTable.patch_width data hwidth)
    hroomCap hΛ (fun p => (caps p).1) (fun p => (caps p).2) (PatchTable.records_marked data hrecords)
    (PatchTable.records_inventory data hrecords hid) entry word (some root)
    (fun j => history[j]?) hold hlen hshort hoverlap hreads
  obtain ⟨hf,ho⟩ := PatchTable.path_budget data H hrecords hid hL hroomCap hwidth hmark hstock
    (component_rule_sets_of_cutoff _ R hcutoff) w hlen hshort hpath
  refine ⟨os,w,?_,hsp,hpath,hf,ho⟩
  have he := hw
  dsimp only [entry] at he
  simp [prepareNegative,hselect,he]

#print axioms prepareNegative_correct

/-- A source reference can now be written relative to the final patch
anchor. The windows read by the replay are the very same symbolic lifts. -/
theorem prepareNegative_reanchor (pad : α) (x : Fin ℓ → α)
    (history : Array (Completed ℓ α)) (L current rule : ℕ) (root anchor : Fin ℓ)
    (left : ℕ) (removed replacement : List α) (right : ℕ)
    (word : Fin (left+removed.length+right) → α)
    (hc : history.size ≤ current) (hr : ∀ j : Fin history.size, history[j].rule < rule)
    {os : List (Occurrence ℓ L α)} {w : Lift ℓ (left+removed.length+right) α}
    (h : prepareNegative pad x history L current rule root left removed replacement right word =
      some (os,w)) :
    let entry : Entry α := ⟨rule,0,left,removed,replacement,right,
      os.map (fun o => o.location.reference anchor)⟩
    negativeLift L current entry (some anchor) (fun j => history[j]?) = some w := by
  unfold prepareNegative at h
  cases hselect : select pad x history L word with
  | none => simp [hselect] at h
  | some wins =>
    let entry : Entry α := ⟨rule,0,left,removed,replacement,right,
      wins.map (fun o => o.location.reference root)⟩
    change (do let os ← select pad x history L word; _) = _ at h
    rw [hselect] at h
    change (negativeLift L current entry (some root) (fun j => history[j]?)).bind
      (fun neg => some (wins,neg)) = some (os,w) at h
    cases hn : negativeLift L current entry (some root) (fun j => history[j]?) with
    | none => simp [hn] at h
    | some neg =>
      rw [hn] at h
      have e : (wins,neg) = (os,w) := Option.some.inj h
      obtain ⟨hos,hw⟩ := Prod.mk.inj e
      subst os w
      have hlookup := select_lookup_at pad x history L word hselect
      have same : List.Forall₂ (fun ref ref' => readReference L current rule (some root)
          (fun j => history[j]?) ref = readReference L current rule (some anchor)
            (fun j => history[j]?) ref') entry.references (wins.map (fun o => o.location.reference anchor)) := by
        change List.Forall₂ _ (wins.map (fun o => o.location.reference root)) _
        clear e h hn entry hselect neg
        generalize selectedStarts L (left+removed.length+right) = starts at hlookup
        induction hlookup with
        | nil => exact .nil
        | cons hfirst _ ih =>
          exact .cons ((lookup_reference hfirst root hc hr).trans
            (lookup_reference hfirst anchor hc hr).symm) ih
      exact (negativeLift_reads_congr entry _ (some root) (some anchor) _ same).symm.trans hn

#print axioms prepareNegative_reanchor

end DeletionCode.Explicit.LetterGraphCuts
