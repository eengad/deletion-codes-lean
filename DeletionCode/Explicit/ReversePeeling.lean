import DeletionCode.Explicit.RulePatchCore

/-! Recovery in reverse peeling order, with patch-local missing letters. -/

namespace DeletionCode.Explicit.RulePatch

variable {d s c ℓ q : ℕ}

/-- Write just the positions of the pivot bubble. -/
def restorePositions (P : Finset (Fin ℓ)) (value old : Fin ℓ → Fin q) : Fin ℓ → Fin q :=
  fun i => if i ∈ P then value i else old i

def restore
    (active : Fin d × Fin s → Finset (Fin ℓ)) (digit : Fin d × Fin s → ℕ)
    (read : (Fin d × Fin s) → ℕ → (Fin ℓ → Fin q) → Option (Fin ℓ → Fin q)) :
    List (Fin d × Fin s) → (Fin ℓ → Fin q) → Option (Fin ℓ → Fin q)
  | [], word => some word
  | e :: es, word => do
    let old ← restore active digit read es word
    let v ← read e (digit e) old
    pure (restorePositions (active e) v old)

theorem restore_preserves
    (active : Fin d × Fin s → Finset (Fin ℓ)) (digit : Fin d × Fin s → ℕ)
    (read : (Fin d × Fin s) → ℕ → (Fin ℓ → Fin q) → Option (Fin ℓ → Fin q))
    {es : List (Fin d × Fin s)} {word out : Fin ℓ → Fin q}
    (hout : restore active digit read es word = some out)
    {i : Fin ℓ} (hi : ∀ e ∈ es, i ∉ active e) : out i = word i := by
  induction es generalizing out with
  | nil =>
    have h : word = out := Option.some.inj hout
    rw [← h]
  | cons e es ih =>
    cases htail : restore active digit read es word with
    | none => simp [restore,htail] at hout
    | some old =>
      cases hv : read e (digit e) old with
      | none => simp [restore,htail,hv] at hout
      | some v =>
        have h : restorePositions (active e) v old = out := by simpa [restore,htail,hv] using hout
        rw [← h,restorePositions,ite_eq_right (hi e (by simp))]
        exact ih htail (fun f hf => hi f (by simp [hf]))

theorem LegalTrace.rules_in {a : Incidence d s c} {S T : Finset (Fin d)}
    {es : List (Fin d × Fin s)} (h : LegalTrace a S es T) :
    ∀ e ∈ es, e.1 ∈ S := by
  induction h with
  | stop _ => simp
  | step hm _ _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | ht
    · exact hm
    · exact Finset.mem_of_mem_erase (ih e ht)

private theorem unique_edge {a : Incidence d s c} {S : Finset (Fin d)} {e f : Fin d × Fin s}
    (hf : f.1 ∈ S) (honly : atPatch a S (a e) = {e}) (h : a f = a e) :
    f = e := by
  have hm : f ∈ atPatch a S (a e) :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hf,Finset.mem_univ _⟩,h⟩
  exact Finset.mem_singleton.mp (honly ▸ hm)

/-- Each previously omitted patch is unavailable during recursive recovery. -/
def available (owner : Fin ℓ → Option (Fin c)) (blocked : Finset (Fin c)) (i : Fin ℓ) : Prop :=
  ∀ p ∈ blocked, owner i ≠ some p

/-- A bucket reader needs only the nonpivot bubbles of its rule. After
executing the reverse trace all letters outside previously omitted patches
agree with the source. -/
theorem LegalTrace.restore_agrees {a : Incidence d s c} {S T : Finset (Fin d)}
    {es : List (Fin d × Fin s)} (h : LegalTrace a S es T)
    (active : Fin d × Fin s → Finset (Fin ℓ)) (owner : Fin ℓ → Option (Fin c))
    (hfit : ∀ e i, i ∈ active e → owner i = some (a e))
    (digit : Fin d × Fin s → ℕ)
    (read : (Fin d × Fin s) → ℕ → (Fin ℓ → Fin q) → Option (Fin ℓ → Fin q))
    (x word : Fin ℓ → Fin q) (blocked : Finset (Fin c))
    (hblock : ∀ e : Fin d × Fin s, e.1 ∈ S → a e ∉ blocked)
    (hlit : ∀ i, available owner blocked i → (∀ e ∈ es, i ∉ active e) → word i = x i)
    (hread : ∀ e ∈ es, ∀ y : Fin ℓ → Fin q,
      (∀ j ≠ e.2, ∀ i ∈ active (e.1,j), y i = x i) →
      ∃ v, read e (digit e) y = some v ∧ ∀ i ∈ active e, v i = x i) :
    ∃ out, restore active digit read es word = some out ∧
      ∀ i, available owner blocked i → out i = x i := by
  induction h generalizing blocked with
  | stop _ =>
    exact ⟨word,rfl,fun i hi => hlit i hi (by simp)⟩
  | @step S T es e hm honly tail ih =>
    let B := insert (a e) blocked
    have hexclude {f : Fin d × Fin s} (hf : f.1 ∈ S.erase e.1) : a f ≠ a e := by
      intro hp
      have heq := unique_edge (Finset.mem_of_mem_erase hf) honly hp
      exact (Finset.mem_erase.mp hf).1 (congrArg Prod.fst heq)
    have hb : ∀ f : Fin d × Fin s, f.1 ∈ S.erase e.1 → a f ∉ B := by
      intro f hf hp
      rcases Finset.mem_insert.mp hp with heq | hb
      · exact hexclude hf heq
      · exact hblock f (Finset.mem_of_mem_erase hf) hb
    have hl : ∀ i, available owner B i → (∀ f ∈ es, i ∉ active f) → word i = x i := by
      intro i hi htail
      apply hlit i (fun p hp => hi p (Finset.mem_insert_of_mem hp))
      intro f hf hactive
      rcases List.mem_cons.mp hf with rfl | hft
      · exact hi (a f) (Finset.mem_insert_self _ _) (hfit f i hactive)
      · exact htail f hft hactive
    obtain ⟨old,ho,hagree⟩ := ih B hb hl (fun f hf => hread f (List.mem_cons_of_mem _ hf))
    have hother : ∀ j ≠ e.2, ∀ i ∈ active (e.1,j), old i = x i := by
      intro j hj i hi
      apply hagree i
      intro p hp he
      have hpeq : a (e.1,j) = p := Option.some.inj ((hfit (e.1,j) i hi).symm.trans he)
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact hj (congrArg Prod.snd (unique_edge (f := (e.1,j)) hm honly hpeq))
      · exact hblock (e.1,j) hm (hpeq.symm ▸ hp')
    obtain ⟨v,hv,hcorrect⟩ := hread e (by simp) old hother
    refine ⟨restorePositions (active e) v old, by simp [restore,ho,hv], ?_⟩
    intro i hi
    by_cases ha : i ∈ active e
    · simpa only [restorePositions,ite_eq_left ha] using hcorrect i ha
    · rw [restorePositions,ite_eq_right ha]
      by_cases howner : owner i = some (a e)
      · have hnone : ∀ f ∈ es, i ∉ active f := by
          intro f hf hfi
          exact hexclude (tail.rules_in f hf) (Option.some.inj ((hfit f i hfi).symm.trans howner))
        rw [restore_preserves active digit read ho hnone]
        exact hlit i hi (fun f hf => (List.mem_cons.mp hf).elim (fun he => he ▸ ha) (hnone f))
      · exact hagree i (fun p hp => (Finset.mem_insert.mp hp).elim (fun he => he ▸ howner) (hi p))

theorem LegalTrace.pivotPatches_nodup {a : Incidence d s c} {S T : Finset (Fin d)}
    {es : List (Fin d × Fin s)} (h : LegalTrace a S es T) :
    (es.map a).Nodup := by
  induction h with
  | stop _ => simp
  | @step S T es e hm honly tail ih =>
    rw [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih⟩
    intro he
    obtain ⟨f,hf,hfe⟩ := List.mem_map.mp he
    have hs := tail.rules_in f hf
    have eq := unique_edge (Finset.mem_of_mem_erase hs) honly hfe
    exact (Finset.mem_erase.mp hs).1 (congrArg Prod.fst eq)

theorem LegalTrace.count {a : Incidence d s c} {S T : Finset (Fin d)}
    {es : List (Fin d × Fin s)} (h : LegalTrace a S es T) :
    S.card = es.length+T.card := by
  induction h with
  | stop _ => simp
  | @step S T es e hm _ _ ih =>
    have hcard := Finset.card_erase_of_mem hm
    have hpos := Finset.card_pos.mpr (show S.Nonempty from ⟨e.1,hm⟩)
    simp only [List.length_cons]
    omega

theorem restore_word {a : Incidence d s c} {S T : Finset (Fin d)}
    {es : List (Fin d × Fin s)} (h : LegalTrace a S es T)
    (active : Fin d × Fin s → Finset (Fin ℓ)) (owner : Fin ℓ → Option (Fin c))
    (hfit : ∀ e i, i ∈ active e → owner i = some (a e))
    (digit : Fin d × Fin s → ℕ)
    (read : (Fin d × Fin s) → ℕ → (Fin ℓ → Fin q) → Option (Fin ℓ → Fin q))
    (x word : Fin ℓ → Fin q)
    (hlit : ∀ i, (∀ e ∈ es, i ∉ active e) → word i = x i)
    (hread : ∀ e ∈ es, ∀ y : Fin ℓ → Fin q,
      (∀ j ≠ e.2, ∀ i ∈ active (e.1,j), y i = x i) →
      ∃ v, read e (digit e) y = some v ∧ ∀ i ∈ active e, v i = x i) :
    restore active digit read es word = some x := by
  obtain ⟨out,hr,ha⟩ := h.restore_agrees active owner hfit digit read x word ∅
    (by simp) (fun i _ => hlit i) hread
  have he : out = x := funext (fun i => ha i (by simp [available]))
  rwa [he] at hr

#print axioms restore_word

end DeletionCode.Explicit.RulePatch
