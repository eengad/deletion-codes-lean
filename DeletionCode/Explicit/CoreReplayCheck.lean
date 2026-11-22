import DeletionCode.Explicit.CoreReplay
import DeletionCode.Explicit.BubbleFamilies

/-! Read final bubble words from the active letters of a replay slot. -/

namespace DeletionCode.Explicit.CoreWeight

open ReplayGrammar ReplayEntry LetterSequence FieldHash Borrowed

variable {ℓ q E r : ℕ}

/-- The symbols at fresh offsets are part of the shape. Original offsets
are precisely the coordinates filled from the source assignment. -/
def freshPattern (u : StoredLift ℓ (Fin q)) : List (Option (Fin q)) :=
  List.ofFn fun i => match u.2.letters i with
    | .original _ => none
    | .fresh _ _ a => some a

private def spelled (u : StoredLift ℓ (Fin q)) (x : Fin ℓ → Fin q) : List (Fin q) :=
  List.ofFn (u.2.spelling x)

/-- Read the flanks from the assigned negative lift. The removed letters
must agree with the recorded word, and the positive lift must spell its
resulting replacement. -/
def recoveredBubble (K b L Λ : ℕ) (x : Fin ℓ → Fin q)
    (p : DecodedEntry q × Completed ℓ (Fin q)) : Option (BubbleWord (Fin q) K b L) :=
  let e := p.1.entry
  let neg := spelled p.2.negative x
  let pos := spelled p.2.positive x
  if p.2.negative.2.freshOffsets.card ≤ Λ then do
    let w ← BubbleFamilies.localWord K b L e.left e.removed e.replacement neg
    if w.positiveWord = pos then some w else none
  else none

private def finalRuleValid (K b L Λ s : ℕ) (pad : Fin q)
    (m : Materialized ℓ q E r) (x : Fin ℓ → Fin q) (id : Fin E) : Bool :=
  letI : Inhabited (Fin q) := ⟨pad⟩
  let entries := m.entries.filter (fun p => p.1.finalBubble && p.1.entry.rule == id.val)
  match entries.mapM (recoveredBubble K b L Λ x) with
  | none => false
  | some words =>
    if h : words.length = s then
      Catalogue.validCheck (fun i : Fin s => words.get (Fin.cast h.symm i))
        (fun _ => (0 : Fin 1))
    else false

/-- Check all the final rule rows of a compact core. -/
def coreCheck (K b L Λ s : ℕ) (pad : Fin q)
    (m : Materialized ℓ q E r) (x : Fin ℓ → Fin q) : Bool :=
  (m.rules.sort (· ≤ ·)).all (finalRuleValid K b L Λ s pad m x)

/-- The concrete Stage 1 replay data used by the core-weight enumerator. -/
def coreReplayData (ℓ q E L b t r₀ K Λ : ℕ) (pad : Fin q) :
    ReplayData ℓ q (q^L) t r₀ (descriptionBound E L b q) :=
  checkedReplayData pad (fun m x => coreCheck K b L Λ (2*t) pad m x)

private theorem recoveredBubble_congr (K b L Λ : ℕ)
    {x y : Fin ℓ → Fin q} (p : DecodedEntry q × Completed ℓ (Fin q))
    (hn : p.2.negative.2.spelling x = p.2.negative.2.spelling y)
    (hp : p.2.positive.2.spelling x = p.2.positive.2.spelling y) :
    recoveredBubble K b L Λ x p = recoveredBubble K b L Λ y p := by
  simp only [recoveredBubble,spelled,hn,hp]
  rfl

private theorem mapM_option_congr {A B : Type*} (xs : List A) (f g : A → Option B)
    (h : ∀ a ∈ xs, f a = g a) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    rw [List.mapM_cons,List.mapM_cons,h a List.mem_cons_self,
      ih (fun u hu => h u (List.mem_cons_of_mem _ hu))]

/-- Validation uses the same active assignment as the recovered row matrix. -/
theorem coreCheck_congr (K b L Λ s : ℕ) (pad : Fin q) (m : Materialized ℓ q E r)
    {x y : Fin ℓ → Fin q} (h : ∀ i ∈ m.support, x i = y i) :
    coreCheck K b L Λ s pad m x = coreCheck K b L Λ s pad m y := by
  unfold coreCheck
  apply congrArg (fun p => (m.rules.sort (· ≤ ·)).all p)
  funext id
  let entries := m.entries.filter (fun p => p.1.finalBubble && p.1.entry.rule == id.val)
  have hs : entries.mapM (recoveredBubble K b L Λ x) = entries.mapM (recoveredBubble K b L Λ y) := by
    apply mapM_option_congr
    intro p hp
    obtain ⟨hm,hp⟩ := List.mem_filter.mp hp
    have hf : p.1.finalBubble = true := (Bool.and_eq_true_iff.mp hp).1
    obtain ⟨hn,hpos⟩ := m.final_spelling_congr h hm hf
    exact recoveredBubble_congr K b L Λ p hn hpos
  have heps := hs
  simp only [entries] at heps
  simp only [finalRuleValid,heps]

theorem coreCheck_of_families (K b L Λ s : ℕ) (pad : Fin q) (m : Materialized ℓ q E r)
    (x : Fin ℓ → Fin q)
    (h : ∀ id ∈ m.rules, ∃ words : Fin s → BubbleWord (Fin q) K b L,
      @Catalogue.ValidCatalogue _ ⟨pad⟩ K b L s 1 words (fun _ => 0) ∧
      ((m.entries.filter (fun p => p.1.finalBubble && p.1.entry.rule == id.val)).mapM
        (recoveredBubble K b L Λ x)) = some (List.ofFn words)) :
    coreCheck K b L Λ s pad m x = true := by
  unfold coreCheck
  apply List.all_eq_true.mpr
  intro id hi
  obtain ⟨words,hw,hr⟩ := h id ((Finset.mem_sort _).mp hi)
  let : Inhabited (Fin q) := ⟨pad⟩
  have hv := (Catalogue.validCheck_iff words (fun _ => (0 : Fin 1))).mpr hw
  unfold finalRuleValid
  dsimp only
  rw [hr]
  simpa using hv

theorem core_rules_from_source {E L b t r₀ K Λ : ℕ} (pad : Fin q)
    (k : ReplaySlot ℓ q E L b t r₀) (x : Fin ℓ → Fin q)
    {m : Materialized ℓ q E (k.1.val+1)} (h : materialize k = some m)
    (ha : coreCheck K b L Λ (2*t) pad m x = true) :
    (coreReplayData ℓ q E L b t r₀ K Λ pad).rules k (fun i => x i.val) =
      some (m.matrix L pad x) := by
  apply rules_of_materialized pad _ k x h
  rw [coreCheck_congr K b L Λ (2*t) pad m]
  · exact ha
  · intro i hi
    have hs : slotSupport k = m.support := by simp [slotSupport,h]
    have hi' : i ∈ slotSupport k := hs.symm ▸ hi
    simp [slotWord,hi']

#print axioms coreCheck_congr
#print axioms core_rules_from_source

end DeletionCode.Explicit.CoreWeight
