import DeletionCode.Explicit.RecognizerBirth
import DeletionCode.Explicit.WitnessTables
import DeletionCode.Explicit.ReplayFamilyMember
import DeletionCode.Explicit.FamilyBuckets
import DeletionCode.Explicit.PeelingBuckets
import DeletionCode.Explicit.CoreReplayCheck

/-! Renumbered witness lifts retain their source letters and family membership. -/

namespace DeletionCode.Explicit.LetterSequence

variable {ℓ n : ℕ} {α : Type*}

@[simp] theorem Lift.spelling_renameEntries (u : Lift ℓ n α) (f : ℕ → ℕ) (x : Fin ℓ → α) :
    (u.renameEntries f).spelling x = u.spelling x := by
  funext i
  simp only [Lift.spelling,Lift.renameEntries_letter]
  cases u.letters i <;> rfl

@[simp] theorem Lift.positions_renameEntries (u : Lift ℓ n α) (f : ℕ → ℕ) :
    (u.renameEntries f).positions = u.positions := by
  ext p
  simp only [Lift.mem_positions,Lift.renameEntries_letter,Letter.position_renameEntry]

@[simp] theorem Lift.freshOffsets_renameEntries (u : Lift ℓ n α) (f : ℕ → ℕ) :
    (u.renameEntries f).freshOffsets = u.freshOffsets := by
  ext i
  simp [Lift.freshOffsets,Lift.renameEntries_letter,Letter.position_renameEntry]

end DeletionCode.Explicit.LetterSequence

namespace DeletionCode.Explicit.Recognizer

open LetterSequence LetterGraphCuts ReplayEntry ReplayGrammar Borrowed
open PeelingBuckets BubbleFamilies RuleAddition PatchSupport

variable {ℓ q K b L Λ R s : ℕ}

def sliceRecord (hs : History ℓ q L s) (root : RuleVertex hs) (x : Fin ℓ → Fin q)
    (T : Finset (Fin (hs.length*s))) (j : Fin (hs.length*s)) : Recorded ℓ q :=
  ⟨(witnessEntry hs root x j).relabel (compactIndex T) (witnessRuleNumber hs root),
    (witnessLifts hs j).relabel (compactIndex T) (witnessRuleNumber hs root)⟩

private theorem slice_vector {hs : History ℓ q L s} (root : RuleVertex hs) (pad : Fin q)
    (x : Fin ℓ → Fin q) (T : Finset (Fin (hs.length*s))) (j : Fin (hs.length*s)) :
    vectorOf L pad (sliceRecord hs root x T j) x =
      fun i => LiftDictionary.bubbleVector pad x (witnessLifts hs j) (finFunctionFinEquiv.symm i) := by
  funext i
  simp [vectorOf,sliceRecord,Completed.relabel,LiftDictionary.bubbleVector]

/-- The source letters in the compact lift recover its original catalogue
bubble. The same bubble is used for the small-family index, the pivot
bucket, and the core-slot validity check. -/
theorem slice_rule_families
    {P : Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs)
    (root : RuleVertex hs) (T : Finset (Fin (hs.length*s))) (i : Fin hs.length) :
    ∃ words : Fin s → BubbleWord (Fin q) K b L,
      @Catalogue.ValidCatalogue _ ⟨pad⟩ K b L s 1 words (fun _ => 0) ∧
      (hs.get i).row = CatalogueEnumeration.row pad words ∧
      ∀ j : Fin s,
        let p := sliceRecord hs root x T (finProdFinEquiv (i,j))
        (replayShape p).member K b L Λ pad (originalValues p.2.negative.2 x) = some (words j) ∧
        vector pad (words j) = vectorOf L pad p x ∧
        (∀ f g, CoreWeight.recoveredBubble K b L Λ x (⟨p.1,f,g⟩,p.2) = some (words j)) := by
  let : Inhabited (Fin q) := ⟨pad⟩
  have hL : 0 < L := by have pp := P.window; omega
  obtain ⟨words,hw,hrow,_,hprep⟩ := (h.batch_at i).fromCatalogue
  have hcat := (CatalogueEnumeration.mem_rules_iff pad hL words).mp hw
  refine ⟨words,hcat,hrow,?_⟩
  intro j
  dsimp only
  let w := words j
  let gate := (hs.get i).bubbles j
  let p := sliceRecord hs root x T (finProdFinEquiv (i,j))
  have hspec := (hprep j).2
  have hn := hspec.spelling
  have hp := hspec.positiveSpelling
  have he : finProdFinEquiv.symm (finProdFinEquiv (i,j)) = (i,j) :=
    Equiv.symm_apply_apply _ _
  let patch := PatchTable.incidence (gates hs) (i,j)
  have hentry : p.1 = (gate.replayEntry x (witnessPatchNumber hs root patch) (patchAnchor hs patch)).relabel
      (compactIndex T) (witnessRuleNumber hs root) := by
    simp only [p,sliceRecord,witnessEntry,he,gate,patch]
  have hdata : p.2 = gate.completed.relabel (compactIndex T) (witnessRuleNumber hs root) := by
    simp only [p,sliceRecord,witnessLifts,he,lifts,gate]
  have fields := prepareBubble_entry_fields pad x (completed (hs.take i.val)) w origin (patchAnchor hs patch)
    ((completed (hs.take i.val)).size+j.val) (hs.take i.val).length (witnessPatchNumber hs root patch)
    (left_pos P w) (right_pos P w) (hprep j).1 hn
  obtain ⟨hleft,hright,hremoved,hins⟩ :
      p.1.left = w.left.length ∧ p.1.right = w.right.length ∧
      p.1.removed = w.removed ∧ p.1.replacement = w.replacement := by rw [hentry]; exact fields
  have hnegative : List.ofFn (p.2.negative.2.spelling x) = w.negativeWord := by
    refine (congrArg (fun e : Completed ℓ (Fin q) => List.ofFn (e.negative.2.spelling x)) hdata).trans ?_
    change List.ofFn ((gate.gate.negative.renameEntries _).spelling x) = _
    rw [Lift.spelling_renameEntries]
    exact hn
  have hpositive : List.ofFn (p.2.positive.2.spelling x) = w.positiveWord := by
    refine (congrArg (fun e : Completed ℓ (Fin q) => List.ofFn (e.positive.2.spelling x)) hdata).trans ?_
    change List.ofFn ((gate.gate.positive.renameEntries _).spelling x) = _
    rw [Lift.spelling_renameEntries]
    exact hp
  have hfresh : p.2.negative.2.freshOffsets.card ≤ Λ := by
    have he' := congrArg (fun e : Completed ℓ (Fin q) => e.negative.2.freshOffsets.card) hdata
    rw [he']
    change (gate.gate.negative.renameEntries _).freshOffsets.card ≤ _
    rw [Lift.freshOffsets_renameEntries]
    exact hspec.fresh.trans ((Nat.le_add_right _ b).trans P.counts)
  have hmember := member_of_replay_spelling pad p x w (member_catalogue words hcat j)
    hleft hright hremoved hins hnegative hfresh
  have hvec : vector pad w = vectorOf L pad p x := by
    rw [slice_vector]
    funext col
    have he' := hspec.vector_eq (pad := pad) (finFunctionFinEquiv.symm col)
    simpa [w,witnessLifts,lifts,he] using he'.symm
  refine ⟨hmember,hvec,?_⟩
  intro f g
  change (if p.2.negative.2.freshOffsets.card ≤ Λ then
    (do
      let m ← localWord K b L p.1.left p.1.removed p.1.replacement (List.ofFn (p.2.negative.2.spelling x))
      if m.positiveWord = List.ofFn (p.2.positive.2.spelling x) then some m else none)
    else none) = some w
  rw [if_pos hfresh,hleft,hremoved,hins,hnegative,hpositive,CatalogueEnumeration.localWord_roundtrip]
  simp


theorem sliceRecord_active_lower
    {P : Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q} {origin : Fin ℓ}
    {hs : History ℓ q L s} (h : RecordedBatches P pad x origin hs)
    (hf : LiftsFit (gates hs) (lifts hs) Λ)
    (root : RuleVertex hs) (T : Finset (Fin (hs.length*s))) (j : Fin (hs.length*s)) :
    L-Λ ≤ (active (sliceRecord hs root x T j).2.negative.2).card := by
  let e := finProdFinEquiv.symm j
  let p := sliceRecord hs root x T j
  let : Inhabited (Fin q) := ⟨pad⟩
  obtain ⟨words,hwords,_,_,hw⟩ := (h.batch_at e.1).fromCatalogue
  have hpos : 0 < L := by have h := P.window; omega
  have hcat := (CatalogueEnumeration.mem_rules_iff pad hpos words).mp hwords
  have hlen : L ≤ (words e.2).negativeWord.length := hcat.length_lower e.2 false
  have hnegative := congrArg List.length (hw e.2).2.spelling
  have hp : L ≤ p.2.negative.1 := by
    change L ≤ ((hs.get e.1).bubbles e.2).left + ((hs.get e.1).bubbles e.2).removed +
      ((hs.get e.1).bubbles e.2).right
    simp only [List.length_ofFn] at hnegative
    omega
  have hf' : p.2.negative.2.freshOffsets.card ≤ Λ := by
    change ((witnessLifts hs j).negative.2.renameEntries _).freshOffsets.card ≤ Λ
    rw [Lift.freshOffsets_renameEntries]
    exact (hf e Side.negative).2.1
  have hsize : (replayShape p).fresh.length = p.2.negative.1 := by
    simp [replayShape,shapeOf]
  have hc : (active p.2.negative.2).card + p.2.negative.2.freshOffsets.card = p.2.negative.1 := by
    calc
      _ = (replayShape p).originalCount + (replayShape p).freshCount :=
        congrArg₂ (· + ·) (replayShape_card pad p).symm (replayShape_freshCount pad p).symm
      _ = (replayShape p).fresh.length := shapeCounts_add _
      _ = _ := hsize
  change L-Λ ≤ (active p.2.negative.2).card
  omega

private theorem shapeOf_rename {m : ℕ} (a r : ℕ) (u v : QWord q)
    (p : Lift ℓ m (Fin q)) (f : ℕ → ℕ) :
    shapeOf a r u v (p.renameEntries f) = shapeOf a r u v p := by
  unfold shapeOf
  congr 1
  simp only [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply,Lift.renameEntries_letter]
  cases p.letters i <;> rfl

theorem sliceRecord_shape (hs : History ℓ q L s) (root : RuleVertex hs) (x : Fin ℓ → Fin q)
    (T U : Finset (Fin (hs.length*s))) (j : Fin (hs.length*s)) :
    replayShape (sliceRecord hs root x T j) = replayShape (sliceRecord hs root x U j) := by
  change shapeOf _ _ _ _ ((witnessLifts hs j).negative.2.renameEntries (compactIndex T)) =
    shapeOf _ _ _ _ ((witnessLifts hs j).negative.2.renameEntries (compactIndex U))
  rw [shapeOf_rename,shapeOf_rename]
  rfl

#print axioms sliceRecord_shape
#print axioms sliceRecord_active_lower
#print axioms slice_rule_families

end DeletionCode.Explicit.Recognizer
