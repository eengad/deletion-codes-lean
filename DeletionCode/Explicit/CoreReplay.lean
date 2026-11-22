import DeletionCode.Explicit.ReplayGrammar
import DeletionCode.Explicit.RulePatchCore
import DeletionCode.Explicit.LiftDictionary

/-! The symbolic part of the replay slot used in the core-weight catalogue. -/

namespace DeletionCode.Explicit.CoreWeight

open ReplayGrammar ReplayEntry LetterSequence RulePatch LiftDictionary FieldHash

variable {ℓ q E L b t r₀ : ℕ}

abbrev ReplaySlot (ℓ q E L b t r₀ : ℕ) :=
  Slot ℓ t r₀ (descriptionBound E L b q)

def patchKeys (E : ℕ) (ds : List (DecodedEntry q)) : Finset (Fin E) :=
  Finset.univ.filter (fun p => ds.any (fun d => d.entry.patch == p.val))

def finalRuleKeys (E : ℕ) (ds : List (DecodedEntry q)) : Finset (Fin E) :=
  Finset.univ.filter (fun r => ds.any (fun d => d.finalRule && d.entry.rule == r.val))

/-- The replayed description, with the chronological lifts and the ordered
indices of its final rules. -/
structure Materialized (ℓ q E r : ℕ) where
  entries : List (DecodedEntry q × Completed ℓ (Fin q))
  rules : Finset (Fin E)
  rule_count : rules.card = r

private def belongs (r : ℕ) (d : DecodedEntry q) : Bool :=
  d.finalBubble && d.entry.rule == r

private def finalEntries {r : ℕ} (m : Materialized ℓ q E r) :
    List (DecodedEntry q × Completed ℓ (Fin q)) :=
  m.entries.filter (fun p => p.1.finalBubble)

private def boundsChecked (s : ℕ) (ds : List (DecodedEntry q)) (keys : Finset (Fin E)) : Bool :=
  let counts := (keys.sort (· ≤ ·)).all fun r =>
    decide ((ds.filter (belongs r.val)).length = s)
  counts && ds.all (fun d => !d.finalBubble ||
    ((keys.sort (· ≤ ·)).any (fun r => d.entry.rule == r.val)))

/-- Read a root only for patch keys present in the description. -/
def anchorLookup (patches : Finset (Fin E)) (roots : ↥patches → Fin ℓ) (i : ℕ) :
    Option (Fin ℓ) :=
  if hi : i < E then
    if hp : (⟨i,hi⟩ : Fin E) ∈ patches then some (roots ⟨⟨i,hi⟩,hp⟩) else none
  else none

/-- The slot's description decides which patches use anchors. Anchors are
read in patch order, with unused suffix codes rejected by `unpackAnchors`. -/
def materialize (k : ReplaySlot ℓ q E L b t r₀) :
    Option (Materialized ℓ q E (k.1.val+1)) := do
  let c ← unpackDescription k.2.1
  let ds ← decodeDescription c
  let keys := finalRuleKeys E ds
  if hr : keys.card = k.1.val+1 then
    if boundsChecked (2*t) ds keys then
      let patches := patchKeys E ds
      if patches.card ≤ t*(k.1.val+1) then
        let roots ← unpackAnchors patches k.2.2
        let lifts ← replay L (anchorLookup patches roots) (ds.map DecodedEntry.entry)
        some ⟨ds.zip lifts.toList,keys,hr⟩
      else none
    else none
  else none

private theorem boundsChecked_of_counts (s : ℕ) (ds : List (DecodedEntry q))
    (keys : Finset (Fin E))
    (hcount : ∀ id ∈ keys, (ds.filter (belongs id.val)).length = s)
    (hkeys : ∀ d ∈ ds, d.finalBubble = true → ∃ id ∈ keys, d.entry.rule = id.val) :
    boundsChecked s ds keys = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro id hi
    exact decide_eq_true (hcount id (by simpa using hi))
  · apply List.all_eq_true.mpr
    intro d hd
    by_cases hf : d.finalBubble = true
    · obtain ⟨id,hi,he⟩ := hkeys d hd hf
      have hsome : ((keys.sort (· ≤ ·)).any (fun r => d.entry.rule == r.val)) = true :=
        List.any_eq_true.mpr ⟨id,by simpa using hi,beq_iff_eq.mpr he⟩
      simp [hsome]
    · simp [hf]

/-- A bounded, valid description with at most `t*r` distinct anchors occurs
at a concrete slot of the core enumerator, with the same output array. -/
theorem materialize_of_encoding (pad : Fin q) (ds : List (DecodedEntry q)) (i : Fin r₀)
    (hℓ : 0 < ℓ) (hb : b ≤ L) (hlen : ds.length ≤ E)
    (hfits : ∀ d ∈ ds, EntryFits E L b d.entry)
    (hr : (finalRuleKeys E ds).card = i.val+1)
    (hcount : ∀ id ∈ finalRuleKeys E ds, (ds.filter (belongs id.val)).length = 2*t)
    (hkeys : ∀ d ∈ ds, d.finalBubble = true → ∃ id ∈ finalRuleKeys E ds, d.entry.rule = id.val)
    (hp : (patchKeys E ds).card ≤ t*(i.val+1))
    (roots : ↥(patchKeys E ds) → Fin ℓ) (out : Array (Completed ℓ (Fin q)))
    (heval : replay L (anchorLookup (patchKeys E ds) roots) (ds.map DecodedEntry.entry) = some out) :
    ∃ c, encodeDescription E L b q pad ds = some c ∧
      materialize (⟨i,packDescription c,packAnchors hℓ (patchKeys E ds) hp roots⟩
        : ReplaySlot ℓ q E L b t r₀) =
        some ⟨ds.zip out.toList,finalRuleKeys E ds,hr⟩ := by
  obtain ⟨c,hc,hd⟩ := encodeDescription_roundtrip pad ds hb hlen hfits
  refine ⟨c,hc,?_⟩
  simp [materialize,unpack_packDescription,hd,hr,boundsChecked_of_counts _ _ _ hcount hkeys,
    hp,unpack_packAnchors,heval]

#print axioms materialize_of_encoding

/-- The source coordinates of one symbolic lift, also used for a positive
lift so every letter can be read even before its provenance is certified. -/
private def originalPositions (w : StoredLift ℓ (Fin q)) : Finset (Fin ℓ) :=
  Finset.univ.filter (fun p => p.val ∈ w.2.positions)

def Materialized.support {r : ℕ} (m : Materialized ℓ q E r) : Finset (Fin ℓ) :=
  Finset.univ.filter (fun i => (finalEntries m).any (fun p =>
    decide (i ∈ originalPositions p.2.negative ∪ originalPositions p.2.positive)))

/-- The rows of the final rules in increasing rule-index order. -/
def Materialized.matrix {r : ℕ} (m : Materialized ℓ q E r) (L : ℕ)
    (pad : Fin q) (word : Fin ℓ → Fin q) : TernaryMatrix r (q^L) :=
  fun i col =>
    let id := (m.rules.orderEmbOfFin m.rule_count i).val
    let g := finFunctionFinEquiv.symm col
    ((m.entries.filter (fun p => belongs id p.1)).map
      (fun p => bubbleVector (L := L) pad word p.2 g)).sum

theorem Materialized.mem_support {r : ℕ} (m : Materialized ℓ q E r) {i : Fin ℓ} :
    i ∈ m.support ↔ ∃ p ∈ m.entries, p.1.finalBubble = true ∧
      (i.val ∈ p.2.negative.2.positions ∨ i.val ∈ p.2.positive.2.positions) := by
  constructor
  · intro hi
    have h := (Finset.mem_filter.mp hi).2
    obtain ⟨p,hp,hi'⟩ := List.any_eq_true.mp h
    obtain ⟨hp',hf⟩ := List.mem_filter.mp hp
    exact ⟨p,hp',hf,by simpa [originalPositions] using hi'⟩
  · rintro ⟨p,hp,hf,hi⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      List.any_eq_true.mpr ⟨p,List.mem_filter.mpr ⟨hp,hf⟩,by simpa [originalPositions] using hi⟩⟩

theorem lift_spelling_congr {m : ℕ} (w : Lift ℓ m (Fin q)) {x y : Fin ℓ → Fin q}
    (h : ∀ i : Fin ℓ, i.val ∈ w.positions → x i = y i) : w.spelling x = w.spelling y := by
  funext j
  cases hj : w.letters j with
  | original i =>
    have hi : i.val ∈ w.positions := w.mem_positions.mpr ⟨j,i,by rw [hj]; rfl,rfl⟩
    simpa [Lift.spelling,hj,Letter.symbol] using h i hi
  | fresh id off sym => simp [Lift.spelling,hj,Letter.symbol]

theorem Materialized.final_spelling_congr {r : ℕ} (m : Materialized ℓ q E r)
    {x y : Fin ℓ → Fin q} (h : ∀ i ∈ m.support, x i = y i)
    {p : DecodedEntry q × Completed ℓ (Fin q)} (hm : p ∈ m.entries) (hf : p.1.finalBubble = true) :
    p.2.negative.2.spelling x = p.2.negative.2.spelling y ∧
      p.2.positive.2.spelling x = p.2.positive.2.spelling y :=
  ⟨lift_spelling_congr p.2.negative.2 (fun a ha => h a (m.mem_support.mpr ⟨p,hm,hf,Or.inl ha⟩)),
    lift_spelling_congr p.2.positive.2 (fun a ha => h a (m.mem_support.mpr ⟨p,hm,hf,Or.inr ha⟩))⟩

/-- Every row of the reconstructed matrix uses only the declared active
coordinates. Supplier data is symbolic and adds no further coordinates. -/
theorem Materialized.matrix_congr {r : ℕ} (m : Materialized ℓ q E r) (L : ℕ)
    (pad : Fin q) {x y : Fin ℓ → Fin q} (h : ∀ i ∈ m.support, x i = y i) :
    m.matrix L pad x = m.matrix L pad y := by
  funext i j
  unfold Materialized.matrix
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  obtain ⟨hm,hp⟩ := List.mem_filter.mp hp
  have hf : p.1.finalBubble = true := (Bool.and_eq_true_iff.mp hp).1
  obtain ⟨hn,hpos⟩ := m.final_spelling_congr h hm hf
  unfold bubbleVector
  rw [hn,hpos]

def slotSupport (k : ReplaySlot ℓ q E L b t r₀) : Finset (Fin ℓ) :=
  ((materialize k).map Materialized.support).getD ∅

/-- Complete the active assignment with the padding symbol outside its support. -/
def slotWord (pad : Fin q) (k : ReplaySlot ℓ q E L b t r₀)
    (letter : ↥(slotSupport k) → Fin q) : Fin ℓ → Fin q :=
  fun i => if h : i ∈ slotSupport k then letter ⟨i,h⟩ else pad

/-- Build the abstract core-weight evaluator from compact replay. The
caller supplies the remaining candidate checks on the recovered rows
and words. Every demanded symbol at an active position comes from the
enumerated assignment. -/
def checkedReplayData (pad : Fin q)
    (accept : {r : ℕ} → Materialized ℓ q E r → (Fin ℓ → Fin q) → Bool) :
    ReplayData ℓ q (q^L) t r₀ (descriptionBound E L b q) where
  support := slotSupport
  rules k letter := do
    let m ← materialize k
    let word := slotWord pad k letter
    if accept m word then some (m.matrix L pad word) else none

theorem rules_of_materialized (pad : Fin q)
    (accept : {r : ℕ} → Materialized ℓ q E r → (Fin ℓ → Fin q) → Bool)
    (k : ReplaySlot ℓ q E L b t r₀) (x : Fin ℓ → Fin q)
    {m : Materialized ℓ q E (k.1.val+1)} (h : materialize k = some m)
    (ha : accept m (slotWord pad k (fun i => x i.val)) = true) :
    (checkedReplayData pad accept).rules k (fun i => x i.val) = some (m.matrix L pad x) := by
  have hs : slotSupport k = m.support := by simp [slotSupport,h]
  have he : m.matrix L pad (slotWord pad k (fun i => x i.val)) = m.matrix L pad x := by
    apply m.matrix_congr
    intro i hi
    rw [← hs] at hi
    simp [slotWord,hi]
  simp [checkedReplayData,h,ha,he]

#print axioms Materialized.matrix_congr
#print axioms rules_of_materialized

end DeletionCode.Explicit.CoreWeight
