import DeletionCode.Explicit.ReplayEntry
import DeletionCode.Explicit.FieldPath
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Basic

/-! Dictionary lifts for exposed negative grams (`d:add-rule` and
`d:selected-replay`). -/

namespace DeletionCode.Explicit.LiftDictionary

open LetterSequence ReplayEntry Qary.SignedSupport
open scoped BigOperators

variable {ℓ L : ℕ} {α : Type*}

/-- Source starts remain absolute until the consumer's patch anchor is known. -/
inductive Location where
  | source (start : ℕ)
  | supplier (entry : ℕ) (side : Side) (offset : ℕ)
  deriving DecidableEq

structure Occurrence (ℓ L : ℕ) (α : Type*) where
  location : Location
  lift : Lift ℓ L α

private def sourceOccurrences (ℓ L : ℕ) : List (Occurrence ℓ L α) :=
  (List.finRange (ℓ+1)).filterMap fun i =>
    if h : i.val+L ≤ ℓ then some ⟨.source i.val, sourceWindow i.val L h⟩ else none

private def liftOccurrences (j : ℕ) (side : Side) (L : ℕ) (u : StoredLift ℓ α) :
    List (Occurrence ℓ L α) :=
  (List.finRange (u.1+1)).filterMap fun i =>
    if h : i.val+L ≤ u.1 then some ⟨.supplier j side i.val,u.2.window i.val L h⟩ else none

/-- Source windows are first. The array is ordered by rule and then by bubble.
For each bubble the negative side precedes the positive side. Valid offsets
within each side are scanned in increasing order. -/
def occurrences (history : Array (Completed ℓ α)) (L : ℕ) : List (Occurrence ℓ L α) :=
  sourceOccurrences ℓ L ++ (List.finRange history.size).flatMap fun j =>
    liftOccurrences j.val .negative L (history[j]).negative ++
    liftOccurrences j.val .positive L (history[j]).positive

def lookup [DecidableEq α] (x : Fin ℓ → α) (history : Array (Completed ℓ α))
    (g : Gram α L) : Option (Occurrence ℓ L α) :=
  (occurrences history L).find? (fun occ => decide (occ.lift.spelling x = g))

private theorem source_mem (history : Array (Completed ℓ α)) (a : ℕ) (h : a+L ≤ ℓ) :
    (⟨.source a,sourceWindow a L h⟩ : Occurrence ℓ L α) ∈ occurrences history L := by
  apply List.mem_append_left
  apply List.mem_filterMap.mpr
  exact ⟨⟨a,by omega⟩,by simp,by simp only [dite_eq_left h,Completed.lift]⟩

private theorem supplier_mem (history : Array (Completed ℓ α)) (j : Fin history.size) (side : Side)
    (a : ℕ) (h : a+L ≤ (history[j].lift side).1) :
    (⟨.supplier j.val side a,(history[j].lift side).2.window a L h⟩ : Occurrence ℓ L α)
      ∈ occurrences history L := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨j,by simp,?_⟩
  cases side with
  | negative =>
    change a+L ≤ history[j].negative.1 at h
    apply List.mem_append_left
    apply List.mem_filterMap.mpr
    exact ⟨⟨a,by change a < history[j].negative.1+1; change a+L ≤ history[j].negative.1 at h; omega⟩,
      by simp,by simp only [dite_eq_left h,Completed.lift]⟩
  | positive =>
    change a+L ≤ history[j].positive.1 at h
    apply List.mem_append_right
    apply List.mem_filterMap.mpr
    exact ⟨⟨a,by change a < history[j].positive.1+1; change a+L ≤ history[j].positive.1 at h; omega⟩,
      by simp,by simp only [dite_eq_left h,Completed.lift]⟩

theorem lookup_none_iff [DecidableEq α] (x : Fin ℓ → α) (history : Array (Completed ℓ α)) (g : Gram α L) :
    lookup x history g = none ↔ ∀ o ∈ occurrences history L, o.lift.spelling x ≠ g := by
  simp [lookup,List.find?_eq_none]

theorem lookup_spelling [DecidableEq α] {x : Fin ℓ → α} {history : Array (Completed ℓ α)}
    {g : Gram α L} {o : Occurrence ℓ L α} (h : lookup x history g = some o) :
    o.lift.spelling x = g := by
  unfold lookup at h
  exact of_decide_eq_true (List.find?_some (p := fun a : Occurrence ℓ L α =>
    decide (a.lift.spelling x = g)) h)

def paddedLetters {n : ℕ} (pad : α) (x : Fin n → α) : ℕ → α :=
  fun i => if h : i < n then x ⟨i,h⟩ else pad

private theorem source_gram (pad : α) (x : Fin ℓ → α) (a : ℕ) (h : a+L ≤ ℓ) :
    gram (paddedLetters pad x) L a = (sourceWindow a L h).spelling x := by
  funext i
  have hi : a+i.val < ℓ := by omega
  simp [gram,paddedLetters,hi]

theorem lift_gram (pad : α) (x : Fin ℓ → α) (u : StoredLift ℓ α) (a : ℕ)
    (h : a+L ≤ u.1) :
    gram (paddedLetters pad (u.2.spelling x)) L a = (u.2.window a L h).spelling x := by
  funext i
  have hi : a+i.val < u.1 := by omega
  simp [gram,paddedLetters,hi,Lift.window,Lift.spelling]

theorem fieldSpectrum_zero [DecidableEq α] (w : ℕ → α) (n : ℕ) (g : Gram α L)
    (h : ∀ a : Fin (n+1), a.val+L ≤ n → gram w L a.val ≠ g) :
    fieldSpectrum w n L g = 0 := by
  unfold fieldSpectrum
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a.val+L ≤ n
  · simp [ha,h a ha]
  · simp [ha]

/-- The vector of a lifted bubble is the difference of its two spellings'
spectra. All terms use the same global gram coordinates. -/
def bubbleVector [DecidableEq α] (pad : α) (x : Fin ℓ → α) (e : Completed ℓ α) : Gram α L → ZMod 3 :=
  fieldSpectrum (paddedLetters pad (e.positive.2.spelling x)) e.positive.1 L -
    fieldSpectrum (paddedLetters pad (e.negative.2.spelling x)) e.negative.1 L

/-- The rule's bubbles are exactly the supplied entries carrying its label. -/
def liftedRule [DecidableEq α] (pad : α) (x : Fin ℓ → α) (history : Array (Completed ℓ α))
    (r : ℕ) : Gram α L → ZMod 3 :=
  fun g => ∑ j : Fin history.size, if history[j].rule = r then bubbleVector pad x history[j] g else 0

/-- The zero-one fibre condition used in `d:exposed`. -/
def IsZeroOne (u : Gram α L → ZMod 3) : Prop := ∀ g, u g = 0 ∨ u g = 1

def Exposed (v : Gram α L → ZMod 3) (W : Submodule (ZMod 3) (Gram α L → ZMod 3))
    (ρ : Gram α L → ZMod 3) : Prop :=
  ∃ w ∈ W, IsZeroOne (v+w) ∧ IsZeroOne (v+w+ρ)

private theorem exposed_negative {v ρ : Gram α L → ZMod 3}
    {W : Submodule (ZMod 3) (Gram α L → ZMod 3)} (h : Exposed v W ρ)
    {g : Gram α L} (hg : ρ g = -1) : ∃ w ∈ W, v g + w g = 1 := by
  obtain ⟨w,hw,hu,ht⟩ := h
  refine ⟨w,hw,?_⟩
  rcases hu g with h0 | h1
  · have hc := ht g
    change (v+w) g + ρ g = 0 ∨ (v+w) g + ρ g = 1 at hc
    rw [h0,hg,zero_add] at hc
    exact ((by decide : ¬ ((-1 : ZMod 3) = 0 ∨ (-1 : ZMod 3) = 1)) hc).elim
  · exact h1

/-- Every negative gram of an exposed rule has a dictionary lift. The fibre
witness need only be a zero-one vector, as in the manuscript. -/
theorem lookup_of_exposed_negative [DecidableEq α] (pad : α) (x : Fin ℓ → α)
    (history : Array (Completed ℓ α)) {ρ : Gram α L → ZMod 3} {g : Gram α L}
    (h : Exposed (fieldSpectrum (paddedLetters pad x) ℓ L)
      (Submodule.span (ZMod 3) (Set.range (liftedRule pad x history))) ρ)
    (hg : ρ g = -1) :
    ∃ o, lookup x history g = some o ∧ o.lift.spelling x = g := by
  cases hl : lookup x history g with
  | some o => exact ⟨o,rfl,lookup_spelling hl⟩
  | none =>
    exfalso
    have miss := (lookup_none_iff x history g).mp hl
    have hsrc : fieldSpectrum (paddedLetters pad x) ℓ L g = 0 := by
      apply fieldSpectrum_zero
      intro a ha
      rw [source_gram pad x a.val ha]
      exact miss _ (source_mem history a.val ha)
    have hold (j : Fin history.size) (side : Side) :
        fieldSpectrum (paddedLetters pad ((history[j].lift side).2.spelling x))
          (history[j].lift side).1 L g = 0 := by
      apply fieldSpectrum_zero
      intro a ha
      rw [lift_gram pad x (history[j].lift side) a.val ha]
      exact miss _ (supplier_mem history j side a.val ha)
    have hsum (r : ℕ) : liftedRule pad x history r g = 0 := by
      unfold liftedRule
      apply Finset.sum_eq_zero
      intro i _
      by_cases hr : history[i].rule = r
      · simp only [ite_eq_left hr,bubbleVector,Pi.sub_apply]
        have hp := hold i .positive
        have hn := hold i .negative
        simp only [Completed.lift] at hp hn
        rw [hp,hn,sub_self]
      · exact ite_eq_right hr
    let ev : (Gram α L → ZMod 3) →ₗ[ZMod 3] ZMod 3 := LinearMap.proj g
    have hspan : Submodule.span (ZMod 3) (Set.range (liftedRule pad x history)) ≤ LinearMap.ker ev :=
      Submodule.span_le.mpr (by rintro _ ⟨r,rfl⟩; exact LinearMap.mem_ker.mpr (hsum r))
    obtain ⟨w,hw,h1⟩ := exposed_negative h hg
    have hw0 : w g = 0 := LinearMap.mem_ker.mp (hspan hw)
    rw [hsrc,hw0,add_zero] at h1
    exact (by decide : (0 : ZMod 3) ≠ 1) h1

#print axioms lookup_spelling
#print axioms lookup_of_exposed_negative

/-- Convert an occurrence to the replay format without changing suppliers.
Only the source starts need to be made relative to the consumer's anchor. -/
def Location.reference (root : Fin ℓ) : Location → Reference
  | .source a => .source ((a : ℤ)-(root.val : ℤ))
  | .supplier j side a => .supplier j side a

private theorem source_occurrence_readable (history : Array (Completed ℓ α))
    (current rule : ℕ) (root : Fin ℓ) {o : Occurrence ℓ L α}
    (hm : o ∈ sourceOccurrences ℓ L) :
    readReference L current rule (some root) (fun j => history[j]?) (o.location.reference root) =
      some o.lift := by
  rw [sourceOccurrences,List.mem_filterMap] at hm
  obtain ⟨a,_,hm⟩ := hm
  split at hm
  next ha =>
    have eq := Option.some.inj hm
    subst o
    exact read_encoded_source L current rule a.val root (fun j => history[j]?) ha
  next => contradiction

private theorem supplier_occurrence_readable (history : Array (Completed ℓ α))
    (current rule : ℕ) (root : Fin ℓ) (j : Fin history.size) (side : Side)
    {o : Occurrence ℓ L α} (hj : j.val < current) (hr : history[j].rule < rule)
    (hm : o ∈ liftOccurrences j.val side L (history[j].lift side)) :
    readReference L current rule (some root) (fun j => history[j]?) (o.location.reference root) =
      some o.lift := by
  rw [liftOccurrences,List.mem_filterMap] at hm
  obtain ⟨a,_,hm⟩ := hm
  split at hm
  next ha =>
    have eq := Option.some.inj hm
    subst o
    exact read_supplier L current rule (some root) (fun j => history[j]?) hj
      (Array.getElem?_eq_getElem j.isLt) hr ha
  next => contradiction

/-- When the dictionary is frozen before the new rule, each returned window
can be read back verbatim by the replay decoder. -/
theorem lookup_reference [DecidableEq α] {x : Fin ℓ → α} {history : Array (Completed ℓ α)}
    {g : Gram α L} {o : Occurrence ℓ L α} (h : lookup x history g = some o)
    (root : Fin ℓ) {current rule : ℕ} (hc : history.size ≤ current)
    (hr : ∀ j : Fin history.size, history[j].rule < rule) :
    readReference L current rule (some root) (fun j => history[j]?) (o.location.reference root) =
      some o.lift := by
  have hm : o ∈ occurrences history L := List.mem_of_find?_eq_some h
  rw [occurrences,List.mem_append] at hm
  rcases hm with hs | he
  · exact source_occurrence_readable history current rule root hs
  · obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp he
    rcases List.mem_append.mp hj with hn | hp
    · exact supplier_occurrence_readable history current rule root j .negative
        (j.isLt.trans_le hc) (hr j) hn
    · exact supplier_occurrence_readable history current rule root j .positive
        (j.isLt.trans_le hc) (hr j) hp

/-- The dictionary can return replayable records for all selected windows of
an exposed negative local word. The disjoint catalogue paths supply the
hypothesis that each of these grams has coefficient `-1`. -/
theorem selected_windows_readable [DecidableEq α] (pad : α) (x : Fin ℓ → α)
    (history : Array (Completed ℓ α)) {ρ : Gram α L → ZMod 3}
    (h : Exposed (fieldSpectrum (paddedLetters pad x) ℓ L)
      (Submodule.span (ZMod 3) (Set.range (liftedRule pad x history))) ρ)
    {n : ℕ} (word : Fin n → α) (hn : L ≤ n)
    (hneg : ∀ a, a+L ≤ n → ρ (gram (paddedLetters pad word) L a) = -1)
    (root : Fin ℓ) {current rule : ℕ} (hc : history.size ≤ current)
    (hr : ∀ j : Fin history.size, history[j].rule < rule)
    {a : ℕ} (ha : a ∈ selectedStarts L n) :
    ∃ o, lookup x history (gram (paddedLetters pad word) L a) = some o ∧
      o.lift.spelling x = gram (paddedLetters pad word) L a ∧
      Reads L current rule (some root) (fun j => history[j]?) (o.location.reference root) o.lift := by
  have hbound : a+L ≤ n := by
    rcases selectedStarts_mem.mp ha with hzero | hmid | hlast <;> omega
  obtain ⟨o,ho,hm⟩ := lookup_of_exposed_negative pad x history h (hneg a hbound)
  exact ⟨o,ho,hm,reads_of_read (lookup_reference ho root hc hr)⟩

#print axioms lookup_reference
#print axioms selected_windows_readable

/-- Resolve the entire selected-window list in its prescribed order. Each
occurrence keeps an absolute location until the patch anchor is known. -/
def select [DecidableEq α] (pad : α) (x : Fin ℓ → α) (history : Array (Completed ℓ α))
    (L : ℕ) {n : ℕ} (word : Fin n → α) : Option (List (Occurrence ℓ L α)) :=
  (selectedStarts L n).mapM fun a => lookup x history (gram (paddedLetters pad word) L a)

private theorem mapM_spec {A B : Type*} (f : A → Option B) (P : A → B → Prop) (xs : List A)
    (h : ∀ a ∈ xs, ∃ b, f a = some b ∧ P a b) :
    ∃ ys, xs.mapM f = some ys ∧ List.Forall₂ P xs ys := by
  induction xs with
  | nil => exact ⟨[],rfl,List.Forall₂.nil⟩
  | cons a as ih =>
    obtain ⟨b,hb,hp⟩ := h a (List.mem_cons_self ..)
    obtain ⟨ys,hr,hs⟩ := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    exact ⟨b::ys,by simp [hb,hr],List.Forall₂.cons hp hs⟩

/-- All selected windows of an exposed negative local word are returned in
order, with the required spelling and a reference replay can read. -/
theorem select_spec [DecidableEq α] (pad : α) (x : Fin ℓ → α)
    (history : Array (Completed ℓ α)) {ρ : Gram α L → ZMod 3}
    (h : Exposed (fieldSpectrum (paddedLetters pad x) ℓ L)
      (Submodule.span (ZMod 3) (Set.range (liftedRule pad x history))) ρ)
    {n : ℕ} (word : Fin n → α) (hn : L ≤ n)
    (hneg : ∀ a, a+L ≤ n → ρ (gram (paddedLetters pad word) L a) = -1)
    (root : Fin ℓ) {current rule : ℕ} (hc : history.size ≤ current)
    (hr : ∀ j : Fin history.size, history[j].rule < rule) :
    ∃ os, select pad x history L word = some os ∧
      List.Forall₂ (fun a (o : Occurrence ℓ L α) =>
        o.lift.spelling x = gram (paddedLetters pad word) L a ∧
        Reads L current rule (some root) (fun j => history[j]?) (o.location.reference root) o.lift)
        (selectedStarts L n) os := by
  unfold select
  apply mapM_spec
  intro a ha
  exact selected_windows_readable pad x history h word hn hneg root hc hr ha

theorem select_lookup_at [DecidableEq α] (pad : α) (x : Fin ℓ → α)
    (history : Array (Completed ℓ α)) (L : ℕ) {n : ℕ} (word : Fin n → α)
    {os : List (Occurrence ℓ L α)} (h : select pad x history L word = some os) :
    List.Forall₂ (fun a o => lookup x history (gram (paddedLetters pad word) L a) = some o)
      (selectedStarts L n) os := by
  unfold select at h
  generalize selectedStarts L n = starts at h ⊢
  induction starts generalizing os with
  | nil =>
    simp at h
    subst os
    exact .nil
  | cons a rest ih =>
    cases hfirst : lookup x history (gram (paddedLetters pad word) L a) with
    | none => simp [List.mapM_cons,hfirst] at h
    | some o =>
      cases hrest : rest.mapM (fun a => lookup x history (gram (paddedLetters pad word) L a)) with
      | none => simp [List.mapM_cons,hfirst,hrest] at h
      | some tail =>
        simp [List.mapM_cons,hfirst,hrest] at h
        subst os
        exact .cons hfirst (ih hrest)

#print axioms select_spec

end DeletionCode.Explicit.LiftDictionary
