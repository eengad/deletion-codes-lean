import DeletionCode.Explicit.FamilyEnumeration
import DeletionCode.Qary.BubbleCatalogue

/-! The deterministic finite catalogue scanned by recognition and colouring. -/

namespace DeletionCode.Explicit.CatalogueEnumeration

open Borrowed BubbleFamilies FieldHash

variable {q K b L s : ℕ}

theorem localWord_roundtrip (w : BubbleWord (Fin q) K b L) :
    localWord K b L w.left.length w.removed w.replacement w.negativeWord = some w := by
  have hl : w.negativeWord.take w.left.length = w.left := by
    simp [BubbleWord.negativeWord,List.append_assoc]
  have hr : w.negativeWord.drop (w.left.length+w.removed.length) = w.right := by
    have he : w.left.length+w.removed.length = (w.left++w.removed).length := by simp
    rw [he]
    simp [BubbleWord.negativeWord]
  unfold localWord
  simp only [hl,hr]
  have h : w.removed.length ≤ b ∧ w.replacement.length ≤ b ∧ w.removed ≠ w.replacement ∧
      L-1-K-b ≤ w.left.length ∧ w.left.length ≤ L-1 ∧
      L-1-K-b ≤ w.right.length ∧ w.right.length ≤ L-1 :=
    ⟨w.removed_bound,w.replacement_bound,w.different,w.left_lower,w.left_upper,w.right_lower,w.right_upper⟩
  rw [dite_eq_left h]
  simp

def localWords (q K b L : ℕ) : List (BubbleWord (Fin q) K b L) :=
  (allShapes q L b 0).flatMap fun shape =>
    (wordsOfLength q shape.left).flatMap fun a =>
      (wordsOfLength q shape.right).filterMap fun r =>
        localWord K b L shape.left shape.removed shape.replacement (a++shape.removed++r)

theorem mem_localWords (w : BubbleWord (Fin q) K b L) (hL : 0 < L) :
    w ∈ localWords q K b L := by
  let shape : Shape q := ⟨w.left.length,w.right.length,w.removed,w.replacement,
    List.replicate w.negativeWord.length none⟩
  have hshape : shape ∈ allShapes q L b 0 := mem_allShapes shape
    (by dsimp [shape]; have h := w.left_upper; omega)
    (by dsimp [shape]; have h := w.right_upper; omega)
    w.removed_bound w.replacement_bound (by simp [shape,BubbleWord.negativeWord,Nat.add_assoc])
    (by simp [shape,Shape.freshCount])
  exact List.mem_flatMap.mpr ⟨shape,hshape,List.mem_flatMap.mpr
    ⟨w.left,mem_wordsOfLength.mpr rfl,List.mem_filterMap.mpr
      ⟨w.right,mem_wordsOfLength.mpr rfl,localWord_roundtrip w⟩⟩⟩

private def tuples {A : Type*} (alphabet : List A) : ℕ → List (List A)
  | 0 => [[]]
  | n+1 => alphabet.flatMap fun a => (tuples alphabet n).map (a :: ·)

private theorem ofFn_mem_tuples {A : Type*} (alphabet : List A) {n : ℕ} (w : Fin n → A)
    (hw : ∀ i, w i ∈ alphabet) : List.ofFn w ∈ tuples alphabet n := by
  induction n with
  | zero => simp [tuples]
  | succ n ih =>
    rw [List.ofFn_succ]
    exact List.mem_flatMap.mpr ⟨w 0,hw 0,List.mem_map.mpr
      ⟨List.ofFn fun i => w i.succ,ih _ (fun i => hw i.succ),rfl⟩⟩

/-- Words are kept with their catalogue decomposition for provenance. -/
def rules (q K b L s : ℕ) (pad : Fin q) : List (Fin s → BubbleWord (Fin q) K b L) :=
  letI : Inhabited (Fin q) := ⟨pad⟩
  (tuples (localWords q K b L) s).filterMap fun ws =>
    if h : ws.length = s then
      let members := fun i : Fin s => ws.get (Fin.cast h.symm i)
      if Catalogue.validCheck members (fun _ => (0 : Fin 1)) then some members else none
    else none

set_option linter.style.haveILetI false in
theorem mem_rules_iff (pad : Fin q) (hL : 0 < L) (words : Fin s → BubbleWord (Fin q) K b L) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    words ∈ rules q K b L s pad ↔ Catalogue.ValidCatalogue words (fun _ => (0 : Fin 1)) := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  constructor
  · intro h
    obtain ⟨ws,hm,hout⟩ := List.mem_filterMap.mp h
    split at hout
    next hl =>
      dsimp only at hout
      split at hout
      next hc =>
        obtain rfl := Option.some.inj hout
        exact (Catalogue.validCheck_iff _ _).mp hc
      next => contradiction
    next => contradiction
  · intro h
    have he := ofFn_mem_tuples (localWords q K b L) words (fun i => mem_localWords (words i) hL)
    have hc := (Catalogue.validCheck_iff _ _).mpr h
    refine List.mem_filterMap.mpr ⟨List.ofFn words,he,?_⟩
    simp [hc]

def row (pad : Fin q) (words : Fin s → BubbleWord (Fin q) K b L) :
    Fin (q^L) → F₃ :=
  fun g => ∑ i, vector pad (words i) g

#print axioms mem_rules_iff

end DeletionCode.Explicit.CatalogueEnumeration
