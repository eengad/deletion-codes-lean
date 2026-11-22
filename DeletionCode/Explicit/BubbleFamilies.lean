import DeletionCode.Explicit.CatalogueCheck
import DeletionCode.Explicit.EditBallCount
import DeletionCode.Explicit.FieldPath
import DeletionCode.Explicit.FieldHash
import DeletionCode.Explicit.LetterSequence
import Mathlib.Algebra.BigOperators.Fin

/-! Shapes and their finite families of local bubbles. -/

namespace DeletionCode.Explicit.BubbleFamilies

open DeletionCode.Explicit.Borrowed DeletionCode.Explicit.FieldHash

/-- The offsets and symbols of fresh letters, with both central words
and flank lengths fixed. No source position is part of a shape. -/
structure Shape (q : ℕ) where
  left : ℕ
  right : ℕ
  removed : QWord q
  replacement : QWord q
  fresh : List (Option (Fin q))
  deriving DecidableEq

variable {q : ℕ}

def Shape.originalCount (s : Shape q) : ℕ :=
  (s.fresh.filter Option.isNone).length

def Shape.freshCount (s : Shape q) : ℕ :=
  (s.fresh.filter Option.isSome).length

/-- Fill original offsets in order, while leaving the recorded fresh
symbols fixed. There must be exactly one value for each original offset. -/
def fill : List (Option (Fin q)) → QWord q → Option (QWord q)
  | [], [] => some []
  | [], _ :: _ => none
  | some a :: tail, values => (fill tail values).map (a :: ·)
  | none :: tail, a :: values => (fill tail values).map (a :: ·)
  | none :: _, [] => none

/-- Recover the bounded local words from a proposed negative spelling.
The removed portion is checked against the recorded word. -/
def localWord (K b L : ℕ) (leftLen : ℕ) (removed replacement : QWord q) (neg : QWord q) :
    Option (BubbleWord (Fin q) K b L) :=
  let left := neg.take leftLen
  let right := neg.drop (leftLen+removed.length)
  if h : removed.length ≤ b ∧ replacement.length ≤ b ∧ removed ≠ replacement ∧
      L-1-K-b ≤ left.length ∧ left.length ≤ L-1 ∧
      L-1-K-b ≤ right.length ∧ right.length ≤ L-1 then
    let w : BubbleWord (Fin q) K b L :=
      ⟨left,right,removed,replacement,h.1,h.2.1,h.2.2.1,h.2.2.2.1,
        h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩
    if w.negativeWord = neg then some w else none
  else none

def Shape.member (s : Shape q) (K b L Λ : ℕ) (pad : Fin q) (values : QWord q) :
    Option (BubbleWord (Fin q) K b L) :=
  letI : Inhabited (Fin q) := ⟨pad⟩
  if s.freshCount ≤ Λ ∧ s.fresh.length = s.left+s.removed.length+s.right then do
    let neg ← fill s.fresh values
    let w ← localWord K b L s.left s.removed s.replacement neg
    if Catalogue.validCheck (fun _ : Fin 1 => w) (fun _ => (0 : Fin 1)) then some w else none
  else none

def Shape.members (s : Shape q) (K b L Λ : ℕ) (pad : Fin q) :
    List (QWord q × BubbleWord (Fin q) K b L) :=
  (wordsOfLength q s.originalCount).filterMap
    (fun w => (s.member K b L Λ pad w).map (fun member => (w,member)))

/-- Every member contributes the spectrum difference in one common set
of gram coordinates. -/
def vector {K b L : ℕ} (pad : Fin q) (w : BubbleWord (Fin q) K b L) :
    Fin (q^L) → F₃ :=
  fun i => listFieldSpectrum pad w.positiveWord L (finFunctionFinEquiv.symm i) -
    listFieldSpectrum pad w.negativeWord L (finFunctionFinEquiv.symm i)

def Shape.vectors (s : Shape q) (K b L Λ : ℕ) (pad : Fin q) :
    Finset (Fin (q^L) → F₃) :=
  ((s.members K b L Λ pad).map (fun p => vector pad p.2)).toFinset

theorem mem_members (s : Shape q) (K b L Λ : ℕ) (pad : Fin q) (values : QWord q)
    (w : BubbleWord (Fin q) K b L) :
    (values,w) ∈ s.members K b L Λ pad ↔
      values.length = s.originalCount ∧ s.member K b L Λ pad values = some w := by
  unfold Shape.members
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨u,hu,he⟩
    cases hp : s.member K b L Λ pad u with
    | none => simp [hp] at he
    | some m =>
      have eq : (u,m) = (values,w) := by simpa [hp] using he
      obtain ⟨e₁,e₂⟩ := Prod.mk.inj eq
      subst u m
      exact ⟨mem_wordsOfLength.mp hu,hp⟩
  · rintro ⟨hl,hm⟩
    exact ⟨values,mem_wordsOfLength.mpr hl,by simp [hm]⟩

/-- A shape has at most one candidate per assignment of its original symbols. -/
theorem vectors_card_le (s : Shape q) (K b L Λ : ℕ) (pad : Fin q) :
    (s.vectors K b L Λ pad).card ≤ q^s.originalCount := by
  calc
    _ ≤ ((s.members K b L Λ pad).map (fun p => vector pad p.2)).length :=
      List.toFinset_card_le _
    _ = (s.members K b L Λ pad).length := by simp
    _ ≤ (wordsOfLength q s.originalCount).length := List.length_filterMap_le _ _
    _ = q^s.originalCount := length_wordsOfLength _ _

open LetterSequence

private def patternLetter {ℓ : ℕ} : Letter ℓ (Fin q) → Option (Fin q)
  | .original _ => none
  | .fresh _ _ a => some a

private def assignedLetter {ℓ : ℕ} (x : Fin ℓ → Fin q) : Letter ℓ (Fin q) → Option (Fin q)
  | .original i => some (x i)
  | .fresh .. => none

private theorem fill_letters {ℓ : ℕ} (x : Fin ℓ → Fin q) (letters : List (Letter ℓ (Fin q))) :
    fill (letters.map patternLetter) (letters.filterMap (assignedLetter x)) =
      some (letters.map (Letter.symbol x)) := by
  induction letters with
  | nil => rfl
  | cons w tail ih => cases w <;> simp [List.filterMap_cons,patternLetter,assignedLetter,fill,Letter.symbol,ih]

private theorem assigned_length {ℓ : ℕ} (x : Fin ℓ → Fin q) (letters : List (Letter ℓ (Fin q))) :
    (letters.filterMap (assignedLetter x)).length =
      ((letters.map patternLetter).filter Option.isNone).length := by
  induction letters with
  | nil => rfl
  | cons w tail ih => cases w <;> simp [List.filterMap_cons,patternLetter,assignedLetter,ih]

def shapeOf {ℓ n : ℕ} (left right : ℕ) (removed replacement : QWord q)
    (w : Lift ℓ n (Fin q)) : Shape q :=
  ⟨left,right,removed,replacement,(List.ofFn w.letters).map patternLetter⟩

def originalValues {ℓ n : ℕ} (w : Lift ℓ n (Fin q)) (x : Fin ℓ → Fin q) : QWord q :=
  (List.ofFn w.letters).filterMap (assignedLetter x)

theorem originalValues_length {ℓ n : ℕ} (left right : ℕ) (removed replacement : QWord q)
    (w : Lift ℓ n (Fin q)) (x : Fin ℓ → Fin q) :
    (originalValues w x).length = (shapeOf left right removed replacement w).originalCount :=
  assigned_length x (List.ofFn w.letters)

theorem fill_shapeOf {ℓ n : ℕ} (left right : ℕ) (removed replacement : QWord q)
    (w : Lift ℓ n (Fin q)) (x : Fin ℓ → Fin q) :
    fill (shapeOf left right removed replacement w).fresh (originalValues w x) =
      some (List.ofFn (w.spelling x)) := by
  change _ = some (List.ofFn fun i => (w.letters i).symbol x)
  simpa [shapeOf,originalValues,List.map_ofFn,Function.comp_def] using fill_letters x (List.ofFn w.letters)

private def project : List (Option (Fin q)) → QWord q → Option (QWord q)
  | [], [] => some []
  | some _ :: tail, _ :: values => project tail values
  | none :: tail, a :: values => (project tail values).map (a :: ·)
  | _, _ => none

private theorem project_fill {pattern : List (Option (Fin q))} {values word : QWord q}
    (h : fill pattern values = some word) : project pattern word = some values := by
  induction pattern generalizing values word with
  | nil => cases values <;> simp_all [fill,project]
  | cons head rest ih =>
    cases head with
    | none =>
      cases values with
      | nil => simp [fill] at h
      | cons a as =>
        cases hfill : fill rest as with
        | none => simp [fill,hfill] at h
        | some suffix =>
          have he : a :: suffix = word := by simpa [fill,hfill] using h
          subst word
          simp [project,ih hfill]
    | some a =>
      cases hfill : fill rest values with
      | none => simp [fill,hfill] at h
      | some suffix =>
        have he : a :: suffix = word := by simpa [fill,hfill] using h
        subst word
        exact ih hfill

theorem fill_injective {pattern : List (Option (Fin q))} {x y w : QWord q}
    (hx : fill pattern x = some w) (hy : fill pattern y = some w) : x = y :=
  Option.some.inj ((project_fill hx).symm.trans (project_fill hy))

theorem fill_length {pattern : List (Option (Fin q))} {values word : QWord q}
    (h : fill pattern values = some word) : word.length = pattern.length := by
  induction pattern generalizing values word with
  | nil => cases values <;> simp_all [fill]
  | cons head rest ih =>
    cases head with
    | none =>
      cases values with
      | nil => simp [fill] at h
      | cons a as =>
        cases hfill : fill rest as with
        | none => simp [fill,hfill] at h
        | some suf =>
          have he : a::suf = word := by simpa [fill,hfill] using h
          subst word
          simp [ih hfill]
    | some a =>
      cases hfill : fill rest values with
      | none => simp [fill,hfill] at h
      | some suf =>
        have he : a::suf = word := by simpa [fill,hfill] using h
        subst word
        simp [ih hfill]

theorem localWord_negative {K b L left : ℕ} {removed replacement neg : QWord q}
    {w : BubbleWord (Fin q) K b L}
    (h : localWord K b L left removed replacement neg = some w) :
    w.negativeWord = neg := by
  unfold localWord at h
  dsimp only at h
  split at h
  next hh =>
    split at h
    next hword =>
      have he := Option.some.inj h
      exact he ▸ hword
    next => contradiction
  next => contradiction

theorem member_data (s : Shape q) (K b L Λ : ℕ) (pad : Fin q) {values : QWord q}
    {w : BubbleWord (Fin q) K b L} (h : s.member K b L Λ pad values = some w) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    fill s.fresh values = some w.negativeWord ∧ s.freshCount ≤ Λ ∧
      Catalogue.ValidCatalogue (fun _ : Fin 1 => w) (fun _ => (0 : Fin 1)) := by
  let inst : Inhabited (Fin q) := ⟨pad⟩
  unfold Shape.member at h
  split at h
  next ht =>
    cases hfill : fill s.fresh values with
    | none => simp [hfill] at h
    | some neg =>
      cases hb : localWord K b L s.left s.removed s.replacement neg with
      | none => simp [hfill,hb] at h
      | some m =>
        by_cases hv : Catalogue.validCheck (fun _ : Fin 1 => m) (fun _ => (0 : Fin 1)) = true
        · have he : m = w := by simpa [hfill,hb,hv] using h
          subst w
          exact ⟨congrArg some (localWord_negative hb).symm,ht.1,(Catalogue.validCheck_iff _ _).mp hv⟩
        · simp [hfill,hb,hv] at h
  next => contradiction

#print axioms fill_shapeOf

#print axioms mem_members
#print axioms vectors_card_le

end DeletionCode.Explicit.BubbleFamilies
