import DeletionCode.Explicit.ReplayFamily
import DeletionCode.Explicit.ReversePeeling
import DeletionCode.Explicit.PivotRadix
import DeletionCode.Explicit.LiftDictionary
import DeletionCode.Explicit.CoreReplay

/-! Compute the missing bucket from the other bubbles of the peeled rule. -/

namespace DeletionCode.Explicit.PeelingBuckets

open FieldHash ReplayEntry BubbleFamilies LetterSequence LiftDictionary
open scoped BigOperators

variable {ℓ q d s θ : ℕ}

abbrev Recorded (ℓ q : ℕ) := Entry (Fin q) × Completed ℓ (Fin q)

def vectorOf (L : ℕ) (pad : Fin q) (p : Recorded ℓ q) (x : Fin ℓ → Fin q) :
    Fin (q^L) → F₃ :=
  fun i => bubbleVector pad x p.2 (finFunctionFinEquiv.symm i)

def bucketValues (K b L Λ : ℕ) (pad : Fin q) (H : TernaryMatrix θ (q^L)) (p : Recorded ℓ q)
    (z : Fin θ → F₃) : List (QWord q) :=
  (bucket (replayShape p) K b L Λ pad H z).map Prod.fst

def pivotDigit (K b L Λ : ℕ) (pad : Fin q) (H : TernaryMatrix θ (q^L))
    (p : Recorded ℓ q) (x : Fin ℓ → Fin q) : ℕ :=
  (bucketValues K b L Λ pad H p (H.mulVec (vectorOf L pad p x))).idxOf
    (originalValues p.2.negative.2 x)

def neededHash (L : ℕ) (pad : Fin q) (H : TernaryMatrix θ (q^L))
    (record : Fin d × Fin s → Recorded ℓ q) (pivot : Fin d × Fin s) (x : Fin ℓ → Fin q) :
    Fin θ → F₃ :=
  -∑ j ∈ (Finset.univ.erase pivot.2), H.mulVec (vectorOf L pad (record (pivot.1,j)) x)

def readPivot (K b L Λ : ℕ) (pad : Fin q) (H : TernaryMatrix θ (q^L))
    (record : Fin d × Fin s → Recorded ℓ q) (pivot : Fin d × Fin s)
    (digit : ℕ) (old : Fin ℓ → Fin q) : Option (Fin ℓ → Fin q) := do
  let p := record pivot
  let vals ← (bucketValues K b L Λ pad H p (neededHash L pad H record pivot old))[digit]?
  let S := active p.2.negative.2
  if hv : vals.length = S.card then
    some (SmallFamilyCodec.assemble S (fun i => vals.get (Fin.cast hv.symm i))
      (SmallFamilyCodec.select Sᶜ old))
  else none

theorem vector_congr (L : ℕ) (pad : Fin q) (p : Recorded ℓ q) {x y : Fin ℓ → Fin q}
    (hpos : p.2.positive.2.positions ⊆ p.2.negative.2.positions)
    (h : ∀ i ∈ active p.2.negative.2, x i = y i) :
    vectorOf L pad p x = vectorOf L pad p y := by
  have hn := CoreWeight.lift_spelling_congr p.2.negative.2 (x := x) (y := y)
    (fun i hi => h i ((active_iff _ _).mpr hi))
  have hp := CoreWeight.lift_spelling_congr p.2.positive.2 (x := x) (y := y)
    (fun i hi => h i ((active_iff _ _).mpr (hpos hi)))
  funext i
  change (fieldSpectrum (paddedLetters pad (p.2.positive.2.spelling x)) _ L -
    fieldSpectrum (paddedLetters pad (p.2.negative.2.spelling x)) _ L) _ =
    (fieldSpectrum (paddedLetters pad (p.2.positive.2.spelling y)) _ L -
      fieldSpectrum (paddedLetters pad (p.2.negative.2.spelling y)) _ L) _
  rw [hn,hp]

theorem neededHash_eq (L : ℕ) (pad : Fin q) (H : TernaryMatrix θ (q^L))
    (record : Fin d × Fin s → Recorded ℓ q) (pivot : Fin d × Fin s) (x : Fin ℓ → Fin q)
    (hzero : ∑ j : Fin s, H.mulVec (vectorOf L pad (record (pivot.1,j)) x) = 0) :
    neededHash L pad H record pivot x = H.mulVec (vectorOf L pad (record pivot) x) := by
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin s))
    (fun j => H.mulVec (vectorOf L pad (record (pivot.1,j)) x)) (Finset.mem_univ pivot.2)
  rw [hzero] at hsum
  change -(∑ j ∈ Finset.univ.erase pivot.2,
    H.mulVec (vectorOf L pad (record (pivot.1,j)) x)) = _
  have he := eq_neg_of_add_eq_zero_left hsum
  simpa only [Prod.eta,neg_neg] using congrArg Neg.neg he

/-- The pivot's true assignment is found in the bucket of its own hash. -/
theorem digit_lt_bucket (K b L Λ : ℕ) (pad : Fin q) (H : TernaryMatrix θ (q^L))
    (p : Recorded ℓ q) (x : Fin ℓ → Fin q)
    {w : Borrowed.BubbleWord (Fin q) K b L}
    (hm : (replayShape p).member K b L Λ pad (originalValues p.2.negative.2 x) = some w)
    (hw : vector pad w = vectorOf L pad p x) :
    pivotDigit K b L Λ pad H p x <
      (bucketValues K b L Λ pad H p (H.mulVec (vectorOf L pad p x))).length := by
  apply List.idxOf_lt_length_iff.mpr
  apply List.mem_map.mpr
  refine ⟨(originalValues p.2.negative.2 x,w),List.mem_filter.mpr ⟨?_,?_⟩,rfl⟩
  · exact (mem_members (replayShape p) K b L Λ pad _ _).mpr
      ⟨originalValues_length _ _ _ _ _ _,hm⟩
  · simp [hw]

/-- With all its nonpivot bubbles restored, the actual bucket reader
writes the correct active letters of the pivot. -/
theorem readPivot_correct (K b L Λ : ℕ) (pad : Fin q) (H : TernaryMatrix θ (q^L))
    (record : Fin d × Fin s → Recorded ℓ q) (pivot : Fin d × Fin s) (x y : Fin ℓ → Fin q)
    (hpos : ∀ e, (record e).2.positive.2.positions ⊆ (record e).2.negative.2.positions)
    (hzero : ∑ j : Fin s, H.mulVec (vectorOf L pad (record (pivot.1,j)) x) = 0)
    (hagree : ∀ j ≠ pivot.2, ∀ i ∈ active (record (pivot.1,j)).2.negative.2, y i = x i)
    {w : Borrowed.BubbleWord (Fin q) K b L}
    (hm : (replayShape (record pivot)).member K b L Λ pad
      (originalValues (record pivot).2.negative.2 x) = some w)
    (hw : vector pad w = vectorOf L pad (record pivot) x) :
    ∃ out, readPivot K b L Λ pad H record pivot (pivotDigit K b L Λ pad H (record pivot) x) y = some out ∧
      ∀ i ∈ active (record pivot).2.negative.2, out i = x i := by
  have he : neededHash L pad H record pivot y = neededHash L pad H record pivot x := by
    unfold neededHash
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [vector_congr L pad _ (hpos _) (hagree j (Finset.mem_erase.mp hj).1)]
  rw [neededHash_eq L pad H record pivot x hzero] at he
  have hidx := digit_lt_bucket K b L Λ pad H _ x hm hw
  have hget := List.getElem_idxOf hidx
  have hsome := List.getElem?_eq_getElem hidx
  unfold pivotDigit at hsome
  rw [hget] at hsome
  have ho : (bucketValues K b L Λ pad H (record pivot)
      (H.mulVec (vectorOf L pad (record pivot) x)))[pivotDigit K b L Λ pad H (record pivot) x]? =
      some (originalValues (record pivot).2.negative.2 x) := hsome
  let S := active (record pivot).2.negative.2
  have hvalues : originalValues (record pivot).2.negative.2 x =
      List.ofFn (SmallFamilyCodec.select S x) := originalValues_eq_select _ _
  refine ⟨SmallFamilyCodec.assemble S (SmallFamilyCodec.select S x) (SmallFamilyCodec.select Sᶜ y),?_,?_⟩
  · simp only [readPivot,he,ho,hvalues,Option.bind_eq_bind,Option.bind_some]
    simp [S,SmallFamilyCodec.select]
    rfl
  · intro i hi
    change i ∈ S at hi
    simp [SmallFamilyCodec.assemble,SmallFamilyCodec.select,hi]

#print axioms readPivot_correct

end DeletionCode.Explicit.PeelingBuckets
