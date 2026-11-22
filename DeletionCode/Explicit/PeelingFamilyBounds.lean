import DeletionCode.Explicit.SmallCompression
import DeletionCode.Explicit.FamilyBuckets
import DeletionCode.Explicit.PivotRadix

/-! A chosen hash bounds the pivot digits of all large replayed families. -/

namespace DeletionCode.Explicit.PeelingFamilyBounds

open UniformParameters ConcreteSource BubbleFamilies ReplayEntry PeelingBuckets SmallCompression

variable {q b t ℓ : ℕ}

def tables (q b t ℓ : ℕ) (pad : Fin q) :=
  BubbleFamilies.families q (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ) pad

def vectors (q b t ℓ : ℕ) (pad : Fin q) (j : Fin (familyCount q b t ℓ pad)) :
    BucketBalance.Family (q^(gram q b t ℓ)) :=
  ((tables q b t ℓ pad).get j).2

def Balanced (pad : Fin q) (H : Hash q b t ℓ) : Prop :=
  BucketBalance.potential (vectors q b t ℓ pad) H ≤ 3*(familyCount q b t ℓ pad)

private theorem shape_guard (p : Shape q) (K b L Λ : ℕ) (pad : Fin q)
    {u : QWord q} {v : Borrowed.BubbleWord (Fin q) K b L}
    (h : p.member K b L Λ pad u = some v) :
    p.freshCount ≤ Λ ∧ p.fresh.length = p.left+p.removed.length+p.right := by
  unfold Shape.member at h
  split at h
  next hg => exact hg
  next => contradiction

set_option maxHeartbeats 750000 in
theorem large_record_bounds (pad : Fin q) (H : Hash q b t ℓ) (hH : Balanced pad H)
    (hL : 1 ≤ gram q b t ℓ) (r : Recorded ℓ q) (x : Fin ℓ → Fin q)
    (left : r.1.left < gram q b t ℓ) (right : r.1.right < gram q b t ℓ)
    (removed : r.1.removed.length ≤ b) (inserted : r.1.replacement.length ≤ b)
    {w : Borrowed.BubbleWord (Fin q) (windowLength q ℓ) b (gram q b t ℓ)}
    (hm : (replayShape r).member (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ) pad
      (originalValues r.2.negative.2 x) = some w)
    (hv : vector pad w = vectorOf (gram q b t ℓ) pad r x)
    (hlarge : isSmall (b := b) (t := t) pad r = false) :
    let m := ((replayShape r).members (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ) pad).length
    hashCount q b t ℓ ≤ m ∧
      pivotDigit (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ) pad H r x <
        pivotRadix m (hashCount q b t ℓ) := by
  dsimp only
  let K := windowLength q ℓ
  let L := gram q b t ℓ
  let Λ := omittedLetters q b t ℓ
  let θ := hashWidth q b t ℓ
  let P := hashCount q b t ℓ
  let J := familyCount q b t ℓ pad
  let S := replayShape r
  let M := (S.members K b L Λ pad).length
  obtain ⟨hf,hlen⟩ := shape_guard S K b L Λ pad hm
  have hshape : S ∈ allShapes q L b Λ := mem_allShapes S left right removed inserted hlen hf
  have hmem : (originalValues r.2.negative.2 x,w) ∈ S.members K b L Λ pad :=
    (mem_members S K b L Λ pad _ _).mpr ⟨originalValues_length _ _ _ _ _ _,hm⟩
  have hvec : (S.vectors K b L Λ pad).Nonempty :=
    ⟨vector pad w,List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,hmem,rfl⟩)⟩
  have htab : (S,S.vectors K b L Λ pad) ∈ tables q b t ℓ pad :=
    mem_families_of_nonempty pad S hshape hvec
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp htab
  have hj' : j.val < J := j.isLt
  let idx : Fin J := ⟨j.val,hj'⟩
  have hdecode : vectors q b t ℓ pad idx = S.vectors K b L Λ pad := congrArg Prod.snd hj
  have hM : 12*J*P^2 ≤ M := by
    unfold isSmall at hlarge
    exact Nat.le_of_not_gt (of_decide_eq_false hlarge)
  have hM' : 12*J*(3^θ)^2 ≤ (vectors q b t ℓ pad idx).card := by
    rw [hdecode,vectors_card S K b L Λ pad hL]
    exact hM
  have hP : 0 < P := by change 0 < 3^θ; positivity
  have hJ : 0 < J := Nat.zero_lt_of_lt idx.isLt
  have hP' : P ≤ M := by
    calc
      P ≤ P^2 := by
        simpa only [pow_one] using (Nat.pow_le_pow_right hP (show 1 ≤ 2 by decide))
      _ ≤ 12*J*P^2 := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) hJ)
      _ ≤ M := hM
  refine ⟨hP',?_⟩
  apply (digit_lt_bucket K b L Λ pad H r x hm hv).trans_le
  simp only [bucketValues,List.length_map]
  exact bucket_fits_pivotRadix pad hL (vectors q b t ℓ pad) H hH idx S hdecode hM' _

#print axioms large_record_bounds

end DeletionCode.Explicit.PeelingFamilyBounds
