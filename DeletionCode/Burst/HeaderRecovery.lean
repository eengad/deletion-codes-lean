import DeletionCode.Burst.SeedTransfer

/-! Deterministic recovery and bounded-alphabet seed transfer for burst headers. -/
namespace DeletionCode.Burst.HeaderRecovery
open DeletionCode.Qary.Windows DeletionCode.Burst.BlockWords DeletionCode.Burst.SeedTransfer
open DeletionCode.Qary.HeaderRecovery (Seed Bits padBits)
variable {α : Type*} [Inhabited α]

def transferPositiveSeed (k b : ℕ) (h : Header α) (seed : Seed α) (extras : Bits α b) : Seed α :=
  lengthenMany h.leftLength k h.removed
    (shortenMany h.leftLength k h.replacement.length
      (fun i => padBits extras i.val) seed)

theorem transfer_positive_seed_in_bounds (k b : ℕ) (h : Header α)
    (seed : Seed α) (extras : Bits α b) (hv : h.Valid k b)
    (hbound : seed.offset + k ≤ positiveLength h) :
    (transferPositiveSeed k b h seed extras).offset + k ≤ negativeLength h := by
  have hs := shortenMany_bound h.leftLength k h.replacement.length h.rightLength seed
    (fun i => padBits extras i.val) (rightLength_ge hv) hbound
  have hi := lengthenMany_bound h.leftLength k (h.leftLength + h.rightLength)
    h.removed _ hs
  unfold transferPositiveSeed negativeLength
  omega

theorem transfer_positive_seed_exists (k b : ℕ) (h : Header α) (negative : Letters α)
    (seed : Seed α) (hv : h.Valid k b) (hm : h.Matches negative)
    (hbound : seed.offset + k ≤ positiveLength h)
    (hseed : Agree (positivePath h negative) seed.offset seed.bits 0 k) :
    ∃ extras : Bits α b,
      Agree negative (transferPositiveSeed k b h seed extras).offset
        (transferPositiveSeed k b h seed extras).bits 0 k ∧
      (transferPositiveSeed k b h seed extras).offset + k ≤ negativeLength h := by
  obtain ⟨es, hes, _⟩ := shortenMany_exists (positivePath h negative)
    h.leftLength k h.replacement.length h.rightLength seed (rightLength_ge hv) hbound hseed
  let extras : Bits α b := fun i => if hi : i.val < h.replacement.length then es ⟨i.val, hi⟩ else default
  have he : (fun i : Fin h.replacement.length => padBits extras i.val) = es := by
    funext i
    have hb : i.val < b := lt_of_lt_of_le i.isLt hv.replacement_le
    simp [padBits, extras, hb, i.isLt]
  have hcommon : deleteBlock (positivePath h negative) h.leftLength h.replacement.length =
      deleteBlock negative h.leftLength h.removed.length := by
    rw [positivePath, edit_word_eq, delete_insertBlock]
  rw [hcommon] at hes
  have hi := lengthenMany_correct (deleteBlock negative h.leftLength h.removed.length)
    h.leftLength k h.removed _ hes
  rw [insert_deleteBlock negative h.leftLength h.removed hm] at hi
  refine ⟨extras, ?_, transfer_positive_seed_in_bounds k b h seed extras hv hbound⟩
  simpa only [transferPositiveSeed, he] using hi

def transferFinite (k b : ℕ) (h : Header α) (offset : ℕ)
    (bits : Bits α k) (extras : Bits α b) : ℕ × Bits α k :=
  let output := transferPositiveSeed k b h ⟨offset, padBits bits⟩ extras
  (output.offset, fun i => output.bits i.val)

theorem transferFinite_exists (k b : ℕ) (h : Header α) (negative : Letters α)
    (offset : ℕ) (bits : Bits α k) (hv : h.Valid k b) (hm : h.Matches negative)
    (hbound : offset + k ≤ positiveLength h)
    (hseed : ∀ i : Fin k, positivePath h negative (offset + i.val) = bits i) :
    ∃ extras : Bits α b,
      (transferFinite k b h offset bits extras).1 + k ≤ negativeLength h ∧
      ∀ i : Fin k, negative ((transferFinite k b h offset bits extras).1 + i.val) =
        (transferFinite k b h offset bits extras).2 i := by
  have hs : Agree (positivePath h negative) offset (padBits bits) 0 k := by
    intro i hi
    simpa only [padBits, Nat.zero_add, dite_eq_left hi] using hseed ⟨i, hi⟩
  obtain ⟨extras, he, hb⟩ := transfer_positive_seed_exists k b h negative
    ⟨offset, padBits bits⟩ hv hm hbound hs
  refine ⟨extras, hb, ?_⟩
  intro i
  simpa only [transferFinite, Nat.zero_add] using he i.val i.isLt

theorem rebuild_positive_preserves_agreement (h : Header α) (p q : Letters α)
    (hknown : Agree p 0 q 0 (negativeLength h)) :
    Agree (rebuildPositive h p) 0 (rebuildPositive h q) 0 (positiveLength h) := by
  intro i hi
  by_cases hl : i < h.leftLength
  · have hb : i < negativeLength h := by unfold negativeLength; omega
    simpa [rebuildPositive, positivePath, Edit.word, hl] using hknown i hb
  · by_cases hm : i < h.leftLength + h.replacement.length
    · simp [rebuildPositive, positivePath, Edit.word, hl, hm]
    · have hb : i + h.removed.length - h.replacement.length < negativeLength h := by
        unfold positiveLength at hi
        unfold negativeLength
        omega
      simpa [rebuildPositive, positivePath, Edit.word, hl, hm] using hknown _ hb

def rebuildPositiveFinite (h : Header α)
    (negative : Bits α (negativeLength h)) : Bits α (positiveLength h) :=
  fun i => rebuildPositive h (padBits negative) i.val

theorem rebuildPositiveFinite_correct (h : Header α) (negative : Letters α)
    (known : Bits α (negativeLength h))
    (hknown : ∀ i : Fin (negativeLength h), known i = negative i.val) :
    ∀ i : Fin (positiveLength h), rebuildPositiveFinite h known i = positivePath h negative i.val := by
  have hk : Agree (padBits known) 0 negative 0 (negativeLength h) := by
    intro i hi
    simpa only [padBits, Nat.zero_add, dite_eq_left hi] using hknown ⟨i, hi⟩
  intro i
  simpa only [rebuildPositiveFinite, rebuildPositive, Nat.zero_add] using
    rebuild_positive_preserves_agreement h _ _ hk i.val i.isLt

#print axioms transferFinite_exists
#print axioms rebuildPositiveFinite_correct
end DeletionCode.Burst.HeaderRecovery
