import DeletionCode.Explicit.Wrapper
import DeletionCode.Explicit.EditBall

/-! The exact image test and bounded search of `d:wrapper-decoding`. -/

namespace DeletionCode.Explicit.Wrapper

open Burst

variable {q b t : ℕ} (W : Wrapper q)

private def splitEnd {α : Type*} (w : List α) (n : ℕ) :=
  (w.take (w.length - n), w.drop (w.length - n))

private theorem splitEnd_append {α : Type*} (a v : List α) (n : ℕ) (hv : v.length = n) :
    splitEnd (a ++ v) n = (a, v) := by
  subst n
  simp [splitEnd]

/-- Finite indices of the assigned inner tags. Each length determines its bin. -/
private def rows : List (ℕ × ℕ) :=
  (List.range (W.k + 1)).flatMap fun l =>
    (List.range W.labelCount).map (fun z => (l, z))

private theorem mem_rows {l z : ℕ} (hl : l ≤ W.k) (hz : z < W.labelCount) :
    (l, z) ∈ W.rows := by simp [rows, List.mem_flatMap, Nat.lt_succ_of_le hl, hz]

def verifyInverse (w x : QWord q) : Option (QWord q) := do
  let u ← W.repairData.inverse W.k x
  if W.encode u = w then some u else none

private theorem verifyInverse_sound {w x u : QWord q} (h : W.verifyInverse w x = some u) :
    u.length = W.k ∧ W.encode u = w := by
  cases hi : W.repairData.inverse W.k x with
  | none => simp [verifyInverse, hi] at h
  | some a =>
    by_cases he : W.encode a = w
    · have ha : a = u := by simpa [verifyInverse, hi, he] using h
      subst u
      exact ⟨W.repairData.inverse_length hi, he⟩
    · simp [verifyInverse, hi, he] at h

/-- Read both tags on an undamaged candidate. A match gives the length of
the preceding payload. Re-encoding is the exact final membership check. -/
def readRow (w : QWord q) (row : ℕ × ℕ) : Option (QWord q) :=
  let l := row.1
  let j := W.bin l
  let (h, outerTag) := splitEnd w W.mOut
  let (padded, innerTag) := splitEnd h (W.m₀ + j)
  if outerTag = W.outer j ∧ innerTag = W.inner j l row.2 then
    W.verifyInverse w (splitEnd padded l).2
  else none

private theorem readRow_sound {w u : QWord q} {row : ℕ × ℕ} (h : W.readRow w row = some u) :
    u.length = W.k ∧ W.encode u = w := by
  unfold readRow at h
  dsimp only at h
  split at h
  · exact W.verifyInverse_sound h
  · contradiction

private theorem readRow_encode (H : W.Laws b t) {u : QWord q} (hu : u.length = W.k) :
    let x := W.repairData.repair u
    W.readRow (W.encode u) (x.length, W.label x) = some u := by
  let x := W.repairData.repair u
  have hx : x.length ≤ W.k := hu ▸ W.repairData.repair_length_le u
  have ha : W.repairData.accepted x = true := W.repairData.repair_accepted u
  have outEq := splitEnd_append (W.headPart x) (W.outer (W.bin x.length)) W.mOut
    (H.outer_length _ (W.bin_le_max _))
  have inEq := splitEnd_append (W.padded x) (W.innerPart x) (W.m₀ + W.bin x.length)
    (H.inner_length _ _ hx (H.label_lt _ hx ha))
  have payload : (splitEnd (W.padded x) x.length).2 = x := by
    unfold padded
    rw [splitEnd_append _ _ _ rfl]
  have hi : W.repairData.inverse W.k x = some u := hu ▸ W.repairData.inverse_repair u
  change W.readRow (W.wrap x) (x.length, W.label x) = some u
  change splitEnd (W.wrap x) W.mOut = _ at outEq
  change splitEnd (W.headPart x) _ = _ at inEq
  simp [readRow, outEq, inEq, innerPart, payload, verifyInverse, hi,
    show W.encode u = W.wrap x from rfl]

def imageTest (w : QWord q) : Option (QWord q) :=
  if w.length = W.k + W.m₀ + W.mOut then W.rows.findSome? (W.readRow w) else none

theorem imageTest_sound {w u : QWord q} (h : W.imageTest w = some u) :
    u.length = W.k ∧ W.encode u = w := by
  unfold imageTest at h
  split at h
  · obtain ⟨_, _, hr⟩ := List.exists_of_findSome?_eq_some h
    exact W.readRow_sound hr
  · contradiction

theorem imageTest_encode (H : W.Laws b t) {u : QWord q} (hu : u.length = W.k) :
    W.imageTest (W.encode u) = some u := by
  cases h : W.imageTest (W.encode u) with
  | some v =>
    obtain ⟨hv, he⟩ := W.imageTest_sound h
    exact congrArg some (encode_injective H hv hu he)
  | none =>
    let x := W.repairData.repair u
    have hx : x.length ≤ W.k := hu ▸ W.repairData.repair_length_le u
    have ha : W.repairData.accepted x = true := W.repairData.repair_accepted u
    have hm := W.mem_rows hx (H.label_lt _ hx ha)
    have hn : W.rows.findSome? (W.readRow (W.encode u)) = none := by
      simpa [imageTest, encode_length H hu] using h
    have hf := List.findSome?_eq_none_iff.mp hn _ hm
    rw [readRow_encode W H hu] at hf
    contradiction

/-- The exact membership result includes the message recovered by the test. -/
theorem imageTest_iff (H : W.Laws b t) {w u : QWord q} :
    W.imageTest w = some u ↔ u.length = W.k ∧ W.encode u = w := by
  refine ⟨W.imageTest_sound, ?_⟩
  rintro ⟨hu, rfl⟩
  exact W.imageTest_encode H hu

def decode (b t : ℕ) (z : QWord q) : Option (QWord q) :=
  (candidates (W.k + W.m₀ + W.mOut) b t z).findSome? W.imageTest

theorem decode_correct (H : W.Laws b t) {u z : QWord q} (hu : u.length = W.k)
    (hz : WithinBursts b t (W.encode u) z) : W.decode b t z = some u := by
  have hc := mem_candidates.mpr ⟨encode_length H hu, hz⟩
  cases h : W.decode b t z with
  | none =>
    have hn := List.findSome?_eq_none_iff.mp h (W.encode u) hc
    rw [W.imageTest_encode H hu] at hn
    contradiction
  | some v =>
    obtain ⟨w, hw, hv⟩ := List.exists_of_findSome?_eq_some h
    obtain ⟨hvlen, rfl⟩ := W.imageTest_sound hv
    exact congrArg some (eq_of_common_output H hvlen hu (mem_candidates.mp hw).2 hz)

#print axioms imageTest_iff
#print axioms decode_correct

end DeletionCode.Explicit.Wrapper
