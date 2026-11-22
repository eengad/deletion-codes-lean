import DeletionCode.Explicit.ReplayFamily
import DeletionCode.Explicit.MixedRadix
import DeletionCode.Explicit.CompressorFrame

/-! Write a one-anchor description and the indexed small-family payload. -/

namespace DeletionCode.Explicit.ReplayPayload

open ReplayGrammar ReplayEntry BubbleFamilies

variable {ℓ q E L b : ℕ}

def readPrefix (n : ℕ) (w : QWord q) : Option ((Fin n → Fin q) × QWord q) :=
  if h : n ≤ w.length then
    some ((fun i => w.get ⟨i.val,i.isLt.trans_le h⟩),w.drop n)
  else none

theorem read_append {n : ℕ} (u : Fin n → Fin q) (v : QWord q) :
    readPrefix n (List.ofFn u ++ v) = some (u,v) := by
  have h : n ≤ (List.ofFn u ++ v).length := by simp
  unfold readPrefix
  rw [dite_eq_left h]
  congr 1
  apply Prod.ext
  · funext i
    change (List.ofFn u ++ v)[i.val] = u i
    have hi : i.val < (List.ofFn u).length := by simp
    rw [List.getElem_append_left hi]
    simp
  · change (List.ofFn u ++ v).drop n = v
    simpa only [List.length_ofFn] using (List.drop_left (l₁ := List.ofFn u) (l₂ := v))

def indexWord {M : ℕ} (hq : 1 < q) (i : Fin M) : Fin (Nat.clog q M) → Fin q :=
  finFunctionFinEquiv.symm (Fin.castLE (Nat.le_pow_clog hq M) i)

def readIndex (M : ℕ) (w : QWord q) : Option (Fin M × QWord q) := do
  let (u,v) ← readPrefix (Nat.clog q M) w
  let k := (finFunctionFinEquiv u).val
  if hk : k < M then some (⟨k,hk⟩,v) else none

theorem read_index {M : ℕ} (hq : 1 < q) (i : Fin M) (tail : QWord q) :
    readIndex M (List.ofFn (indexWord hq i) ++ tail) = some (i,tail) := by
  unfold readIndex
  rw [read_append]
  change (if h : (finFunctionFinEquiv (indexWord hq i)).val < M then
    some (⟨(finFunctionFinEquiv (indexWord hq i)).val,h⟩,tail) else none) = some (i,tail)
  unfold indexWord
  rw [Equiv.apply_symm_apply]
  change (if h : i.val < M then some (⟨i.val,h⟩,tail) else none) = some (i,tail)
  rw [dite_eq_left i.isLt]

private def samePatch (p : ℕ) (ds : List (DecodedEntry q)) : Bool :=
  ds.all (fun d => d.entry.patch == p)

private def final (ds : List (DecodedEntry q)) : Option (DecodedEntry q) :=
  match ds.filter (fun d => d.finalBubble) with
  | [d] => some d
  | _ => none

/-- The single anchor names the one patch used by a small-family slice. -/
def materialize (c : DescriptionCode E L b q) (anchor : Fin ℓ) :
    Option (Entry (Fin q) × Completed ℓ (Fin q)) := do
  let ds ← decodeDescription c
  let d ← final ds
  if samePatch d.entry.patch ds then
    let ws ← replay L (fun p => if p = d.entry.patch then some anchor else none) (ds.map DecodedEntry.entry)
    let i := (ds.map DecodedEntry.finalBubble).idxOf true
    let w ← ws[i]?
    some (d.entry,w)
  else none

private abbrev headerBound (ℓ q E L b : ℕ) : ℕ :=
  descriptionBound E L b q * ℓ

private def header (hq : 1 < q) (c : DescriptionCode E L b q) (anchor : Fin ℓ) :
    Fin (Nat.clog q (headerBound ℓ q E L b)) → Fin q :=
  indexWord hq (finProdFinEquiv (packDescription c,anchor))

private def readHeader (w : QWord q) :
    Option (DescriptionCode E L b q × Fin ℓ × QWord q) := do
  let (i,rest) ← readIndex (headerBound ℓ q E L b) w
  let (packed,anchor) := finProdFinEquiv.symm i
  let c ← unpackDescription packed
  some (c,anchor,rest)

private theorem read_header (hq : 1 < q) (c : DescriptionCode E L b q) (root : Fin ℓ) (rest : QWord q) :
    readHeader (List.ofFn (header hq c root) ++ rest) = some (c,root,rest) := by
  unfold readHeader header
  rw [read_index]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [Equiv.symm_apply_apply]
  simp [unpack_packDescription]

def encode (hq : 1 < q) (K b L Λ : ℕ) (pad : Fin q)
    (c : DescriptionCode E L b q) (root : Fin ℓ) (x : Fin ℓ → Fin q) : Option (QWord q) := do
  let p ← materialize c root
  let packed ← SmallFamilyCodec.encode hq (active p.2.negative.2) (replayAssignments K b L Λ pad p) x
  some (List.ofFn (header hq c root) ++ List.ofFn packed)

def decode (ℓ E K b L Λ : ℕ) (pad : Fin q) (payload : QWord q) : Option (Fin ℓ → Fin q) := do
  let (c,root,tail) ← readHeader (E := E) (L := L) (b := b) (ℓ := ℓ) payload
  let p ← materialize c root
  let S := active p.2.negative.2
  let members := replayAssignments K b L Λ pad p
  let (u,_) ← readPrefix (SmallFamilyCodec.payloadLength S members) tail
  SmallFamilyCodec.decode S members u

theorem encode_roundtrip (hq : 1 < q) (K b L Λ : ℕ) (pad : Fin q)
    (c : DescriptionCode E L b q) (root : Fin ℓ) (x : Fin ℓ → Fin q)
    {p : Entry (Fin q) × Completed ℓ (Fin q)} (hc : materialize c root = some p)
    {m : Borrowed.BubbleWord (Fin q) K b L}
    (hm : (replayShape p).member K b L Λ pad (originalValues p.2.negative.2 x) = some m) :
    ∃ payload, encode hq K b L Λ pad c root x = some payload ∧
      payload.length ≤ Nat.clog q (headerBound ℓ q E L b) + (ℓ-(active p.2.negative.2).card) +
        Nat.clog q (replayAssignments K b L Λ pad p).length ∧
      ∀ trailing : QWord q, decode ℓ E K b L Λ pad (payload++trailing) = some x := by
  obtain ⟨u,he,hd⟩ := replay_payload_roundtrip hq K b L Λ pad p x hm
  refine ⟨List.ofFn (header hq c root) ++ List.ofFn u,?_,?_,?_⟩
  · simp [encode,hc,he]
  · simp only [List.length_append,List.length_ofFn]
    have h := SmallFamilyCodec.payloadLength_le hq (active p.2.negative.2) (replayAssignments K b L Λ pad p)
    omega
  · intro tail
    simp [decode,List.append_assoc,read_header,hc,read_append,hd]

/-- The one-anchor parser recovers the marked gate at its original index. -/
theorem materialize_of_replay (c : DescriptionCode E L b q) (anchor : Fin ℓ)
    (ds : List (DecodedEntry q)) (d : DecodedEntry q)
    (hc : decodeDescription c = some ds) (hd : ds.filter (·.finalBubble) = [d])
    (hp : ∀ p ∈ ds, p.entry.patch = d.entry.patch)
    (ws : Array (Completed ℓ (Fin q)))
    (hr : replay L (fun p => if p = d.entry.patch then some anchor else none) (ds.map (·.entry)) = some ws)
    (w : Completed ℓ (Fin q)) (hw : ws[(ds.map (·.finalBubble)).idxOf true]? = some w) :
    materialize c anchor = some (d.entry,w) := by
  have hs : samePatch d.entry.patch ds = true := List.all_eq_true.mpr
    (fun p hm => beq_iff_eq.mpr (hp p hm))
  simp [materialize,hc,final,hd,hs,hr,hw]

#print axioms materialize_of_replay
#print axioms read_index
#print axioms encode_roundtrip

end DeletionCode.Explicit.ReplayPayload
