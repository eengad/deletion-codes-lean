import DeletionCode.Explicit.ReplayPayload
import DeletionCode.Explicit.PeelingPayload

/-! Serialize the full witness for reverse peeling and read its fields
before decoding the mixed-radix payload. -/

namespace DeletionCode.Explicit.PeelingFrame

open FieldHash ReplayGrammar ReplayEntry ReplayPayload RulePatch CoreWeight

variable {ℓ q K b L Λ s D θ : ℕ}

/-- An index gives the number of witness rules. The remaining fields use
only that count and the patch keys in the description. -/
structure Header (ℓ q s D : ℕ) where
  count : Fin (D+1)
  entries : List (DecodedEntry q)
  roots : ↥(patchKeys (s*count.val) entries) → Fin ℓ
  tail : QWord q

def writeHeader (hq : 1 < q) (hℓ : 0 < ℓ) (d : Fin (D+1))
    (c : DescriptionCode (s*d.val) L b q) (ds : List (DecodedEntry q))
    (roots : ↥(patchKeys (s*d.val) ds) → Fin ℓ) : QWord q :=
  let patches := patchKeys (s*d.val) ds
  List.ofFn (indexWord hq d) ++
    List.ofFn (indexWord hq (packDescription c)) ++
    List.ofFn (indexWord hq (packAnchors hℓ patches le_rfl roots))

def readHeader (ℓ q s D L b : ℕ) (payload : QWord q) : Option (Header ℓ q s D) := do
  let (d,rest) ← readIndex (D+1) payload
  let (i,rest) ← readIndex (descriptionBound (s*d.val) L b q) rest
  let c ← unpackDescription i
  let ds ← decodeDescription c
  let patches := patchKeys (s*d.val) ds
  let (k,tail) ← readIndex (ℓ^patches.card) rest
  let roots ← unpackAnchors patches k
  some ⟨d,ds,roots,tail⟩

theorem read_written_header (hq : 1 < q) (hℓ : 0 < ℓ) (d : Fin (D+1))
    (c : DescriptionCode (s*d.val) L b q) (ds : List (DecodedEntry q))
    (hc : decodeDescription c = some ds)
    (roots : ↥(patchKeys (s*d.val) ds) → Fin ℓ) (tail : QWord q) :
    readHeader ℓ q s D L b (writeHeader hq hℓ d c ds roots ++ tail) = some ⟨d,ds,roots,tail⟩ := by
  simp [readHeader,writeHeader,List.append_assoc,read_index,unpack_packDescription,hc,unpack_packAnchors]

theorem header_length (hq : 1 < q) (hℓ : 0 < ℓ) (d : Fin (D+1))
    (c : DescriptionCode (s*d.val) L b q) (ds : List (DecodedEntry q))
    (roots : ↥(patchKeys (s*d.val) ds) → Fin ℓ) :
    (writeHeader hq hℓ d c ds roots).length ≤
      Nat.clog q (D+1) + Nat.clog q (descriptionBound (s*d.val) L b q) +
        (patchKeys (s*d.val) ds).card * Nat.clog q ℓ := by
  simp only [writeHeader,List.length_append,List.length_ofFn,Nat.add_assoc]
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply (Nat.clog_le_iff_le_pow hq).mpr
  calc
    _ ≤ (q^Nat.clog q ℓ)^(patchKeys (s*d.val) ds).card :=
      Nat.pow_le_pow_left (Nat.le_pow_clog hq ℓ) _
    _ = _ := by rw [← Nat.pow_mul,Nat.mul_comm (Nat.clog q ℓ)]

structure Program (ℓ q d s : ℕ) where
  record : Fin d × Fin s → PeelingBuckets.Recorded ℓ q
  incidence : Incidence d s (s*d)

def materialize (d : Fin (D+1)) (ds : List (DecodedEntry q))
    (roots : ↥(patchKeys (s*d.val) ds) → Fin ℓ) (L : ℕ) :
    Option (Program ℓ q d.val s) := do
  let out ← replay L (anchorLookup (patchKeys (s*d.val) ds) roots) (ds.map (·.entry))
  let pairs := ds.zip out.toList
  if h : pairs.length = d.val*s then
    let source (e : Fin d.val × Fin s) :=
      pairs.get (Fin.cast h.symm (finProdFinEquiv e))
    if hp : ∀ e, (source e).1.entry.patch < s*d.val then
      some ⟨fun e => ((source e).1.entry,(source e).2),fun e => ⟨(source e).1.entry.patch,hp e⟩⟩
    else none
  else none

theorem materialize_of_table (d : Fin (D+1))
    (rows : Fin (d.val*s) → DecodedEntry q × Completed ℓ (Fin q))
    (roots : ↥(patchKeys (s*d.val) (List.ofFn fun i => (rows i).1)) → Fin ℓ)
    (hr : replay L (anchorLookup (patchKeys (s*d.val) (List.ofFn fun i => (rows i).1)) roots)
      ((List.ofFn fun i => (rows i).1).map (·.entry)) = some (List.ofFn fun i => (rows i).2).toArray)
    (hb : ∀ i, (rows i).1.entry.patch < s*d.val) :
    materialize d (List.ofFn fun i => (rows i).1) roots L =
      some ⟨fun e => ((rows (finProdFinEquiv e)).1.entry,(rows (finProdFinEquiv e)).2),
        fun e => ⟨(rows (finProdFinEquiv e)).1.entry.patch, hb (finProdFinEquiv e)⟩⟩ := by
  unfold materialize
  rw [hr]
  simp only [Option.bind_eq_bind,Option.bind_some,List.toList_toArray]
  have he : (List.ofFn fun i => (rows i).1).zip (List.ofFn fun i => (rows i).2) = List.ofFn rows := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  let pairs := (List.ofFn fun i => (rows i).1).zip (List.ofFn fun i => (rows i).2)
  have hlen : pairs.length = d.val*s := by rw [show pairs = List.ofFn rows from he,List.length_ofFn]
  have hc (i : Fin (d.val*s)) : pairs.get (Fin.cast hlen.symm i) = rows i := by
    have hOpt : pairs[i.val]? = some (rows i) := by rw [show pairs = List.ofFn rows from he]; simp [i.isLt]
    have hlt : i.val < pairs.length := by rw [hlen]; exact i.isLt
    rw [List.getElem?_eq_getElem hlt] at hOpt
    exact Option.some.inj hOpt
  change (if h : pairs.length = d.val*s then
    (if hp : ∀ e : Fin d.val × Fin s, (pairs.get (Fin.cast h.symm (finProdFinEquiv e))).1.entry.patch < s*d.val then
      some (⟨fun e => ((pairs.get (Fin.cast h.symm (finProdFinEquiv e))).1.entry,
        (pairs.get (Fin.cast h.symm (finProdFinEquiv e))).2),
        fun e => ⟨(pairs.get (Fin.cast h.symm (finProdFinEquiv e))).1.entry.patch,hp e⟩⟩ :
          Program ℓ q d.val s)
    else none) else none) = _
  rw [dite_eq_left hlen]
  have hbp (e : Fin d.val × Fin s) :
      (pairs.get (Fin.cast hlen.symm (finProdFinEquiv e))).1.entry.patch < s*d.val := by
    rw [hc]
    exact hb _
  rw [dite_eq_left hbp]
  simp only [hc]

def trace {d : ℕ} (p : Program ℓ q d s) : List (Fin d × Fin s) :=
  (peel p.incidence Finset.univ).1

def encode (hq : 1 < q) (hℓ : 0 < ℓ) (K b L Λ : ℕ) (pad : Fin q)
    (d : Fin (D+1)) (c : DescriptionCode (s*d.val) L b q)
    (anchors : ℕ → Fin ℓ) (H : TernaryMatrix θ (q^L)) (x : Fin ℓ → Fin q) :
    Option (QWord q) := do
  let ds ← decodeDescription c
  let roots : ↥(patchKeys (s*d.val) ds) → Fin ℓ := fun p => anchors p.val.val
  let prog ← materialize d ds roots L
  let packed ← PeelingPayload.encode hq K b L Λ pad prog.record (trace prog) H x
  some (writeHeader hq hℓ d c ds roots ++ List.ofFn packed)

def decode (ℓ s D K b L Λ : ℕ) (pad : Fin q) (H : TernaryMatrix θ (q^L))
    (payload : QWord q) : Option (Fin ℓ → Fin q) := do
  let hd ← readHeader ℓ q s D L b payload
  let prog ← materialize hd.count hd.entries hd.roots L
  let (data,_) ← readPrefix
    (MixedRadix.width q (PeelingPayload.radices K b L Λ pad prog.record (trace prog) (3^θ))) hd.tail
  PeelingPayload.decode K b L Λ pad prog.record (trace prog) H data

theorem encode_roundtrip (hq : 1 < q) (hℓ : 0 < ℓ) (K b L Λ : ℕ) (pad : Fin q)
    (d : Fin (D+1)) (c : DescriptionCode (s*d.val) L b q)
    (anchors : ℕ → Fin ℓ) (H : TernaryMatrix θ (q^L)) (x : Fin ℓ → Fin q)
    {ds : List (DecodedEntry q)} (hc : decodeDescription c = some ds)
    {p : Program ℓ q d.val s} (hp : materialize d ds (fun a => anchors a.val.val) L = some p)
    {packed : Fin (MixedRadix.width q (PeelingPayload.radices K b L Λ pad p.record (trace p) (3^θ))) → Fin q}
    (he : PeelingPayload.encode hq K b L Λ pad p.record (trace p) H x = some packed)
    (hd : PeelingPayload.decode K b L Λ pad p.record (trace p) H packed = some x) :
    ∃ payload, encode hq hℓ K b L Λ pad d c anchors H x = some payload ∧
      payload.length ≤ Nat.clog q (D+1)+Nat.clog q (descriptionBound (s*d.val) L b q)+
        (patchKeys (s*d.val) ds).card*Nat.clog q ℓ+
        MixedRadix.width q (PeelingPayload.radices K b L Λ pad p.record (trace p) (3^θ)) ∧
      ∀ rest : QWord q, decode ℓ s D K b L Λ pad H (payload++rest) = some x := by
  let roots : ↥(patchKeys (s*d.val) ds) → Fin ℓ := fun a => anchors a.val.val
  refine ⟨writeHeader hq hℓ d c ds roots ++ List.ofFn packed,?_,?_,?_⟩
  · simp [encode,hc,hp,he,roots]
  · simp only [List.length_append,List.length_ofFn]
    exact Nat.add_le_add_right (header_length hq hℓ d c ds roots) _
  · intro rest
    simp [decode,List.append_assoc,read_written_header hq hℓ d c ds hc,roots,hp,read_append,hd]

#print axioms read_written_header
#print axioms encode_roundtrip

end DeletionCode.Explicit.PeelingFrame
