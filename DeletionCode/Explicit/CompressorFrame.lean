import DeletionCode.Explicit.Labels
import DeletionCode.Explicit.Repair
import Mathlib.Algebra.BigOperators.Fin

/-! A fixed-width branch identifier followed by a self-delimiting
branch payload and padding to the one-step repair length. -/

namespace DeletionCode.Explicit.CompressorFrame

variable {q : ℕ}

abbrev headerLength (q : ℕ) : ℕ := Nat.clog q 3

theorem headerLength_le (hq : 1 < q) : headerLength q ≤ 2 := by
  apply (Nat.clog_le_iff_le_pow hq).mpr
  have h := Nat.pow_le_pow_left (show 2 ≤ q by omega) 2
  exact (show 3 ≤ 2^2 by decide).trans h

private def header (hq : 1 < q) (kind : Fin 3) : QWord q :=
  List.ofFn (finFunctionFinEquiv.symm (Fin.castLE (Nat.le_pow_clog hq 3) kind))

private theorem header_length (hq : 1 < q) (kind : Fin 3) :
    (header hq kind).length = headerLength q := by simp [header,headerLength]

private def parseHeader (w : QWord q) : Option (Fin 3 × QWord q) :=
  let width := headerLength q
  if h : width ≤ w.length then
    let k := finFunctionFinEquiv (fun i : Fin width => w.get ⟨i.val,i.isLt.trans_le h⟩)
    if good : k.val < 3 then some (⟨k.val,good⟩,w.drop width) else none
  else none

private theorem parse_header (hq : 1 < q) (kind : Fin 3) (tail : QWord q) :
    parseHeader (header hq kind ++ tail) = some (kind,tail) := by
  have hlen := header_length hq kind
  have h : headerLength q ≤ (header hq kind ++ tail).length := by simp [hlen]
  have hx : (fun i : Fin (headerLength q) => (header hq kind ++ tail).get
        ⟨i.val,i.isLt.trans_le h⟩) =
        finFunctionFinEquiv.symm (Fin.castLE (Nat.le_pow_clog hq 3) kind) := by
    funext i
    have hi : i.val < (header hq kind).length := by rw [hlen]; exact i.isLt
    change (header hq kind ++ tail)[i.val] = _
    rw [List.getElem_append_left hi]
    simp [header]
  unfold parseHeader
  simp only [dite_eq_left h]
  rw [hx,Equiv.apply_symm_apply]
  have hv : (Fin.castLE (Nat.le_pow_clog hq 3) kind).val < 3 := kind.isLt
  rw [dite_eq_left hv]
  have hdrop : (header hq kind ++ tail).drop (headerLength q) = tail := by
    rw [← hlen,List.drop_left]
  rw [hdrop]
  rfl

/-- Each decoder reads its own payload fields. It can return a word only
at the indicated original block length. -/
structure Branch (q : ℕ) where
  encode : QWord q → Option (QWord q)
  decode : ℕ → QWord q → Option (QWord q)

structure Branch.Laws (B : Branch q) (pad : Fin q) : Prop where
  fits : ∀ {x payload}, B.encode x = some payload →
    headerLength q+payload.length ≤ x.length-1
  inverse : ∀ {x payload}, B.encode x = some payload → ∀ n,
    B.decode x.length (payload++List.replicate n pad) = some x
  decoded_length : ∀ {ℓ payload x}, B.decode ℓ payload = some x → x.length = ℓ

/-- Use the first branch that supplies a payload, in the paper's order
of rare addresses, small families, and peeling. -/
def choose (families : Fin 3 → Branch q) (x : QWord q) :
    Option (Fin 3 × QWord q) :=
  (List.finRange 3).findSome? fun j => ((families j).encode x).map (j,·)

private theorem choose_sound (families : Fin 3 → Branch q) {x payload : QWord q} {j : Fin 3}
    (h : choose families x = some (j,payload)) : (families j).encode x = some payload := by
  obtain ⟨_,k,_,_,hk,_⟩ := List.findSome?_eq_some_iff.mp h
  cases he : (families k).encode x with
  | none => simp [he] at hk
  | some y =>
    have eq : (k,y) = (j,payload) := by simpa [he] using hk
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    exact he

theorem choose_complete (families : Fin 3 → Branch q) {x payload : QWord q} {j : Fin 3}
    (h : (families j).encode x = some payload) : (choose families x).isSome := by
  cases hj : choose families x with
  | some v => rfl
  | none =>
    exfalso
    have hjmem : j ∈ List.finRange 3 := by simp
    have he := (List.findSome?_eq_none_iff.mp hj) j hjmem
    simp [h] at he

private def frame (hq : 1 < q) (pad : Fin q) (ℓ : ℕ) (j : Fin 3) (payload : QWord q) : QWord q :=
  let body := header hq j ++ payload
  body ++ List.replicate (ℓ-1-body.length) pad

def compress (hq : 1 < q) (pad : Fin q) (families : Fin 3 → Branch q) (x : QWord q) :
    Option (QWord q) :=
  (choose families x).map fun (j,payload) => frame hq pad x.length j payload

def decompress (families : Fin 3 → Branch q) (w : QWord q) : Option (QWord q) := do
  let (j,tail) ← parseHeader w
  (families j).decode (w.length+1) tail

private theorem frame_length (hq : 1 < q) (pad : Fin q) (j : Fin 3) (payload : QWord q)
    {ℓ : ℕ} (h : headerLength q+payload.length ≤ ℓ-1) :
    (frame hq pad ℓ j payload).length = ℓ-1 := by
  simp only [frame,List.length_append,List.length_replicate,header_length]
  omega

theorem compress_correct (hq : 1 < q) (pad : Fin q) (families : Fin 3 → Branch q)
    (laws : ∀ j, (families j).Laws pad) {x w : QWord q}
    (hx : 0 < x.length) (h : compress hq pad families x = some w) :
    w.length+1 = x.length ∧ decompress families w = some x := by
  cases he : choose families x with
  | none => simp [compress,he] at h
  | some pair =>
    obtain ⟨j,payload⟩ := pair
    have hb := choose_sound families he
    have hfit := (laws j).fits hb
    have hw : frame hq pad x.length j payload = w := by simpa [compress,he] using h
    have hl : w.length+1 = x.length := by rw [← hw, frame_length hq pad j payload hfit]; omega
    refine ⟨hl,?_⟩
    unfold decompress
    rw [hl,← hw]
    simp only [frame,List.append_assoc,parse_header]
    have hasi := (laws j).inverse hb (x.length-1-((header hq j).length+payload.length))
    change (families j).decode x.length
      (payload ++ List.replicate (x.length-1-(header hq j ++ payload).length) pad) = some x
    simpa only [List.length_append] using hasi

theorem decompress_length (families : Fin 3 → Branch q) (pad : Fin q)
    (laws : ∀ j, (families j).Laws pad) {x w : QWord q}
    (h : decompress families w = some x) : x.length = w.length+1 := by
  cases he : parseHeader w with
  | none => simp [decompress,he] at h
  | some pair =>
    obtain ⟨j,payload⟩ := pair
    exact (laws j).decoded_length (by simpa [decompress,he] using h)

#print axioms compress_correct
#print axioms decompress_length

end DeletionCode.Explicit.CompressorFrame
