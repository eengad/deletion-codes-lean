import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega

/-! Fixed-width padding of instruction lists, with a proved decoding round trip. -/
namespace DeletionCode.RecordPacking

variable {α β : Type*}

def pack (padding : β) (xs : List β) (size : ℕ) : Fin size → β :=
  fun i => xs[i.val]?.getD padding

def unpack (decode : β → Option (Option α)) :
    (size : ℕ) → (Fin size → β) → Option (List α)
  | 0, _ => some []
  | size + 1, rows =>
    (decode (rows ⟨0, by omega⟩)).bind fun entry =>
      (unpack decode size (fun i => rows i.succ)).map fun rest => entry.toList ++ rest

theorem unpack_of_positions (decode : β → Option (Option α)) (size : ℕ)
    (rows : Fin size → β) (xs : List α) (hsize : xs.length ≤ size)
    (hrows : ∀ i, decode (rows i) = some xs[i.val]?) :
    unpack decode size rows = some xs := by
  induction size generalizing xs with
  | zero =>
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    rfl
  | succ size ih =>
    cases xs with
    | nil =>
      have hfirst := hrows ⟨0, by omega⟩
      change decode (rows 0) = some none at hfirst
      have hrest : ∀ i : Fin size, decode (rows i.succ) = some ([] : List α)[i.val]? := by
        intro i
        simpa using hrows i.succ
      have hr := ih (fun i => rows i.succ) [] (by simp) hrest
      simp [unpack, hfirst, hr]
    | cons a xs =>
      have hfirst := hrows ⟨0, by omega⟩
      change decode (rows 0) = some (some a) at hfirst
      have hrest : ∀ i : Fin size, decode (rows i.succ) = some xs[i.val]? := by
        intro i
        simpa using hrows i.succ
      have hr := ih (fun i => rows i.succ) xs (by simp at hsize; omega) hrest
      simp [unpack, hfirst, hr]

theorem unpack_pack (decode : β → Option (Option α)) (encode : α → β)
    (padding : β) (hpadding : decode padding = some none)
    (xs : List α) (hencode : ∀ a ∈ xs, decode (encode a) = some (some a))
    (size : ℕ) (hsize : xs.length ≤ size) :
    unpack decode size (pack padding (xs.map encode) size) = some xs := by
  apply unpack_of_positions decode size _ xs hsize
  intro i
  unfold pack
  cases hget : xs[i.val]? with
  | none => simpa [List.getElem?_map, hget] using hpadding
  | some a =>
    have ha : a ∈ xs := List.mem_of_getElem? hget
    simpa [List.getElem?_map, hget] using hencode a ha

#print axioms unpack_of_positions
#print axioms unpack_pack

end DeletionCode.RecordPacking
