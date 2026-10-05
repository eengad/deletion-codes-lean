import DeletionCode.Burst.ChronologicalRecords
import DeletionCode.CloseAnchorCount
import Mathlib.Data.List.OfFn
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring

/-!
Finite records for actual chronological burst scripts. Each packet records
the current-word position, removed and inserted lengths, and at most b target
letters. The total decoder also accepts malformed records as an overcount.
-/
namespace DeletionCode.Burst.FiniteRecords

variable {α : Type*}

abbrev Payload (α : Type*) (b : ℕ) :=
  Fin (b + 1) × Fin (b + 1) × (Fin b → α)

abbrev Record (α : Type*) (b N r : ℕ) :=
  (Fin r → Fin N) × (Fin r → Payload α b)

def replacement {b : ℕ} (p : Payload α b) : List α :=
  List.ofFn (fun i : Fin p.2.1.val => p.2.2 ⟨i.val, by omega⟩)

def edit {b : ℕ} (pos : ℕ) (p : Payload α b) : Edit α :=
  ⟨pos, p.1.val, replacement p⟩

def edits {b N r : ℕ} (rec : Record α b N r) : List (Edit α) :=
  List.ofFn (fun i => edit (rec.1 i).val (rec.2 i))

def decode {b N r : ℕ} (x : Word α) (rec : Record α b N r) : Word α :=
  run x (edits rec)

theorem payload_card [Fintype α] (b : ℕ) :
    Fintype.card (Payload α b) = (b + 1) ^ 2 * Fintype.card α ^ b := by
  simp only [Payload, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  ring

theorem record_card [Fintype α] (b N r : ℕ) :
    Fintype.card (Record α b N r) =
      N ^ r * ((b + 1) ^ 2 * Fintype.card α ^ b) ^ r := by
  simp only [Record, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  congr 1
  congr 1
  ring

def encodePayload [Inhabited α] {b : ℕ} (e : Edit α) (h : e.Bounded b) : Payload α b :=
  (⟨e.removed, Nat.lt_succ_of_le h.1⟩,
    ⟨e.replacement.length, Nat.lt_succ_of_le h.2⟩,
    fun i => e.replacement.getD i.val default)

theorem replacement_encodePayload [Inhabited α] {b : ℕ} (e : Edit α)
    (h : e.Bounded b) : replacement (encodePayload e h) = e.replacement := by
  apply List.ext_getElem
  · simp [replacement, encodePayload]
  · intro i hi hj
    simp only [replacement, encodePayload, List.getElem_ofFn]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem edit_encodePayload [Inhabited α] {b : ℕ} (e : Edit α) (h : e.Bounded b) :
    edit e.pos (encodePayload e h) = e := by
  unfold edit
  rw [replacement_encodePayload]
  cases e
  rfl

def encode [Inhabited α] {b N : ℕ} (es : List (Edit α))
    (hp : ∀ i : Fin es.length, (es.get i).pos < N)
    (hb : ∀ i : Fin es.length, (es.get i).Bounded b) : Record α b N es.length :=
  (fun i => ⟨(es.get i).pos, hp i⟩, fun i => encodePayload (es.get i) (hb i))

theorem edits_encode [Inhabited α] {b N : ℕ} (es : List (Edit α))
    (hp : ∀ i : Fin es.length, (es.get i).pos < N)
    (hb : ∀ i : Fin es.length, (es.get i).Bounded b) :
    edits (encode es hp hb) = es := by
  simp only [edits, encode, edit_encodePayload]
  exact List.ofFn_get es

theorem decode_encode [Inhabited α] {b N : ℕ} {x y : Word α}
    {es : List (Edit α)} (h : Executes b x es y)
    (hp : ∀ i : Fin es.length, (es.get i).pos < N) :
    decode x (encode es hp (fun i => (h.get_valid i).1)) = y := by
  rw [decode, edits_encode, h.run_eq]

theorem exists_record [Inhabited α] {b r s : ℕ} {x y : Word α}
    (h : Script b x y r) (hr : r ≤ s) :
    ∃ rec : Record α b (x.length + s * b + 1) r, decode x rec = y := by
  obtain ⟨es, hlen, hex⟩ := h.exists_executes
  subst r
  have hp (i : Fin es.length) : (es.get i).pos < x.length + s * b + 1 := by
    have hi := hex.position_le i
    have hmul : i.val * b ≤ s * b := Nat.mul_le_mul_right b (by omega)
    omega
  exact ⟨encode es hp (fun i => (hex.get_valid i).1), decode_encode hex hp⟩

def Bad {b N r : ℕ} (n D : ℕ) (rec : Record α b N r) : Prop :=
  CloseAnchorCount.Bad n D rec.1

noncomputable def badEquiv (b N r n D : ℕ) :
    {rec : Record α b N r // Bad n D rec} ≃
      {a : Fin r → Fin N // CloseAnchorCount.Bad n D a} ×
        (Fin r → Payload α b) where
  toFun rec := (⟨rec.val.1, rec.property⟩, rec.val.2)
  invFun p := ⟨(p.1.val, p.2), p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem bad_record_card_le [Fintype α] (b N r n D : ℕ) :
    Nat.card {rec : Record α b N r // Bad n D rec} ≤
      r * (r + 2) * (2 * D) * N ^ (r - 1) *
        ((b + 1) ^ 2 * Fintype.card α ^ b) ^ r := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (badEquiv b N r n D),
    Fintype.card_prod, Fintype.card_fun, payload_card, Fintype.card_fin]
  apply Nat.mul_le_mul_right
  rw [Fintype.card_subtype]
  exact CloseAnchorCount.bad_card_le r N n D

end DeletionCode.Burst.FiniteRecords
