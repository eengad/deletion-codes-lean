import DeletionCode.Explicit.EditBall
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Weighted lexicographic addresses and their inverse, `d:address` and
`d:addresses`. The implementations query only one-letter extensions. -/
namespace DeletionCode.Explicit.WeightedAddress

variable {q ℓ : ℕ}
abbrev Mass (q : ℕ) := QWord q → ℕ

theorem words_nodup (q n : ℕ) : (wordsOfLength q n).Nodup := by
  induction n with
  | zero => simp [wordsOfLength]
  | succ n ih =>
    rw [wordsOfLength, List.nodup_flatMap]
    refine ⟨fun a _ => ih.map (fun _ _ h => List.cons.inj h |>.2), ?_⟩
    apply (List.nodup_finRange q).imp
    intro a b hab z ha hb
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨t, _, h⟩ := List.mem_map.mp hb
    exact hab (List.cons.inj h).1.symm

def extensionMass (weight : Mass q) (p : QWord q) (n : ℕ) : ℕ :=
  ((wordsOfLength q n).map fun w => weight (p ++ w)).sum

def Exact (weight mass : Mass q) (ℓ : ℕ) : Prop :=
  ∀ p n, p.length + n = ℓ → mass p = extensionMass weight p n

def earlier (a : Fin q) : List (Fin q) := (List.finRange q).take a.val

def before (mass : Mass q) (p : QWord q) (a : Fin q) : ℕ :=
  ((earlier a).map fun b => mass (p ++ [b])).sum

def offset (mass : Mass q) : QWord q → QWord q → ℕ
  | _, [] => 0
  | p, a :: w => before mass p a + offset mass (p ++ [a]) w

def encode (mass : Mass q) (w : QWord q) : ℕ := offset mass [] w

private theorem split_digits (a : Fin q) :
    List.finRange q = earlier a ++ a :: (List.finRange q).drop (a.val + 1) := by
  have h : a.val < (List.finRange q).length := by simp
  conv_lhs => rw [← List.take_append_drop a.val (List.finRange q)]
  rw [List.drop_eq_getElem_cons h, List.getElem_finRange]
  rfl

private theorem earlier_lt {a b : Fin q} (h : b ∈ earlier a) : b < a := by
  rwa [earlier, List.mem_take_iff_idxOf_lt (List.mem_finRange b), List.idxOf_finRange] at h

private theorem later_gt {a b : Fin q} (h : b ∈ (List.finRange q).drop (a.val + 1)) :
    a < b := by
  obtain ⟨i, hi, rfl⟩ := List.mem_drop_iff_getElem.mp h
  rw [List.getElem_finRange]
  change a.val < a.val + 1 + i
  omega

private theorem sum_map_flatMap {A B : Type*} (xs : List A) (f : A → List B) (g : B → ℕ) :
    ((xs.flatMap f).map g).sum = (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih, List.sum_append]

theorem extensionMass_branch (weight : Mass q) (p : QWord q) (n : ℕ) :
    extensionMass weight p (n + 1) =
      ((List.finRange q).map fun a => extensionMass weight (p ++ [a]) n).sum := by
  simp only [extensionMass, wordsOfLength, sum_map_flatMap, List.map_map, Function.comp_def,
    List.append_assoc, List.singleton_append]

private theorem exact_branch {weight mass : Mass q} (hex : Exact weight mass ℓ)
    {p : QWord q} {n : ℕ} (hl : p.length + (n + 1) = ℓ) :
    mass p = ((List.finRange q).map fun a => mass (p ++ [a])).sum := by
  rw [hex p (n + 1) hl, extensionMass_branch]
  congr 1
  apply List.map_congr_left
  intro a _
  rw [hex (p ++ [a]) n (by simp at *; omega)]

private theorem before_add_le {weight mass : Mass q} (hex : Exact weight mass ℓ)
    {p : QWord q} {n : ℕ} (hl : p.length + (n + 1) = ℓ) (a : Fin q) :
    before mass p a + mass (p ++ [a]) ≤ mass p := by
  rw [exact_branch hex hl, split_digits a]
  simp only [before, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  omega

theorem offset_add_le {weight mass : Mass q} (hex : Exact weight mass ℓ)
    (p w : QWord q) (hlen : p.length + w.length = ℓ) :
    offset mass p w + weight (p ++ w) ≤ mass p := by
  induction w generalizing p with
  | nil => simp [offset, hex p 0 (by simpa using hlen), extensionMass, wordsOfLength]
  | cons a w ih =>
    have hnext : (p ++ [a]).length + w.length = ℓ := by simp at *; omega
    have htail := ih (p ++ [a]) hnext
    have hwhole := before_add_le hex (n := w.length) (by simpa using hlen) a
    simp only [offset, List.append_assoc, List.singleton_append] at htail ⊢
    omega

/-- The proof uses the same order as lexicographic enumeration. -/
theorem offset_eq_lex_sum {weight mass : Mass q} (hex : Exact weight mass ℓ)
    (p w : QWord q) (hlen : p.length + w.length = ℓ) :
    offset mass p w = ((wordsOfLength q w.length).map fun z =>
      if List.Lex (· < ·) z w then weight (p ++ z) else 0).sum := by
  induction w generalizing p with
  | nil => simp [offset, wordsOfLength, List.not_lex_nil]
  | cons a w ih =>
    have hp (b : Fin q) : (p ++ [b]).length + w.length = ℓ := by simp at *; omega
    simp only [offset, List.length_cons, wordsOfLength, sum_map_flatMap, List.map_map,
      Function.comp_def]
    rw [split_digits a, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    have hfront : (List.map (fun b => (List.map (fun z =>
        if List.Lex (· < ·) (b :: z) (a :: w) then weight (p ++ b :: z) else 0)
          (wordsOfLength q w.length)).sum) (earlier a)).sum = before mass p a := by
      unfold before
      congr 1
      apply List.map_congr_left
      intro b hb
      have hh := earlier_lt hb
      simp only [List.cons_lex_cons_iff, hh, true_or, ite_true]
      rw [hex _ _ (hp b)]
      simp [extensionMass, List.append_assoc]
    have hback : (List.map (fun b => (List.map (fun z =>
        if List.Lex (· < ·) (b :: z) (a :: w) then weight (p ++ b :: z) else 0)
          (wordsOfLength q w.length)).sum) ((List.finRange q).drop (a.val + 1))).sum = 0 := by
      apply List.sum_eq_zero
      intro m hm
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
      have hh := later_gt hb
      simp [List.cons_lex_cons_iff, hh.not_gt, hh.ne', List.sum_replicate]
    rw [hfront, hback, add_zero, ih (p ++ [a]) (hp a)]
    simp [List.cons_lex_cons_iff, List.append_assoc]

/-- Locate the child interval, carrying the residual address and making
one query per child tried. -/
def pick (child : Fin q → ℕ) : List (Fin q) → ℕ → Option (Fin q × ℕ)
  | [], _ => none
  | a :: as, r =>
    let m := child a
    if r < m then some (a, r) else pick child as (r - m)

theorem pick_residual_le {child : Fin q → ℕ} {xs : List (Fin q)} {r s : ℕ} {a : Fin q}
    (h : pick child xs r = some (a, s)) : s ≤ r := by
  induction xs generalizing r with
  | nil => simp [pick] at h
  | cons x xs ih =>
    simp only [pick] at h
    split at h
    · cases h; exact le_rfl
    · exact (ih h).trans (Nat.sub_le _ _)

private theorem pick_append_hit (child : Fin q → ℕ) (ys zs : List (Fin q))
    {a : Fin q} {r : ℕ} (hr : r < child a) :
    pick child (ys ++ a :: zs) ((ys.map child).sum + r) = some (a, r) := by
  induction ys with
  | nil => simp [pick, hr]
  | cons x ys ih =>
    have hh : ¬ child x + ((ys.map child).sum + r) < child x := by omega
    simpa only [List.cons_append, List.map_cons, List.sum_cons, pick, hh, ite_false,
      Nat.add_assoc, Nat.add_sub_cancel_left] using ih

theorem pick_hit (mass : Mass q) (p : QWord q) (a : Fin q) {r : ℕ}
    (hr : r < mass (p ++ [a])) :
    pick (fun b => mass (p ++ [b])) (List.finRange q) (before mass p a + r) =
      some (a, r) := by
  unfold before
  conv_lhs => rw [split_digits a]
  exact pick_append_hit _ _ _ hr

abbrev State (q : ℕ) := Option (QWord q × ℕ)

def decodeStep (mass : Mass q) (state : State q) : State q :=
  state.bind fun (p, r) =>
    (pick (fun b => mass (p ++ [b])) (List.finRange q) r).map fun (a, s) => (p ++ [a], s)

def decode (mass : Mass q) (ℓ r : ℕ) : Option (QWord q) :=
  if r < mass [] then ((decodeStep mass)^[ℓ] (some ([], r))).map Prod.fst else none

theorem decode_from_interval {weight mass : Mass q} (hex : Exact weight mass ℓ)
    (p w : QWord q) (hlen : p.length + w.length = ℓ)
    {k : ℕ} (hk : k < weight (p ++ w)) :
    (decodeStep mass)^[w.length] (some (p, offset mass p w + k)) = some (p ++ w, k) := by
  induction w generalizing p with
  | nil => simp [offset]
  | cons a w ih =>
    have htail : (p ++ [a]).length + w.length = ℓ := by simp at *; omega
    have hk' : k < weight ((p ++ [a]) ++ w) := by simpa using hk
    have hb := offset_add_le hex (p ++ [a]) w htail
    have hchild : offset mass (p ++ [a]) w + k < mass (p ++ [a]) := by omega
    simp only [List.length_cons, Function.iterate_succ_apply, offset, Nat.add_assoc,
      decodeStep, Option.bind_some]
    rw [pick_hit _ _ _ hchild]
    simpa only [Option.map_some, List.append_assoc, List.singleton_append] using ih _ htail hk'

theorem decode_encode {weight mass : Mass q} (hex : Exact weight mass ℓ)
    {w : QWord q} (hlen : w.length = ℓ) (hw : 0 < weight w) :
    decode mass ℓ (encode mass w) = some w := by
  have ht := decode_from_interval hex [] w (by simpa using hlen) (k := 0) (by simpa using hw)
  have hb := offset_add_le hex [] w (by simpa using hlen)
  have hr : encode mass w < mass [] := by simp [encode] at *; omega
  rw [decode, if_pos hr, ← hlen]
  simpa [encode] using congrArg (Option.map Prod.fst) ht

theorem encode_injective {weight mass : Mass q} (hex : Exact weight mass ℓ) :
    Set.InjOn (encode mass) {w | w.length = ℓ ∧ 0 < weight w} := by
  intro v hv w hw h
  exact Option.some.inj ((decode_encode hex hv.1 hv.2).symm.trans
    (h ▸ decode_encode hex hw.1 hw.2))

theorem encode_lt {weight mass : Mass q} (hex : Exact weight mass ℓ) {h : ℕ}
    (hroot : mass [] ≤ q ^ (ℓ - h)) {w : QWord q} (hlen : w.length = ℓ) (hw : 0 < weight w) :
    encode mass w < q ^ (ℓ - h) := by
  have hb := offset_add_le hex [] w (by simpa using hlen)
  simp only [List.nil_append] at hb
  unfold encode
  omega

theorem encode_eq_lex_sum {weight mass : Mass q} (hex : Exact weight mass ℓ)
    {w : QWord q} (hlen : w.length = ℓ) :
    encode mass w = ((wordsOfLength q ℓ).map fun z =>
      if List.Lex (· < ·) z w then weight z else 0).sum := by
  simpa only [encode, List.nil_append, hlen] using offset_eq_lex_sum hex [] w
    (by simpa using hlen)

#print axioms words_nodup
#print axioms extensionMass_branch
#print axioms encode_eq_lex_sum
#print axioms decode_from_interval
#print axioms decode_encode
#print axioms encode_injective
#print axioms encode_lt

end DeletionCode.Explicit.WeightedAddress
