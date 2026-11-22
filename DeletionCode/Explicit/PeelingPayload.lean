import DeletionCode.Explicit.PeelingBuckets
import DeletionCode.Explicit.MixedRadix

/-! Rank the literal field and the pivot digits in a single mixed-radix integer. -/

namespace DeletionCode.Explicit.PeelingPayload

open FieldHash PeelingBuckets BubbleFamilies RulePatch
open scoped BigOperators

variable {ℓ q d s c θ : ℕ}

abbrev Edges (d s : ℕ) := Fin d × Fin s

def activeSet (record : Edges d s → Recorded ℓ q) (trace : List (Edges d s)) : Finset (Fin ℓ) :=
  trace.toFinset.biUnion fun p => active (record p).2.negative.2

def radices (K b L Λ : ℕ) (pad : Fin q) (record : Edges d s → Recorded ℓ q)
    (trace : List (Edges d s)) (P : ℕ) : List ℕ :=
  q^((activeSet record trace)ᶜ.card) :: trace.map fun pivot =>
    pivotRadix ((replayShape (record pivot)).members K b L Λ pad).length P

def values (K b L Λ : ℕ) (pad : Fin q) (record : Edges d s → Recorded ℓ q)
    (trace : List (Edges d s)) (H : TernaryMatrix θ (q^L)) (x : Fin ℓ → Fin q) : List ℕ :=
  (finFunctionFinEquiv (SmallFamilyCodec.select (activeSet record trace)ᶜ x)).val ::
    trace.map (fun j => pivotDigit K b L Λ pad H (record j) x)

def encode (hq : 1 < q) (K b L Λ : ℕ) (pad : Fin q) (record : Edges d s → Recorded ℓ q)
    (trace : List (Edges d s)) (H : TernaryMatrix θ (q^L)) (x : Fin ℓ → Fin q) :
    Option (Fin (MixedRadix.width q (radices K b L Λ pad record trace (3^θ))) → Fin q) :=
  MixedRadix.encode hq _ (values K b L Λ pad record trace H x)

def decode (K b L Λ : ℕ) (pad : Fin q) (record : Edges d s → Recorded ℓ q)
    (trace : List (Edges d s)) (H : TernaryMatrix θ (q^L))
    (payload : Fin (MixedRadix.width q (radices K b L Λ pad record trace (3^θ))) → Fin q) :
    Option (Fin ℓ → Fin q) := do
  let packed ← MixedRadix.decode _ payload
  match packed with
  | [] => none
  | first :: rest =>
    let S := activeSet record trace
    if h : first < q^Sᶜ.card then
      let literal := finFunctionFinEquiv.symm (⟨first,h⟩ : Fin (q^Sᶜ.card))
      let start := SmallFamilyCodec.assemble S (fun _ => pad) literal
      restore (fun e => active (record e).2.negative.2) (fun e => rest.getD (trace.idxOf e) 0)
        (readPivot K b L Λ pad H record) trace start
    else none

private theorem map_fits {A : Type*} (trace : List A) (radix digit : A → ℕ)
    (h : ∀ e ∈ trace, digit e < radix e) :
    MixedRadix.Fits (trace.map radix) (trace.map digit) := by
  induction trace with
  | nil => exact .nil
  | cons e es ih => exact .cons (h e (by simp)) (ih (fun e he => h e (List.mem_cons_of_mem _ he)))

private theorem getD_map_idx {A : Type*} [BEq A] [LawfulBEq A] (f : A → ℕ)
    (trace : List A) {e : A} (h : e ∈ trace) :
    (trace.map f).getD (trace.idxOf e) 0 = f e := by
  have hidx := List.idxOf_lt_length_iff.mpr h
  have hmap : trace.idxOf e < (trace.map f).length := by simpa using hidx
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hmap,Option.getD_some,List.getElem_map,
    List.getElem_idxOf hidx]

/-- The decoder uses exactly the radices available before reading any
hash. Its reverse step derives each missing hash from the other bubbles. -/
theorem encode_roundtrip (hq : 1 < q) (K b L Λ : ℕ) (pad : Fin q)
    (a : Incidence d s c) (trace : List (Edges d s)) (terminal : Finset (Fin d))
    (htrace : LegalTrace a Finset.univ trace terminal)
    (record : Edges d s → Recorded ℓ q) (owner : Fin ℓ → Option (Fin c))
    (hfit : ∀ e i, i ∈ active (record e).2.negative.2 → owner i = some (a e))
    (H : TernaryMatrix θ (q^L)) (x : Fin ℓ → Fin q)
    (hpos : ∀ e, (record e).2.positive.2.positions ⊆ (record e).2.negative.2.positions)
    (hzero : ∀ i : Fin d, ∑ j : Fin s, H.mulVec (vectorOf L pad (record (i,j)) x) = 0)
    (hm : ∀ e ∈ trace, ∃ w : Borrowed.BubbleWord (Fin q) K b L,
      (replayShape (record e)).member K b L Λ pad (originalValues (record e).2.negative.2 x) = some w ∧
      vector pad w = vectorOf L pad (record e) x)
    (hd : ∀ e ∈ trace, pivotDigit K b L Λ pad H (record e) x <
      pivotRadix ((replayShape (record e)).members K b L Λ pad).length (3^θ)) :
    ∃ payload, encode hq K b L Λ pad record trace H x = some payload ∧
      decode K b L Λ pad record trace H payload = some x := by
  let S := activeSet record trace
  let raw := fun e => pivotDigit K b L Λ pad H (record e) x
  let sz := fun e => pivotRadix ((replayShape (record e)).members K b L Λ pad).length (3^θ)
  let literal := finFunctionFinEquiv (SmallFamilyCodec.select Sᶜ x)
  have hfitDigits : MixedRadix.Fits (radices K b L Λ pad record trace (3^θ))
      (values K b L Λ pad record trace H x) := .cons literal.isLt (map_fits trace sz raw hd)
  obtain ⟨payload,hen,hde⟩ := MixedRadix.encode_roundtrip hq hfitDigits
  refine ⟨payload,hen,?_⟩
  let start := SmallFamilyCodec.assemble S (fun _ => pad) (SmallFamilyCodec.select Sᶜ x)
  let digit := fun e => (trace.map raw).getD (trace.idxOf e) 0
  have hread (e : Edges d s) (he : e ∈ trace) (y : Fin ℓ → Fin q)
      (hy : ∀ j ≠ e.2, ∀ i ∈ active (record (e.1,j)).2.negative.2, y i = x i) :
      ∃ v, readPivot K b L Λ pad H record e (digit e) y = some v ∧
        ∀ i ∈ active (record e).2.negative.2, v i = x i := by
    obtain ⟨w,hw,hvec⟩ := hm e he
    simpa only [digit,getD_map_idx raw trace he] using
      readPivot_correct K b L Λ pad H record e x y hpos (hzero e.1) hy hw hvec
  have hlit (i : Fin ℓ) (h : ∀ e ∈ trace, i ∉ active (record e).2.negative.2) : start i = x i := by
    have hi : i ∉ S := by
      intro hs
      obtain ⟨e,he,hm⟩ := Finset.mem_biUnion.mp hs
      exact h e (List.mem_toFinset.mp he) hm
    simp [start,SmallFamilyCodec.assemble,SmallFamilyCodec.select,hi]
  have hr := restore_word htrace _ owner hfit digit (readPivot K b L Λ pad H record) x start hlit hread
  unfold decode
  rw [hde]
  change (if h : literal.val < q^Sᶜ.card then
    restore (fun e => active (record e).2.negative.2) digit (readPivot K b L Λ pad H record) trace
      (SmallFamilyCodec.assemble S (fun _ => pad) (finFunctionFinEquiv.symm ⟨literal.val,h⟩))
    else none) = some x
  rw [dite_eq_left literal.isLt]
  change restore _ digit _ trace
    (SmallFamilyCodec.assemble S (fun _ => pad) (finFunctionFinEquiv.symm literal)) = _
  dsimp only [literal]
  rw [Equiv.symm_apply_apply]
  exact hr

theorem activeSet_count {a : Incidence d s c} (record : Edges d s → Recorded ℓ q)
    (owner : Fin ℓ → Option (Fin c))
    (hfit : ∀ e i, i ∈ active (record e).2.negative.2 → owner i = some (a e))
    (trace : List (Edges d s)) (hn : (trace.map a).Nodup) :
    (activeSet record trace).card = (trace.map (fun e => (active (record e).2.negative.2).card)).sum := by
  induction trace with
  | nil => simp [activeSet]
  | cons e es ih =>
    rw [List.map_cons,List.nodup_cons] at hn
    have hd : Disjoint (active (record e).2.negative.2) (activeSet record es) := by
      rw [Finset.disjoint_left]
      intro i hi hj
      obtain ⟨e',he',hj⟩ := Finset.mem_biUnion.mp hj
      have he := Option.some.inj ((hfit e i hi).symm.trans (hfit e' i hj))
      exact hn.1 (List.mem_map.mpr ⟨e',List.mem_toFinset.mp he',he.symm⟩)
    have he : activeSet record (e::es) =
        active (record e).2.negative.2 ∪ activeSet record es := by
      simp [activeSet,Finset.biUnion_insert]
    rw [he,Finset.card_union_of_disjoint hd,ih hn.2,List.map_cons,List.sum_cons]

/-- The unrounded payload capacity from the reverse-peeling length
estimate, after clearing its denominator. -/
theorem capacity (K b L Λ : ℕ) (pad : Fin q) (hL : 1 ≤ L)
    (a : Incidence d s c) (trace : List (Edges d s)) (htrace : LegalTrace a Finset.univ trace ∅)
    (record : Edges d s → Recorded ℓ q) (owner : Fin ℓ → Option (Fin c))
    (hfit : ∀ e i, i ∈ active (record e).2.negative.2 → owner i = some (a e))
    (P : ℕ) (hM : ∀ e ∈ trace, P ≤ ((replayShape (record e)).members K b L Λ pad).length) :
    (radices K b L Λ pad record trace P).prod * P^d ≤ q^ℓ * 3^d := by
  let S := activeSet record trace
  let f := fun (e : Edges d s) => ((active (record e).2.negative.2).card,
    pivotRadix ((replayShape (record e)).members K b L Λ pad).length P)
  let digits := trace.map f
  have hcount : trace.length = d := by simpa using htrace.count.symm
  have hs : (digits.map Prod.fst).sum = S.card := by
    simp only [digits,List.map_map,Function.comp_def,f]
    exact (activeSet_count record owner hfit trace htrace.pivotPatches_nodup).symm
  have hcap := BubbleFamilies.payload_capacity q P digits (by
    intro p hp
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    have h := pivotRadix_capacity pad hL (replayShape (record e)) (hM e he)
    rw [replayShape_card pad (record e)] at h
    exact h)
  have hT : (digits.map Prod.snd).prod =
      (trace.map (fun e => pivotRadix ((replayShape (record e)).members K b L Λ pad).length P)).prod := by
    simp [digits,List.map_map,Function.comp_def,f]
  rw [hT,hs,show digits.length = d by simp [digits,hcount]] at hcap
  have hle : S.card ≤ ℓ := by simpa using Finset.card_le_univ S
  have hcompl : Sᶜ.card+S.card = ℓ := by
    rw [Finset.card_compl,Fintype.card_fin,Nat.sub_add_cancel hle]
  unfold radices
  rw [List.prod_cons,Nat.mul_assoc]
  calc
    _ ≤ q^Sᶜ.card * (3^d*q^S.card) := Nat.mul_le_mul_left _ hcap
    _ = q^ℓ*3^d := by rw [Nat.mul_left_comm,← Nat.pow_add,hcompl,Nat.mul_comm]

#print axioms capacity
#print axioms encode_roundtrip

end DeletionCode.Explicit.PeelingPayload
