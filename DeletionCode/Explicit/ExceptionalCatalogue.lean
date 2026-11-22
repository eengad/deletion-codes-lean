import DeletionCode.Explicit.ExceptionalLocality
import DeletionCode.Explicit.ExceptionalRecordCount
import Mathlib.Data.List.FinRange

/-! The assignment catalogue for exceptional chronological records,
`d:exceptions` and `d:exception-mean`. -/
namespace DeletionCode.Explicit.ExceptionalWeight

open Burst FieldHash Qary.SignedSupport
open scoped BigOperators

variable {ℓ q n L b t K θ : ℕ}

def supportList (s : Finset (Fin ℓ)) : List (Fin ℓ) :=
  (List.finRange ℓ).filter (· ∈ s)

@[simp] theorem mem_supportList {s : Finset (Fin ℓ)} {i : Fin ℓ} :
    i ∈ supportList s ↔ i ∈ s := by simp [supportList, List.mem_finRange]

@[simp] theorem supportList_length (s : Finset (Fin ℓ)) : (supportList s).length = s.card := by
  have h : (supportList s).toFinset = s := by ext; simp
  calc
    (supportList s).length = (supportList s).toFinset.card :=
      (List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)).symm
    _ = s.card := congrArg Finset.card h

def representative (pad : Fin q) (s : Finset (Fin ℓ)) (letters : QWord q) (i : Fin ℓ) : Fin q :=
  letters.getD ((supportList s).idxOf i) pad

def prescribe (pad : Fin q) (s : Finset (Fin ℓ)) (letters : QWord q) :
    CoreWeight.Assignment ℓ q :=
  ⟨s, fun i => representative pad s letters i.val⟩

theorem representative_agrees (pad : Fin q) (s : Finset (Fin ℓ)) (x : Fin ℓ → Fin q)
    {i : Fin ℓ} (hi : i ∈ s) :
    representative pad s ((supportList s).map x) i = x i := by
  have hm : i ∈ supportList s := mem_supportList.mpr hi
  simp only [representative, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_idxOf hm, Option.map_some, Option.getD_some]

def validEdit (b : ℕ) (e : Edit (Fin q)) (w : QWord q) : Bool :=
  decide (e.removed ≤ b) && (decide (e.replacement.length ≤ b) &&
    (decide (e.pos + e.removed ≤ w.length) && !decide (e.sourceBlock w = e.replacement)))

theorem validEdit_iff (b : ℕ) (e : Edit (Fin q)) (w : QWord q) :
    validEdit b e w = true ↔ e.Valid b w := by
  simp [validEdit, Edit.Valid, Edit.Bounded, Edit.InBounds, and_assoc]

def validRun (b : ℕ) (w : QWord q) : List (Edit (Fin q)) → Option (QWord q)
  | [] => some w
  | e :: es => if validEdit b e w then validRun b (e.apply w) es else none

theorem validRun_iff {w z : QWord q} {es : List (Edit (Fin q))} :
    validRun b w es = some z ↔ Executes b w es z := by
  induction es generalizing w with
  | nil =>
    simp only [validRun, Option.some.injEq]
    exact ⟨fun h => h ▸ .nil w, fun h => by cases h; rfl⟩
  | cons e es ih =>
    simp only [validRun]
    split
    · rename_i h
      exact ⟨fun he => .cons ((validEdit_iff ..).mp h) (ih.mp he),
        fun he => by cases he with | cons hv ht => exact ih.mpr ht⟩
    · rename_i h
      exact ⟨fun hn => by contradiction, fun he => by
        cases he with | cons hv ht => exact False.elim (h ((validEdit_iff ..).mpr hv))⟩

def entry? (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L) (b : ℕ)
    (es : List (Edit (Fin q))) (s : Finset (Fin ℓ)) (letters : QWord q) :
    Option (Entry ℓ q n) :=
  let a := prescribe pad s letters
  let w := List.ofFn (representative pad s letters)
  (validRun b w es).bind fun z =>
    let ξ := delta pad cols w z
    if h : z.length = ℓ ∧ ξ ≠ 0 then some ⟨a, ξ, h.2⟩ else none

def catalogueFor (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L) (b : ℕ)
    (ℓ : ℕ) (es : List (Edit (Fin q))) : List (Entry ℓ q n) :=
  let s := touched L (initialTokens ℓ q) es
  (wordsOfLength q (supportList s).length).filterMap (entry? pad cols b es s)

def catalogue (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L) (b t ℓ : ℕ) :
    List (Entry ℓ q n) :=
  (chronological q b t L ℓ).flatMap (catalogueFor pad cols b ℓ)

def family (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L) (b t ℓ : ℕ)
    (i : Fin (catalogue pad cols b t ℓ).length) : Entry ℓ q n :=
  (catalogue pad cols b t ℓ)[i]

private theorem entry_support {pad : Fin q} {cols : Fin n ≃ Gram (Fin q) L}
    {es : List (Edit (Fin q))} {s : Finset (Fin ℓ)} {letters : QWord q}
    {E : Entry ℓ q n} (h : entry? pad cols b es s letters = some E) :
    E.assignment.support = s := by
  unfold entry? at h
  dsimp only at h
  cases hrun : validRun b (List.ofFn (representative pad s letters)) es with
  | none => simp [hrun] at h
  | some z =>
    simp only [hrun, Option.bind_some] at h
    split at h
    · cases h
      rfl
    · contradiction

private theorem mem_catalogueFor_support {pad : Fin q} {cols : Fin n ≃ Gram (Fin q) L}
    {es : List (Edit (Fin q))} {E : Entry ℓ q n} (h : E ∈ catalogueFor pad cols b ℓ es) :
    E.assignment.support = touched L (initialTokens ℓ q) es := by
  obtain ⟨letters, _, he⟩ := List.mem_filterMap.mp h
  exact entry_support he

theorem catalogue_support_le {pad : Fin q} {cols : Fin n ≃ Gram (Fin q) L}
    {E : Entry ℓ q n} (h : E ∈ catalogue pad cols b t ℓ) :
    E.assignment.support.card ≤ (2*t)*(2*L+b) := by
  obtain ⟨es, hes, hE⟩ := List.mem_flatMap.mp h
  obtain ⟨_, hlen, _, hbounded⟩ := mem_chronological.mp hes
  rw [mem_catalogueFor_support hE]
  exact (touched_card_le L b _ es (fun e he => (hbounded e he).2.1)).trans
    (Nat.mul_le_mul_right _ hlen)

theorem catalogue_covers (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L) (hL : 0 < L)
    (x : Fin ℓ → Fin q) (z : QWord q) (hz : z.length = ℓ)
    (h : Burst.Exceptional b t ℓ (8*(L+t*b)) (List.ofFn x) z)
    (hd : delta pad cols (List.ofFn x) z ≠ 0) :
    ∃ j, CoreWeight.Matches (family pad cols b t ℓ j).assignment x ∧
        (family pad cols b t ℓ j).changeVector = delta pad cols (List.ofFn x) z := by
  have hne : z ≠ List.ofFn x := fun he => hd (by simp [he, delta])
  obtain ⟨es, hex, hlen, hbad⟩ := h
  have hs : es ∈ chronological q b t L ℓ := by
    apply mem_chronological.mpr
    refine ⟨?_, hlen, hbad, ?_⟩
    · cases es with
      | nil => cases hex; exact (hne rfl).elim
      | cons => simp
    · intro e he
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
      have hpos := hex.position_le ⟨i,hi⟩
      have hb := (hex.get_valid ⟨i,hi⟩).1
      have hi' := Nat.mul_le_mul_right b (show i ≤ 2*t by omega)
      simp only [List.length_ofFn, List.get_eq_getElem] at hpos hb
      exact ⟨by omega, hb⟩
  let s := touched L (initialTokens ℓ q) es
  let letters := (supportList s).map x
  let y := representative pad s letters
  let v := List.ofFn y
  have hy (i : Fin ℓ) (hi : i ∈ s) : x i = y i := (representative_agrees pad s x hi).symm
  have he := transfer_record pad cols hL (ws := initialTokens ℓ q)
    (y := y) (by simpa only [spell_initial] using hex) hy
  rw [spell_initial, spell_initial] at he
  obtain ⟨hrun, hlay, hdelta⟩ := he
  let z' := run v es
  have hdz : delta pad cols v z' ≠ 0 := fun hzero => hd (hdelta.trans hzero)
  have hs' : z'.length = ℓ := hlay.symm.trans hz
  let E : Entry ℓ q n := ⟨prescribe pad s letters, delta pad cols v z', hdz⟩
  have hm : E ∈ catalogue pad cols b t ℓ := by
    apply List.mem_flatMap.mpr
    refine ⟨es, hs, ?_⟩
    change E ∈ (wordsOfLength q (supportList s).length).filterMap (entry? pad cols b es s)
    apply List.mem_filterMap.mpr
    refine ⟨letters, mem_wordsOfLength.mpr (List.length_map _), ?_⟩
    have hrun' : validRun b v es = some z' := validRun_iff.mpr hrun
    unfold entry?
    change (validRun b v es).bind _ = _
    rw [hrun']
    simp only [Option.bind_some]
    rw [dite_eq_left (show z'.length = ℓ ∧ delta pad cols v z' ≠ 0 from ⟨hs', hdz⟩)]
  obtain ⟨i, hi, hE⟩ := List.mem_iff_getElem.mp hm
  refine ⟨⟨i,hi⟩, ?_, ?_⟩
  · change CoreWeight.Matches ((catalogue pad cols b t ℓ)[i]).assignment x
    rw [hE]
    exact fun j => hy j.val j.property
  · change ((catalogue pad cols b t ℓ)[i]).changeVector = _
    rw [hE]
    exact hdelta.symm

theorem catalogue_weight_pos (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L) (hL : L ≤ ℓ)
    (hK : K < L) (H : TernaryMatrix θ n) {x : Fin ℓ → Fin q}
    (hx : Exceptional pad cols H b t K x) :
    0 < weight (family pad cols b t ℓ) H x := by
  obtain ⟨hu, z, hz, hn, hr, hh⟩ := hx
  have hlen : z.length = (List.ofFn x).length := hz.trans List.length_ofFn.symm
  have hu' : Qary.Windows.KUnique (fun i => (List.ofFn x).getD i pad) (List.ofFn x).length K := by
    rwa [List.length_ofFn]
  have hd := delta_ne_zero pad cols hlen (by omega) (by simpa) hK hu' hn
  obtain ⟨i, hi, hδ⟩ := catalogue_covers pad cols (by omega) x z hz hr hd
  apply (CoreWeight.weight_pos_iff _ _ _).mpr
  refine ⟨i, ((family pad cols b t ℓ i).kept_iff H).mpr ?_, hi⟩
  rw [hδ, delta, Matrix.mulVec_sub, hh, sub_self]

private theorem per_record_mass_le (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L)
    (hq : 0 < q) (es : List (Edit (Fin q))) :
    ((catalogueFor pad cols b ℓ es).map
      (fun E => (1 : ℚ)/(q : ℚ)^E.assignment.support.card)).sum ≤ 1 := by
  let s := touched L (initialTokens ℓ q) es
  let c : ℚ := 1/(q : ℚ)^s.card
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let xs := catalogueFor pad cols b ℓ es
  have hlen : xs.length ≤ q^s.card := by
    unfold xs catalogueFor
    exact (List.length_filterMap_le ..).trans_eq (by rw [length_wordsOfLength, supportList_length])
  have hsum : (xs.map (fun E => (1 : ℚ)/(q : ℚ)^E.assignment.support.card)).sum ≤
      (xs.length : ℚ) * c := by
    simpa [nsmul_eq_mul] using (List.sum_le_length_nsmul
      (xs.map (fun E => (1 : ℚ)/(q : ℚ)^E.assignment.support.card)) c
      (fun u hu => by
        obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hu
        rw [mem_catalogueFor_support hE]))
  apply hsum.trans
  have hh : (xs.length : ℚ) ≤ (q : ℚ)^s.card := by exact_mod_cast hlen
  exact (mul_le_mul_of_nonneg_right hh hc).trans_eq (by
    simp only [c, mul_one_div]
    exact div_self (pow_ne_zero _ (by exact_mod_cast hq.ne')))

private theorem sum_map_flatMap {α β : Type*} (xs : List α) (f : α → List β) (g : β → ℚ) :
    ((xs.flatMap f).map g).sum = (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih, List.sum_append]

theorem catalogue_assignment_mass_le (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L)
    (hq : 2 ≤ q) (hL : 1 ≤ L) (hℓ : 2*t*b+1 ≤ ℓ) :
    (∑ i, (1 : ℚ)/(q : ℚ)^(family pad cols b t ℓ i).assignment.support.card) ≤
      (recordConstant b (2*t) t : ℚ) * (q : ℚ)^(b*(2*t)) * L * (ℓ : ℚ)^(2*t-1) := by
  rw [← List.sum_ofFn]
  have he : List.ofFn (fun i => (1 : ℚ)/(q : ℚ)^(family pad cols b t ℓ i).assignment.support.card) =
      (catalogue pad cols b t ℓ).map (fun E => (1 : ℚ)/(q : ℚ)^E.assignment.support.card) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_ofFn, List.getElem_map, family, Fin.getElem_fin]
  rw [he, catalogue, sum_map_flatMap]
  have hsum := List.sum_le_length_nsmul ((chronological q b t L ℓ).map fun es =>
      ((catalogueFor pad cols b ℓ es).map fun E => (1 : ℚ)/(q : ℚ)^E.assignment.support.card).sum)
    1 (by
      intro u hu
      obtain ⟨es, _, rfl⟩ := List.mem_map.mp hu
      exact per_record_mass_le pad cols (by omega) es)
  simp only [List.length_map, nsmul_eq_mul, mul_one] at hsum
  exact hsum.trans (by exact_mod_cast chronological_length_le hq hL hℓ)

theorem catalogue_uniform_mean (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L)
    (hq : 2 ≤ q) (hL : 1 ≤ L) (hℓ : 2*t*b+1 ≤ ℓ) :
    BucketBalance.completionMean (BucketBalance.freeHash θ n)
      (rootMass (family pad cols b t ℓ)) ≤
      (recordConstant b (2*t) t : ℚ) * (q : ℚ)^(b*(2*t)) * L * (ℓ : ℚ)^(2*t-1) / (3 : ℚ)^θ :=
  uniform_mean_le _ (catalogue_assignment_mass_le pad cols hq hL hℓ)

#print axioms catalogue_support_le
#print axioms catalogue_covers
#print axioms catalogue_weight_pos
#print axioms catalogue_uniform_mean

end DeletionCode.Explicit.ExceptionalWeight
