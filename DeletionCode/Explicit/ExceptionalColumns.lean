import DeletionCode.Explicit.ExceptionalCatalogue

/-! The executable lexicographic gram indexing used by the exceptional
catalogue's row-major serialization. -/
namespace DeletionCode.Explicit.ExceptionalWeight

open Qary.SignedSupport
open scoped BigOperators

def dictionaryGram (q L : ℕ) (i : Fin (q^L)) : Gram (Fin q) L :=
  let w := (wordsOfLength q L)[i.val]'(by rw [length_wordsOfLength]; exact i.isLt)
  fun j => w[j.val]'(by rw [mem_wordsOfLength.mp (List.getElem_mem _)]; exact j.isLt)

private theorem dictionary_spelling (q L : ℕ) (i : Fin (q^L)) :
    List.ofFn (dictionaryGram q L i) =
      (wordsOfLength q L)[i.val]'(by rw [length_wordsOfLength]; exact i.isLt) := by
  apply List.ext_getElem
  · rw [List.length_ofFn, mem_wordsOfLength.mp (List.getElem_mem _)]
  · intro j hj hj'
    simp only [dictionaryGram, List.getElem_ofFn]

/-- Lexicographic order of the columns is the order of `wordsOfLength`. -/
def dictionary (q L : ℕ) : Fin (q^L) ≃ Gram (Fin q) L where
  toFun := dictionaryGram q L
  invFun g := ⟨(wordsOfLength q L).idxOf (List.ofFn g), by
    rw [← length_wordsOfLength]
    exact List.idxOf_lt_length_iff.mpr (mem_wordsOfLength.mpr List.length_ofFn)⟩
  left_inv i := by
    apply Fin.ext
    simp only [dictionary_spelling]
    exact (WeightedAddress.words_nodup q L).idxOf_getElem _ _
  right_inv g := by
    have hmem : List.ofFn g ∈ wordsOfLength q L := mem_wordsOfLength.mpr List.length_ofFn
    have he := dictionary_spelling q L ⟨(wordsOfLength q L).idxOf (List.ofFn g), by
      rw [← length_wordsOfLength]; exact List.idxOf_lt_length_iff.mpr hmem⟩
    rw [List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hmem)] at he
    exact List.ofFn_inj.mp he

theorem dictionary_at (q L : ℕ) (i : Fin (q^L)) :
    List.ofFn (dictionary q L i) =
      (wordsOfLength q L)[i.val]'(by rw [length_wordsOfLength]; exact i.isLt) :=
  dictionary_spelling q L i

/-- Compare a supplied gram with every in-bounds starting position. -/
def gramCount (w gs : QWord q) : ℕ :=
  (List.range (w.length+1)).countP fun i =>
    decide (i+gs.length ≤ w.length) && ((w.drop i).take gs.length == gs)

theorem gramCount_field (pad : Fin q) (w : QWord q) (L : ℕ) (g : Gram (Fin q) L) :
    (gramCount w (List.ofFn g) : ZMod 3) = listFieldSpectrum pad w L g := by
  have hw (i : ℕ) (hi : i+L ≤ w.length) :
      (w.drop i).take L = List.ofFn g ↔ gram (fun k => w.getD k pad) L i = g := by
    constructor
    · intro h
      funext j
      have hj : j.val < ((w.drop i).take L).length := by
        simp [List.length_take, List.length_drop]; have := j.isLt; omega
      have hk : i+j.val < w.length := by have := j.isLt; omega
      have he := congrArg (fun xs : QWord q => xs[j.val]?) h
      rw [List.getElem?_take_of_lt j.isLt, List.getElem?_drop, List.getElem?_eq_getElem hk,
        List.getElem?_eq_getElem (by simpa using j.isLt), List.getElem_ofFn] at he
      simpa [gram, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using he
    · intro h
      apply List.ext_getElem
      · simp [List.length_take, List.length_drop]; omega
      · intro j hj hgj
        have hjL : j < L := by simpa using hgj
        have hk : i+j < w.length := by omega
        have he := congrFun h ⟨j,hjL⟩
        simpa [gram, List.getElem_ofFn, List.getElem_take, List.getElem_drop,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using he
  unfold gramCount listFieldSpectrum fieldSpectrum
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    if i+L ≤ w.length ∧ gram (fun k => w.getD k pad) L i = g then (1 : ZMod 3) else 0)]
  have hcount : (List.range (w.length+1)).countP (fun i =>
      decide (i+(List.ofFn g).length ≤ w.length) &&
        ((w.drop i).take (List.ofFn g).length == List.ofFn g)) =
      ∑ i ∈ Finset.range (w.length+1),
        if i+L ≤ w.length ∧ gram (fun k => w.getD k pad) L i = g then 1 else 0 := by
    have hn (i : ℕ) :
        (decide (i+(List.ofFn g).length ≤ w.length) &&
          ((w.drop i).take (List.ofFn g).length == List.ofFn g)) =
        decide (i+L ≤ w.length ∧ gram (fun k => w.getD k pad) L i = g) := by
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_ofFn, beq_iff_eq]
      exact and_congr_right (hw i)
    simp_rw [hn]
    rw [List.countP_eq_length_filter, Finset.sum_boole]
    rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
    apply congrArg Finset.card
    ext i
    simp
  simpa only [hcount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

#print axioms dictionary_at
#print axioms gramCount_field

end DeletionCode.Explicit.ExceptionalWeight
