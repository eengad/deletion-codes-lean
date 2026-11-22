import DeletionCode.Qary.SpectrumPath
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The finite-field spectrum in manuscript `d:field-path`. -/

namespace DeletionCode.Explicit

open Qary.Windows Qary.SignedSupport Qary.SpectrumPath
open scoped BigOperators

/-- Count the valid occurrences of a gram directly in the prime field. -/
def fieldSpectrum {α : Type*} [DecidableEq α] (word : Letters α) (n L : ℕ)
    (g : Gram α L) : ZMod 3 :=
  ∑ i : Fin (n + 1), if i.val + L ≤ n ∧ gram word L i.val = g then 1 else 0

theorem fieldSpectrum_eq_cast {α : Type*} [DecidableEq α] (word : Letters α) (n L : ℕ)
    (g : Gram α L) : fieldSpectrum word n L g = (wordSpectrum word n L g : ZMod 3) := by
  classical
  unfold fieldSpectrum wordSpectrum
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

private theorem spectrum_nonnegative {α : Type*} (word : Letters α) (n L : ℕ) (g : Gram α L) :
    0 ≤ wordSpectrum word n L g := by
  classical
  unfold wordSpectrum
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> decide

/-- Summing over grams counts the same set of valid positions for every word. -/
private theorem total_spectrum {α : Type*} [Fintype α] (word : Letters α) (n L : ℕ) :
    ∑ g, wordSpectrum word n L g = ∑ i : Fin (n + 1), if i.val + L ≤ n then (1 : ℤ) else 0 := by
  classical
  unfold wordSpectrum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val + L ≤ n <;> simp [hi]

/-- A word with unique `(L−1)`-windows is determined among all words of the
same length by its mod-three spectrum. Uniqueness is required only of `x`. -/
theorem field_path {α : Type*} [Fintype α] [DecidableEq α] (x z : Letters α) (n L : ℕ)
    (hL : 1 ≤ L) (hn : L ≤ n) (hu : KUnique x n (L - 1))
    (h : fieldSpectrum z n L = fieldSpectrum x n L) : Agree z 0 x 0 n := by
  classical
  apply equal_spectrum_recovers_word x z n L hL hn hu
  have le_each (g : Gram α L) : wordSpectrum x n L g ≤ wordSpectrum z n L g := by
    have hnon := spectrum_nonnegative z n L g
    rcases spectrum_boolean x n L hu g with hx | hx
    · simpa only [hx] using hnon
    · have hcast := congrFun h g
      rw [fieldSpectrum_eq_cast, fieldSpectrum_eq_cast, hx] at hcast
      have hz : wordSpectrum z n L g ≠ 0 := by
        intro hz
        rw [hz] at hcast
        exact (by decide : ¬ ((0 : ℤ) : ZMod 3) = ((1 : ℤ) : ZMod 3)) hcast
      omega
  have htotal := (total_spectrum x n L).trans (total_spectrum z n L).symm
  funext g
  by_contra hne
  have hlt : wordSpectrum x n L g < wordSpectrum z n L g := lt_of_le_of_ne (le_each g) (Ne.symm hne)
  have hsum := Finset.sum_lt_sum (s := Finset.univ) (fun i _ => le_each i)
    ⟨g, Finset.mem_univ _, hlt⟩
  exact (ne_of_lt hsum) htotal

/-- The list-word version reads only in-bounds windows. The supplied alphabet
symbol makes the existing total letter-sequence interface executable. -/
def listFieldSpectrum {α : Type*} [DecidableEq α] (pad : α) (w : List α) (L : ℕ) :=
  fieldSpectrum (fun i => w.getD i pad) w.length L

theorem field_path_list {α : Type*} [Fintype α] [DecidableEq α]
    (pad : α) (x z : List α) (L : ℕ) (hlen : z.length = x.length)
    (hL : 1 ≤ L) (hn : L ≤ x.length)
    (hu : KUnique (fun i => x.getD i pad) x.length (L - 1))
    (h : listFieldSpectrum pad z L = listFieldSpectrum pad x L) : z = x := by
  unfold listFieldSpectrum at h
  rw [hlen] at h
  have hagree := field_path (fun i => x.getD i pad) (fun i => z.getD i pad) x.length L hL hn hu h
  apply List.ext_getElem hlen
  intro i hz hx
  simpa only [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hz,
    List.getElem?_eq_getElem hx, Option.getD_some] using hagree i hx

#print axioms field_path_list

#print axioms field_path

end DeletionCode.Explicit
