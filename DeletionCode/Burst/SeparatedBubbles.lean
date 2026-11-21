import DeletionCode.Burst.SeparatedTransport
import DeletionCode.Burst.Relocation
import DeletionCode.Burst.LocalDisjoint
import Mathlib.Algebra.BigOperators.Pi

/-!
Separated chronological histories yield actual disjoint source bubbles. Their
local words also occur around each chronological edit, so exact telescoping
gives the full spectrum identity and, for equal endpoint lengths, balance.
-/
namespace DeletionCode.Burst

open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords
open DeletionCode.Qary.SignedSupport
open scoped BigOperators

variable {α : Type*} [Inhabited α]

structure SourcePackets (α : Type*) [Inhabited α] (k b : ℕ)
    (source : Word α) (es : List (Edit α)) where
  packet : (i : Fin es.length) → LocalBubble α k b source
    ((originalEdit es i).apply source) (originalPosition es i)
  removed : ∀ i, (packet i).bubble.removed = (originalEdit es i).sourceBlock source
  replacement : ∀ i, (packet i).bubble.replacement = (es.get i).replacement

theorem exists_sourcePackets {k b t : ℕ} {x y : Word α} {es : List (Edit α)}
    (hk : 1 ≤ k) (hx : KUnique (listLetters x) x.length k)
    (h : Executes b x es y) (hlen : es.length ≤ 2 * t)
    (hsep : Separated x.length (8 * (windowLength k b + t * b)) es) :
    Nonempty (SourcePackets α k b x es) := by
  classical
  have hL : b ≤ windowLength k b := by unfold windowLength; omega
  have hex (i : Fin es.length) := exists_localBubble hk (originalEdit es i) x
    (originalEdit_valid h hlen hsep (by unfold windowLength; omega) hL i) hx
    (originalPosition_margins h hlen hsep hL i).1
    (originalPosition_margins h hlen hsep hL i).2
  choose packets hremoved hreplacement using hex
  exact ⟨⟨packets, hremoved, hreplacement⟩⟩

omit [Inhabited α] in
theorem run_take_succ (x : Word α) (es : List (Edit α)) (i : Fin es.length) :
    run x (es.take (i.val + 1)) = (es.get i).apply (run x (es.take i.val)) := by
  rw [List.take_succ_eq_append_getElem i.isLt, run_append]
  rfl

omit [Inhabited α] in
theorem history_telescope {b : ℕ} {x y : Word α} {es : List (Edit α)}
    (h : Executes b x es y) (F : Word α → ℤ) :
    F y - F x = ∑ i : Fin es.length,
      (F ((es.get i).apply (run x (es.take i.val))) - F (run x (es.take i.val))) := by
  have ht : F y - F x = ∑ i : Fin es.length,
      (F (run x (es.take (i.val + 1))) - F (run x (es.take i.val))) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun i => F (run x (es.take (i + 1))) - F (run x (es.take i))) es.length]
    simpa only [List.take_length, List.take_zero, run, h.run_eq] using
      (Finset.sum_range_sub (fun i => F (run x (es.take i))) es.length).symm
  simpa only [run_take_succ] using ht

namespace SourcePackets

variable {k b t : ℕ} {x y : Word α} {es : List (Edit α)}

theorem chronological_packet (p : SourcePackets α k b x es)
    (h : Executes b x es y) (hlen : es.length ≤ 2 * t)
    (hsep : Separated x.length (8 * (windowLength k b + t * b)) es)
    (i : Fin es.length) :
    ∃ q : LocalBubble α k b (run x (es.take i.val))
      ((es.get i).apply (run x (es.take i.val))) (es.get i).pos,
      q.bubble = (p.packet i).bubble := by
  have hL : 1 ≤ windowLength k b := by unfold windowLength; omega
  have hbL : b ≤ windowLength k b := by unfold windowLength; omega
  have hv := originalEdit_valid h hlen hsep hL hbL i
  have hs := originalPosition_margins h hlen hsep hbL i
  have hc := chronologicalPosition_margins h hlen hsep hbL i
  apply (p.packet i).relocate (run x (es.take i.val)) (es.get i)
  · rw [p.removed i, Edit.sourceBlock_length _ _ hv.2.1]
    rfl
  · exact p.replacement i
  · omega
  · omega
  · omega
  · exact separated_prefix_agree h hlen hsep hL hbL i

theorem spectrum_sum (p : SourcePackets α k b x es)
    (h : Executes b x es y) (hlen : es.length ≤ 2 * t)
    (hsep : Separated x.length (8 * (windowLength k b + t * b)) es) :
    wordSpectrum (listLetters y) y.length (windowLength k b) -
      wordSpectrum (listLetters x) x.length (windowLength k b) =
      ∑ i : Fin es.length,
        (wordSpectrum (listLetters (p.packet i).bubble.positiveWord)
          (p.packet i).bubble.positiveWord.length (windowLength k b) -
        wordSpectrum (listLetters (p.packet i).bubble.negativeWord)
          (p.packet i).bubble.negativeWord.length (windowLength k b)) := by
  classical
  funext g
  simp only [Pi.sub_apply, Finset.sum_apply]
  rw [history_telescope h (fun word => wordSpectrum (listLetters word) word.length
    (windowLength k b) g)]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨q, hq⟩ := p.chronological_packet h hlen hsep i
  have hd := q.spectrum_delta g
  simpa only [hq] using hd

theorem balanced (p : SourcePackets α k b x es)
    (h : Executes b x es y) (hlen : es.length ≤ 2 * t)
    (hsep : Separated x.length (8 * (windowLength k b + t * b)) es)
    (hxy : x.length = y.length) :
    (∑ i : Fin es.length, (p.packet i).bubble.negativeWord.length) =
      ∑ i : Fin es.length, (p.packet i).bubble.positiveWord.length := by
  have hd := history_telescope h (fun word => (word.length : ℤ))
  have hstep (i : Fin es.length) :
      (((es.get i).apply (run x (es.take i.val))).length : ℤ) -
        (run x (es.take i.val)).length =
      ((p.packet i).bubble.positiveWord.length : ℤ) - (p.packet i).bubble.negativeWord.length := by
    obtain ⟨q, hq⟩ := p.chronological_packet h hlen hsep i
    have hs := congrArg (fun n : ℕ => (n : ℤ)) q.toLocalContext.source_length
    have ht := congrArg (fun n : ℕ => (n : ℤ)) q.toLocalContext.target_length
    simp only [Nat.cast_add, hq] at hs ht
    omega
  simp_rw [hstep] at hd
  rw [← hxy, sub_self, Finset.sum_sub_distrib] at hd
  have heq : (∑ i : Fin es.length, ((p.packet i).bubble.negativeWord.length : ℤ)) =
      ∑ i : Fin es.length, ((p.packet i).bubble.positiveWord.length : ℤ) := by omega
  exact_mod_cast heq

theorem separated_windows (p : SourcePackets α k b x es)
    (hk : 1 ≤ k) (hx : KUnique (listLetters x) x.length k)
    (h : Executes b x es y) (hlen : es.length ≤ 2 * t)
    (hsep : Separated x.length (8 * (windowLength k b + t * b)) es)
    (i j : Fin es.length) (hne : i ≠ j) (side₁ side₂ : Bool) (a c : ℕ)
    (ha : a + (windowLength k b - 1) ≤ ((p.packet i).pathWord side₁).length)
    (hc : c + (windowLength k b - 1) ≤ ((p.packet j).pathWord side₂).length) :
    ¬ Agree (listLetters ((p.packet i).pathWord side₁)) a
      (listLetters ((p.packet j).pathWord side₂)) c (windowLength k b - 1) := by
  apply LocalBubble.windows_ne_of_separation hk hx (p.packet i) (p.packet j) ?_ side₁ side₂ a c ha hc
  have hh := originalPositions_separated h hlen hsep i j hne
  have hLb : b ≤ windowLength k b := by unfold windowLength; omega
  omega

end SourcePackets

#print axioms exists_sourcePackets
#print axioms SourcePackets.spectrum_sum
#print axioms SourcePackets.balanced
#print axioms SourcePackets.separated_windows

end DeletionCode.Burst
