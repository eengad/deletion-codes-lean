import DeletionCode.Burst.SeparatedBubbles
import DeletionCode.Explicit.Borrowed.Relocation
import DeletionCode.Explicit.Borrowed.LocalDisjoint

/-!
Separated chronological histories yield actual disjoint source bubbles. Their
local words also occur around each chronological edit, so exact telescoping
gives the full spectrum identity and, for equal endpoint lengths, balance.
-/
namespace DeletionCode.Explicit.Borrowed

open DeletionCode.Burst
open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords
open DeletionCode.Qary.SignedSupport
open scoped BigOperators

variable {α : Type*} [Inhabited α]

structure SourcePackets (α : Type*) [Inhabited α] (K b L : ℕ)
    (source : Word α) (es : List (Edit α)) where
  packet : (i : Fin es.length) → LocalBubble α K b L source
    ((originalEdit es i).apply source) (originalPosition es i)
  removed : ∀ i, (packet i).bubble.removed = (originalEdit es i).sourceBlock source
  replacement : ∀ i, (packet i).bubble.replacement = (es.get i).replacement

theorem exists_sourcePackets {K b L t : ℕ} {x y : Word α} {es : List (Edit α)}
    (hk : 1 ≤ K) (hwindow : 3 * (K + b + 1) ≤ L)
    (hx : KUnique (listLetters x) x.length K)
    (h : Executes b x es y) (hlen : es.length ≤ 2 * t)
    (hsep : Separated x.length (8 * (L + t * b)) es) :
    Nonempty (SourcePackets α K b L x es) := by
  classical
  have hbL : b ≤ L := by omega
  have hex (i : Fin es.length) := exists_localBubble hk hwindow (originalEdit es i) x
    (originalEdit_valid h hlen hsep (by omega) hbL i) hx
    (originalPosition_margins h hlen hsep hbL i).1
    (originalPosition_margins h hlen hsep hbL i).2
  choose packets hremoved hreplacement using hex
  exact ⟨⟨packets, hremoved, hreplacement⟩⟩

namespace SourcePackets

variable {K b L t : ℕ} {x y : Word α} {es : List (Edit α)}

theorem chronological_packet (p : SourcePackets α K b L x es)
    (hwindow : 3 * (K + b + 1) ≤ L)
    (h : Executes b x es y) (hlen : es.length ≤ 2 * t)
    (hsep : Separated x.length (8 * (L + t * b)) es)
    (i : Fin es.length) :
    ∃ q : LocalBubble α K b L (run x (es.take i.val))
      ((es.get i).apply (run x (es.take i.val))) (es.get i).pos,
      q.bubble = (p.packet i).bubble := by
  have hL : 1 ≤ L := by omega
  have hbL : b ≤ L := by omega
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

theorem spectrum_sum (p : SourcePackets α K b L x es)
    (hwindow : 3 * (K + b + 1) ≤ L)
    (h : Executes b x es y) (hlen : es.length ≤ 2 * t)
    (hsep : Separated x.length (8 * (L + t * b)) es) :
    wordSpectrum (listLetters y) y.length L -
      wordSpectrum (listLetters x) x.length L =
      ∑ i : Fin es.length,
        (wordSpectrum (listLetters (p.packet i).bubble.positiveWord)
          (p.packet i).bubble.positiveWord.length L -
        wordSpectrum (listLetters (p.packet i).bubble.negativeWord)
          (p.packet i).bubble.negativeWord.length L) := by
  classical
  funext g
  simp only [Pi.sub_apply, Finset.sum_apply]
  rw [history_telescope h (fun word => wordSpectrum (listLetters word) word.length
    L g)]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨q, hq⟩ := p.chronological_packet hwindow h hlen hsep i
  have hd := q.spectrum_delta hwindow g
  simpa only [hq] using hd

theorem balanced (p : SourcePackets α K b L x es)
    (hwindow : 3 * (K + b + 1) ≤ L)
    (h : Executes b x es y) (hlen : es.length ≤ 2 * t)
    (hsep : Separated x.length (8 * (L + t * b)) es)
    (hxy : x.length = y.length) :
    (∑ i : Fin es.length, (p.packet i).bubble.negativeWord.length) =
      ∑ i : Fin es.length, (p.packet i).bubble.positiveWord.length := by
  have hd := history_telescope h (fun word => (word.length : ℤ))
  have hstep (i : Fin es.length) :
      (((es.get i).apply (run x (es.take i.val))).length : ℤ) -
        (run x (es.take i.val)).length =
      ((p.packet i).bubble.positiveWord.length : ℤ) - (p.packet i).bubble.negativeWord.length := by
    obtain ⟨q, hq⟩ := p.chronological_packet hwindow h hlen hsep i
    have hs := congrArg (fun n : ℕ => (n : ℤ)) q.toLocalContext.source_length
    have ht := congrArg (fun n : ℕ => (n : ℤ)) q.toLocalContext.target_length
    simp only [Nat.cast_add, hq] at hs ht
    omega
  simp_rw [hstep] at hd
  rw [← hxy, sub_self, Finset.sum_sub_distrib] at hd
  have heq : (∑ i : Fin es.length, ((p.packet i).bubble.negativeWord.length : ℤ)) =
      ∑ i : Fin es.length, ((p.packet i).bubble.positiveWord.length : ℤ) := by omega
  exact_mod_cast heq

theorem separated_windows (p : SourcePackets α K b L x es)
    (hk : 1 ≤ K) (hwindow : 3 * (K + b + 1) ≤ L)
    (hx : KUnique (listLetters x) x.length K)
    (h : Executes b x es y) (hlen : es.length ≤ 2 * t)
    (hsep : Separated x.length (8 * (L + t * b)) es)
    (i j : Fin es.length) (hne : i ≠ j) (side₁ side₂ : Bool) (a c : ℕ)
    (ha : a + (L - 1) ≤ ((p.packet i).pathWord side₁).length)
    (hc : c + (L - 1) ≤ ((p.packet j).pathWord side₂).length) :
    ¬ Agree (listLetters ((p.packet i).pathWord side₁)) a
      (listLetters ((p.packet j).pathWord side₂)) c (L - 1) := by
  apply LocalBubble.windows_ne_of_separation hk hwindow hx (p.packet i) (p.packet j) ?_ side₁ side₂ a c ha hc
  have hh := originalPositions_separated h hlen hsep i j hne
  have hLb : b ≤ L := by omega
  omega

end SourcePackets

#print axioms exists_sourcePackets
#print axioms SourcePackets.spectrum_sum
#print axioms SourcePackets.balanced
#print axioms SourcePackets.separated_windows

end DeletionCode.Explicit.Borrowed
