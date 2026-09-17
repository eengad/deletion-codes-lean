import DeletionCode.EditRigidity
import Mathlib.Order.Interval.Set.Basic

/-!
Disjoint source intervals give vertex-disjoint local changes. The source
interval containing an unchanged segment, a deletion, or an insertion is
specified in source coordinates. Every surviving letter of the corresponding
output segment is proved to originate in that interval. Shared-source
rigidity then rules out common long windows between disjoint intervals.
-/
namespace DeletionCode.EditLocality

open Windows HeaderRecovery SingleEditOrigins

/-- A deletion occurs at a letter of the source interval; an insertion occurs
at one of its gaps. Unchanged words are allowed for the negative path. -/
def Inside (e : Edit) (start len : ℕ) : Prop :=
  match e with
  | .unchanged => True
  | .delete pos => start ≤ pos ∧ pos < start + len
  | .insert pos _ => start ≤ pos ∧ pos ≤ start + len

theorem local_output_bound (e : Edit) (start len n : ℕ)
    (he : Inside e start len) (hbound : start + len ≤ n) :
    start + e.outputLength len ≤ e.outputLength n := by
  cases e <;> simp only [Inside, Edit.outputLength] at he ⊢ <;> omega

/-- Surviving letters of a local output segment have source indices inside
its original interval. This is derived from the actual edit's origin map. -/
theorem origin_in_source_interval (e : Edit) (start len i r : ℕ)
    (he : Inside e start len) (hstart : start ≤ i)
    (hend : i < start + e.outputLength len) (hr : e.origin i = some r) :
    start ≤ r ∧ r < start + len := by
  cases e with
  | unchanged =>
    have hir := Option.some.inj hr
    change i < start + len at hend
    omega
  | delete pos =>
    by_cases hcut : i < pos <;>
      simp only [Inside, Edit.outputLength, Edit.origin, hcut, ite_true, ite_false,
        Option.some.injEq] at he hend hr <;> omega
  | insert pos bit =>
    change start ≤ pos ∧ pos ≤ start + len at he
    change i < start + (len + 1) at hend
    by_cases hcut : i < pos
    · have hir : i = r := by
        simpa only [Edit.origin, ite_eq_left hcut, Option.some.injEq] using hr
      omega
    · by_cases heq : i = pos
      · simp only [Edit.origin, ite_eq_right hcut, ite_eq_left heq, reduceCtorEq] at hr
      · have hir : i - 1 = r := by
          simpa only [Edit.origin, ite_eq_right hcut, ite_eq_right heq,
            Option.some.injEq] using hr
        omega

/-- No equal (L-1)-windows arise from changes in disjoint source intervals.
This includes either side of either local replacement, by using unchanged
as the edit for a path lying in the original word. -/
theorem local_windows_ne {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e f : Edit) (he : e.Valid n) (hf : f.Valid n)
    (s p t q : ℕ) (hei : Inside e s p) (hfi : Inside f t q)
    (hsp : s + p ≤ n) (htq : t + q ≤ n)
    (hdis : Disjoint (Set.Ico s (s + p)) (Set.Ico t (t + q)))
    (a b : ℕ) (ha : s ≤ a) (hb : t ≤ b)
    (haend : a + (windowLength k - 1) ≤ s + e.outputLength p)
    (hbend : b + (windowLength k - 1) ≤ t + f.outputLength q) :
    ¬ Agree (e.word x) a (f.word x) b (windowLength k - 1) := by
  intro hag
  have heout := local_output_bound e s p n hei hsp
  have hfout := local_output_bound f t q n hfi htq
  obtain ⟨offset, r, hoffset, _, horigin⟩ :=
    EditRigidity.shared_source_letters hk x hx e f he hf a b (by omega) (by omega) hag
  have hzero := horigin 0 (by omega)
  have hre := origin_in_source_interval e s p (a + offset + 0) (r + 0) hei
    (by omega) (by omega) hzero.1
  have hrf := origin_in_source_interval f t q (b + offset + 0) (r + 0) hfi
    (by omega) (by omega) hzero.2
  exact Set.disjoint_left.mp hdis hre hrf

/-- All vertices of the local output path, including its two endpoints. -/
def localVertices (e : Edit) (x : Letters) (start len L : ℕ) :
    Set (SupportComponents.Vertex L) :=
  {v | ∃ a, start ≤ a ∧ a + (L - 1) ≤ start + e.outputLength len ∧
    SpectrumPath.vertexAt (e.word x) L a = v}

theorem local_vertex_sets_disjoint {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e f : Edit) (he : e.Valid n) (hf : f.Valid n)
    (s p t q : ℕ) (hei : Inside e s p) (hfi : Inside f t q)
    (hsp : s + p ≤ n) (htq : t + q ≤ n)
    (hdis : Disjoint (Set.Ico s (s + p)) (Set.Ico t (t + q))) :
    Disjoint (localVertices e x s p (windowLength k))
      (localVertices f x t q (windowLength k)) := by
  apply Set.disjoint_left.mpr
  intro v hv hw
  obtain ⟨a, ha, haend, hva⟩ := hv
  obtain ⟨b, hb, hbend, hvb⟩ := hw
  apply local_windows_ne hk x hx e f he hf s p t q hei hfi hsp htq hdis a b ha hb haend hbend
  intro i hi
  exact congrFun (hva.trans hvb.symm) ⟨i, hi⟩

#print axioms local_output_bound
#print axioms origin_in_source_interval
#print axioms local_windows_ne
#print axioms local_vertex_sets_disjoint

end DeletionCode.EditLocality
