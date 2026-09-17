import DeletionCode.AnchorRecords
import DeletionCode.TaggedAnchorCount
import DeletionCode.ExceptionalProbability
import DeletionCode.ExceptionalCountArithmetic

/-!
Count actual exceptional partner words by images of finite chronological
alignment records. Different records may decode to the same word; image
cardinality gives the upper bound without assuming uniqueness of alignment.
-/
namespace DeletionCode.ExceptionalPartnerCount

open HeaderRecovery TaggedAnchorCount AlignmentTrace FiniteConflictGraph TraceEditData
open ExceptionalProbability ExceptionalCountArithmetic
open scoped BigOperators

def decodeWord {n r : ℕ} (x : Bits n) (record : Record n r) : Bits n :=
  fun i => (AnchorRecords.decode (List.ofFn x) (packets record)).getD i.val false

theorem decodeWord_eq {n r : ℕ} (x y : Bits n) (record : Record n r)
    (h : AnchorRecords.decode (List.ofFn x) (packets record) = List.ofFn y) :
    decodeWord x record = y := by
  funext i
  simp [decodeWord, h, List.getD, i.isLt]

noncomputable def shortPartners {n : ℕ} (t : ℕ) (x : Bits n) : Finset (Bits n) := by
  classical
  exact (Finset.range t).biUnion fun d =>
    (Finset.univ : Finset (Record n (2 * d))).image (decodeWord x)

noncomputable def fullPartners {n : ℕ} (t k : ℕ) (x : Bits n) : Finset (Bits n) := by
  classical
  exact ((Finset.univ : Finset (Record n (2 * t))).filter
    (Bad (n - t) (4 * windowLength k))).image (decodeWord x)

theorem shortPartners_card_le {n : ℕ} (t : ℕ) (x : Bits n) :
    (shortPartners t x).card ≤ ∑ d ∈ Finset.range t, n ^ (2 * d) * 4 ^ (2 * d) := by
  classical
  unfold shortPartners
  apply le_trans Finset.card_biUnion_le
  apply Finset.sum_le_sum
  intro d _
  calc
    _ ≤ (Finset.univ : Finset (Record n (2 * d))).card := Finset.card_image_le
    _ = _ := by rw [Finset.card_univ, record_card]

theorem fullPartners_card_le {n : ℕ} (t k : ℕ) (x : Bits n) :
    (fullPartners t k x).card ≤
      (2 * t) * (2 * t + 2) * (2 * (4 * windowLength k)) * n ^ (2 * t - 1) * 4 ^ (2 * t) := by
  classical
  unfold fullPartners
  apply le_trans Finset.card_image_le
  have h := bad_record_card_le n (2 * t) (n - t) (4 * windowLength k)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  exact h

/-- Cardinality transfer from a concrete record cover. The cover is supplied
by the trace encoding in the complete theorem below. -/
theorem candidatePartners_card_le_of_cover {n : ℕ} (t k : ℕ) (x : Bits n)
    (hn : 1 ≤ n)
    (hcover : candidatePartners t k x ⊆ shortPartners t x ∪ fullPartners t k x) :
    (candidatePartners t k x).card ≤ exceptionalConstant t * windowLength k * n ^ (2 * t - 1) := by
  calc
    _ ≤ (shortPartners t x ∪ fullPartners t k x).card := Finset.card_le_card hcover
    _ ≤ (shortPartners t x).card + (fullPartners t k x).card := Finset.card_union_le _ _
    _ ≤ (∑ d ∈ Finset.range t, n ^ (2 * d) * 4 ^ (2 * d)) +
        (2 * t) * (2 * t + 2) * (2 * (4 * windowLength k)) * n ^ (2 * t - 1) * 4 ^ (2 * t) :=
      Nat.add_le_add (shortPartners_card_le t x) (fullPartners_card_le t k x)
    _ ≤ _ := combined_records_bound n t (windowLength k) hn (by unfold windowLength; omega)

/-- Failure of actual matched-column separation forces one of the close-anchor
conditions on any faithful finite record. Repeated anchors retain distinct indices. -/
theorem bad_record_of_not_separated {n r B : ℕ} (trace : Trace) (record : Record n r)
    (heq : packets record = AnchorRecords.encode trace) (hnot : ¬ Separated B trace) :
    Bad trace.matchedCount B record := by
  obtain ⟨e, he, ha⟩ := AnchorRecords.vector_edit_indices trace record.1 record.2 heq
  by_contra hbad
  apply hnot
  constructor
  · intro i hi
    let c : EditColumn trace := ⟨i, hi⟩
    have heq' := ha c
    have hl : ¬ (record.1 (e c)).val < B := fun h => hbad (Or.inl ⟨e c, h⟩)
    have hr : ¬ Nat.dist (record.1 (e c)).val trace.matchedCount < B :=
      fun h => hbad (Or.inr (Or.inl ⟨e c, h⟩))
    rw [heq'] at hl hr
    have hle := trace.matchedAnchor_le i.val
    change ¬ trace.matchedAnchor i.val < B at hl
    change ¬ Nat.dist (trace.matchedAnchor i.val) trace.matchedCount < B at hr
    unfold Nat.dist at hr
    constructor <;> omega
  · intro i j hi hj hij
    let c : EditColumn trace := ⟨i, hi⟩
    let d : EditColumn trace := ⟨j, hj⟩
    have hne : e c ≠ e d := by
      intro h
      have hv := congrArg (fun q : EditColumn trace => q.val.val) (he h)
      change i.val = j.val at hv
      omega
    have hp : ¬ Nat.dist (record.1 (e c)).val (record.1 (e d)).val < B :=
      fun h => hbad (Or.inr (Or.inr ⟨e c, e d, hne, h⟩))
    rw [ha c, ha d] at hp
    change ¬ Nat.dist (trace.matchedAnchor i.val) (trace.matchedAnchor j.val) < B at hp
    have hmono := TraceSeparation.matchedAnchor_mono trace (Nat.le_of_lt hij)
    unfold Nat.dist at hp
    omega

/-- Every actual exceptional partner is the decoded image of a short record
or a full-size record with a constrained anchor. -/
theorem candidatePartners_covered {n : ℕ} (t k : ℕ) (x : Bits n) :
    candidatePartners t k x ⊆ shortPartners t x ∪ fullPartners t k x := by
  classical
  intro y hy
  obtain ⟨hxy, d, trace, hs, ht, hd, hi, hcase⟩ :=
    (mem_candidatePartners t k x y).mp hy
  have hdpos : 1 ≤ d := by
    by_contra h
    have hzero : d = 0 := by omega
    have hz := AnchorRecords.target_eq_source_of_zero trace (hd.trans hzero) (hi.trans hzero)
    rw [hs, ht] at hz
    exact hxy (List.ofFn_injective hz).symm
  have hlen : trace.source.length = n := by rw [hs, List.length_ofFn]
  obtain ⟨anchors, data, hrecord⟩ := AnchorRecords.exists_finite_record trace n d hlen hd hi hdpos
  let record : Record n (2 * d) := (anchors, data)
  have hp : packets record = AnchorRecords.encode trace := hrecord
  have hdecode : decodeWord x record = y := by
    apply decodeWord_eq
    rw [hp, ← hs, AnchorRecords.decode_encode, ht]
  rcases hcase with hshort | ⟨hfull, hnot⟩
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    exact ⟨d, Finset.mem_range.mpr hshort, Finset.mem_image.mpr ⟨record, Finset.mem_univ _, hdecode⟩⟩
  · subst t
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨record, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hdecode⟩
    have hm : trace.matchedCount = n - d := by
      have h := trace.source_length
      omega
    rw [← hm]
    exact bad_record_of_not_separated trace record hp hnot

/-- The combinatorial half of the paper's nonseparated-family lemma, with an
explicit constant depending only on t. No uniqueness assumption is needed. -/
theorem candidatePartners_card_le {n : ℕ} (t k : ℕ) (x : Bits n) (hn : 1 ≤ n) :
    (candidatePartners t k x).card ≤ exceptionalConstant t * windowLength k * n ^ (2 * t - 1) :=
  candidatePartners_card_le_of_cover t k x hn (candidatePartners_covered t k x)

#print axioms bad_record_of_not_separated
#print axioms candidatePartners_covered
#print axioms candidatePartners_card_le

end DeletionCode.ExceptionalPartnerCount
