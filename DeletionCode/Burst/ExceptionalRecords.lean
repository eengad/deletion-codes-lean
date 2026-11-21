import DeletionCode.Burst.ChronologicalSeparation

namespace DeletionCode.Burst.ExceptionalRecords

open FiniteRecords
open scoped BigOperators

variable {α : Type*} [Fintype α]

noncomputable def shortWords (b N t : ℕ) (x : Word α) : Finset (Word α) := by
  classical
  exact (Finset.range (2 * t)).biUnion (fun r =>
    (Finset.univ : Finset (Record α b N r)).image (decode x))

noncomputable def badWords (b N t n D : ℕ) (x : Word α) : Finset (Word α) := by
  classical
  exact ((Finset.univ : Finset (Record α b N (2 * t))).filter (Bad n D)).image (decode x)

noncomputable def words (b t n D : ℕ) (x : Word α) : Finset (Word α) := by
  classical
  exact shortWords b (n + 2 * t * b + 1) t x ∪
    badWords b (n + 2 * t * b + 1) t n D x

theorem shortWords_card_le (b N t : ℕ) (x : Word α) :
    (shortWords b N t x).card ≤
      ∑ r ∈ Finset.range (2 * t), N ^ r * ((b + 1) ^ 2 * Fintype.card α ^ b) ^ r := by
  classical
  apply (Finset.card_biUnion_le).trans
  apply Finset.sum_le_sum
  intro r hr
  exact (Finset.card_image_le).trans_eq (by simp only [Finset.card_univ, record_card])

theorem badWords_card_le (b N t n D : ℕ) (x : Word α) :
    (badWords b N t n D x).card ≤
      (2 * t) * (2 * t + 2) * (2 * D) * N ^ (2 * t - 1) *
        ((b + 1) ^ 2 * Fintype.card α ^ b) ^ (2 * t) := by
  classical
  apply Finset.card_image_le.trans
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    (bad_record_card_le (α := α) b N (2 * t) n D)

theorem words_card_le (b t n D : ℕ) (x : Word α) :
    (words b t n D x).card ≤
      (∑ r ∈ Finset.range (2 * t),
        (n + 2 * t * b + 1) ^ r * ((b + 1) ^ 2 * Fintype.card α ^ b) ^ r) +
      (2 * t) * (2 * t + 2) * (2 * D) * (n + 2 * t * b + 1) ^ (2 * t - 1) *
        ((b + 1) ^ 2 * Fintype.card α ^ b) ^ (2 * t) := by
  classical
  exact (Finset.card_union_le ..).trans (Nat.add_le_add
    (shortWords_card_le ..) (badWords_card_le ..))

theorem mem_words [Inhabited α] {b t n D : ℕ} {x y : Word α}
    (hx : x.length = n) (hD : 2 * t * b < D) (h : Exceptional b t n D x y) :
    y ∈ words b t n D x := by
  classical
  obtain ⟨es, hex, hlen, hbad⟩ := h
  have hp (i : Fin es.length) : (es.get i).pos < n + 2 * t * b + 1 := by
    have hi := hex.position_le i
    have hmul : i.val * b ≤ (2 * t) * b := Nat.mul_le_mul_right b (by omega)
    omega
  let record := encode es hp (fun i => (hex.get_valid i).1)
  have hdec : decode x record = y := decode_encode hex hp
  by_cases hshort : es.length < 2 * t
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨es.length, Finset.mem_range.mpr hshort, ?_⟩
    exact Finset.mem_image.mpr ⟨record, Finset.mem_univ _, hdec⟩
  · have heq : es.length = 2 * t := by omega
    have hsep : ¬Separated n D es := hbad.resolve_left hshort
    have hrec : Bad n D record := not_separated_bad es hp
      (fun i => (hex.get_valid i).1) (by omega) hsep
    apply Finset.mem_union_right
    unfold badWords
    have hy : y ∈ ((Finset.univ : Finset (Record α b (n + 2 * t * b + 1) es.length)).filter
        (Bad n D)).image (decode x) :=
      Finset.mem_image.mpr ⟨record, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrec⟩, hdec⟩
    have hc := congrArg (fun r =>
      ((Finset.univ : Finset (Record α b (n + 2 * t * b + 1) r)).filter
        (Bad n D)).image (decode x)) heq
    rw [← hc]
    exact hy

end DeletionCode.Burst.ExceptionalRecords
