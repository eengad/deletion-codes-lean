import DeletionCode.Explicit.Borrowed.CatalogueCoverage

/-! The existence development is recovered at its fixed window length. -/
namespace DeletionCode.Explicit.Borrowed

open DeletionCode.Burst DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords
open DeletionCode.Qary.SignedSupport

variable {α : Type*} {K b : ℕ}

private def BubbleWord.toFixed (p : BubbleWord α K b (windowLength K b)) :
    Burst.BubbleWord α K b :=
  ⟨p.left, p.right, p.removed, p.replacement, p.removed_bound, p.replacement_bound,
    p.different, p.left_lower, p.left_upper, p.right_lower, p.right_upper⟩

private def BubbleWord.ofFixed (p : Burst.BubbleWord α K b) :
    BubbleWord α K b (windowLength K b) :=
  ⟨p.left, p.right, p.removed, p.replacement, p.removed_bound, p.replacement_bound,
    p.different, p.left_lower, p.left_upper, p.right_lower, p.right_upper⟩

variable [Inhabited α]

/-- At the original window length, the two local-bubble existence conclusions agree. -/
theorem exists_localBubble_fixed_iff (e : Edit α) (x : Word α) :
    (∃ p : LocalBubble α K b (windowLength K b) x (e.apply x) e.pos,
      p.bubble.removed = e.sourceBlock x ∧ p.bubble.replacement = e.replacement) ↔
    (∃ p : Burst.LocalBubble α K b x (e.apply x) e.pos,
      p.bubble.removed = e.sourceBlock x ∧ p.bubble.replacement = e.replacement) := by
  constructor
  · rintro ⟨p, hU, hV⟩
    exact ⟨⟨⟨p.bubble.toFixed, p.before, p.after, p.source_eq, p.target_eq, p.edit_pos⟩,
      p.initial_agreement, p.terminal_agreement, p.negative_unique, p.positive_unique,
      p.endpoints⟩, hU, hV⟩
  · rintro ⟨p, hU, hV⟩
    exact ⟨⟨⟨BubbleWord.ofFixed p.bubble, p.before, p.after, p.source_eq, p.target_eq, p.edit_pos⟩,
      p.initial_agreement, p.terminal_agreement, p.negative_unique, p.positive_unique,
      p.endpoints⟩, hU, hV⟩

/-- `exists_localBubble` specialized to the statement in `Burst.LocalBubble`. -/
theorem exists_localBubble_fixed (hk : 1 ≤ K) (e : Edit α) (x : Word α)
    (he : e.Valid b x) (hx : KUnique (listLetters x) x.length K)
    (hleft : 2 * (windowLength K b + b) ≤ e.pos)
    (hright : e.pos + e.removed + 2 * (windowLength K b + b) ≤ x.length) :
    ∃ p : Burst.LocalBubble α K b x (e.apply x) e.pos,
      p.bubble.removed = e.sourceBlock x ∧ p.bubble.replacement = e.replacement :=
  (exists_localBubble_fixed_iff e x).mp (exists_localBubble hk le_rfl e x he hx hleft hright)

/-- With the original window length and length balance, rule membership is equivalent. -/
theorem rule_fixed_iff {t : ℕ} (w : Gram α (windowLength K b) → ℤ) :
    Catalogue.Rule t K b (windowLength K b) w ↔ Burst.Catalogue.Rule t K b w := by
  constructor
  · rintro ⟨words, hvalid, hbalance, hspectrum⟩
    refine ⟨fun i => (words i).toFixed, ?_, hbalance, hspectrum⟩
    exact ⟨hvalid.geometry, hvalid.common_start, hvalid.common_end, hvalid.within_rule_disjoint⟩
  · rintro ⟨words, hvalid, hbalance, hspectrum⟩
    refine ⟨fun i => BubbleWord.ofFixed (words i), ?_, hbalance, hspectrum⟩
    exact ⟨fun i side => (Catalogue.word_length_bounds (BubbleWord.ofFixed (words i)) side le_rfl).1,
      hvalid.geometry, hvalid.common_start, hvalid.common_end, hvalid.within_rule_disjoint⟩

/-- `catalogueRule` specialized to the statement in `Burst.CatalogueCoverage`. -/
theorem catalogueRule_fixed [Fintype α] [DecidableEq α] {t : ℕ} {x y : Word α} {es : List (Edit α)}
    (hk : 1 ≤ K) (hx : KUnique (listLetters x) x.length K)
    (h : Executes b x es y) (hlen : es.length = 2 * t)
    (hsep : Separated x.length (8 * (windowLength K b + t * b)) es)
    (hxy : x.length = y.length) :
    Burst.Catalogue.Rule t K b (wordSpectrum (listLetters y) y.length (windowLength K b) -
      wordSpectrum (listLetters x) x.length (windowLength K b)) :=
  (rule_fixed_iff _).mp (CatalogueCoverage.catalogueRule hk le_rfl hx h hlen hsep hxy)

/-- The manuscript parameters (`d:parameters`) imply the window hypothesis (`eq:lengths`). -/
theorem parameter_window_bound (eta b C : ℕ) (hC : 32 ≤ C) :
    3 * ((3 * eta + 4) + b + 1) ≤ C * (eta + b + 3) := by
  have h := Nat.mul_le_mul_right (eta + b + 3) hC
  omega

#print axioms exists_localBubble_fixed
#print axioms rule_fixed_iff
#print axioms catalogueRule_fixed
#print axioms parameter_window_bound

end DeletionCode.Explicit.Borrowed
