import DeletionCode.Burst.WordFacts

/-! Reversal preserves source uniqueness and turns a valid burst into a valid burst. -/
namespace DeletionCode.Burst

open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords

variable {α : Type*} [Inhabited α]

theorem unique_reverse {k : ℕ} (x : Word α)
    (hx : KUnique (listLetters x) x.length k) :
    KUnique (listLetters x.reverse) x.reverse.length k := by
  intro a b ha hb hag
  simp only [List.length_reverse] at ha hb
  have hsource : Agree (listLetters x) (x.length - a - k)
      (listLetters x) (x.length - b - k) k := by
    intro i hi
    have hj : k - 1 - i < k := by omega
    have heq := hag (k - 1 - i) hj
    have hai : a + (k - 1 - i) < x.length := by omega
    have hbi : b + (k - 1 - i) < x.length := by omega
    rw [listLetters_reverse x hai, listLetters_reverse x hbi] at heq
    have hia : x.length - 1 - (a + (k - 1 - i)) = x.length - a - k + i := by omega
    have hib : x.length - 1 - (b + (k - 1 - i)) = x.length - b - k + i := by omega
    simpa only [hia, hib] using heq
  have heq := hx (x.length - a - k) (x.length - b - k) (by omega) (by omega) hsource
  omega

namespace Edit

def reverseOn (e : Edit α) (n : ℕ) : Edit α :=
  ⟨n - e.pos - e.removed, e.removed, e.replacement.reverse⟩

omit [Inhabited α] in
theorem reverseOn_split (e : Edit α) (x : Word α) (he : e.InBounds x.length) :
    e.reverseOn x.length =
      Edit.mk (x.drop (e.pos + e.removed)).reverse.length
        (e.sourceBlock x).reverse.length e.replacement.reverse := by
  simp only [reverseOn, List.length_reverse, List.length_drop, sourceBlock_length e x he]
  congr 1
  omega

omit [Inhabited α] in
theorem reverse_decomposition (e : Edit α) (x : Word α) :
    x.reverse = (x.drop (e.pos + e.removed)).reverse ++
      (e.sourceBlock x).reverse ++ (x.take e.pos).reverse := by
  conv_lhs => rw [← e.decomposition x]
  simp only [List.reverse_append, List.append_assoc]

omit [Inhabited α] in
theorem reverseOn_valid (e : Edit α) (x : Word α) {b : ℕ} (he : e.Valid b x) :
    (e.reverseOn x.length).Valid b x.reverse := by
  have hv := valid_split (x.drop (e.pos + e.removed)).reverse
    (e.sourceBlock x).reverse e.replacement.reverse (x.take e.pos).reverse
    (by simpa only [List.length_reverse, e.sourceBlock_length x he.2.1] using he.1.1)
    (by simpa only [List.length_reverse] using he.1.2)
    (fun hh => he.2.2 (List.reverse_inj.mp hh))
  rw [← e.reverseOn_split x he.2.1, ← e.reverse_decomposition x] at hv
  exact hv

omit [Inhabited α] in
theorem reverseOn_apply (e : Edit α) (x : Word α) (he : e.InBounds x.length) :
    (e.reverseOn x.length).apply x.reverse = (e.apply x).reverse := by
  rw [e.reverseOn_split x he, e.reverse_decomposition x, apply_split]
  simp only [apply, List.reverse_append, List.append_assoc]

end Edit

#print axioms unique_reverse
#print axioms Edit.reverseOn_valid
#print axioms Edit.reverseOn_apply

end DeletionCode.Burst
