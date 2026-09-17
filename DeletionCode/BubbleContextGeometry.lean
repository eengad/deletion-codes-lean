import DeletionCode.BubbleEndpoints
import DeletionCode.BubblePathSimplicity
import DeletionCode.BubbleLocalSpectrum

/-!
The full path geometry of a concrete local bubble replacement. A source word
is an actual concatenation X ++ negativeWord ++ Y. The other concatenation
is realized by one actual edit, so simplicity and endpoint-only intersection
follow from the checked rigidity results. No substring realizations or
edited-word uniqueness are supplied by the caller.
-/
namespace DeletionCode.BubbleContextGeometry

open Windows HeaderRecovery CatalogueWords SpectrumLocalization

structure Geometry {k : ℕ} (bubble : BubbleWord k) : Prop where
  long_simple : Function.Injective (fun i : Fin (windowLength k - bubble.rho + 2) =>
    SpectrumPath.vertexAt (listLetters bubble.longWord) (windowLength k) i.val)
  short_simple : Function.Injective (fun i : Fin (windowLength k - bubble.rho + 1) =>
    SpectrumPath.vertexAt (listLetters bubble.shortWord) (windowLength k) i.val)
  endpoints : ∀ a b, a ≤ windowLength k - bubble.rho + 1 →
    b ≤ windowLength k - bubble.rho →
    Agree (listLetters bubble.longWord) a (listLetters bubble.shortWord) b
      (windowLength k - 1) →
    (a = 0 ∧ b = 0) ∨
      (a = windowLength k - bubble.rho + 1 ∧ b = windowLength k - bubble.rho)

theorem cut_bounds {k : ℕ} (bubble : BubbleWord k) :
    editOffset k < bubble.longWord.length ∧ editOffset k ≤ bubble.shortWord.length := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [bubble.longWord_length, bubble.shortWord_length, longLength, shortLength,
    BubbleWord.header, editOffset, windowLength]
  omega

theorem lengths {k : ℕ} (bubble : BubbleWord k) :
    bubble.shortWord.length + 1 = bubble.longWord.length := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [bubble.longWord_length, bubble.shortWord_length, longLength, shortLength,
    BubbleWord.header, windowLength]
  omega

theorem middle_agree (x p y : List Bool) :
    Agree (listLetters p) 0 (listLetters (x ++ (p ++ y))) x.length p.length := by
  intro i hi
  simpa only [Nat.zero_add] using (listLetters_middle x p y i hi).symm

/-- The fixed canonical run deletion also works inside arbitrary context. -/
theorem erase_context {k : ℕ} (bubble : BubbleWord k) (x y : List Bool) :
    (x ++ (bubble.longWord ++ y)).eraseIdx (x.length + editOffset k) =
      x ++ (bubble.shortWord ++ y) := by
  rw [List.eraseIdx_append_of_length_le (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.eraseIdx_append_of_lt_length (cut_bounds bubble).1, bubble.eraseIdx_longWord]

theorem delete_context {k : ℕ} (bubble : BubbleWord k) (x y : List Bool) :
    deleteAt (listLetters (x ++ (bubble.longWord ++ y))) (x.length + editOffset k) =
      listLetters (x ++ (bubble.shortWord ++ y)) := by
  rw [← listLetters_eraseIdx, erase_context]

theorem insert_context {k : ℕ} (bubble : BubbleWord k) (x y : List Bool) :
    insertAt (listLetters (x ++ (bubble.shortWord ++ y)))
        (x.length + editOffset k) bubble.bit =
      listLetters (x ++ (bubble.longWord ++ y)) := by
  have hbit : listLetters (x ++ (bubble.longWord ++ y)) (x.length + editOffset k) =
      bubble.bit := by
    rw [listLetters_middle x bubble.longWord y _ (cut_bounds bubble).1]
    exact bubble.header_bit
  calc
    insertAt (listLetters (x ++ (bubble.shortWord ++ y)))
        (x.length + editOffset k) bubble.bit =
      insertAt (deleteAt (listLetters (x ++ (bubble.longWord ++ y)))
        (x.length + editOffset k)) (x.length + editOffset k)
        (listLetters (x ++ (bubble.longWord ++ y)) (x.length + editOffset k)) := by
          rw [delete_context, hbit]
    _ = _ := insert_delete _ _

theorem deletion_geometry {k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (hleft : bubble.left.getLast? = some (!bubble.bit))
    (hright : bubble.right.head? = some (!bubble.bit)) (x y : List Bool)
    (hx : KUnique (listLetters (x ++ (bubble.longWord ++ y)))
      (x ++ (bubble.longWord ++ y)).length k) : Geometry bubble := by
  have hlength := lengths bubble
  have hcut := (cut_bounds bubble).1
  have hpos : x.length + editOffset k < (x ++ (bubble.longWord ++ y)).length := by
    simp only [List.length_append]
    omega
  have hl : x.length + bubble.longWord.length ≤ (x ++ (bubble.longWord ++ y)).length := by
    simp only [List.length_append]
    omega
  have hs : x.length + bubble.shortWord.length ≤ (x ++ (bubble.longWord ++ y)).length - 1 := by
    simp only [List.length_append]
    omega
  have hshort : Agree (listLetters bubble.shortWord) 0
      (deleteAt (listLetters (x ++ (bubble.longWord ++ y))) (x.length + editOffset k))
      x.length bubble.shortWord.length := by
    rw [delete_context]
    exact middle_agree x bubble.shortWord y
  have hsimple := BubblePathSimplicity.deletion_vertices_injective hk bubble _ hx
    (x.length + editOffset k) hpos x.length hl hs (middle_agree x bubble.longWord y) hshort
  exact ⟨hsimple.1, hsimple.2, fun a b ha hb hag =>
    BubbleEndpoints.deletion_endpoints hk bubble hleft hright _ hx
      (x.length + editOffset k) hpos x.length hl hs
      (middle_agree x bubble.longWord y) hshort a b ha hb hag⟩

theorem insertion_geometry {k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (hleft : bubble.left.getLast? = some (!bubble.bit))
    (hright : bubble.right.head? = some (!bubble.bit)) (x y : List Bool)
    (hx : KUnique (listLetters (x ++ (bubble.shortWord ++ y)))
      (x ++ (bubble.shortWord ++ y)).length k) : Geometry bubble := by
  have hlength := lengths bubble
  have hcut := (cut_bounds bubble).2
  have hpos : x.length + editOffset k ≤ (x ++ (bubble.shortWord ++ y)).length := by
    simp only [List.length_append]
    omega
  have hl : x.length + bubble.longWord.length ≤ (x ++ (bubble.shortWord ++ y)).length + 1 := by
    simp only [List.length_append]
    omega
  have hs : x.length + bubble.shortWord.length ≤ (x ++ (bubble.shortWord ++ y)).length := by
    simp only [List.length_append]
    omega
  have hlong : Agree (listLetters bubble.longWord) 0
      (insertAt (listLetters (x ++ (bubble.shortWord ++ y)))
        (x.length + editOffset k) bubble.bit) x.length bubble.longWord.length := by
    rw [insert_context]
    exact middle_agree x bubble.longWord y
  have hsimple := BubblePathSimplicity.insertion_vertices_injective hk bubble _ hx
    (x.length + editOffset k) bubble.bit hpos x.length hl hs hlong
    (middle_agree x bubble.shortWord y)
  exact ⟨hsimple.1, hsimple.2, fun a b ha hb hag =>
    BubbleEndpoints.insertion_endpoints hk bubble hleft hright _ hx
      (x.length + editOffset k) bubble.bit hpos x.length hl hs hlong
      (middle_agree x bubble.shortWord y) a b ha hb hag⟩

/-- In either orientation, source uniqueness and the actual grammar boundary
bits suffice for both simple paths and the endpoint-only intersection. -/
theorem context_geometry {k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (hleft : bubble.left.getLast? = some (!bubble.bit))
    (hright : bubble.right.head? = some (!bubble.bit)) (x y : List Bool)
    (hx : KUnique (listLetters (x ++ (bubble.negativeWord ++ y)))
      (x ++ (bubble.negativeWord ++ y)).length k) : Geometry bubble := by
  cases ho : bubble.orientation with
  | deletion =>
    simp only [BubbleWord.negativeWord, ho] at hx
    exact deletion_geometry hk bubble hleft hright x y hx
  | insertion =>
    simp only [BubbleWord.negativeWord, ho] at hx
    exact insertion_geometry hk bubble hleft hright x y hx

#print axioms erase_context
#print axioms delete_context
#print axioms insert_context
#print axioms deletion_geometry
#print axioms insertion_geometry
#print axioms context_geometry

end DeletionCode.BubbleContextGeometry
