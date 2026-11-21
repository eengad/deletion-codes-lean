import DeletionCode.BubbleEndpoints
import DeletionCode.BubblePathSimplicity
import DeletionCode.BubbleLocalSpectrum

/-!
The full path geometry of a concrete local bubble replacement. A source word
is an actual concatenation X ++ negativeWord ++ Y. The other concatenation
is realized by one actual edit (a deletion, an insertion, or a substitution),
so simplicity and endpoint-only intersection follow from the checked
rigidity results. No substring realizations or edited-word uniqueness are
supplied by the caller.
-/
namespace DeletionCode.BubbleContextGeometry

open Windows HeaderRecovery CatalogueWords SpectrumLocalization

/-- Path geometry of a bubble, stated for its actual negative and positive
words in every orientation: both local paths are simple, and they meet only
at their initial and terminal vertices. -/
structure Geometry {k : ℕ} (bubble : BubbleWord k) : Prop where
  negative_simple : Function.Injective
    (fun i : Fin (bubble.negativeWord.length - windowLength k + 2) =>
      SpectrumPath.vertexAt (listLetters bubble.negativeWord) (windowLength k) i.val)
  positive_simple : Function.Injective
    (fun i : Fin (bubble.positiveWord.length - windowLength k + 2) =>
      SpectrumPath.vertexAt (listLetters bubble.positiveWord) (windowLength k) i.val)
  endpoints : ∀ i j, i ≤ bubble.negativeWord.length - windowLength k + 1 →
    j ≤ bubble.positiveWord.length - windowLength k + 1 →
    Agree (listLetters bubble.negativeWord) i (listLetters bubble.positiveWord) j
      (windowLength k - 1) →
    (i = 0 ∧ j = 0) ∨
      (i = bubble.negativeWord.length - windowLength k + 1 ∧
        j = bubble.positiveWord.length - windowLength k + 1)

theorem word_lengths {k : ℕ} (bubble : BubbleWord k) :
    bubble.longWord.length = 2 * windowLength k - bubble.rho ∧
      bubble.shortWord.length = 2 * windowLength k - bubble.rho - 1 ∧
      bubble.flipWord.length = 2 * windowLength k - bubble.rho ∧
      1 ≤ bubble.rho ∧ bubble.rho + 2 ≤ windowLength k := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  refine ⟨?_, ?_, ?_, hlo, ?_⟩
  · simpa only [longLength, BubbleWord.header] using bubble.longWord_length
  · simpa only [shortLength, longLength, BubbleWord.header] using bubble.shortWord_length
  · simpa only [longLength, BubbleWord.header] using bubble.flipWord_length
  · unfold windowLength
    omega

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

/-- Inserting the opposite letter at the run offset produces the flipped
word, inside arbitrary context. -/
theorem insert_flip_context {k : ℕ} (bubble : BubbleWord k) (x y : List Bool) :
    insertAt (listLetters (x ++ (bubble.shortWord ++ y)))
        (x.length + editOffset k) (!bubble.bit) =
      listLetters (x ++ (bubble.flipWord ++ y)) := by
  have hpre : (x ++ (bubble.left ++ List.replicate (bubble.rho - 1) bubble.bit)).length =
      x.length + editOffset k := by
    rw [List.length_append, bubble.prefix_length]
  have hshort : x ++ (bubble.shortWord ++ y) =
      (x ++ (bubble.left ++ List.replicate (bubble.rho - 1) bubble.bit)) ++
        (bubble.right ++ y) := by
    simp only [BubbleWord.shortWord, List.append_assoc]
  have hflip : x ++ (bubble.flipWord ++ y) =
      (x ++ (bubble.left ++ List.replicate (bubble.rho - 1) bubble.bit)) ++
        ((!bubble.bit) :: (bubble.right ++ y)) := by
    simp only [BubbleWord.flipWord, List.append_assoc, List.cons_append]
  rw [hshort, hflip, ← hpre]
  exact BubbleWord.listLetters_insert_split _ _ _

/-- The canonical substitution at the run offset also works inside context. -/
theorem flip_context {k : ℕ} (bubble : BubbleWord k) (x y : List Bool) :
    flipAt (listLetters (x ++ (bubble.longWord ++ y))) (x.length + editOffset k) =
      listLetters (x ++ (bubble.flipWord ++ y)) := by
  rw [← insert_context bubble x y, flip_insertAt, insert_flip_context]

theorem deletion_geometry {k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (ho : bubble.orientation = .deletion)
    (hleft : bubble.left.getLast? = some (!bubble.bit))
    (hright : bubble.right.head? = some (!bubble.bit)) (x y : List Bool)
    (hx : KUnique (listLetters (x ++ (bubble.longWord ++ y)))
      (x ++ (bubble.longWord ++ y)).length k) : Geometry bubble := by
  have hlens := word_lengths bubble
  have hL : windowLength k = 3 * (k + 1) := rfl
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
  have hneg : bubble.negativeWord = bubble.longWord := by
    simp only [BubbleWord.negativeWord, ho]
  have hposw : bubble.positiveWord = bubble.shortWord := by
    simp only [BubbleWord.positiveWord, ho]
  refine ⟨?_, ?_, ?_⟩
  · rw [hneg]
    exact BubblePathSimplicity.local_vertex_injective hk _ hx .unchanged trivial
      bubble.longWord x.length hl (middle_agree x bubble.longWord y) (by omega)
  · rw [hposw]
    exact BubblePathSimplicity.local_vertex_injective hk _ hx (.delete (x.length + editOffset k))
      hpos bubble.shortWord x.length hs hshort (by omega)
  · rw [hneg, hposw]
    intro a b ha hb hag
    have h := BubbleEndpoints.deletion_endpoints hk bubble hleft hright _ hx
      (x.length + editOffset k) hpos x.length hl hs
      (middle_agree x bubble.longWord y) hshort a b (by omega) (by omega) hag
    rcases h with h | h
    · exact Or.inl h
    · right
      omega

theorem insertion_geometry {k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (ho : bubble.orientation = .insertion)
    (hleft : bubble.left.getLast? = some (!bubble.bit))
    (hright : bubble.right.head? = some (!bubble.bit)) (x y : List Bool)
    (hx : KUnique (listLetters (x ++ (bubble.shortWord ++ y)))
      (x ++ (bubble.shortWord ++ y)).length k) : Geometry bubble := by
  have hlens := word_lengths bubble
  have hL : windowLength k = 3 * (k + 1) := rfl
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
  have hneg : bubble.negativeWord = bubble.shortWord := by
    simp only [BubbleWord.negativeWord, ho]
  have hposw : bubble.positiveWord = bubble.longWord := by
    simp only [BubbleWord.positiveWord, ho]
  refine ⟨?_, ?_, ?_⟩
  · rw [hneg]
    exact BubblePathSimplicity.local_vertex_injective hk _ hx .unchanged trivial
      bubble.shortWord x.length hs (middle_agree x bubble.shortWord y) (by omega)
  · rw [hposw]
    exact BubblePathSimplicity.local_vertex_injective hk _ hx
      (.insert (x.length + editOffset k) bubble.bit) hpos bubble.longWord x.length hl hlong
      (by omega)
  · rw [hneg, hposw]
    intro a b ha hb hag
    have h := BubbleEndpoints.insertion_endpoints hk bubble hleft hright _ hx
      (x.length + editOffset k) bubble.bit hpos x.length hl hs hlong
      (middle_agree x bubble.shortWord y) b a (by omega) (by omega)
      (fun r hr => (hag r hr).symm)
    rcases h with h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · right
      omega

/-- A substitution bubble needs no flank-bit condition: the source contains
the longer word and the flipped word is realized by one actual substitution. -/
theorem substitution_geometry {k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (ho : bubble.orientation = .substitution) (x y : List Bool)
    (hx : KUnique (listLetters (x ++ (bubble.longWord ++ y)))
      (x ++ (bubble.longWord ++ y)).length k) : Geometry bubble := by
  have hlens := word_lengths bubble
  have hL : windowLength k = 3 * (k + 1) := rfl
  have hcut := (cut_bounds bubble).1
  have hpos : x.length + editOffset k < (x ++ (bubble.longWord ++ y)).length := by
    simp only [List.length_append]
    omega
  have hl : x.length + bubble.longWord.length ≤ (x ++ (bubble.longWord ++ y)).length := by
    simp only [List.length_append]
    omega
  have hf : x.length + bubble.flipWord.length ≤ (x ++ (bubble.longWord ++ y)).length := by
    simp only [List.length_append]
    omega
  have hflip : Agree (listLetters bubble.flipWord) 0
      (flipAt (listLetters (x ++ (bubble.longWord ++ y))) (x.length + editOffset k))
      x.length bubble.flipWord.length := by
    rw [flip_context]
    exact middle_agree x bubble.flipWord y
  have hsimple := BubblePathSimplicity.substitution_vertices_injective hk bubble _ hx
    (x.length + editOffset k) hpos x.length hl hf (middle_agree x bubble.longWord y) hflip
  have hneg : bubble.negativeWord = bubble.longWord := by
    simp only [BubbleWord.negativeWord, ho]
  have hposw : bubble.positiveWord = bubble.flipWord := by
    simp only [BubbleWord.positiveWord, ho]
  refine ⟨?_, ?_, ?_⟩
  · rw [hneg]
    exact hsimple.1
  · rw [hposw]
    exact hsimple.2
  · rw [hneg, hposw]
    exact BubbleEndpoints.substitution_endpoints hk bubble _ hx (x.length + editOffset k) hpos
      x.length hl hf (middle_agree x bubble.longWord y) hflip

/-- In every orientation, source uniqueness suffices for both simple paths
and the endpoint-only intersection; the grammar boundary bits are needed
only for deletion and insertion bubbles. -/
theorem context_geometry {k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (hboundary : bubble.orientation ≠ .substitution →
      bubble.left.getLast? = some (!bubble.bit) ∧ bubble.right.head? = some (!bubble.bit))
    (x y : List Bool)
    (hx : KUnique (listLetters (x ++ (bubble.negativeWord ++ y)))
      (x ++ (bubble.negativeWord ++ y)).length k) : Geometry bubble := by
  cases ho : bubble.orientation with
  | deletion =>
    have hb := hboundary (by rw [ho]; decide)
    simp only [BubbleWord.negativeWord, ho] at hx
    exact deletion_geometry hk bubble ho hb.1 hb.2 x y hx
  | insertion =>
    have hb := hboundary (by rw [ho]; decide)
    simp only [BubbleWord.negativeWord, ho] at hx
    exact insertion_geometry hk bubble ho hb.1 hb.2 x y hx
  | substitution =>
    simp only [BubbleWord.negativeWord, ho] at hx
    exact substitution_geometry hk bubble ho x y hx

#print axioms erase_context
#print axioms delete_context
#print axioms insert_context
#print axioms flip_context
#print axioms deletion_geometry
#print axioms insertion_geometry
#print axioms substitution_geometry
#print axioms context_geometry

end DeletionCode.BubbleContextGeometry
