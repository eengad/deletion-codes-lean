import DeletionCode.Burst.SuffixBoundary

/-!
Two equal local boundary windows can meet only at the first common window or
the last common window. Rigidity supplies a surviving source letter; its
position puts both windows on the same side of the replacement, where the
actual first or last mismatch excludes every interior intersection.
-/
namespace DeletionCode.Burst

open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords

variable {α : Type*} [Inhabited α]

theorem global_endpoints {k b : ℕ} (hk : 1 ≤ k) (e : Edit α) (x : Word α)
    (he : e.Valid b x) (hx : KUnique (listLetters x) x.length k)
    (p : PrefixBoundary (k := k) (b := b) e x)
    (q : SuffixBoundary (k := k) (b := b) e x)
    (hp : windowLength k b - 1 ≤ p.index)
    (hq : windowLength k b - 1 ≤ q.suffix)
    (i j : ℕ)
    (hi : p.index - (windowLength k b - 1) ≤ i ∧ i ≤ x.length - q.suffix)
    (hj : p.index - (windowLength k b - 1) ≤ j ∧
      j ≤ e.outputLength x.length - q.suffix)
    (hag : Agree (listLetters x) i (e.word (listLetters x)) j (windowLength k b - 1)) :
    (i = p.index - (windowLength k b - 1) ∧ j = p.index - (windowLength k b - 1)) ∨
    (i = x.length - q.suffix ∧ j = e.outputLength x.length - q.suffix) := by
  let idEdit : Edit α := ⟨0, 0, []⟩
  have hword : idEdit.word (listLetters x) = listLetters x := by
    funext a
    simp [idEdit, Edit.word]
  have hbound : idEdit.Bounded b := by simp [idEdit, Edit.Bounded]
  have hvalid : idEdit.InBounds x.length := by simp [idEdit, Edit.InBounds]
  have hn := q.source_bound
  have hn' := q.target_bound
  have hag' : Agree (idEdit.word (listLetters x)) i (e.word (listLetters x)) j
      (windowLength k b - 1) := by simpa only [hword] using hag
  obtain ⟨s, r, hsk, _, hsource⟩ := Rigidity.shared_source_letters hk (listLetters x) hx
    idEdit e hbound he.1 hvalid he.2.1 i j
    (by simp only [idEdit, Edit.outputLength]; omega) (by omega) hag'
  have h0 := hsource 0 (by omega)
  have hr : i + s = r := by simpa [idEdit, Edit.origin] using h0.1
  have hsrc : e.origin (j + s) = some r := by simpa only [Nat.add_zero] using h0.2
  rcases e.origin_before_or_after hsrc with ⟨hbefore, hrj⟩ | ⟨hafter, hrj⟩
  · have hij : i = j := by omega
    have hiBefore : i < e.pos := by omega
    have hfirst := p.before
    have hstart : i = p.index - (windowLength k b - 1) := by
      by_contra hnstart
      have hoff : p.index - i < windowLength k b - 1 := by omega
      have heq := hag (p.index - i) hoff
      have hind : i + (p.index - i) = p.index := by omega
      rw [← hij, hind] at heq
      exact p.different heq
    exact Or.inl ⟨hstart, hij ▸ hstart⟩
  · have hdisp : i + e.replacement.length = j + e.removed := by omega
    have hend := q.before
    have hv := he.2.1
    unfold Edit.InBounds at hv
    have hcross : x.length - q.suffix < i + (windowLength k b - 1) := by omega
    have hlast : i = x.length - q.suffix := by
      by_contra hnlast
      have hoff : x.length - q.suffix - 1 - i < windowLength k b - 1 := by omega
      have heq := hag (x.length - q.suffix - 1 - i) hoff
      have hind : i + (x.length - q.suffix - 1 - i) = x.length - q.suffix - 1 := by omega
      have hind' : j + (x.length - q.suffix - 1 - i) =
          e.outputLength x.length - q.suffix - 1 := by
        unfold Edit.outputLength at *
        omega
      rw [hind, hind'] at heq
      exact q.different heq
    right
    refine ⟨hlast, ?_⟩
    unfold Edit.outputLength at *
    omega

#print axioms global_endpoints

end DeletionCode.Burst
