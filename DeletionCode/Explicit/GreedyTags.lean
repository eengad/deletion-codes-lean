import DeletionCode.Explicit.EditBallCount
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Positivity

/-! Manuscript `d:tag-code`. Scan words in lexicographic order, removing the
marked neighbours of each retained tag from the remainder of the scan. -/

namespace DeletionCode.Explicit

theorem nodup_wordsOfLength (q m : ℕ) : (wordsOfLength q m).Nodup := by
  induction m with
  | zero => simp [wordsOfLength]
  | succ m ih =>
    apply List.nodup_flatMap.mpr
    constructor
    · intro a _
      exact ih.map (fun _ _ h => (List.cons.inj h).2)
    · apply (List.nodup_finRange q).imp
      intro a a' hne w hw hw'
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hw
      obtain ⟨v, _, he⟩ := List.mem_map.mp hw'
      exact hne (List.cons.inj he).1.symm

private def unmarked {q : ℕ} (b s : ℕ) (w : QWord q) (xs : List (QWord q)) :=
  let marked := editBall b s w
  xs.filter fun y => decide (y ∉ marked)

@[simp] private theorem mem_unmarked {q b s : ℕ} {w y : QWord q} {xs : List (QWord q)} :
    y ∈ unmarked b s w xs ↔ y ∈ xs ∧ y ∉ editBall b s w := by simp [unmarked]

def scan {q : ℕ} (b s : ℕ) : ℕ → List (QWord q) → List (QWord q)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, w :: xs => w :: scan b s fuel (unmarked b s w xs)

/-- A separated list is returned in scan order. Every word originally scanned
is in the ball of a retained word. -/
private theorem scan_spec {q : ℕ} (b s fuel : ℕ) (xs : List (QWord q)) (hf : xs.length ≤ fuel) :
    (∀ y ∈ scan b s fuel xs, y ∈ xs) ∧
    (scan b s fuel xs).Pairwise (fun u v => ¬ Burst.WithinBursts b s u v) ∧
    ∀ y ∈ xs, ∃ w ∈ scan b s fuel xs, y ∈ editBall b s w := by
  induction fuel generalizing xs with
  | zero => cases xs <;> simp_all [scan]
  | succ fuel ih =>
    cases xs with
    | nil => simp [scan]
    | cons w xs =>
      have hsub : (unmarked b s w xs).length ≤ xs.length := List.length_filter_le ..
      obtain ⟨hmem, hsep, hcov⟩ := ih (unmarked b s w xs) (by simp only [List.length_cons] at hf; omega)
      rw [scan]
      refine ⟨?_, List.pairwise_cons.mpr ⟨?_, hsep⟩, ?_⟩
      · intro y h
        rcases List.mem_cons.mp h with rfl | hy
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_unmarked.mp (hmem _ hy)).1
      · intro y hy h
        exact (mem_unmarked.mp (hmem _ hy)).2 (mem_editBall.mpr h)
      · intro y hy
        by_cases hm : y ∈ editBall b s w
        · exact ⟨w, List.mem_cons_self, hm⟩
        · have hne : y ≠ w := by
            rintro rfl
            exact hm (mem_editBall.mpr ⟨0, Nat.zero_le _, .refl _⟩)
          have ht : y ∈ xs := (List.mem_cons.mp hy).resolve_left hne
          obtain ⟨v, hv, hy'⟩ := hcov y (mem_unmarked.mpr ⟨ht, hm⟩)
          exact ⟨v, List.mem_cons_of_mem _ hv, hy'⟩

def greedyTags (q b s m : ℕ) : List (QWord q) :=
  let xs := wordsOfLength q m
  scan b s xs.length xs

theorem greedyTags_spec (q b s m : ℕ) :
    (∀ w ∈ greedyTags q b s m, w.length = m) ∧
    (greedyTags q b s m).Pairwise (fun u v => ¬ Burst.WithinBursts b s u v) ∧
    ∀ y : QWord q, y.length = m → ∃ w ∈ greedyTags q b s m, y ∈ editBall b s w := by
  obtain ⟨hm, hs, hc⟩ := scan_spec b s _ (wordsOfLength q m) (Nat.le_refl _)
  exact ⟨fun _ h => mem_wordsOfLength.mp (hm _ h), hs, fun _ h => hc _ (mem_wordsOfLength.mpr h)⟩

/-- The greedy scan produces at least the requested number of tags under the
paper's exact numerical hypothesis. -/
theorem greedyTags_count {q : ℕ} (hq : 0 < q) (b s m M : ℕ)
    (henough : M * tagBallBound q b s m ≤ q ^ m) : M ≤ (greedyTags q b s m).length := by
  let tags := greedyTags q b s m
  obtain ⟨hlen, _, hcov⟩ := greedyTags_spec q b s m
  have cover : (wordsOfLength q m).toFinset ⊆ (tags.flatMap (editBall b s)).toFinset := by
    intro y hy
    have h := mem_wordsOfLength.mp (List.mem_toFinset.mp hy)
    exact List.mem_toFinset.mpr (List.mem_flatMap.mpr (hcov y h))
  have cross : q ^ m ≤ tags.length * tagBallBound q b s m := calc
    q ^ m = (wordsOfLength q m).toFinset.card := by
      rw [List.card_toFinset, (nodup_wordsOfLength q m).dedup, length_wordsOfLength]
    _ ≤ (tags.flatMap (editBall b s)).toFinset.card := Finset.card_le_card cover
    _ ≤ (tags.flatMap (editBall b s)).length := List.toFinset_card_le _
    _ ≤ _ := length_flatMap_bound _ _ _ (by
      intro w hw
      simpa only [hlen w hw] using editBall_le_tagBallBound hq b s w)
  have hp : 0 < tagBallBound q b s m := by unfold tagBallBound; positivity
  exact Nat.le_of_mul_le_mul_right (Nat.le_trans henough cross) hp

#print axioms greedyTags_spec
#print axioms greedyTags_count

end DeletionCode.Explicit
