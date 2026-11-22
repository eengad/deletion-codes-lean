import DeletionCode.Burst.Rigidity

/-! Shared-letter rigidity at the manuscript's independent window length. -/
namespace DeletionCode.Explicit.Borrowed

open DeletionCode.Burst (Edit windowLength)
open DeletionCode.Qary.Windows

variable {α : Type*} [Inhabited α]

/-- Equal windows after bounded edits have a common consecutive block of source letters.
The identity edit (zero letters removed and inserted) represents an unedited word. -/
theorem shared_source_letters {n K b L : ℕ} (hk : 1 ≤ K)
    (hwindow : 3 * (K + b + 1) ≤ L)
    (x : Letters α) (hx : KUnique x n K) (e f : Edit α)
    (he : e.Bounded b) (hf : f.Bounded b)
    (hev : e.InBounds n) (hfv : f.InBounds n)
    (a c : ℕ) (ha : a + (L - 1) ≤ e.outputLength n)
    (hc : c + (L - 1) ≤ f.outputLength n)
    (hag : Agree (e.word x) a (f.word x) c (L - 1)) :
    ∃ s r : ℕ, s + K ≤ L - 1 ∧ r + K ≤ n ∧
      ∀ i, i < K → e.origin (a + s + i) = some (r + i) ∧
        f.origin (c + s + i) = some (r + i) := by
  change windowLength K b ≤ L at hwindow
  obtain ⟨s, r, hs, hr, hagree⟩ := Burst.Rigidity.shared_source_letters hk x hx e f he hf
    hev hfv a c (by omega) (by omega) (fun i hi => hag i (by omega))
  exact ⟨s, r, by omega, hr, hagree⟩

/-- The edited word is `(L - 1)`-unique. -/
theorem one_burst_unique {n K b L : ℕ} (hk : 1 ≤ K)
    (hwindow : 3 * (K + b + 1) ≤ L)
    (x : Letters α) (hx : KUnique x n K) (e : Edit α)
    (he : e.Bounded b) (hev : e.InBounds n) :
    KUnique (e.word x) (e.outputLength n) (L - 1) := by
  change windowLength K b ≤ L at hwindow
  exact Qary.SpectrumPath.kunique_mono _ _ _ _
    (Burst.Rigidity.one_burst_unique hk x hx e he hev) (by omega)

#print axioms shared_source_letters
#print axioms one_burst_unique

end DeletionCode.Explicit.Borrowed
