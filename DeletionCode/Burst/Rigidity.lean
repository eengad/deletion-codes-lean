import DeletionCode.Burst.Origins
import DeletionCode.Qary.SpectrumPath

/-!
Two bounded substring replacements cannot obstruct all three length-k blocks
at offsets 0, k+b, and 2(k+b). Equal (L-1)-windows therefore contain a common
surviving source block. Source uniqueness identifies its source coordinates.
This proves uniqueness and Boolean spectra for actual one-burst neighbours.
-/
namespace DeletionCode.Burst.Rigidity

open DeletionCode.Qary.Windows

variable {α : Type*}

def Avoids (k start pos len : ℕ) : Prop := start + k ≤ pos ∨ pos + len ≤ start

theorem avoids_later_of_not_avoids {k b start next pos len : ℕ}
    (hlen : len ≤ b) (hgap : start + k + b ≤ next)
    (hbad : ¬ Avoids k start pos len) : Avoids k next pos len := by
  unfold Avoids at *
  right
  omega

theorem exists_clean_block (k b a c p q u v : ℕ) (hu : u ≤ b) (hv : v ≤ b) :
    ∃ s : ℕ, s + k ≤ windowLength k b - 1 ∧
      (a + s + k ≤ p ∨ p + u ≤ a + s) ∧
      (c + s + k ≤ q ∨ q + v ≤ c + s) := by
  have hL : windowLength k b - 1 = 3 * k + 3 * b + 2 := by
    unfold windowLength
    omega
  by_cases ha0 : Avoids k a p u
  · by_cases hc0 : Avoids k c q v
    · refine ⟨0, by omega, ?_, ?_⟩
      · simpa only [Avoids, Nat.add_zero] using ha0
      · simpa only [Avoids, Nat.add_zero] using hc0
    · have hc1 : Avoids k (c + (k + b)) q v :=
        avoids_later_of_not_avoids hv (by omega) hc0
      have hc2 : Avoids k (c + 2 * (k + b)) q v :=
        avoids_later_of_not_avoids hv (by omega) hc0
      by_cases ha1 : Avoids k (a + (k + b)) p u
      · exact ⟨k + b, by omega, ha1, hc1⟩
      · have ha2 : Avoids k (a + 2 * (k + b)) p u :=
          avoids_later_of_not_avoids hu (by omega) ha1
        exact ⟨2 * (k + b), by omega, ha2, hc2⟩
  · have ha1 : Avoids k (a + (k + b)) p u :=
      avoids_later_of_not_avoids hu (by omega) ha0
    have ha2 : Avoids k (a + 2 * (k + b)) p u :=
      avoids_later_of_not_avoids hu (by omega) ha0
    by_cases hc1 : Avoids k (c + (k + b)) q v
    · exact ⟨k + b, by omega, ha1, hc1⟩
    · have hc2 : Avoids k (c + 2 * (k + b)) q v :=
        avoids_later_of_not_avoids hv (by omega) hc1
      exact ⟨2 * (k + b), by omega, ha2, hc2⟩

theorem shared_source_letters [Inhabited α] {n k b : ℕ} (hk : 1 ≤ k)
    (x : Letters α) (hx : KUnique x n k) (e f : Edit α)
    (he : e.Bounded b) (hf : f.Bounded b)
    (hev : e.InBounds n) (hfv : f.InBounds n)
    (a c : ℕ) (ha : a + (windowLength k b - 1) ≤ e.outputLength n)
    (hc : c + (windowLength k b - 1) ≤ f.outputLength n)
    (hag : Agree (e.word x) a (f.word x) c (windowLength k b - 1)) :
    ∃ s r : ℕ, s + k ≤ windowLength k b - 1 ∧ r + k ≤ n ∧
      ∀ i, i < k → e.origin (a + s + i) = some (r + i) ∧
        f.origin (c + s + i) = some (r + i) := by
  obtain ⟨s, hsk, hea, hfc⟩ := exists_clean_block k b a c e.pos f.pos
    e.replacement.length f.replacement.length he.2 hf.2
  obtain ⟨r, hr⟩ := e.clean_block a s k hea
  obtain ⟨r', hr'⟩ := f.clean_block c s k hfc
  have hrlast := e.origin_lt hev (i := a + s + (k - 1)) (by omega)
    (hr (k - 1) (by omega))
  have hr'last := f.origin_lt hfv (i := c + s + (k - 1)) (by omega)
    (hr' (k - 1) (by omega))
  have hri : r + k ≤ n := by omega
  have hr'i : r' + k ≤ n := by omega
  have hsource : Agree x r x r' k := by
    intro i hi
    have heq := hag (s + i) (by omega)
    calc
      x (r + i) = e.word x (a + s + i) := (e.word_of_origin x (hr i hi)).symm
      _ = f.word x (c + s + i) := by simpa only [Nat.add_assoc] using heq
      _ = x (r' + i) := f.word_of_origin x (hr' i hi)
  have hrr := hx r r' hri hr'i hsource
  subst r'
  exact ⟨s, r, hsk, hri, fun i hi => ⟨hr i hi, hr' i hi⟩⟩

theorem one_burst_unique [Inhabited α] {n k b : ℕ} (hk : 1 ≤ k)
    (x : Letters α) (hx : KUnique x n k) (e : Edit α)
    (he : e.Bounded b) (hev : e.InBounds n) :
    KUnique (e.word x) (e.outputLength n) (windowLength k b - 1) := by
  intro a c ha hc hag
  obtain ⟨s, r, _, _, hsource⟩ :=
    shared_source_letters hk x hx e e he he hev hev a c ha hc hag
  have h0 := hsource 0 (by omega)
  have hac := e.origin_injective h0.1 h0.2
  omega

theorem one_burst_spectrum_boolean [Inhabited α] {n k b : ℕ} (hk : 1 ≤ k)
    (x : Letters α) (hx : KUnique x n k) (e : Edit α)
    (he : e.Bounded b) (hev : e.InBounds n) :
    ∀ g, Qary.SignedSupport.wordSpectrum (e.word x) (e.outputLength n)
      (windowLength k b) g = 0 ∨
      Qary.SignedSupport.wordSpectrum (e.word x) (e.outputLength n)
      (windowLength k b) g = 1 :=
  Qary.SpectrumPath.spectrum_boolean _ _ _ (one_burst_unique hk x hx e he hev)

#print axioms exists_clean_block
#print axioms shared_source_letters
#print axioms one_burst_unique
#print axioms one_burst_spectrum_boolean

end DeletionCode.Burst.Rigidity
