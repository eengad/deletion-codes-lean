import DeletionCode.Burst.ChronologicalSeparation

/-!
Transport of separated chronological edit neighborhoods back to the source.
The inverse coordinate shifts are bounded by b at every step. Separation is
assumed only for the recorded current-word positions, never source positions.
-/
namespace DeletionCode.Burst.SourceTransport

open DeletionCode.Qary.Windows

variable {α : Type*}

/-- Pull a surviving position backward through one replacement. -/
def backward (e : Edit α) (p : ℕ) : ℕ :=
  if p < e.pos then p else p + e.removed - e.replacement.length

/-- Earlier operations are undone in reverse chronological order. -/
def sourcePosition : List (Edit α) → ℕ → ℕ
  | [], p => p
  | e :: es, p => backward e (sourcePosition es p)

def runLetters [Inhabited α] (x : Letters α) : List (Edit α) → Letters α
  | [] => x
  | e :: es => runLetters (e.word x) es

theorem backward_dist (e : Edit α) {b : ℕ} (hb : e.Bounded b) (p : ℕ) :
    Nat.dist (backward e p) p ≤ b := by
  have h₁ := hb.1
  have h₂ := hb.2
  unfold backward Nat.dist
  split <;> omega

theorem sourcePosition_dist (es : List (Edit α)) {b : ℕ}
    (hb : ∀ e ∈ es, e.Bounded b) (p : ℕ) :
    Nat.dist (sourcePosition es p) p ≤ es.length * b := by
  induction es with
  | nil => simp [sourcePosition]
  | cons e es ih =>
      have he := backward_dist e (hb e (List.mem_cons_self ..)) (sourcePosition es p)
      have ht := ih (fun f hf => hb f (List.mem_cons_of_mem _ hf))
      have htri := Nat.dist.triangle_inequality (backward e (sourcePosition es p))
        (sourcePosition es p) p
      simp only [sourcePosition, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem centered_agree [Inhabited α] (e : Edit α) (x : Letters α)
    (p H : ℕ) (hH : 1 ≤ H) (hp : H ≤ p)
    (hside : p + H ≤ e.pos ∨ e.pos + e.replacement.length + H ≤ p) :
    Agree (e.word x) (p - H) x (backward e p - H) (2 * H) := by
  intro i hi
  rcases hside with hbefore | hafter
  · have hp' : p < e.pos := by omega
    have hi' : p - H + i < e.pos := by omega
    simp only [Edit.word, backward, hp', hi', ite_true]
  · have hp' : ¬p < e.pos := by omega
    have hi' : ¬p - H + i < e.pos := by omega
    have hi'' : ¬p - H + i < e.pos + e.replacement.length := by omega
    have heq : p - H + i + e.removed - e.replacement.length =
        (p + e.removed - e.replacement.length) - H + i := by omega
    simp only [Edit.word, backward, hp', hi', hi'', ite_false, heq]

/-- A whole neighborhood of a later recorded center is unchanged in the
source, up to the accumulated coordinate shift. -/
theorem local_agree [Inhabited α] (es : List (Edit α)) (x : Letters α)
    (b p H : ℕ) (hH : 1 ≤ H)
    (hb : ∀ e ∈ es, e.Bounded b)
    (hmargin : H + es.length * b ≤ p)
    (hfar : ∀ e ∈ es, H + b + es.length * b ≤ Nat.dist p e.pos) :
    Agree (runLetters x es) (p - H) x (sourcePosition es p - H) (2 * H) := by
  induction es generalizing x with
  | nil => intro i hi; rfl
  | cons e es ih =>
      have hb' : ∀ f ∈ es, f.Bounded b := fun f hf => hb f (List.mem_cons_of_mem _ hf)
      have hdist := sourcePosition_dist es hb' p
      have he := hb e (List.mem_cons_self ..)
      have hfe := hfar e (List.mem_cons_self ..)
      have hlen : (e :: es).length * b = es.length * b + b := by
        simp [Nat.add_mul]
      rw [hlen] at hmargin hfe
      have hc : H ≤ sourcePosition es p := by unfold Nat.dist at hdist; omega
      have hside : sourcePosition es p + H ≤ e.pos ∨
          e.pos + e.replacement.length + H ≤ sourcePosition es p := by
        have hb₂ := he.2
        unfold Nat.dist at hdist hfe
        omega
      have ht := ih (e.word x) hb' (by omega) (by
        intro f hf
        have hh := hfar f (List.mem_cons_of_mem _ hf)
        rw [hlen] at hh
        omega)
      have heq := centered_agree e x (sourcePosition es p) H hH hc hside
      intro i hi
      exact (ht i hi).trans (heq i hi)

/-- Accumulated shifts preserve a quantitative separation of source centers. -/
theorem dist_source_positions (es fs : List (Edit α)) {b p q D : ℕ}
    (he : ∀ e ∈ es, e.Bounded b) (hf : ∀ f ∈ fs, f.Bounded b)
    (hsep : D ≤ Nat.dist p q) :
    D ≤ Nat.dist (sourcePosition es p) (sourcePosition fs q) +
      (es.length + fs.length) * b := by
  have hp := sourcePosition_dist es he p
  have hq := sourcePosition_dist fs hf q
  have h₁ := Nat.dist.triangle_inequality p (sourcePosition es p) (sourcePosition fs q)
  have h₂ := Nat.dist.triangle_inequality p (sourcePosition fs q) q
  rw [Nat.dist_comm p (sourcePosition es p)] at h₁
  rw [Nat.add_mul]
  omega

end DeletionCode.Burst.SourceTransport
