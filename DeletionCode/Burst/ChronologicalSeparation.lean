import DeletionCode.Burst.FiniteRecords

/-!
Separation is tested on the positions recorded in the actual intermediate
words. It does not assume that the records are already source coordinates.
-/
namespace DeletionCode.Burst

variable {α : Type*}

def PositionsSeparated {r : ℕ} (n D : ℕ) (a : Fin r → ℕ) : Prop :=
  (∀ i, D ≤ a i ∧ a i + D ≤ n) ∧
    ∀ i j, i ≠ j → D ≤ Nat.dist (a i) (a j)

def Separated (n D : ℕ) (es : List (Edit α)) : Prop :=
  PositionsSeparated n D (fun i => (es.get i).pos)

theorem not_separated_bad [Inhabited α] {b N n D : ℕ}
    (es : List (Edit α)) (hp : ∀ i : Fin es.length, (es.get i).pos < N)
    (hb : ∀ i : Fin es.length, (es.get i).Bounded b)
    (hN : N ≤ n + D) (hsep : ¬Separated n D es) :
    FiniteRecords.Bad n D (FiniteRecords.encode es hp hb) := by
  classical
  by_contra hbad
  apply hsep
  constructor
  · intro i
    change D ≤ (es.get i).pos ∧ (es.get i).pos + D ≤ n
    have hleft : D ≤ (es.get i).pos := by
      by_contra hh
      apply hbad
      exact Or.inl ⟨i, by simpa only [FiniteRecords.encode] using Nat.lt_of_not_ge hh⟩
    have hright : D ≤ Nat.dist (es.get i).pos n := by
      by_contra hh
      apply hbad
      exact Or.inr (Or.inl ⟨i, by
        simpa only [FiniteRecords.encode] using (Nat.lt_of_not_ge hh)⟩)
    have hpi := hp i
    unfold Nat.dist at hright
    exact ⟨hleft, by omega⟩
  · intro i j hij
    by_contra hh
    apply hbad
    exact Or.inr (Or.inr ⟨i, j, hij, by
      simpa only [FiniteRecords.encode] using (Nat.lt_of_not_ge hh)⟩)

/-- A partner admitting a short or nonseparated chronological script. -/
def Exceptional (b t n D : ℕ) (x y : Word α) : Prop :=
  ∃ es, Executes b x es y ∧ es.length ≤ 2 * t ∧
    (es.length < 2 * t ∨ ¬Separated n D es)

theorem confusable_dichotomy {b t n D : ℕ} {x y : Word α}
    (h : Confusable b t x y) :
    Exceptional b t n D x y ∨
      ∃ es, Executes b x es y ∧ es.length = 2 * t ∧ Separated n D es := by
  classical
  obtain ⟨r, hr, hs⟩ := h.script
  obtain ⟨es, hlen, hex⟩ := hs.exists_executes
  by_cases hshort : es.length < 2 * t
  · exact Or.inl ⟨es, hex, by omega, Or.inl hshort⟩
  by_cases hsep : Separated n D es
  · exact Or.inr ⟨es, hex, by omega, hsep⟩
  · exact Or.inl ⟨es, hex, by omega, Or.inr hsep⟩

end DeletionCode.Burst
