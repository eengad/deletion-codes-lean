import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
Equal-length confusability from genuine edit scripts. Each elementary edit
inserts, removes, or replaces one bit at an arbitrary list split. Alignments
are built from the four column types of the manuscript's edit version:
matched, deletion, insertion and substitution columns.

The confusability lemma is proved by induction along a script: an alignment
of cost at most e from the original word to the current word is maintained,
and each of the three edits raises its cost by at most one.
-/
namespace DeletionCode.EditAlignment

abbrev Word := List Bool

/-- A script with its exact numbers of deletions, insertions and substitutions. -/
inductive Script : Word → Word → ℕ → ℕ → ℕ → Prop
  | refl (word : Word) : Script word word 0 0 0
  | delete {y pre suffix : Word} {bit : Bool} {d i s : ℕ} :
      Script y (pre ++ bit :: suffix) d i s → Script y (pre ++ suffix) (d + 1) i s
  | insert {y pre suffix : Word} {bit : Bool} {d i s : ℕ} :
      Script y (pre ++ suffix) d i s → Script y (pre ++ bit :: suffix) d (i + 1) s
  | substitute {y pre suffix : Word} {bit : Bool} {d i s : ℕ} :
      Script y (pre ++ bit :: suffix) d i s → Script y (pre ++ (!bit) :: suffix) d i (s + 1)

/-- An alignment made exclusively of the four column types. A substitution
column holds a source bit and its negation on the target side. -/
inductive Alignment : Word → Word → ℕ → ℕ → ℕ → Prop
  | nil : Alignment [] [] 0 0 0
  | matched (bit : Bool) {y z : Word} {d i s : ℕ} :
      Alignment y z d i s → Alignment (bit :: y) (bit :: z) d i s
  | deletion (bit : Bool) {y z : Word} {d i s : ℕ} :
      Alignment y z d i s → Alignment (bit :: y) z (d + 1) i s
  | insertion (bit : Bool) {y z : Word} {d i s : ℕ} :
      Alignment y z d i s → Alignment y (bit :: z) d (i + 1) s
  | substitution (bit : Bool) {y z : Word} {d i s : ℕ} :
      Alignment y z d i s → Alignment (bit :: y) ((!bit) :: z) d i (s + 1)

theorem Script.trans {x y z : Word} {d₁ i₁ s₁ d₂ i₂ s₂ : ℕ}
    (hxy : Script x y d₁ i₁ s₁) (hyz : Script y z d₂ i₂ s₂) :
    Script x z (d₁ + d₂) (i₁ + i₂) (s₁ + s₂) := by
  induction hyz with
  | refl => simpa using hxy
  | delete h ih => simpa only [Nat.add_assoc] using Script.delete ih
  | insert h ih => simpa only [Nat.add_assoc] using Script.insert ih
  | substitute h ih => simpa only [Nat.add_assoc] using Script.substitute ih

theorem Script.reverse {y z : Word} {d i s : ℕ} (h : Script y z d i s) :
    Script z y i d s := by
  induction h with
  | refl => exact Script.refl _
  | @delete pre suffix bit d i s h ih =>
    have hfirst : Script (pre ++ suffix) (pre ++ bit :: suffix) 0 1 0 :=
      Script.insert (Script.refl _)
    simpa only [Nat.zero_add, Nat.add_comm 1 d] using hfirst.trans ih
  | @insert pre suffix bit d i s h ih =>
    have hfirst : Script (pre ++ bit :: suffix) (pre ++ suffix) 1 0 0 :=
      Script.delete (Script.refl _)
    simpa only [Nat.zero_add, Nat.add_comm 1 i] using hfirst.trans ih
  | @substitute pre suffix bit d i s h ih =>
    have hfirst : Script (pre ++ (!bit) :: suffix) (pre ++ bit :: suffix) 0 0 1 := by
      simpa only [Bool.not_not] using
        Script.substitute (Script.refl (pre ++ (!bit) :: suffix))
    simpa only [Nat.zero_add, Nat.add_comm 1 s] using hfirst.trans ih

theorem Script.length_balance {y z : Word} {d i s : ℕ} (h : Script y z d i s) :
    z.length + d = y.length + i := by
  induction h with
  | refl => omega
  | delete h ih => simp only [List.length_append, List.length_cons] at *; omega
  | insert h ih => simp only [List.length_append, List.length_cons] at *; omega
  | substitute h ih => simp only [List.length_append, List.length_cons] at *; omega

theorem Alignment.refl_self (word : Word) : Alignment word word 0 0 0 := by
  induction word with
  | nil => exact Alignment.nil
  | cons bit tail ih => exact Alignment.matched bit ih

theorem Alignment.length_balance {y z : Word} {d i s : ℕ} (h : Alignment y z d i s) :
    y.length + i = z.length + d := by
  induction h with
  | nil => rfl
  | matched bit h ih => simp only [List.length_cons]; omega
  | deletion bit h ih => simp only [List.length_cons]; omega
  | insertion bit h ih => simp only [List.length_cons]; omega
  | substitution bit h ih => simp only [List.length_cons]; omega

/-- Deleting one target letter raises the alignment cost by at most one:
a matched column becomes a deletion, an insertion column disappears, and a
substitution column becomes a deletion. -/
theorem Alignment.delete_target {y z : Word} {d i s : ℕ} (h : Alignment y z d i s) :
    ∀ (pre suffix : Word) (bit : Bool), z = pre ++ bit :: suffix →
      ∃ d' i' s', Alignment y (pre ++ suffix) d' i' s' ∧ d' + i' + s' ≤ d + i + s + 1 := by
  induction h with
  | nil =>
    intro pre suffix bit hz
    cases pre <;> simp at hz
  | matched b h ih =>
    intro pre suffix bit hz
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      exact ⟨_, _, _, Alignment.deletion b h, by omega⟩
    | cons c pre' =>
      simp only [List.cons_append, List.cons.injEq] at hz
      obtain ⟨rfl, hz'⟩ := hz
      obtain ⟨d', i', s', h', hc⟩ := ih pre' suffix bit hz'
      exact ⟨d', i', s', Alignment.matched b h', hc⟩
  | deletion b h ih =>
    intro pre suffix bit hz
    obtain ⟨d', i', s', h', hc⟩ := ih pre suffix bit hz
    exact ⟨d' + 1, i', s', Alignment.deletion b h', by omega⟩
  | insertion b h ih =>
    intro pre suffix bit hz
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      exact ⟨_, _, _, h, by omega⟩
    | cons c pre' =>
      simp only [List.cons_append, List.cons.injEq] at hz
      obtain ⟨rfl, hz'⟩ := hz
      obtain ⟨d', i', s', h', hc⟩ := ih pre' suffix bit hz'
      exact ⟨d', i' + 1, s', Alignment.insertion b h', by omega⟩
  | substitution b h ih =>
    intro pre suffix bit hz
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      exact ⟨_, _, _, Alignment.deletion b h, by omega⟩
    | cons c pre' =>
      simp only [List.cons_append, List.cons.injEq] at hz
      obtain ⟨rfl, hz'⟩ := hz
      obtain ⟨d', i', s', h', hc⟩ := ih pre' suffix bit hz'
      exact ⟨d', i', s' + 1, Alignment.substitution b h', by omega⟩

/-- Inserting one target letter adds one insertion column. -/
theorem Alignment.insert_target {y z : Word} {d i s : ℕ} (h : Alignment y z d i s) :
    ∀ (pre suffix : Word) (bit : Bool), z = pre ++ suffix →
      ∃ d' i' s', Alignment y (pre ++ bit :: suffix) d' i' s' ∧ d' + i' + s' ≤ d + i + s + 1 := by
  induction h with
  | nil =>
    intro pre suffix bit hz
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hz.symm
    exact ⟨0, 1, 0, Alignment.insertion bit Alignment.nil, by omega⟩
  | matched b h ih =>
    intro pre suffix bit hz
    cases pre with
    | nil =>
      simp only [List.nil_append] at hz
      subst hz
      exact ⟨_, _, _, Alignment.insertion bit (Alignment.matched b h), by omega⟩
    | cons c pre' =>
      simp only [List.cons_append, List.cons.injEq] at hz
      obtain ⟨rfl, hz'⟩ := hz
      obtain ⟨d', i', s', h', hc⟩ := ih pre' suffix bit hz'
      exact ⟨d', i', s', Alignment.matched b h', hc⟩
  | deletion b h ih =>
    intro pre suffix bit hz
    obtain ⟨d', i', s', h', hc⟩ := ih pre suffix bit hz
    exact ⟨d' + 1, i', s', Alignment.deletion b h', by omega⟩
  | insertion b h ih =>
    intro pre suffix bit hz
    cases pre with
    | nil =>
      simp only [List.nil_append] at hz
      subst hz
      exact ⟨_, _, _, Alignment.insertion bit (Alignment.insertion b h), by omega⟩
    | cons c pre' =>
      simp only [List.cons_append, List.cons.injEq] at hz
      obtain ⟨rfl, hz'⟩ := hz
      obtain ⟨d', i', s', h', hc⟩ := ih pre' suffix bit hz'
      exact ⟨d', i' + 1, s', Alignment.insertion b h', by omega⟩
  | substitution b h ih =>
    intro pre suffix bit hz
    cases pre with
    | nil =>
      simp only [List.nil_append] at hz
      subst hz
      exact ⟨_, _, _, Alignment.insertion bit (Alignment.substitution b h), by omega⟩
    | cons c pre' =>
      simp only [List.cons_append, List.cons.injEq] at hz
      obtain ⟨rfl, hz'⟩ := hz
      obtain ⟨d', i', s', h', hc⟩ := ih pre' suffix bit hz'
      exact ⟨d', i', s' + 1, Alignment.substitution b h', by omega⟩

/-- Replacing one target letter by its negation raises the cost by at most
one: a matched column becomes a substitution, an insertion keeps its kind,
and a substitution column becomes matched. -/
theorem Alignment.substitute_target {y z : Word} {d i s : ℕ} (h : Alignment y z d i s) :
    ∀ (pre suffix : Word) (bit : Bool), z = pre ++ bit :: suffix →
      ∃ d' i' s', Alignment y (pre ++ (!bit) :: suffix) d' i' s' ∧
        d' + i' + s' ≤ d + i + s + 1 := by
  induction h with
  | nil =>
    intro pre suffix bit hz
    cases pre <;> simp at hz
  | matched b h ih =>
    intro pre suffix bit hz
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      exact ⟨_, _, _, Alignment.substitution b h, by omega⟩
    | cons c pre' =>
      simp only [List.cons_append, List.cons.injEq] at hz
      obtain ⟨rfl, hz'⟩ := hz
      obtain ⟨d', i', s', h', hc⟩ := ih pre' suffix bit hz'
      exact ⟨d', i', s', Alignment.matched b h', hc⟩
  | deletion b h ih =>
    intro pre suffix bit hz
    obtain ⟨d', i', s', h', hc⟩ := ih pre suffix bit hz
    exact ⟨d' + 1, i', s', Alignment.deletion b h', by omega⟩
  | insertion b h ih =>
    intro pre suffix bit hz
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      exact ⟨_, _, _, Alignment.insertion (!b) h, by omega⟩
    | cons c pre' =>
      simp only [List.cons_append, List.cons.injEq] at hz
      obtain ⟨rfl, hz'⟩ := hz
      obtain ⟨d', i', s', h', hc⟩ := ih pre' suffix bit hz'
      exact ⟨d', i' + 1, s', Alignment.insertion b h', by omega⟩
  | @substitution b y z d i s h ih =>
    intro pre suffix bit hz
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      refine ⟨d, i, s, ?_, by omega⟩
      simpa only [Bool.not_not, List.nil_append] using Alignment.matched b h
    | cons c pre' =>
      simp only [List.cons_append, List.cons.injEq] at hz
      obtain ⟨rfl, hz'⟩ := hz
      obtain ⟨d', i', s', h', hc⟩ := ih pre' suffix bit hz'
      exact ⟨d', i', s' + 1, Alignment.substitution b h', by omega⟩

/-- Every script has an alignment of cost at most the script length. -/
theorem Alignment.of_script {y z : Word} {d i s : ℕ} (h : Script y z d i s) :
    ∃ d' i' s', Alignment y z d' i' s' ∧ d' + i' + s' ≤ d + i + s := by
  induction h with
  | refl => exact ⟨0, 0, 0, Alignment.refl_self _, Nat.le_refl _⟩
  | delete h ih =>
    obtain ⟨d', i', s', h', hc⟩ := ih
    obtain ⟨d'', i'', s'', h'', hc'⟩ := h'.delete_target _ _ _ rfl
    exact ⟨d'', i'', s'', h'', by omega⟩
  | insert h ih =>
    obtain ⟨d', i', s', h', hc⟩ := ih
    obtain ⟨d'', i'', s'', h'', hc'⟩ := h'.insert_target _ _ _ rfl
    exact ⟨d'', i'', s'', h'', by omega⟩
  | substitute h ih =>
    obtain ⟨d', i', s', h', hc⟩ := ih
    obtain ⟨d'', i'', s'', h'', hc'⟩ := h'.substitute_target _ _ _ rfl
    exact ⟨d'', i'', s'', h'', by omega⟩

/-- At most t edits in total, with an actual script witness. -/
def WithinEdits (t : ℕ) (y z : Word) : Prop :=
  ∃ d i s, Script y z d i s ∧ d + i + s ≤ t

/-- Manuscript lemma `lem:confuse`, edit version: two words of equal length
within t edits of a common output have an alignment with d deletions, d
insertions and s substitutions, 2d + s ≤ 2t. Distinctness is unnecessary. -/
theorem equal_length_confusability (y z u : Word) (n t : ℕ)
    (hy : y.length = n) (hz : z.length = n)
    (hyu : WithinEdits t y u) (hzu : WithinEdits t z u) :
    ∃ d s, 2 * d + s ≤ 2 * t ∧ Alignment y z d d s := by
  obtain ⟨dy, iy, sy, hyu, hcosty⟩ := hyu
  obtain ⟨dz, iz, sz, hzu, hcostz⟩ := hzu
  have hscript : Script y z (dy + iz) (iy + dz) (sy + sz) := hyu.trans hzu.reverse
  obtain ⟨d', i', s', halign, hcost⟩ := Alignment.of_script hscript
  have hbalance := halign.length_balance
  have hdi : i' = d' := by omega
  subst hdi
  exact ⟨i', s', by omega, halign⟩

#print axioms Script.trans
#print axioms Script.reverse
#print axioms Script.length_balance
#print axioms Alignment.of_script
#print axioms equal_length_confusability

end DeletionCode.EditAlignment
