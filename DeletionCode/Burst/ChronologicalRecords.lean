import DeletionCode.Burst.Basic

/-!
Chronological lists of genuine bounded substring replacements. No spacing
condition is imposed here; scripts may edit blocks created by earlier steps.
-/
namespace DeletionCode.Burst

variable {α : Type*}

namespace Edit

theorem apply_split (pre U V suffix : Word α) :
    (Edit.mk pre.length U.length V).apply (pre ++ U ++ suffix) =
      pre ++ V ++ suffix := by
  simp [apply, List.take_append, List.drop_append, List.append_assoc]

theorem sourceBlock_split (pre U V suffix : Word α) :
    (Edit.mk pre.length U.length V).sourceBlock (pre ++ U ++ suffix) = U := by
  simp [sourceBlock, List.drop_append, List.take_append, List.append_assoc]

theorem decomposition (e : Edit α) (x : Word α) :
    x.take e.pos ++ e.sourceBlock x ++ x.drop (e.pos + e.removed) = x := by
  rw [sourceBlock, ← List.drop_drop]
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

theorem apply_length (e : Edit α) (x : Word α) (h : e.InBounds x.length) :
    (e.apply x).length = e.outputLength x.length := by
  simp only [apply, outputLength, List.length_append, List.length_take,
    List.length_drop]
  unfold InBounds at h
  rw [Nat.min_eq_left (by omega)]
  omega

theorem sourceBlock_length (e : Edit α) (x : Word α) (h : e.InBounds x.length) :
    (e.sourceBlock x).length = e.removed := by
  simp only [sourceBlock, List.length_take, List.length_drop]
  exact Nat.min_eq_left (by unfold InBounds at h; omega)

theorem apply_ne (e : Edit α) (x : Word α) {b : ℕ} (h : e.Valid b x) :
    e.apply x ≠ x := by
  intro heq
  apply h.2.2
  have hx := (e.decomposition x).trans heq.symm
  simp only [apply] at hx
  exact List.append_cancel_left (List.append_cancel_right hx)

theorem valid_split (pre U V suffix : Word α) {b : ℕ}
    (hU : U.length ≤ b) (hV : V.length ≤ b) (hne : U ≠ V) :
    (Edit.mk pre.length U.length V).Valid b (pre ++ U ++ suffix) := by
  refine ⟨⟨hU, hV⟩, ?_, ?_⟩
  · simp [InBounds]
  · simpa only [sourceBlock_split] using hne

end Edit

theorem Script.trans {b r s : ℕ} {x y z : Word α}
    (hxy : Script b x y r) (hyz : Script b y z s) : Script b x z (r + s) := by
  induction hyz with
  | refl => simpa using hxy
  | step hU hV hne history ih =>
      simpa only [Nat.add_assoc] using Script.step hU hV hne ih

theorem Script.reverse {b r : ℕ} {x y : Word α}
    (h : Script b x y r) : Script b y x r := by
  induction h with
  | refl => exact Script.refl _
  | @step pre suffix U V r hU hV hne history ih =>
      have hfirst : Script b (pre ++ V ++ suffix) (pre ++ U ++ suffix) 1 :=
        Script.step hV hU hne.symm (Script.refl _)
      simpa only [Nat.add_comm 1 r] using hfirst.trans ih

theorem Script.length_le {b r : ℕ} {x y : Word α}
    (h : Script b x y r) : y.length ≤ x.length + r * b := by
  induction h with
  | refl => simp
  | step hU hV hne history ih =>
      simp only [List.length_append, Nat.add_mul, Nat.one_mul] at *
      omega

theorem Script.source_length_le {b r : ℕ} {x y : Word α}
    (h : Script b x y r) : x.length ≤ y.length + r * b := h.reverse.length_le

theorem Confusable.script {b t : ℕ} {x y : Word α} (h : Confusable b t x y) :
    ∃ r, r ≤ 2 * t ∧ Script b x y r := by
  obtain ⟨z, ⟨r, hr, hx⟩, ⟨s, hs, hy⟩⟩ := h
  exact ⟨r + s, by omega, hx.trans hy.reverse⟩

/-- Execute recorded replacements in their chronological order. -/
def run (x : Word α) : List (Edit α) → Word α
  | [] => x
  | e :: es => run (e.apply x) es

/-- Every recorded operation must be valid on the actual current word. -/
inductive Executes (b : ℕ) : Word α → List (Edit α) → Word α → Prop
  | nil (x : Word α) : Executes b x [] x
  | cons {x y : Word α} {e : Edit α} {es : List (Edit α)}
      (valid : e.Valid b x) (tail : Executes b (e.apply x) es y) :
      Executes b x (e :: es) y

theorem run_append (x : Word α) (es fs : List (Edit α)) :
    run x (es ++ fs) = run (run x es) fs := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih => exact ih _

theorem Executes.run_eq {b : ℕ} {x y : Word α} {es : List (Edit α)}
    (h : Executes b x es y) : run x es = y := by
  induction h with
  | nil => rfl
  | cons valid tail ih => exact ih

theorem Executes.append {b : ℕ} {x y z : Word α} {es fs : List (Edit α)}
    (hxy : Executes b x es y) (hyz : Executes b y fs z) :
    Executes b x (es ++ fs) z := by
  induction hxy with
  | nil => exact hyz
  | cons valid tail ih => exact Executes.cons valid (ih hyz)

theorem Executes.script {b : ℕ} {x y : Word α} {es : List (Edit α)}
    (h : Executes b x es y) : Script b x y es.length := by
  induction h with
  | nil => exact Script.refl _
  | @cons x y e es valid tail ih =>
      have hfirst : Script b x (e.apply x) 1 := by
        have hh : Script b x (x.take e.pos ++ e.sourceBlock x ++
            x.drop (e.pos + e.removed)) 0 := by
          rw [e.decomposition x]
          exact Script.refl x
        have hs := Script.step
          (by simpa only [e.sourceBlock_length x valid.2.1] using valid.1.1)
          valid.1.2 valid.2.2 hh
        exact hs
      simpa only [List.length_cons, Nat.add_comm 1] using hfirst.trans ih

theorem Script.exists_executes {b r : ℕ} {x y : Word α}
    (h : Script b x y r) : ∃ es, es.length = r ∧ Executes b x es y := by
  induction h with
  | refl => exact ⟨[], rfl, Executes.nil _⟩
  | @step pre suffix U V r hU hV hne history ih =>
      obtain ⟨es, hlen, hex⟩ := ih
      let e : Edit α := ⟨pre.length, U.length, V⟩
      refine ⟨es ++ [e], by simpa [hlen], ?_⟩
      apply hex.append
      apply Executes.cons (Edit.valid_split pre U V suffix hU hV hne)
      simpa only [e, Edit.apply_split] using Executes.nil (b := b) (pre ++ V ++ suffix)

theorem Executes.length_le {b : ℕ} {x y : Word α} {es : List (Edit α)}
    (h : Executes b x es y) : y.length ≤ x.length + es.length * b := h.script.length_le

theorem Executes.source_length_le {b : ℕ} {x y : Word α} {es : List (Edit α)}
    (h : Executes b x es y) : x.length ≤ y.length + es.length * b :=
  h.script.source_length_le

theorem Executes.take {b : ℕ} {x y : Word α} {es : List (Edit α)}
    (h : Executes b x es y) (i : ℕ) : Executes b x (es.take i) (run x (es.take i)) := by
  induction h generalizing i with
  | nil => simpa only [List.take_nil, run] using Executes.nil (b := b) _
  | cons valid tail ih =>
      cases i with
      | zero => exact Executes.nil _
      | succ i => exact Executes.cons valid (ih i)

theorem Executes.get_valid {b : ℕ} {x y : Word α} {es : List (Edit α)}
    (h : Executes b x es y) (i : Fin es.length) :
    (es.get i).Valid b (run x (es.take i.val)) := by
  induction h with
  | nil => exact Fin.elim0 i
  | @cons x y e es valid tail ih =>
      cases i using Fin.cases with
      | zero => exact valid
      | succ i => exact ih i

theorem Executes.position_le {b : ℕ} {x y : Word α} {es : List (Edit α)}
    (h : Executes b x es y) (i : Fin es.length) :
    (es.get i).pos ≤ x.length + i.val * b := by
  have hv := (h.get_valid i).2.1
  have hl := (h.take i.val).length_le
  rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt i.isLt)] at hl
  unfold Edit.InBounds at hv
  omega

end DeletionCode.Burst
