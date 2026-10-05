import DeletionCode.Burst.SourceTransport
import DeletionCode.Burst.WordFacts
import Mathlib.Tactic.Linarith

namespace DeletionCode.Burst

open DeletionCode.Qary.Windows DeletionCode.Qary.CatalogueWords
open SourceTransport

variable {α : Type*}

theorem Executes.bounded {b : ℕ} {x y : Word α} {es : List (Edit α)}
    (h : Executes b x es y) : ∀ e ∈ es, e.Bounded b := by
  intro e he
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
  simpa only [hi] using (h.get_valid i).1

theorem Executes.listLetters_run [Inhabited α] {b : ℕ} {x y : Word α}
    {es : List (Edit α)} (h : Executes b x es y) :
    listLetters (run x es) = runLetters (listLetters x) es := by
  induction h with
  | nil => rfl
  | cons valid tail ih =>
      simp only [run, runLetters]
      rw [ih, Edit.listLetters_apply _ _ valid.2.1]

def originalPosition (es : List (Edit α)) (i : Fin es.length) : ℕ :=
  sourcePosition (es.take i.val) (es.get i).pos

def originalEdit (es : List (Edit α)) (i : Fin es.length) : Edit α :=
  {es.get i with pos := originalPosition es i}

theorem originalPosition_dist {b : ℕ} {x y : Word α} {es : List (Edit α)}
    (h : Executes b x es y) (i : Fin es.length) :
    Nat.dist (originalPosition es i) (es.get i).pos ≤ i.val * b := by
  have hh := sourcePosition_dist (es.take i.val) (h.take i.val).bounded (es.get i).pos
  simpa only [originalPosition, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt i.isLt)] using hh

theorem prefix_mem_get {es : List (Edit α)} (i : Fin es.length) {e : Edit α}
    (he : e ∈ es.take i.val) : ∃ j : Fin es.length, j.val < i.val ∧ es.get j = e := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp he
  have hji : j.val < i.val := by
    have hh := j.isLt
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt i.isLt)] at hh
    exact hh
  refine ⟨⟨j.val, by omega⟩, hji, ?_⟩
  simpa only [List.get_eq_getElem, List.getElem_take] using hj

theorem originalPosition_margins {b t L : ℕ} {x y : Word α}
    {es : List (Edit α)} (h : Executes b x es y) (hlen : es.length ≤ 2 * t)
    (hsep : Separated x.length (8 * (L + t * b)) es) (hbL : b ≤ L)
    (i : Fin es.length) :
    2 * (L + b) ≤ originalPosition es i ∧
      originalPosition es i + (es.get i).removed + 2 * (L + b) ≤ x.length := by
  have hd := originalPosition_dist h i
  have hp := hsep.1 i
  have hb := (h.get_valid i).1.1
  have hmul : i.val * b ≤ (2 * t) * b := Nat.mul_le_mul_right b (by omega)
  unfold Nat.dist at hd
  have hlow : (es.get i).pos ≤ originalPosition es i + i.val * b := by omega
  have hhigh : originalPosition es i ≤ (es.get i).pos + i.val * b := by omega
  dsimp only at hp
  constructor <;> nlinarith

theorem chronologicalPosition_margins {b t L : ℕ} {x y : Word α}
    {es : List (Edit α)} (h : Executes b x es y) (hlen : es.length ≤ 2 * t)
    (hsep : Separated x.length (8 * (L + t * b)) es) (hbL : b ≤ L)
    (i : Fin es.length) :
    2 * (L + b) ≤ (es.get i).pos ∧
      (es.get i).pos + (es.get i).removed + 2 * (L + b) ≤
        (run x (es.take i.val)).length := by
  have hp := hsep.1 i
  dsimp only at hp
  have hb := (h.get_valid i).1.1
  have hlen' := (h.take i.val).source_length_le
  rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt i.isLt)] at hlen'
  have hmul : i.val * b ≤ (2 * t) * b := Nat.mul_le_mul_right b (by omega)
  constructor <;> nlinarith

theorem originalPositions_separated {b t L : ℕ} {x y : Word α}
    {es : List (Edit α)} (h : Executes b x es y) (hlen : es.length ≤ 2 * t)
    (hsep : Separated x.length (8 * (L + t * b)) es)
    (i j : Fin es.length) (hij : i ≠ j) :
    8 * L + 4 * t * b ≤ Nat.dist (originalPosition es i) (originalPosition es j) := by
  have hh := dist_source_positions (es.take i.val) (es.take j.val)
    (h.take i.val).bounded (h.take j.val).bounded (hsep.2 i j hij)
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt i.isLt),
    Nat.min_eq_left (Nat.le_of_lt j.isLt)] at hh
  have hmul : (i.val + j.val) * b ≤ (4 * t) * b :=
    Nat.mul_le_mul_right b (by omega)
  change 8 * L + 4 * t * b ≤ Nat.dist
    (sourcePosition (es.take i.val) (es.get i).pos)
    (sourcePosition (es.take j.val) (es.get j).pos)
  nlinarith

/-- The entire source neighborhood needed for one local bubble occurs,
unchanged, around the actual chronological operation. -/
theorem separated_prefix_agree [Inhabited α] {b t L : ℕ} {x y : Word α}
    {es : List (Edit α)} (h : Executes b x es y) (hlen : es.length ≤ 2 * t)
    (hsep : Separated x.length (8 * (L + t * b)) es)
    (hL : 1 ≤ L) (hbL : b ≤ L) (i : Fin es.length) :
    Agree (listLetters (run x (es.take i.val))) ((es.get i).pos - (L + b))
      (listLetters x) (originalPosition es i - (L + b)) (2 * (L + b)) := by
  rw [(h.take i.val).listLetters_run]
  apply local_agree (es.take i.val) (listLetters x) b (es.get i).pos (L + b)
    (by omega) (h.take i.val).bounded
  · have hp := (hsep.1 i).1
    have hi : i.val * b ≤ (2 * t) * b := Nat.mul_le_mul_right b (by omega)
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt i.isLt)]
    nlinarith
  · intro e he
    obtain ⟨j, hj, rfl⟩ := prefix_mem_get i he
    have hij : i ≠ j := by intro hh; subst j; omega
    have hp := hsep.2 i j hij
    have hi : i.val * b ≤ (2 * t) * b := Nat.mul_le_mul_right b (by omega)
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt i.isLt)]
    nlinarith

theorem originalEdit_sourceBlock [Inhabited α] {b t L : ℕ} {x y : Word α}
    {es : List (Edit α)} (h : Executes b x es y) (hlen : es.length ≤ 2 * t)
    (hsep : Separated x.length (8 * (L + t * b)) es)
    (hL : 1 ≤ L) (hbL : b ≤ L) (i : Fin es.length) :
    (originalEdit es i).sourceBlock x =
      (es.get i).sourceBlock (run x (es.take i.val)) := by
  have hm := originalPosition_margins h hlen hsep hbL i
  have hsrc : (originalEdit es i).InBounds x.length := by
    change originalPosition es i + (es.get i).removed ≤ x.length
    omega
  have hcurrent := (h.get_valid i).2.1
  have hb := (h.get_valid i).1.1
  have hp := (hsep.1 i).1
  dsimp only at hp
  have hpH : L + b ≤ (es.get i).pos := by nlinarith
  have haH : L + b ≤ originalPosition es i := by omega
  have hag := separated_prefix_agree h hlen hsep hL hbL i
  apply eq_of_listLetters
  · rw [Edit.sourceBlock_length _ _ hsrc, Edit.sourceBlock_length _ _ hcurrent]
    rfl
  · intro j hj
    rw [Edit.sourceBlock_length _ _ hsrc] at hj
    have hj' : j < (es.get i).removed := hj
    simp only [Nat.zero_add]
    rw [Edit.sourceBlock_letters _ _ hj, Edit.sourceBlock_letters _ _ hj']
    change listLetters x (originalPosition es i + j) =
      listLetters (run x (es.take i.val)) ((es.get i).pos + j)
    have heq := hag (L + b + j) (by omega)
    have hs : (es.get i).pos - (L + b) + (L + b + j) = (es.get i).pos + j := by omega
    have ht : originalPosition es i - (L + b) + (L + b + j) =
        originalPosition es i + j := by omega
    rw [hs, ht] at heq
    exact heq.symm

/-- Moving a separated chronological operation back to its derived source
position gives a valid bounded nontrivial burst in the original source. -/
theorem originalEdit_valid [Inhabited α] {b t L : ℕ} {x y : Word α}
    {es : List (Edit α)} (h : Executes b x es y) (hlen : es.length ≤ 2 * t)
    (hsep : Separated x.length (8 * (L + t * b)) es)
    (hL : 1 ≤ L) (hbL : b ≤ L) (i : Fin es.length) :
    (originalEdit es i).Valid b x := by
  refine ⟨(h.get_valid i).1, ?_, ?_⟩
  · have hm := (originalPosition_margins h hlen hsep hbL i).2
    change originalPosition es i + (es.get i).removed ≤ x.length
    omega
  · rw [originalEdit_sourceBlock h hlen hsep hL hbL i]
    exact (h.get_valid i).2.2

end DeletionCode.Burst
