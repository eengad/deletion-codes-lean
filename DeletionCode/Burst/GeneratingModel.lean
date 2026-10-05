import DeletionCode.Burst.ConcreteModel
import DeletionCode.Qary.SupportComponents
import Mathlib.Data.Fintype.Quotient

/-!
Constructing decoder semantics from generating families of actual edited words.
Roots are selected once per family component, and source occurrences are chosen
from the generating condition. Decoder-success and recovery traces are not
assumed in this construction. Signed rule/catalogue identification is separate.
-/
namespace DeletionCode.Burst.GeneratingModel

variable {α : Type*} [DecidableEq α] [Inhabited α]

open DeletionCode.Qary.Windows DeletionCode.Burst.HeaderRecovery DeletionCode.Burst.PathMemory DeletionCode.Burst.SelectedWindows DeletionCode.Qary.RootSelection DeletionCode.Burst.ConcreteModel

structure EditedFamily (α : Type*) [Inhabited α] (B : Type*) (k d : ℕ) where
  header : B → Header α
  long : B → Letters α
  rank : B → ℕ
  valid : ∀ b, (header b).Valid k d
  header_matches : ∀ b, (header b).Matches (long b)
  initial_agreement : ∀ b, Agree (negativePath (header b) (long b)) 0
    (positivePath (header b) (long b)) 0 (windowLength k d - 1)

variable {B : Type*} {k d : ℕ}

def EditedFamily.family (E : EditedFamily α B k d) : Family α B where
  rank := E.rank
  path b side := pathLetters k d (E.header b) (E.long b) side
  extra b side := pathLength k d (E.header b) side - windowLength k d

theorem EditedFamily.path_length_eq (E : EditedFamily α B k d) (b : B) (side : Bool) :
    pathLength k d (E.header b) side = windowLength k d + E.family.extra b side := by
  have hn := (negativeLength_bounds (E.valid b)).1
  have hp := (positiveLength_bounds (E.valid b)).1
  cases side <;> dsimp [family, pathLength] <;> omega

theorem EditedFamily.negative_extra (E : EditedFamily α B k d) (b : B) :
    E.family.extra b false = negativeExtra k d (E.header b) := rfl

def componentSetoid (F : Family α B) (L : ℕ) : Setoid B where
  r := F.Connected L
  iseqv := ⟨fun b => Relation.EqvGen.refl b,
    fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩

abbrev Components (E : EditedFamily α B k d) := Quotient (componentSetoid E.family (windowLength k d))

theorem component_has_root (E : EditedFamily α B k d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k d))
    (C : Components E) :
    ∃ b, Quotient.mk (componentSetoid E.family (windowLength k d)) b = C ∧
      ∃ a, a + negativeLength (E.header b) ≤ n ∧
        Agree x a (negativePath (E.header b) (E.long b)) 0 (negativeLength (E.header b)) := by
  induction C using Quotient.inductionOn with
  | _ b =>
    obtain ⟨r, a, hr, ha, hagree⟩ := E.family.component_root_subword
      x n k (windowLength k d) hx (by dsimp [windowLength]; omega) hg b
    have hlen : windowLength k d + E.family.extra r false = negativeLength (E.header r) :=
      (E.path_length_eq r false).symm
    rw [hlen] at ha hagree
    refine ⟨r, Quotient.sound hr, a, ?_, ?_⟩
    · exact ha
    · exact hagree

noncomputable def selectedRoot (E : EditedFamily α B k d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k d))
    (C : Components E) : B := Classical.choose (component_has_root E x n hx hg C)

theorem selectedRoot_spec (E : EditedFamily α B k d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k d))
    (C : Components E) :
    let b := selectedRoot E x n hx hg C
    Quotient.mk (componentSetoid E.family (windowLength k d)) b = C ∧
      ∃ a, a + negativeLength (E.header b) ≤ n ∧
        Agree x a (negativePath (E.header b) (E.long b)) 0 (negativeLength (E.header b)) :=
  Classical.choose_spec (component_has_root E x n hx hg C)

def SourceValid (E : EditedFamily α B k d) (x : Letters α) (n : ℕ)
    (b : B) (w : Recovery.Slot) (source : Option B) : Prop :=
  match source with
  | none => ∃ a, a + windowLength k d ≤ n ∧
      Agree x a (negativePath (E.header b) (E.long b))
        (windowStart (negativeExtra k d (E.header b)) w) (windowLength k d)
  | some a => E.rank a < E.rank b ∧
      ∃ side j, j + windowLength k d ≤ pathLength k d (E.header a) side ∧
        Agree (negativePath (E.header b) (E.long b))
          (windowStart (negativeExtra k d (E.header b)) w)
          (pathLetters k d (E.header a) (E.long a) side) j (windowLength k d)

theorem source_exists (E : EditedFamily α B k d) (x : Letters α) (n : ℕ)
    (hg : E.family.Generating x n (windowLength k d)) (b : B) (w : Recovery.Slot) :
    ∃ source, SourceValid E x n b w source := by
  have hvalid : windowStart (negativeExtra k d (E.header b)) w ≤ E.family.extra b false :=
    windowStart_le _ w
  rcases hg b _ hvalid with hbase | ⟨a, side, j, hearlier, hj, hagree⟩
  · exact ⟨none, hbase⟩
  · refine ⟨some a, hearlier, side, j, ?_, hagree⟩
    rw [E.path_length_eq a side]
    omega

noncomputable def source (E : EditedFamily α B k d) (x : Letters α) (n : ℕ)
    (hg : E.family.Generating x n (windowLength k d)) (b : B) (w : Recovery.Slot) : Option B :=
  Classical.choose (source_exists E x n hg b w)

theorem source_spec (E : EditedFamily α B k d) (x : Letters α) (n : ℕ)
    (hg : E.family.Generating x n (windowLength k d)) (b : B) (w : Recovery.Slot) :
    SourceValid E x n b w (source E x n hg b w) :=
  Classical.choose_spec (source_exists E x n hg b w)

theorem adjacent_symm (F : Family α B) (L : ℕ) {a b : B} (h : F.Adjacent L a b) :
    F.Adjacent L b a := by
  obtain ⟨sa, sb, i, j, hi, hj, hbi, hbj, hagree⟩ := h
  exact ⟨sb, sa, j, i, hj, hi, hbj, hbi, fun q hq => (hagree q hq).symm⟩

private theorem reach_trans {adj : B → B → Prop} {a b c : B}
    (hab : Recovery.Reach adj a b) (hbc : Recovery.Reach adj b c) :
    Recovery.Reach adj a c := by
  induction hbc with
  | refl => exact hab
  | tail hbc hcd ih => exact Recovery.Reach.tail ih hcd

theorem connected_reach (F : Family α B) (L : ℕ) {a b : B} (h : F.Connected L a b) :
    Recovery.Reach (F.Adjacent L) a b := by
  have aux : ∀ {a b}, F.Connected L a b →
      Recovery.Reach (F.Adjacent L) a b ∧ Recovery.Reach (F.Adjacent L) b a := by
    intro a b h
    induction h with
    | rel a b h => exact ⟨Recovery.Reach.tail (Recovery.Reach.refl a) h,
        Recovery.Reach.tail (Recovery.Reach.refl b) (adjacent_symm F L h)⟩
    | refl a => exact ⟨Recovery.Reach.refl a, Recovery.Reach.refl a⟩
    | symm a b h ih => exact ⟨ih.2, ih.1⟩
    | trans a b c hab hbc ihab ihbc =>
      exact ⟨reach_trans ihab.1 ihbc.1, reach_trans ihbc.2 ihab.2⟩
  exact (aux h).1

noncomputable def schedule (E : EditedFamily α B k d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k d)) : Recovery.Data B where
  rank := E.rank
  source := source E x n hg
  earlier b w a h := by
    have hs := source_spec E x n hg b w
    rw [h] at hs
    exact hs.1
  adjacent := E.family.Adjacent (windowLength k d)
  root b := ∃ C, selectedRoot E x n hx hg C = b
  rooted b := by
    let C : Components E := Quotient.mk _ b
    let r := selectedRoot E x n hx hg C
    refine ⟨r, ⟨C, rfl⟩, connected_reach E.family (windowLength k d) ?_⟩
    exact Quotient.exact (selectedRoot_spec E x n hx hg C).1

/-- All decoder-local semantic facts are derived from a generating edited family. -/
noncomputable def model (E : EditedFamily α B k d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k d)) : Model B x n k d where
  header := E.header
  long := E.long
  schedule := schedule E x n hx hg
  valid := E.valid
  header_matches := E.header_matches
  base_occurrence b w h := by
    have hs := source_spec E x n hg b w
    change source E x n hg b w = none at h
    rw [h] at hs
    exact hs
  supplier_occurrence b w a h := by
    have hs := source_spec E x n hg b w
    change source E x n hg b w = some a at h
    rw [h] at hs
    exact hs.2
  adjacent_seed a b h := by
    obtain ⟨sa, sb, i, j, hi, hj, hbi, hbj, hagree⟩ := h
    refine ⟨sa, sb, i, j, ?_, ?_, ?_⟩
    · rw [E.path_length_eq a sa]
      dsimp [windowLength] at hbi ⊢
      omega
    · rw [E.path_length_eq b sb]
      dsimp [windowLength] at hbj ⊢
      omega
    · intro q hq
      exact hagree q (by dsimp [windowLength]; omega)
  root_occurrence b h := by
    obtain ⟨C, rfl⟩ := h
    exact (selectedRoot_spec E x n hx hg C).2

#print axioms component_has_root
#print axioms source_exists
#print axioms connected_reach
#print axioms model

end DeletionCode.Burst.GeneratingModel
