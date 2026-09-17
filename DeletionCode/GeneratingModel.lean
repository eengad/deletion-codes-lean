import DeletionCode.ConcreteModel
import DeletionCode.SupportComponents
import Mathlib.Data.Fintype.Quotient

/-!
Constructing decoder semantics from generating families of actual edited words.
Roots are selected once per family component, and source occurrences are chosen
from the generating condition. Decoder-success and recovery traces are not
assumed in this construction. Signed rule/catalogue identification is separate.
-/
namespace DeletionCode.GeneratingModel

open Windows HeaderRecovery PathMemory SelectedWindows RootSelection ConcreteModel

structure EditedFamily (B : Type*) (k : ℕ) where
  header : B → Header
  long : B → Letters
  rank : B → ℕ
  rho_lower : ∀ b, 1 ≤ (header b).rho
  rho_upper : ∀ b, (header b).rho ≤ k + 1
  header_bit : ∀ b, long b (editOffset k) = (header b).bit

variable {B : Type*} {k : ℕ}

def EditedFamily.family (E : EditedFamily B k) : Family B where
  rank := E.rank
  path b side := pathLetters k (E.header b) (E.long b) side
  extra b side := pathLength k (E.header b) side - windowLength k

theorem EditedFamily.path_length_eq (E : EditedFamily B k) (b : B) (side : Bool) :
    pathLength k (E.header b) side = windowLength k + E.family.extra b side := by
  have hlo := E.rho_lower b
  have hhi := E.rho_upper b
  cases side <;> cases ho : (E.header b).orientation <;>
    simp [family, pathLength, negativeLength, positiveLength, longLength,
      shortLength, windowLength, ho] <;> omega

theorem EditedFamily.negative_extra (E : EditedFamily B k) (b : B) :
    E.family.extra b false = negativeExtra k (E.header b) := rfl

def componentSetoid (F : Family B) (L : ℕ) : Setoid B where
  r := F.Connected L
  iseqv := ⟨fun b => Relation.EqvGen.refl b,
    fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩

abbrev Components (E : EditedFamily B k) := Quotient (componentSetoid E.family (windowLength k))

theorem component_has_root (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k))
    (C : Components E) :
    ∃ b, Quotient.mk (componentSetoid E.family (windowLength k)) b = C ∧
      ∃ a, a + negativeLength k (E.header b) ≤ n ∧
        Agree x a (negativePath k (E.header b) (E.long b)) 0 (negativeLength k (E.header b)) := by
  induction C using Quotient.inductionOn with
  | _ b =>
    obtain ⟨r, a, hr, ha, hagree⟩ := E.family.component_root_subword
      x n k (windowLength k) hx (by dsimp [windowLength]; omega) hg b
    have hlen : windowLength k + E.family.extra r false = negativeLength k (E.header r) :=
      (E.path_length_eq r false).symm
    rw [hlen] at ha hagree
    refine ⟨r, Quotient.sound hr, a, ?_, ?_⟩
    · exact ha
    · exact hagree

noncomputable def selectedRoot (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k))
    (C : Components E) : B := Classical.choose (component_has_root E x n hx hg C)

theorem selectedRoot_spec (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k))
    (C : Components E) :
    let b := selectedRoot E x n hx hg C
    Quotient.mk (componentSetoid E.family (windowLength k)) b = C ∧
      ∃ a, a + negativeLength k (E.header b) ≤ n ∧
        Agree x a (negativePath k (E.header b) (E.long b)) 0 (negativeLength k (E.header b)) :=
  Classical.choose_spec (component_has_root E x n hx hg C)

def SourceValid (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (b : B) (w : Recovery.Slot) (source : Option B) : Prop :=
  match source with
  | none => ∃ a, a + windowLength k ≤ n ∧
      Agree x a (negativePath k (E.header b) (E.long b))
        (windowStart (negativeExtra k (E.header b)) w) (windowLength k)
  | some a => E.rank a < E.rank b ∧
      ∃ side j, j + windowLength k ≤ pathLength k (E.header a) side ∧
        Agree (negativePath k (E.header b) (E.long b))
          (windowStart (negativeExtra k (E.header b)) w)
          (pathLetters k (E.header a) (E.long a) side) j (windowLength k)

theorem source_exists (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hg : E.family.Generating x n (windowLength k)) (b : B) (w : Recovery.Slot) :
    ∃ source, SourceValid E x n b w source := by
  have hvalid : windowStart (negativeExtra k (E.header b)) w ≤ E.family.extra b false :=
    windowStart_le _ w
  rcases hg b _ hvalid with hbase | ⟨a, side, j, hearlier, hj, hagree⟩
  · exact ⟨none, hbase⟩
  · refine ⟨some a, hearlier, side, j, ?_, hagree⟩
    rw [E.path_length_eq a side]
    omega

noncomputable def source (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hg : E.family.Generating x n (windowLength k)) (b : B) (w : Recovery.Slot) : Option B :=
  Classical.choose (source_exists E x n hg b w)

theorem source_spec (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hg : E.family.Generating x n (windowLength k)) (b : B) (w : Recovery.Slot) :
    SourceValid E x n b w (source E x n hg b w) :=
  Classical.choose_spec (source_exists E x n hg b w)

theorem adjacent_symm (F : Family B) (L : ℕ) {a b : B} (h : F.Adjacent L a b) :
    F.Adjacent L b a := by
  obtain ⟨sa, sb, i, j, hi, hj, hbi, hbj, hagree⟩ := h
  exact ⟨sb, sa, j, i, hj, hi, hbj, hbi, fun q hq => (hagree q hq).symm⟩

private theorem reach_trans {adj : B → B → Prop} {a b c : B}
    (hab : Recovery.Reach adj a b) (hbc : Recovery.Reach adj b c) :
    Recovery.Reach adj a c := by
  induction hbc with
  | refl => exact hab
  | tail hbc hcd ih => exact Recovery.Reach.tail ih hcd

theorem connected_reach (F : Family B) (L : ℕ) {a b : B} (h : F.Connected L a b) :
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

noncomputable def schedule (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k)) : Recovery.Data B where
  rank := E.rank
  source := source E x n hg
  earlier b w a h := by
    have hs := source_spec E x n hg b w
    rw [h] at hs
    exact hs.1
  adjacent := E.family.Adjacent (windowLength k)
  root b := ∃ C, selectedRoot E x n hx hg C = b
  rooted b := by
    let C : Components E := Quotient.mk _ b
    let r := selectedRoot E x n hx hg C
    refine ⟨r, ⟨C, rfl⟩, connected_reach E.family (windowLength k) ?_⟩
    exact Quotient.exact (selectedRoot_spec E x n hx hg C).1

/-- All decoder-local semantic facts are derived from a generating edited family. -/
noncomputable def model (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k)) : Model B x n k where
  header := E.header
  long := E.long
  schedule := schedule E x n hx hg
  rho_lower := E.rho_lower
  rho_upper := E.rho_upper
  header_bit := E.header_bit
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

end DeletionCode.GeneratingModel
