import DeletionCode.Explicit.SmallFamilyCodec
import DeletionCode.Explicit.ReplayGrammar
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.OfFn

/-! A replayed negative lift specifies the family and the positions it encodes. -/

namespace DeletionCode.Explicit.BubbleFamilies

open LetterSequence ReplayEntry Borrowed

variable {q ℓ n : ℕ}

/-- Original positions in their lift order, skipping fresh identifiers. -/
def originalNames (w : Lift ℓ n (Fin q)) : List (Fin ℓ) :=
  (List.ofFn w.letters).filterMap Letter.position

def active (w : Lift ℓ n (Fin q)) : Finset (Fin ℓ) := (originalNames w).toFinset

theorem active_iff (w : Lift ℓ n (Fin q)) (p : Fin ℓ) :
    p ∈ active w ↔ p.val ∈ w.positions := by
  simp only [active,List.mem_toFinset,originalNames,List.mem_filterMap,List.mem_ofFn,Lift.mem_positions]
  constructor
  · rintro ⟨a,⟨i,rfl⟩,h⟩
    exact ⟨i,p,h,rfl⟩
  · rintro ⟨i,p',h,he⟩
    have e : p' = p := Fin.ext he
    exact ⟨w.letters i,⟨i,rfl⟩,e ▸ h⟩

private theorem originalNames_pairwise (w : Lift ℓ n (Fin q)) :
    (originalNames w).Pairwise (· < ·) := by
  rw [originalNames,List.pairwise_filterMap,List.pairwise_ofFn]
  exact fun _ _ h _ hp _ hq => w.increasing h hp hq

private theorem originalNames_eq_activeOrder (w : Lift ℓ n (Fin q)) :
    originalNames w = List.ofFn (fun i : Fin (active w).card => ((active w).orderIsoOfFin rfl i).val) := by
  let S := active w
  let ys := List.ofFn (fun i : Fin S.card => (S.orderIsoOfFin rfl i).val)
  have hpair : ys.Pairwise (· < ·) := List.pairwise_ofFn.mpr
    (fun _ _ h => (S.orderEmbOfFin rfl).strictMono h)
  have hys : ys.toFinset = S := by
    ext p
    simp only [ys,List.mem_toFinset,List.mem_ofFn]
    constructor
    · rintro ⟨i,rfl⟩
      exact (S.orderIsoOfFin rfl i).property
    · intro hp
      let i := (S.orderIsoOfFin rfl).symm ⟨p,hp⟩
      exact ⟨i,congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨p,hp⟩)⟩
  have h₁ := originalNames_pairwise w
  have hsets : (originalNames w).toFinset = ys.toFinset := hys.symm
  have hp := List.toFinset_eq_iff_perm_dedup.mp hsets
  rw [List.dedup_eq_self.mpr (h₁.imp (fun h => ne_of_lt h)),
    List.dedup_eq_self.mpr (hpair.imp (fun h => ne_of_lt h))] at hp
  exact hp.eq_of_sortedLE (List.sortedLE_iff_pairwise.mpr (h₁.imp (fun h => le_of_lt h)))
    (List.sortedLE_iff_pairwise.mpr (hpair.imp (fun h => le_of_lt h)))

private theorem originalValues_eq_map (w : Lift ℓ n (Fin q)) (x : Fin ℓ → Fin q) :
    originalValues w x = (originalNames w).map x := by
  let f : Letter ℓ (Fin q) → Option (Fin q) := fun a =>
    match a with | .original i => some (x i) | .fresh .. => none
  change (List.ofFn w.letters).filterMap f =
    ((List.ofFn w.letters).filterMap Letter.position).map x
  generalize List.ofFn w.letters = letters
  induction letters with
  | nil => rfl
  | cons a tail ih => cases a <;> simp [List.filterMap_cons,Letter.position,f,ih]

theorem originalValues_eq_select (w : Lift ℓ n (Fin q)) (x : Fin ℓ → Fin q) :
    originalValues w x = List.ofFn (SmallFamilyCodec.select (active w) x) := by
  rw [originalValues_eq_map,originalNames_eq_activeOrder,List.map_ofFn]
  rfl

def replayShape (p : Entry (Fin q) × Completed ℓ (Fin q)) : Shape q :=
  shapeOf p.1.left p.1.right p.1.removed p.1.replacement p.2.negative.2

theorem replayShape_card (pad : Fin q) (p : Entry (Fin q) × Completed ℓ (Fin q)) :
    (replayShape p).originalCount = (active p.2.negative.2).card := by
  have h := originalValues_length p.1.left p.1.right p.1.removed p.1.replacement
    p.2.negative.2 (fun _ => pad)
  rw [originalValues_eq_select,List.length_ofFn] at h
  exact h.symm

def replayAssignments (K b L Λ : ℕ) (pad : Fin q)
    (p : Entry (Fin q) × Completed ℓ (Fin q)) :
    List (Fin (active p.2.negative.2).card → Fin q) :=
  (SmallFamilyCodec.shapeAssignments (replayShape p) K b L Λ pad).map
    (fun v i => v (Fin.cast (replayShape_card pad p).symm i))

theorem select_mem_replayAssignments (K b L Λ : ℕ) (pad : Fin q)
    (p : Entry (Fin q) × Completed ℓ (Fin q)) (x : Fin ℓ → Fin q)
    {w : BubbleWord (Fin q) K b L}
    (h : (replayShape p).member K b L Λ pad (originalValues p.2.negative.2 x) = some w) :
    SmallFamilyCodec.select (active p.2.negative.2) x ∈ replayAssignments K b L Λ pad p := by
  let hs := replayShape_card pad p
  let f : Fin (replayShape p).originalCount → Fin q := fun i =>
    SmallFamilyCodec.select (active p.2.negative.2) x (Fin.cast hs i)
  have he : List.ofFn f = originalValues p.2.negative.2 x := by
    rw [originalValues_eq_select]
    apply List.ext_getElem
    · simp [hs]
    · intro i hi₁ hi₂
      simp [f]
  apply List.mem_map.mpr
  exact ⟨f,SmallFamilyCodec.mem_shapeAssignments _ K b L Λ pad f (he.symm ▸ h),by funext i; rfl⟩

/-- A replayed member supplies exactly the active-letter payload that the
decoder expects for the small-family branch. -/
theorem replay_payload_roundtrip (hq : 1 < q) (K b L Λ : ℕ) (pad : Fin q)
    (p : Entry (Fin q) × Completed ℓ (Fin q)) (x : Fin ℓ → Fin q)
    {w : BubbleWord (Fin q) K b L}
    (h : (replayShape p).member K b L Λ pad (originalValues p.2.negative.2 x) = some w) :
    let S := active p.2.negative.2
    let members := replayAssignments K b L Λ pad p
    ∃ payload, SmallFamilyCodec.encode hq S members x = some payload ∧
      SmallFamilyCodec.decode S members payload = some x :=
  SmallFamilyCodec.encode_roundtrip hq _ _ _ (select_mem_replayAssignments K b L Λ pad p x h)

#print axioms replayShape_card
#print axioms replay_payload_roundtrip

end DeletionCode.Explicit.BubbleFamilies
