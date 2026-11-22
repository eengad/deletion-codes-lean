import DeletionCode.Explicit.ExceptionalWeight
import DeletionCode.Qary.SpectrumLocalization
import Mathlib.Data.List.Nodup

/-! Locality for exceptional records, including replacements at a word boundary
and replacements of previously inserted letters. -/
namespace DeletionCode.Explicit.ExceptionalWeight

open Burst Qary.Windows Qary.SignedSupport Qary.CatalogueWords Qary.SpectrumLocalization

variable {α : Type*}

private theorem context_delta_guarded [Inhabited α] (pre x z post : List α) (L : ℕ) (hL : 0 < L)
    (hl : pre ≠ [] → L ≤ min x.length z.length + 1)
    (hr : post ≠ [] → L ≤ min x.length z.length + 1)
    (hp : pre ≠ [] → Agree (listLetters x) 0 (listLetters z) 0 (L-1))
    (hs : post ≠ [] → Agree (listLetters x) (x.length+1-L)
      (listLetters z) (z.length+1-L) (L-1)) (g : Gram α L) :
    wordSpectrum (listLetters (pre ++ (z ++ post))) (pre.length+z.length+post.length) L g -
      wordSpectrum (listLetters (pre ++ (x ++ post))) (pre.length+x.length+post.length) L g =
      wordSpectrum (listLetters z) z.length L g - wordSpectrum (listLetters x) x.length L g := by
  by_cases h : pre = [] ∧ post = []
  · obtain ⟨rfl, rfl⟩ := h
    simp
  have hm : L ≤ min x.length z.length + 1 := by
    by_cases hpre : pre = []
    · exact hr (fun hp => h ⟨hpre,hp⟩)
    · exact hl hpre
  have hx : L ≤ x.length + 1 := by omega
  have hz : L ≤ z.length + 1 := by omega
  have hleft : windowSum (listLetters (pre ++ (x ++ post))) L 0 pre.length g =
      windowSum (listLetters (pre ++ (z ++ post))) L 0 pre.length g := by
    apply windowSum_congr
    intro i hi
    apply (gram_eq_iff_agree _ _ _ _ _).mpr
    intro j hj
    simp only [Nat.zero_add]
    by_cases hij : i+j < pre.length
    · rw [listLetters_append_left _ _ _ hij, listLetters_append_left _ _ _ hij]
    · have hpos : pre ≠ [] := fun h => by simp [h] at hi
      have he : i+j = pre.length + (i+j-pre.length) := by omega
      rw [he, listLetters_middle _ _ _ _ (by omega), listLetters_middle _ _ _ _ (by omega)]
      simpa only [Nat.zero_add] using hp hpos (i+j-pre.length) (by omega)
  have hright : windowSum (listLetters (pre ++ (x ++ post))) L
      (pre.length + (x.length+1-L)) post.length g =
    windowSum (listLetters (pre ++ (z ++ post))) L
      (pre.length + (z.length+1-L)) post.length g := by
    apply windowSum_congr
    intro i hi
    apply (gram_eq_iff_agree _ _ _ _ _).mpr
    intro j hj
    have hpos : post ≠ [] := fun h => by simp [h] at hi
    simp only [Nat.add_assoc]
    by_cases hij : i+j < L-1
    · rw [listLetters_middle _ _ _ _ (by omega), listLetters_middle _ _ _ _ (by omega)]
      exact hs hpos (i+j) hij
    · have he (u : List α) (hu : L ≤ u.length+1) :
          pre.length+(u.length+1-L)+(i+j) = pre.length+u.length+(i+j-(L-1)) := by omega
      rw [← Nat.add_assoc pre.length (x.length+1-L), he x hx, listLetters_suffix,
        ← Nat.add_assoc pre.length (z.length+1-L), he z hz, listLetters_suffix]
  rw [spectrum_split _ _ _ _ _ hz, spectrum_split _ _ _ _ _ hx, hleft, hright,
    wordSpectrum_congr _ (listLetters z) z.length L (fun i hi => listLetters_middle pre z post i hi),
    wordSpectrum_congr _ (listLetters x) x.length L (fun i hi => listLetters_middle pre x post i hi)]
  omega

private theorem flank_delta [Inhabited α] [DecidableEq α]
    (pre left old add right post : List α) (L : ℕ) (hL : 0 < L)
    (hl : pre ≠ [] → left.length = L-1) (hr : post ≠ [] → right.length = L-1) :
    listFieldSpectrum default (pre ++ ((left ++ add ++ right) ++ post)) L -
      listFieldSpectrum default (pre ++ ((left ++ old ++ right) ++ post)) L =
    listFieldSpectrum default (left ++ add ++ right) L -
      listFieldSpectrum default (left ++ old ++ right) L := by
  funext g
  change fieldSpectrum _ _ _ _ - fieldSpectrum _ _ _ _ =
    fieldSpectrum _ _ _ _ - fieldSpectrum _ _ _ _
  simp only [fieldSpectrum_eq_cast, List.length_append]
  have h (a : List α) : (fun i => a.getD i default) = listLetters a := rfl
  simp only [h, ← Int.cast_sub]
  apply congrArg (fun m : ℤ => (m : ZMod 3))
  have hloc := context_delta_guarded pre (left ++ old ++ right) (left ++ add ++ right) post L hL
  suffices hh : wordSpectrum (listLetters (pre ++ ((left ++ add ++ right) ++ post)))
        (pre.length+(left ++ add ++ right).length+post.length) L g -
      wordSpectrum (listLetters (pre ++ ((left ++ old ++ right) ++ post)))
        (pre.length+(left ++ old ++ right).length+post.length) L g =
      wordSpectrum (listLetters (left ++ add ++ right)) (left ++ add ++ right).length L g -
        wordSpectrum (listLetters (left ++ old ++ right)) (left ++ old ++ right).length L g by
    simpa only [List.length_append, Nat.add_assoc] using hh
  refine hloc ?_ ?_ ?_ ?_ g
  · intro hp; have := hl hp; simp only [List.length_append]; omega
  · intro hp; have := hr hp; simp only [List.length_append]; omega
  · intro hp i hi
    simp only [Nat.zero_add]
    have hleft := hl hp
    rw [List.append_assoc, List.append_assoc, listLetters_append_left _ _ _ (by omega),
      listLetters_append_left _ _ _ (by omega)]
  · intro hp i hi
    have hright := hr hp
    have eq (u : List α) : (left ++ u ++ right).length + 1 - L + i =
        (left ++ u).length + i := by simp only [List.length_append]; omega
    rw [eq old, eq add, listLetters_append_right, listLetters_append_right]

/-- The portion of the left flank needed even if the edit is near an endpoint. -/
def leftFlank (L pos : ℕ) (x : List α) : List α :=
  (x.take pos).drop (pos - (L-1))

def rightFlank (L pos removed : ℕ) (x : List α) : List α :=
  (x.drop (pos+removed)).take (L-1)

/-- Actual original letters and already inserted constants share the same list. -/
abbrev Token (ℓ q : ℕ) := Fin ℓ ⊕ Fin q

variable {ℓ q n L b : ℕ}

def spell (x : Fin ℓ → Fin q) (w : List (Token ℓ q)) : List (Fin q) :=
  w.map (Sum.elim x id)

def initialTokens (ℓ : ℕ) (q : ℕ) : List (Token ℓ q) :=
  (List.finRange ℓ).map Sum.inl

def editTokens (e : Edit (Fin q)) : Edit (Token ℓ q) :=
  ⟨e.pos, e.removed, e.replacement.map Sum.inr⟩

theorem spell_initial (x : Fin ℓ → Fin q) : spell x (initialTokens ℓ q) = List.ofFn x := by
  rw [List.ofFn_eq_map]
  simp [spell, initialTokens, Function.comp_def]

theorem spell_apply (x : Fin ℓ → Fin q) (ws : List (Token ℓ q)) (e : Edit (Fin q)) :
    spell x ((editTokens e).apply ws) = e.apply (spell x ws) := by
  simp [spell, editTokens, Edit.apply, List.map_take, List.map_drop, Function.comp_def]

def active (L : ℕ) (ws : List (Token ℓ q)) (e : Edit (Fin q)) : Finset (Fin ℓ) :=
  (((leftFlank L e.pos ws ++ (editTokens e).sourceBlock ws) ++
    rightFlank L e.pos e.removed ws).filterMap (fun a => a.elim some (fun _ => none))).toFinset

def touched (L : ℕ) (ws : List (Token ℓ q)) : List (Edit (Fin q)) → Finset (Fin ℓ)
  | [] => ∅
  | e :: es => active L ws e ∪ touched L ((editTokens e).apply ws) es

theorem active_card_le (L : ℕ) (ws : List (Token ℓ q)) (e : Edit (Fin q)) :
    (active L ws e).card ≤ 2*L + e.removed := by
  unfold active
  refine (List.toFinset_card_le _).trans ((List.length_filterMap_le ..).trans ?_)
  simp only [leftFlank, rightFlank, editTokens, Edit.sourceBlock,
    List.length_append, List.length_take, List.length_drop]
  omega

theorem touched_card_le (L b : ℕ) (ws : List (Token ℓ q)) (es : List (Edit (Fin q)))
    (hb : ∀ e ∈ es, e.removed ≤ b) :
    (touched L ws es).card ≤ es.length * (2*L+b) := by
  induction es generalizing ws with
  | nil => simp [touched]
  | cons e es ih =>
    have he := active_card_le L ws e
    have hh := ih ((editTokens e).apply ws) (fun e he => hb e (by simp [he]))
    have hm := hb e (by simp)
    have hu := Finset.card_union_le (active L ws e) (touched L ((editTokens e).apply ws) es)
    simp only [touched, List.length_cons, Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul]
    omega

private theorem spell_eq_on {s : Finset (Fin ℓ)} {x y : Fin ℓ → Fin q}
    (h : ∀ i ∈ s, x i = y i) (ws : List (Token ℓ q))
    (hs : ∀ i, Sum.inl i ∈ ws → i ∈ s) :
    spell x ws = spell y ws := by
  apply List.map_congr_left
  intro a ha
  cases a with
  | inl i => exact h i (hs i ha)
  | inr _ => rfl

private theorem active_agree {x y : Fin ℓ → Fin q} {ws : List (Token ℓ q)} {e : Edit (Fin q)}
    (h : ∀ i ∈ active L ws e, x i = y i) :
    leftFlank L e.pos (spell x ws) = leftFlank L e.pos (spell y ws) ∧
    e.sourceBlock (spell x ws) = e.sourceBlock (spell y ws) ∧
    rightFlank L e.pos e.removed (spell x ws) = rightFlank L e.pos e.removed (spell y ws) := by
  have ha : ∀ i, Sum.inl i ∈ ((leftFlank L e.pos ws ++ (editTokens e).sourceBlock ws) ++
      rightFlank L e.pos e.removed ws) → i ∈ active L ws e := by
    intro i hi
    apply List.mem_toFinset.mpr
    exact List.mem_filterMap.mpr ⟨.inl i, hi, rfl⟩
  have hl := spell_eq_on h (leftFlank L e.pos ws) (fun i hi => ha i (by simp [hi]))
  have hm := spell_eq_on h ((editTokens e).sourceBlock ws) (fun i hi => ha i (by simp [hi]))
  have hr := spell_eq_on h (rightFlank L e.pos e.removed ws) (fun i hi => ha i (by simp [hi]))
  simpa only [spell, leftFlank, rightFlank, Edit.sourceBlock, editTokens,
    List.map_take, List.map_drop] using And.intro hl (And.intro hm hr)

private theorem spectrum_step (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L)
    (w : List (Fin q)) (e : Edit (Fin q)) (hL : 0 < L) (he : e.InBounds w.length) :
    delta pad cols w (e.apply w) =
      delta pad cols (leftFlank L e.pos w ++ e.sourceBlock w ++ rightFlank L e.pos e.removed w)
        (leftFlank L e.pos w ++ e.replacement ++ rightFlank L e.pos e.removed w) := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  let pre := (w.take e.pos).take (e.pos - (L-1))
  let left := leftFlank L e.pos w
  let old := e.sourceBlock w
  let right := rightFlank L e.pos e.removed w
  let post := (w.drop (e.pos+e.removed)).drop (L-1)
  have hl : pre ++ left = w.take e.pos := List.take_append_drop _ _
  have hr : right ++ post = w.drop (e.pos+e.removed) := List.take_append_drop _ _
  have hx : w = pre ++ ((left ++ old ++ right) ++ post) := by
    calc
      w = (w.take e.pos ++ old) ++ w.drop (e.pos+e.removed) := (e.decomposition w).symm
      _ = (pre ++ left ++ old) ++ (right ++ post) := by rw [hl, hr]
      _ = _ := by simp only [List.append_assoc]
  have heq : e.apply w = pre ++ ((left ++ e.replacement ++ right) ++ post) := by
    unfold Edit.apply
    rw [← hl, ← hr]
    simp [List.append_assoc]
  have hleft : pre ≠ [] → left.length = L-1 := by
    intro hp
    have hn : 0 < pre.length := List.length_pos_iff.mpr hp
    simp only [pre, left, leftFlank, List.length_take, List.length_drop] at hn ⊢
    unfold Edit.InBounds at he
    omega
  have hright : post ≠ [] → right.length = L-1 := by
    intro hp
    have hn : 0 < post.length := List.length_pos_iff.mpr hp
    simp only [right, rightFlank, post, List.length_drop, List.length_take] at hn ⊢
    omega
  have h := flank_delta pre left old e.replacement right post L hL hleft hright
  rw [← heq, ← hx] at h
  funext i
  exact congrFun h (cols i)

/-- Validity, final length and the telescoping spectrum difference depend
only on the original positions read in the chronological simulation. -/
theorem transfer_record (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L) (hL : 0 < L)
    {x y : Fin ℓ → Fin q} {ws : List (Token ℓ q)} {es : List (Edit (Fin q))}
    {z : List (Fin q)} (hex : Executes b (spell x ws) es z)
    (h : ∀ i ∈ touched L ws es, x i = y i) :
    Executes b (spell y ws) es (run (spell y ws) es) ∧
    z.length = (run (spell y ws) es).length ∧
    delta pad cols (spell x ws) z = delta pad cols (spell y ws) (run (spell y ws) es) := by
  induction es generalizing ws with
  | nil =>
    cases hex
    refine ⟨.nil _, by simp [run, spell], ?_⟩
    simp [run, delta]
  | cons e es ih =>
    obtain ⟨he, ht⟩ := (show e.Valid b (spell x ws) ∧ Executes b (e.apply (spell x ws)) es z from
      by cases hex with | cons he ht => exact ⟨he,ht⟩)
    have he' := active_agree (fun i hi => h i (Finset.mem_union_left _ hi))
    have hv : e.Valid b (spell y ws) :=
      ⟨he.1, by simpa only [Edit.InBounds, spell, List.length_map] using he.2.1,
        by rw [← he'.2.1]; exact he.2.2⟩
    rw [← spell_apply] at ht
    obtain ⟨hr, hlen, hd⟩ := ih ht (fun i hi => h i (Finset.mem_union_right _ hi))
    simp only [spell_apply] at hr hlen hd
    refine ⟨.cons hv hr, hlen, ?_⟩
    have hstep := spectrum_step pad cols (spell x ws) e hL he.2.1
    rw [he'.1, he'.2.1, he'.2.2, ← spectrum_step pad cols (spell y ws) e hL hv.2.1] at hstep
    unfold delta at *
    simp only [run]
    calc
      _ = (spectrum pad cols z - spectrum pad cols (e.apply (spell x ws))) +
          (spectrum pad cols (e.apply (spell x ws)) - spectrum pad cols (spell x ws)) := by abel
      _ = (spectrum pad cols (run (e.apply (spell y ws)) es) -
          spectrum pad cols (e.apply (spell y ws))) +
          (spectrum pad cols (e.apply (spell y ws)) - spectrum pad cols (spell y ws)) := by
        rw [hd, hstep]
      _ = _ := by abel

#print axioms touched_card_le
#print axioms transfer_record

end DeletionCode.Explicit.ExceptionalWeight
