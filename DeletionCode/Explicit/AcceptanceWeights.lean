import DeletionCode.Explicit.Machine.CataloguePrefix
import DeletionCode.Explicit.Machine.MatchingPrefix

/-! The first two acceptance tests computed from the generated weights. -/
namespace DeletionCode.Explicit.ExceptionalWeight

open Burst FieldHash Qary.SignedSupport Qary.Windows

variable {q ℓ L K b t n θ : ℕ}

/-- A surviving entry can be replayed on every word matching its assignment. -/
theorem catalogue_entry_replays (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L) (hL : 0 < L)
    (E : Entry ℓ q n) (hE : E ∈ catalogue pad cols b t ℓ) (x : Fin ℓ → Fin q)
    (hx : CoreWeight.Matches E.assignment x) :
    ∃ z : QWord q, z.length = ℓ ∧ z ≠ List.ofFn x ∧
      Burst.Exceptional b t ℓ (8 * (L + t*b)) (List.ofFn x) z ∧
      E.changeVector = delta pad cols (List.ofFn x) z := by
  obtain ⟨es, hes, he⟩ := List.mem_flatMap.mp hE
  let s := touched L (initialTokens ℓ q) es
  change E ∈ (wordsOfLength q (supportList s).length).filterMap (entry? pad cols b es s) at he
  obtain ⟨letters, _, hentry⟩ := List.mem_filterMap.mp he
  let y := representative pad s letters
  let w := List.ofFn y
  change (validRun b w es).bind _ = some E at hentry
  cases hrun : validRun b w es with
  | none => simp [hrun] at hentry
  | some z =>
    simp only [hrun, Option.bind_some] at hentry
    split at hentry
    · rename_i hz
      injection hentry with hE'
      subst E
      have hlocal (i : Fin ℓ) (hi : i ∈ s) : y i = x i := (hx ⟨i,hi⟩).symm
      have htransfer := transfer_record pad cols hL (ws := initialTokens ℓ q) (y := x)
        (by simpa only [spell_initial] using (validRun_iff.mp hrun)) hlocal
      rw [spell_initial, spell_initial] at htransfer
      obtain ⟨hex,hsize,hdelta⟩ := htransfer
      let z' := run (List.ofFn x) es
      obtain ⟨_,hlen,hsep,_⟩ := mem_chronological.mp hes
      refine ⟨z', hsize.symm.trans hz.1, ?_, ⟨es,hex,hlen,hsep⟩, hdelta⟩
      intro heq
      apply hz.2 (hdelta.trans ?_)
      change delta pad cols (List.ofFn x) z' = 0
      rw [heq]
      simp [delta]
    · contradiction

theorem catalogue_exceptional_of_weight_pos (pad : Fin q) (cols : Fin n ≃ Gram (Fin q) L)
    (hL : 0 < L) (H : TernaryMatrix θ n) (x : Fin ℓ → Fin q)
    (hu : KUnique (fun i => (List.ofFn x).getD i pad) ℓ K)
    (h : 0 < weight (family pad cols b t ℓ) H x) : Exceptional pad cols H b t K x := by
  obtain ⟨i,hkeep,hmatch⟩ := (CoreWeight.weight_pos_iff _ _ _).mp h
  let E := family pad cols b t ℓ i
  have he : E ∈ catalogue pad cols b t ℓ := List.getElem_mem i.isLt
  obtain ⟨z,hz,hne,hrec,hξ⟩ := catalogue_entry_replays pad cols hL E he x hmatch
  have hhash := (E.kept_iff H).mp hkeep
  rw [hξ, delta, Matrix.mulVec_sub] at hhash
  exact ⟨hu,z,hz,hne,hrec,sub_eq_zero.mp hhash⟩

#print axioms catalogue_entry_replays
#print axioms catalogue_exceptional_of_weight_pos

end DeletionCode.Explicit.ExceptionalWeight

namespace DeletionCode.Explicit.AcceptanceWeights

open FieldHash Qary.Windows Machine MatchingEnumeration
open scoped BigOperators

variable {q ℓ b t K : ℕ}

-- A full-length prefix selects a single word, even when the weight has multiplicity.
theorem fullPrefix_sum (x : Fin ℓ → Fin q) (f : (Fin ℓ → Fin q) → ℕ) :
    (∑ y : Fin ℓ → Fin q, if ∀ i, y (Fin.castLE (le_refl ℓ) i) = x i then f y else 0) = f x := by
  classical
  have he (y : Fin ℓ → Fin q) : (∀ i, y (Fin.castLE (le_refl ℓ) i) = x i) ↔ y = x :=
    ⟨funext, fun h => h ▸ fun _ => rfl⟩
  simp_rw [he]
  simp

def matchingValue (pad : Fin q) (b t ℓ : ℕ) (w : QWord q) : ℕ :=
  MatchingPrefixes.mass pad b t (ℓ,w)

def exceptionalValue (pad : Fin q) (b t ℓ : ℕ) (hs : Ternary.Rows) (w : QWord q) : ℕ :=
  CataloguePrefix.exceptionalPrefixMass pad b t (ℓ,hs,w)

theorem matchingValue_eq (pad : Fin q) (b t : ℕ) (x : Fin ℓ → Fin q) :
    matchingValue pad b t ℓ (List.ofFn x) =
      MatchingWeight.weight x (UniformParameters.windowLength q ℓ) (UniformParameters.omittedLetters q b t ℓ) := by
  rw [matchingValue, MatchingPrefixes.mass_eq, MatchingWeight.prefixMass_eq_sum (le_refl ℓ), fullPrefix_sum]

theorem exceptionalValue_eq (pad : Fin q) (b t : ℕ) (x : Fin ℓ → Fin q)
    (H : TernaryMatrix θ (q^UniformParameters.gram q b t ℓ)) :
    exceptionalValue pad b t ℓ (CataloguePrefix.matrixRows H) (List.ofFn x) =
      ExceptionalWeight.weight (ExceptionalWeight.family pad
        (ExceptionalWeight.dictionary q (UniformParameters.gram q b t ℓ)) b t ℓ) H x := by
  rw [exceptionalValue, CataloguePrefix.exceptionalPrefixMass_eq,
    ExceptionalWeight.prefixMass_eq_sum _ _ (le_refl ℓ), fullPrefix_sum]

def strong (pad : Fin q) (b t ℓ : ℕ) (w : QWord q) : Bool :=
  decide (matchingValue pad b t ℓ w = 0)

theorem strong_iff (pad : Fin q) (b t : ℕ) (x : Fin ℓ → Fin q) :
    strong pad b t ℓ (List.ofFn x) = true ↔
      LetterSequence.Strong x (UniformParameters.windowLength q ℓ) (UniformParameters.omittedLetters q b t ℓ) := by
  classical
  rw [strong, decide_eq_true_eq, matchingValue_eq]
  have h := MatchingWeight.weight_pos_iff_not_strong (x := x)
    (K := UniformParameters.windowLength q ℓ) (Λ := UniformParameters.omittedLetters q b t ℓ)
  constructor
  · intro hz
    by_contra hn
    have hp := h.mpr hn
    omega
  · intro hs
    have hp := mt h.mp (not_not_intro hs)
    omega

def window (K i : ℕ) (w : QWord q) : QWord q := (w.drop i).take K

def uniqueWindows (ℓ K : ℕ) (w : QWord q) : Bool :=
  (List.range (ℓ+1)).all fun i => (List.range (ℓ+1)).all fun j =>
    (decide (i = j) || decide (ℓ < i+K)) ||
      (decide (ℓ < j+K) || decide (window K i w ≠ window K j w))

private theorem window_eq_iff (pad : Fin q) (w : QWord q) (K i j : ℕ)
    (hi : i+K ≤ w.length) (hj : j+K ≤ w.length) :
    window K i w = window K j w ↔ Agree (fun k => w.getD k pad) i (fun k => w.getD k pad) j K := by
  have hl (k : ℕ) (hk : k+K ≤ w.length) : (window K k w).length = K := by
    simp only [window, List.length_take, List.length_drop]
    exact Nat.min_eq_left (by omega)
  have hletter (a k : ℕ) (hk : k < K) (ha : a+K ≤ w.length) :
      (window K a w)[k]'(by rw [hl a ha]; exact hk) = w.getD (a+k) pad := by
    have h : a+k < w.length := by omega
    simp only [window, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h, Option.getD_some]
  constructor
  · intro he k hk
    change w.getD (i+k) pad = w.getD (j+k) pad
    rw [← hletter i k hk hi, ← hletter j k hk hj]
    exact List.getElem_of_eq he (by rw [hl i hi]; exact hk)
  · intro h
    apply List.ext_getElem ((hl i hi).trans (hl j hj).symm)
    intro k hk hj'
    have hk' : k < K := by rwa [hl i hi] at hk
    rw [hletter i k hk' hi, hletter j k hk' hj]
    exact h k hk'

theorem uniqueWindows_iff (pad : Fin q) (w : QWord q) (hw : w.length = ℓ) :
    uniqueWindows ℓ K w = true ↔ KUnique (fun i => w.getD i pad) ℓ K := by
  simp only [uniqueWindows, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, KUnique]
  constructor
  · intro h i j hi hj ha
    rcases h i (by omega) j (by omega) with (hij | hneg) | (hneg | hne)
    · exact hij
    · omega
    · omega
    · exact (hne ((window_eq_iff pad w K i j (by omega) (by omega)).mpr ha)).elim
  · intro h i hi j hj
    by_cases ha : i+K ≤ ℓ
    · by_cases hb : j+K ≤ ℓ
      · by_cases he : window K i w = window K j w
        · exact Or.inl (Or.inl (h i j ha hb ((window_eq_iff pad w K i j (by omega) (by omega)).mp he)))
        · exact Or.inr (Or.inr he)
      · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (Or.inr (by omega))

def exceptional (pad : Fin q) (b t ℓ : ℕ) (hs : Ternary.Rows) (w : QWord q) : Bool :=
  uniqueWindows ℓ (UniformParameters.windowLength q ℓ) w &&
    decide (0 < exceptionalValue pad b t ℓ hs w)

theorem exceptional_iff (pad : Fin q) (b t : ℕ) (x : Fin ℓ → Fin q)
    (hL : UniformParameters.gram q b t ℓ ≤ ℓ)
    (hK : UniformParameters.windowLength q ℓ < UniformParameters.gram q b t ℓ)
    (H : TernaryMatrix θ (q^UniformParameters.gram q b t ℓ)) :
    exceptional pad b t ℓ (CataloguePrefix.matrixRows H) (List.ofFn x) = true ↔
      ExceptionalWeight.Exceptional pad (ExceptionalWeight.dictionary q (UniformParameters.gram q b t ℓ))
        H b t (UniformParameters.windowLength q ℓ) x := by
  rw [exceptional, Bool.and_eq_true, decide_eq_true_eq, uniqueWindows_iff pad _ List.length_ofFn,
    exceptionalValue_eq]
  refine ⟨fun ⟨hu,hw⟩ => ExceptionalWeight.catalogue_exceptional_of_weight_pos pad _ (by omega) H x hu hw, ?_⟩
  intro h
  exact ⟨h.1,ExceptionalWeight.catalogue_weight_pos pad _ hL hK H h⟩

theorem exceptional_iff_admitted (pad : Fin q) (b t : ℕ) (x : Fin ℓ → Fin q)
    (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) (hstart : UniformParameters.minLength q b t ≤ ℓ)
    (H : TernaryMatrix θ (q^UniformParameters.gram q b t ℓ)) :
    exceptional pad b t ℓ (CataloguePrefix.matrixRows H) (List.ofFn x) = true ↔
      ExceptionalWeight.Exceptional pad (ExceptionalWeight.dictionary q (UniformParameters.gram q b t ℓ))
        H b t (UniformParameters.windowLength q ℓ) x := by
  have h := UniformParameters.basicBounds hq hb ht hstart
  exact exceptional_iff pad b t x h.borrowed_length (by have := h.borrowed_gram; omega) H

#print axioms matchingValue_eq
#print axioms exceptionalValue_eq
#print axioms strong_iff
#print axioms uniqueWindows_iff
#print axioms exceptional_iff
#print axioms exceptional_iff_admitted

end DeletionCode.Explicit.AcceptanceWeights
