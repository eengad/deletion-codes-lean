import DeletionCode.Explicit.MatchingWeight
import DeletionCode.Explicit.WeightedAddress
import Mathlib.Data.List.Sort

/-! Bounded-window enumeration of the two increasing position lists in a matching. -/
namespace DeletionCode.Explicit.MatchingEnumeration

open MatchingWeight LetterSequence
open scoped BigOperators

abbrev Positions := List ℕ
abbrev PositionPair := Positions × Positions
abbrev Edges := List (ℕ × ℕ)

/-- Each nonempty list is anchored at its first position. The binary mask
selects offsets strictly after the anchor. -/
def selected (a : ℕ) (bits : QWord 2) : Positions :=
  a :: ((List.range bits.length).filter (fun i => decide (bits.getD i 0 = 1))).map (a + 1 + ·)

def admissible (ℓ K : ℕ) (xs : Positions) : Bool :=
  decide (xs.length = K) && xs.all (fun i => decide (i < ℓ))

def positionLists (ℓ K B : ℕ) : List Positions :=
  if K = 0 then [[]] else
    (List.range ℓ).flatMap fun a =>
      ((wordsOfLength 2 (B-1)).map (selected a)).filter (admissible ℓ K)

def edges (p : PositionPair) : Edges :=
  (List.range (min p.1.length p.2.length)).map fun j => (p.1.getD j 0,p.2.getD j 0)

def distinct (p : PositionPair) : Bool :=
  (edges p).all (fun e => decide (e.1 ≠ e.2))

def patternList (ℓ K Λ : ℕ) : List PositionPair :=
  let xs := positionLists ℓ K (K+3*Λ)
  (xs.flatMap fun f => xs.map fun g => (f,g)).filter distinct

def encodePositions (f : Fin K → Fin ℓ) : Positions := List.ofFn (fun i => (f i).val)
def encodePattern (p : Pattern ℓ K) : PositionPair := (encodePositions p.1, encodePositions p.2)

private theorem selected_sorted (a : ℕ) (bits : QWord 2) : (selected a bits).Pairwise (· < ·) := by
  have hr : (List.range bits.length).Pairwise (· < ·) := List.pairwise_lt_range
  unfold selected
  rw [List.pairwise_cons, List.pairwise_map]
  refine ⟨?_, (hr.filter _).imp (fun h => by omega)⟩
  intro j hj
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
  omega

private theorem selected_mem (a : ℕ) (bits : QWord 2) (j : ℕ) :
    j ∈ selected a bits ↔ j = a ∨ ∃ i < bits.length, bits.getD i 0 = 1 ∧ j = a+1+i := by
  simp only [selected, List.mem_cons, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq]
  exact or_congr_right ⟨fun ⟨i,⟨hi,hb⟩,he⟩ => ⟨i,hi,hb,he.symm⟩,
    fun ⟨i,hi,hb,he⟩ => ⟨i,⟨hi,hb⟩,he.symm⟩⟩

private theorem selected_injective (a m : ℕ) {u v : QWord 2}
    (hu : u.length = m) (hv : v.length = m) (h : selected a u = selected a v) : u = v := by
  apply List.ext_getElem (hu.trans hv.symm)
  intro i hi hj
  have hmem (bits : QWord 2) (h' : i < bits.length) :
      a+1+i ∈ selected a bits ↔ bits[i] = 1 := by
    rw [selected_mem]
    constructor
    · rintro (he | ⟨j,hj,hbit,he⟩)
      · omega
      · have hji : j = i := by omega
        subst j
        simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h'] using hbit
    · intro hb
      exact Or.inr ⟨i,h',by simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h'] using hb,rfl⟩
  have he : u[i] = 1 ↔ v[i] = 1 := by rw [← hmem u hi, ← hmem v hj, h]
  have ha := u[i].isLt
  have hb := v[i].isLt
  apply Fin.ext
  change (u[i] : ℕ) = (v[i] : ℕ)
  by_cases h1 : u[i] = 1
  · rw [h1, he.mp h1]
  · have h2 := mt he.mpr h1
    have hz1 : (u[i] : ℕ) ≠ 1 := fun hn => h1 (Fin.ext hn)
    have hz2 : (v[i] : ℕ) ≠ 1 := fun hn => h2 (Fin.ext hn)
    omega

theorem positionLists_nodup (ℓ K B : ℕ) : (positionLists ℓ K B).Nodup := by
  unfold positionLists
  split
  · simp
  · rw [List.nodup_flatMap]
    refine ⟨?_, (List.nodup_range (n := ℓ)).imp ?_⟩
    · intro a _
      apply List.Nodup.filter
      rw [List.nodup_map_iff_inj_on (WeightedAddress.words_nodup 2 (B-1))]
      intro u hu v hv he
      exact selected_injective a (B-1) (mem_wordsOfLength.mp hu) (mem_wordsOfLength.mp hv) he
    · intro a b hab ys ha hb
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp (List.mem_filter.mp ha).1
      obtain ⟨v,_,he⟩ := List.mem_map.mp (List.mem_filter.mp hb).1
      apply hab
      simpa [selected] using (congrArg List.head? he).symm

theorem prefix_getD {A : Type*} (f : Fin m → A) (i : Fin m) (d : A) :
    (List.ofFn f).getD i.val d = f i := by
  have hi : i.val < (List.ofFn f).length := by rw [List.length_ofFn]; exact i.isLt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem_ofFn,
    Option.getD_some]

private theorem selected_ofFn {f : Fin (K+1) → Fin ℓ} (hf : StrictMono f) (he : ExtentLE f B) :
    ∃ bits ∈ wordsOfLength 2 (B-1), selected (f 0).val bits = encodePositions f := by
  let a := (f 0).val
  let xs := encodePositions f
  let mask : Fin (B-1) → Fin 2 := fun i => if a+1+i.val ∈ xs then 1 else 0
  have hm (i : Fin (B-1)) : (List.ofFn mask).getD i.val 0 = 1 ↔ a+1+i.val ∈ xs := by
    rw [prefix_getD]
    dsimp [mask]
    split <;> simp_all
  refine ⟨List.ofFn mask, mem_wordsOfLength.mpr List.length_ofFn, ?_⟩
  apply (selected_sorted a _).eq_of_mem_iff
  · rw [encodePositions, List.pairwise_ofFn]
    intro i j hij
    exact hf hij
  · intro j
    rw [selected_mem, List.length_ofFn]
    constructor
    · rintro (rfl | ⟨i,hi,hm',rfl⟩)
      · exact List.mem_ofFn.mpr ⟨0,rfl⟩
      · exact (hm ⟨i,hi⟩).mp hm'
    · intro hj
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hj
      have hreach := he 0 i
      have hmin := hf.monotone (Fin.zero_le i)
      change a ≤ (f i).val at hmin
      change (f i).val + 1 ≤ a + B at hreach
      by_cases hzero : (f i).val = a
      · exact Or.inl hzero
      · let j := (f i).val - (a+1)
        have hj' : j < B-1 := by dsimp [j]; omega
        have hval : a+1+j = (f i).val := by dsimp [j]; omega
        exact Or.inr ⟨j,hj',(hm ⟨j,hj'⟩).mpr (hval.symm ▸ hj),hval.symm⟩

theorem mem_positionLists {xs : Positions} (hB : K ≤ B) :
    xs ∈ positionLists ℓ K B ↔
      ∃ f : Fin K → Fin ℓ, StrictMono f ∧ ExtentLE f B ∧ xs = encodePositions f := by
  cases K with
  | zero =>
    simp only [positionLists, ↓reduceIte, List.mem_singleton]
    refine ⟨fun h => ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, h⟩, ?_⟩
    rintro ⟨f,_,_,rfl⟩
    simp [encodePositions]
  | succ k =>
    simp only [positionLists, Nat.succ_ne_zero, ↓reduceIte, List.mem_flatMap, List.mem_range,
      List.mem_filter, List.mem_map, admissible, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    constructor
    · rintro ⟨a,_,⟨bits,hbits,rfl⟩,hlen,hin⟩
      have hs (i : Fin (k+1)) : i.val < (selected a bits).length := hlen.symm ▸ i.isLt
      let f (i : Fin (k+1)) : Fin ℓ :=
        ⟨(selected a bits)[i.val]'(hs i), hin _ (List.getElem_mem _)⟩
      have hm (i : Fin (k+1)) : (f i).val ∈ selected a bits := List.getElem_mem _
      have hr (i : Fin (k+1)) : a ≤ (f i).val ∧ (f i).val < a+B := by
        have hm' := (selected_mem a bits _).mp (hm i)
        have hl := mem_wordsOfLength.mp hbits
        rcases hm' with h | ⟨j,hj,_,h⟩
        · omega
        · omega
      refine ⟨f, ?_, ?_, ?_⟩
      · intro i j hij
        exact List.pairwise_iff_getElem.mp (selected_sorted a bits) _ _ (hs i) (hs j) hij
      · intro i j
        have hi := hr i
        have hj := hr j
        omega
      · apply List.ext_getElem (by simpa [encodePositions] using hlen)
        intro i hi hj
        simp only [encodePositions, List.getElem_ofFn]
        rfl
    · rintro ⟨f,hmono,hext,rfl⟩
      obtain ⟨bits,hb,he⟩ := selected_ofFn hmono hext
      exact ⟨(f 0).val,(f 0).isLt,⟨bits,hb,he⟩,List.length_ofFn,by
        intro i hi
        obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
        exact (f j).isLt⟩


theorem edges_encode (p : Pattern ℓ K) :
    edges (encodePattern p) = List.ofFn (fun i => ((p.1 i).val,(p.2 i).val)) := by
  unfold edges encodePattern encodePositions
  simp only [List.length_ofFn, min_self]
  apply List.ext_getElem (by simp)
  intro j hj hj'
  have h : j < K := by simpa using hj'
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  exact Prod.ext (prefix_getD _ ⟨j,h⟩ _) (prefix_getD _ ⟨j,h⟩ _)

private theorem distinct_encode (p : Pattern ℓ K) :
    distinct (encodePattern p) = true ↔ ∀ i, p.1 i ≠ p.2 i := by
  simp only [distinct, edges_encode, List.all_eq_true, List.mem_ofFn, decide_eq_true_eq]
  refine ⟨fun h i he => h _ ⟨i,rfl⟩ (congrArg Fin.val he), ?_⟩
  rintro h _ ⟨i,rfl⟩ he
  exact h i (Fin.ext he)

theorem encodePattern_injective : Function.Injective (encodePattern (ℓ := ℓ) (K := K)) := by
  intro p p' hp
  apply Prod.ext <;> funext i <;> apply Fin.ext
  · have h := congrArg (fun s : PositionPair => s.1.getD i.val 0) hp
    simpa only [encodePattern, encodePositions, prefix_getD] using h
  · have h := congrArg (fun s : PositionPair => s.2.getD i.val 0) hp
    simpa only [encodePattern, encodePositions, prefix_getD] using h

theorem mem_patternList {p : PositionPair} :
    p ∈ patternList ℓ K Λ ↔ ∃ P ∈ patterns ℓ K Λ, p = encodePattern P := by
  have hB : K ≤ K+3*Λ := Nat.le_add_right ..
  simp only [patternList, List.mem_filter, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨⟨f,hf,g,hg,rfl⟩,hd⟩
    obtain ⟨F,hF,eF,rfl⟩ := (mem_positionLists hB).mp hf
    obtain ⟨G,hG,eG,rfl⟩ := (mem_positionLists hB).mp hg
    exact ⟨(F,G), mem_patterns.mpr ⟨hF,hG,eF,eG,(distinct_encode (F,G)).mp hd⟩,rfl⟩
  · rintro ⟨⟨F,G⟩,hp,rfl⟩
    obtain ⟨hF,hG,eF,eG,hd⟩ := mem_patterns.mp hp
    exact ⟨⟨_,(mem_positionLists hB).mpr ⟨F,hF,eF,rfl⟩,
      _,(mem_positionLists hB).mpr ⟨G,hG,eG,rfl⟩,rfl⟩,(distinct_encode (F,G)).mpr hd⟩

theorem patternList_nodup (ℓ K Λ : ℕ) : (patternList ℓ K Λ).Nodup := by
  let xs := positionLists ℓ K (K+3*Λ)
  have hx : xs.Nodup := positionLists_nodup ..
  apply List.Nodup.filter
  rw [List.nodup_flatMap]
  refine ⟨fun f _ => hx.map (fun g h he => congrArg Prod.snd he), hx.imp ?_⟩
  intro f g hfg p hf hg
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp hf
  obtain ⟨_,_,h⟩ := List.mem_map.mp hg
  exact hfg (congrArg Prod.fst h).symm

private theorem patternList_toFinset :
    (patternList ℓ K Λ).toFinset = (patterns ℓ K Λ).image encodePattern := by
  ext p
  simp only [List.mem_toFinset, Finset.mem_image, mem_patternList]
  exact exists_congr (fun P => and_congr_right (fun _ => eq_comm))

theorem sum_list {A : Type*} [DecidableEq A] (xs : List A) (hn : xs.Nodup) (f : A → ℕ) :
  (xs.map f).sum = ∑ p ∈ xs.toFinset, f p := by
  induction xs with
  | nil => simp
  | cons p xs ih =>
    obtain ⟨hp,hxs⟩ := List.nodup_cons.mp hn
    have hp' : p ∉ xs.toFinset := by simpa using hp
    simp only [List.map_cons, List.sum_cons, List.toFinset_cons, Finset.sum_insert hp', ih hxs]

theorem sum_patterns (f : PositionPair → ℕ) :
    ((patternList ℓ K Λ).map f).sum = ∑ p ∈ patterns ℓ K Λ, f (encodePattern p) := by
  rw [sum_list _ (patternList_nodup ℓ K Λ), patternList_toFinset,
    Finset.sum_image (fun _ _ _ _ h => encodePattern_injective h)]

theorem patternList_length_le (hK : 0 < K) :
    (patternList ℓ K Λ).length ≤ ℓ^2 * 2^(2*(K+3*Λ)) := by
  rw [← List.toFinset_card_of_nodup (patternList_nodup ℓ K Λ), patternList_toFinset,
    Finset.card_image_of_injective _ encodePattern_injective]
  refine (patterns_card_le hK).trans ?_
  rw [mul_pow, Nat.mul_comm 2 (K+3*Λ), pow_mul]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.choose_le_two_pow _ _) _)

#print axioms mem_patternList
#print axioms patternList_length_le

end DeletionCode.Explicit.MatchingEnumeration
