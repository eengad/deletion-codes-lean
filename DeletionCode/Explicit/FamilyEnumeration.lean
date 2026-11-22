import DeletionCode.Explicit.BubbleFamilies
import DeletionCode.Explicit.EditBallCount
import Mathlib.Data.List.Dedup

/-! Bounded enumeration of the nonempty bubble families of `d:local-injective`. -/

namespace DeletionCode.Explicit.BubbleFamilies

private def shortWords (q : ℕ) : ℕ → List (QWord q)
  | 0 => [[]]
  | b+1 => shortWords q b ++ wordsOfLength q (b+1)

private theorem shortWords_spec {q b : ℕ} {w : QWord q} :
    w ∈ shortWords q b ↔ w.length ≤ b := by
  induction b with
  | zero => simp [shortWords]
  | succ b ih =>
    simp only [shortWords,List.mem_append,mem_wordsOfLength,ih]
    omega

private theorem shortWords_count (q b : ℕ) (hq : 2 ≤ q) :
    (shortWords q b).length ≤ 2*q^b := by
  induction b with
  | zero => simp [shortWords]
  | succ b ih =>
    simp only [shortWords,List.length_append,length_wordsOfLength,Nat.pow_succ]
    have h := Nat.mul_le_mul_left (q^b) hq
    calc
      _ ≤ 2*q^b+q^b*q := Nat.add_le_add_right ih _
      _ ≤ q^b*q+q^b*q := Nat.add_le_add_right (by simpa [Nat.mul_comm] using h) _
      _ = _ := by ring

/-- A short list of coded offsets and symbols represents a sparse fresh pattern. -/
private def patternOfMarks (q n : ℕ) (marks : QWord (n*q)) : List (Option (Fin q)) :=
  let pairs : List (Fin n × Fin q) := marks.map finProdFinEquiv.symm
  (List.finRange n).map (fun i => ((pairs.find? (fun p => p.1 == i)).map Prod.snd))

private def patterns (q n Λ : ℕ) : List (List (Option (Fin q))) :=
  (List.range (Λ+1)).flatMap fun k => (wordsOfLength (n*q) k).map (patternOfMarks q n)

private theorem patterns_count (q n Λ cap : ℕ) (hcap : 1 ≤ cap) (hn : n*q ≤ cap) :
    (patterns q n Λ).length ≤ (Λ+1)*cap^Λ := by
  unfold patterns
  apply (length_flatMap_bound _ _ (cap^Λ) ?_).trans (by simp)
  intro k hk
  rw [List.length_map,length_wordsOfLength]
  exact (Nat.pow_le_pow_left hn k).trans
    (Nat.pow_le_pow_right hcap (Nat.le_of_lt_succ (List.mem_range.mp hk)))

def allShapes (q L b Λ : ℕ) : List (Shape q) :=
  (List.range L).flatMap fun a =>
    (List.range L).flatMap fun r =>
      (shortWords q b).flatMap fun u =>
        (shortWords q b).flatMap fun v =>
          (patterns q (a+u.length+r) Λ).map (fun p => ⟨a,r,u,v,p⟩)

def families (q K b L Λ : ℕ) (pad : Fin q) :
    List (Shape q × Finset (Fin (q^L) → FieldHash.F₃)) :=
  (allShapes q L b Λ).dedup.filterMap fun shape =>
    let members := shape.vectors K b L Λ pad
    if members.Nonempty then some (shape,members) else none

def familyBound (q L b Λ : ℕ) : ℕ :=
  12*(L+b+1)^3*q^(2*b)*(Λ+1)*(3*q*(L+b+1))^Λ

theorem allShapes_count (q L b Λ : ℕ) (hq : 2 ≤ q) :
    (allShapes q L b Λ).length ≤ familyBound q L b Λ := by
  let B := 3*q*(L+b+1)
  let C := (Λ+1)*B^Λ
  let W := (shortWords q b).length
  have hB : 1 ≤ B := by
    have hz : 0 < B := by
      unfold B
      exact Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (Nat.succ_pos _)
    omega
  have hlen : (allShapes q L b Λ).length ≤ L*(L*(W*(W*C))) := by
    unfold allShapes
    apply (length_flatMap_bound _ _ (L*(W*(W*C))) ?_).trans (by simp)
    intro a ha
    apply (length_flatMap_bound _ _ (W*(W*C)) ?_).trans (by simp)
    intro r hr
    apply length_flatMap_bound _ _ (W*C)
    intro u hu
    apply length_flatMap_bound _ _ C
    intro v _
    rw [List.length_map]
    apply patterns_count q (a+u.length+r) Λ B hB
    have ha' := List.mem_range.mp ha
    have hr' := List.mem_range.mp hr
    have hu' := shortWords_spec.mp hu
    have hN : a+u.length+r ≤ 3*(L+b+1) := by omega
    calc
      _ ≤ (3*(L+b+1))*q := Nat.mul_le_mul_right _ hN
      _ = B := by dsimp [B]; ring
  have hW : W ≤ 2*q^b := shortWords_count q b hq
  have hl : L*L ≤ (L+b+1)^3 := by
    have h₁ := Nat.pow_le_pow_left (show L ≤ L+b+1 by omega) 2
    have h₂ := Nat.pow_le_pow_right (show 1 ≤ L+b+1 by omega) (show 2 ≤ 3 by decide)
    simpa [Nat.pow_two] using h₁.trans h₂
  calc
    _ ≤ L*(L*(W*(W*C))) := hlen
    _ ≤ L*(L*((2*q^b)*((2*q^b)*C))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul hW (Nat.mul_le_mul_right _ hW)))
    _ = (L*L)*((4*q^(2*b))*C) := by rw [Nat.mul_comm 2 b,Nat.pow_mul]; ring
    _ ≤ (L+b+1)^3*((12*q^(2*b))*C) :=
      Nat.mul_le_mul hl (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide)))
    _ = familyBound q L b Λ := by unfold familyBound; dsimp [C,B]; ring

theorem families_count (q K b L Λ : ℕ) (pad : Fin q) (hq : 2 ≤ q) :
    (families q K b L Λ pad).length ≤ familyBound q L b Λ := by
  unfold families
  apply (List.length_filterMap_le _ _).trans
  exact (List.dedup_sublist _).length_le.trans (allShapes_count q L b Λ hq)

private theorem ofFn_finRange_map {A : Type*} {n : ℕ} (f : Fin n → A) :
    (List.finRange n).map f = List.ofFn f := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [List.getElem_finRange]

private theorem filterOptions_length {A : Type*} (xs : List (Option A)) :
    (xs.filterMap (fun x => x)).length = (xs.filter Option.isSome).length := by
  induction xs with
  | nil => rfl
  | cons a tail ih =>
    cases a <;> simp only [List.filterMap_cons,List.filter_cons,Option.isSome_none,
      Option.isSome_some,Bool.false_eq_true,ite_false,ite_true,List.length_cons,ih]

private theorem coded_pattern_length {q : ℕ} (xs : List (Option (Fin q))) :
    let coded := List.ofFn fun i : Fin xs.length =>
      (xs.get i).map (fun a => finProdFinEquiv (i,a))
    (coded.filterMap id).length = (xs.filter Option.isSome).length := by
  dsimp only
  change ((List.ofFn fun i : Fin xs.length =>
    (xs.get i).map (fun a => finProdFinEquiv (i,a))).filterMap (fun x => x)).length = _
  rw [filterOptions_length]
  have hget (i : Fin xs.length) : ((xs.get i).map (fun a => finProdFinEquiv (i,a))).isSome =
      (xs.get i).isSome := by cases xs.get i <;> rfl
  have hcount (ls : List (Fin xs.length)) :
      ((ls.map fun i => (xs.get i).map (fun a => finProdFinEquiv (i,a))).filter Option.isSome).length =
      ((ls.map xs.get).filter Option.isSome).length := by
    induction ls with
    | nil => rfl
    | cons i ls ih =>
      simp only [List.map_cons,List.filter_cons,hget]
      split <;> simp only [List.length_cons,ih]
  have hf := hcount (List.finRange xs.length)
  simpa only [ofFn_finRange_map,List.ofFn_get] using hf

private theorem patterns_mem {q n Λ : ℕ} (xs : List (Option (Fin q)))
    (hn : xs.length = n) (hΛ : (xs.filter Option.isSome).length ≤ Λ) : xs ∈ patterns q n Λ := by
  subst n
  let coded := List.ofFn fun i : Fin xs.length =>
    (xs.get i).map (fun a => finProdFinEquiv (i,a))
  let marks := coded.filterMap id
  refine List.mem_flatMap.mpr ⟨marks.length,List.mem_range.mpr (by
    have h := coded_pattern_length xs
    change marks.length = _ at h
    omega),List.mem_map.mpr ⟨marks,mem_wordsOfLength.mpr rfl,?_⟩⟩
  let pairs : List (Fin xs.length × Fin q) := marks.map finProdFinEquiv.symm
  have hm (i : Fin xs.length) (a : Fin q) : (i,a) ∈ pairs ↔ xs.get i = some a := by
    constructor
    · intro hi
      obtain ⟨c,hc,he⟩ := List.mem_map.mp hi
      obtain ⟨op,hp,hval⟩ := List.mem_filterMap.mp hc
      have e : op = some c := hval
      obtain ⟨j,hj⟩ := List.mem_ofFn.mp hp
      have hh : (xs.get j).map (fun a => finProdFinEquiv (j,a)) = some c := hj.trans e
      cases hg : xs.get j with
      | none => rw [hg] at hh; cases hh
      | some x =>
        rw [hg] at hh
        have hij : (j,x) = (i,a) := by
          have hc' := Option.some.inj hh
          rw [← hc',Equiv.symm_apply_apply] at he
          exact he
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj hij
        exact hg
    · intro h
      exact List.mem_map.mpr ⟨finProdFinEquiv (i,a),
        List.mem_filterMap.mpr ⟨some (finProdFinEquiv (i,a)),List.mem_ofFn.mpr ⟨i,by rw [h]; rfl⟩,rfl⟩,
        finProdFinEquiv.symm_apply_apply _⟩
  have hf (i : Fin xs.length) : ((pairs.find? (fun p => p.1 == i)).map Prod.snd) = xs.get i := by
    cases hfind : pairs.find? (fun p => p.1 == i) with
    | none =>
      cases hx : xs.get i with
      | none => rfl
      | some a =>
        have h := List.find?_eq_none.mp hfind (i,a) ((hm i a).mpr hx)
        simp at h
    | some p =>
      have hi : p.1 = i := by
        have h := List.find?_some (p := fun p : Fin xs.length × Fin q => p.1 == i) hfind
        simpa using h
      have hp := List.mem_of_find?_eq_some hfind
      have h := (hm p.1 p.2).mp hp
      simpa [hi,hfind] using h.symm
  change ((List.finRange xs.length).map (fun i => ((pairs.find? (fun p => p.1 == i)).map Prod.snd))) = xs
  rw [ofFn_finRange_map]
  simp only [hf,List.ofFn_get]

theorem mem_allShapes {q L b Λ : ℕ} (s : Shape q)
    (hl : s.left < L) (hr : s.right < L) (hu : s.removed.length ≤ b) (hv : s.replacement.length ≤ b)
    (hlen : s.fresh.length = s.left+s.removed.length+s.right) (hf : s.freshCount ≤ Λ) :
    s ∈ allShapes q L b Λ := by
  obtain ⟨a,r,u,v,p⟩ := s
  exact List.mem_flatMap.mpr ⟨a,List.mem_range.mpr hl,List.mem_flatMap.mpr
    ⟨r,List.mem_range.mpr hr,List.mem_flatMap.mpr ⟨u,shortWords_spec.mpr hu,
      List.mem_flatMap.mpr ⟨v,shortWords_spec.mpr hv,List.mem_map.mpr
        ⟨p,patterns_mem p hlen hf,rfl⟩⟩⟩⟩⟩

theorem mem_families_of_nonempty {q K b L Λ : ℕ} (pad : Fin q) (s : Shape q)
    (h : s ∈ allShapes q L b Λ) (hne : (s.vectors K b L Λ pad).Nonempty) :
    (s,s.vectors K b L Λ pad) ∈ families q K b L Λ pad := by
  exact List.mem_filterMap.mpr ⟨s,List.mem_dedup.mpr h,by simp [hne]⟩

#print axioms mem_allShapes

#print axioms families_count

end DeletionCode.Explicit.BubbleFamilies
