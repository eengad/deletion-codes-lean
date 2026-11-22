import DeletionCode.Explicit.CatalogueEnumeration
import DeletionCode.Explicit.Machine.SourceHashChoice
import DeletionCode.Explicit.Machine.AcceptanceWeights
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import Batteries.Tactic.OpenPrivate

/-! Ordered catalogue enumeration with word lists in place of proof-carrying bubbles. -/
namespace DeletionCode.Explicit.Machine.OrderedCatalogue

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Borrowed BubbleFamilies FieldHash
open private shortWords patterns patternOfMarks from DeletionCode.Explicit.FamilyEnumeration
open private tuples from DeletionCode.Explicit.CatalogueEnumeration
open private localValid disjointValid from DeletionCode.Explicit.CatalogueCheck
open Qary.SupportComponents

set_option linter.style.haveILetI false

variable {q K b L s : ℕ}

abbrev BubbleData (q : ℕ) := (QWord q × QWord q) × (QWord q × QWord q)
abbrev ShapeData (q : ℕ) := (ℕ × ℕ) × (QWord q × QWord q)

abbrev wordPairEncoding (q : ℕ) := encPair (wordEncoding q) (wordEncoding q)
abbrev bubbleEncoding (q : ℕ) := encPair (wordPairEncoding q) (wordPairEncoding q)
abbrev shapeEncoding (q : ℕ) := encPair (encPair encUnary encUnary) (wordPairEncoding q)
abbrev ruleEncoding (q : ℕ) := encList (bubbleEncoding q)

def bubbleData (w : BubbleWord (Fin q) K b L) : BubbleData q :=
  ((w.left,w.right),(w.removed,w.replacement))

def side (x : BubbleData q) (positive : Bool) : QWord q :=
  x.1.1 ++ (if positive then x.2.2 else x.2.1) ++ x.1.2

theorem side_eq (w : BubbleWord (Fin q) K b L) (positive : Bool) :
    side (bubbleData w) positive = Catalogue.pathWord w positive := by
  cases positive <;> rfl

def shapes (q b L : ℕ) : List (ShapeData q) :=
  (List.range L).flatMap fun a =>
    (List.range L).flatMap fun r =>
      (shortWords q b).flatMap fun u =>
        (shortWords q b).map fun v => ((a,r),(u,v))

theorem shapes_eq (q b L : ℕ) :
    shapes q b L = (allShapes q L b 0).map (fun a => ((a.left,a.right),(a.removed,a.replacement))) := by
  simp [shapes,allShapes,patterns,wordsOfLength,List.map_flatMap]
  simp [← List.map_eq_flatMap,List.map_map,Function.comp_def]

def localCheck (K b L : ℕ) (x : BubbleData q) : Bool :=
  decide (x.2.1.length ≤ b) && decide (x.2.2.length ≤ b) && decide (x.2.1 ≠ x.2.2) &&
  decide (L-1-K-b ≤ x.1.1.length) && decide (x.1.1.length ≤ L-1) &&
  decide (L-1-K-b ≤ x.1.2.length) && decide (x.1.2.length ≤ L-1)

def expansions (q : ℕ) (x : ShapeData q) : List (BubbleData q) :=
  (wordsOfLength q x.1.1).flatMap fun a =>
    (wordsOfLength q x.1.2).map fun r => ((a,r),x.2)

def localRows (q K b L : ℕ) : List (BubbleData q) :=
  (shapes q b L).flatMap fun x => (expansions q x).filter (localCheck K b L)

theorem localResult (a r u v : QWord q) :
    (localWord K b L a.length u v (a++u++r)).map bubbleData =
      if localCheck K b L ((a,r),(u,v)) then some ((a,r),(u,v)) else none := by
  unfold localWord
  have hl : (a ++ u ++ r).take a.length = a := by simp [List.append_assoc]
  have hr : (a ++ u ++ r).drop (a.length + u.length) = r := by
    have hh : a.length+u.length = (a++u).length := by simp
    rw [hh]
    simp
  simp only [hl,hr]
  have spec : localCheck K b L ((a,r),(u,v)) = true ↔
      u.length ≤ b ∧ v.length ≤ b ∧ u ≠ v ∧
      L-1-K-b ≤ a.length ∧ a.length ≤ L-1 ∧ L-1-K-b ≤ r.length ∧ r.length ≤ L-1 := by
    simp only [localCheck,Bool.and_eq_true_iff,decide_eq_true_eq]
    tauto
  split
  next h =>
    have hc := spec.mpr h
    simp [hc,BubbleWord.negativeWord,bubbleData]
  next h =>
    have hc : localCheck K b L ((a,r),(u,v)) = false := Bool.eq_false_iff.mpr (fun hb => h (spec.mp hb))
    simp [hc]

theorem local_eq (q K b L : ℕ) :
    localRows q K b L = (CatalogueEnumeration.localWords q K b L).map bubbleData := by
  unfold localRows CatalogueEnumeration.localWords
  rw [shapes_eq,List.flatMap_map,List.map_flatMap]
  apply List.flatMap_congr
  intro shape _
  simp only [expansions,List.filter_flatMap,List.map_flatMap]
  apply List.flatMap_congr
  intro a ha
  rw [List.filter_map,← List.filterMap_eq_filter,List.map_filterMap,List.map_filterMap]
  apply List.filterMap_congr
  intro r _
  rw [← mem_wordsOfLength.mp ha]
  simpa only [Option.guard,Function.comp_def,Option.map_ite,Option.map_some,Option.map_none] using
    (localResult (K := K) (b := b) (L := L) a r shape.removed shape.replacement).symm

def vertices (L : ℕ) (w : QWord q) : List (QWord q) :=
  (List.range (w.length-L+2)).map (fun i => DeletionCode.Explicit.AcceptanceWeights.window (L-1) i w)

abbrev PathData (q : ℕ) := List (QWord q)
abbrev Prepared (q : ℕ) := (PathData q × PathData q) × Bool

def prepare (L : ℕ) (w : BubbleData q) : Prepared q :=
  let neg := side w false
  let pos := side w true
  ((vertices L neg,vertices L pos),decide (L ≤ neg.length) && decide (L ≤ pos.length))

def simple (vs : PathData q) : Bool :=
  (List.range vs.length).all fun i => (List.range vs.length).all fun j =>
    decide (i = j) || decide (vs.getD i [] ≠ vs.getD j [])

def cross (vs ws : PathData q) : Bool :=
  (List.range vs.length).all fun i => (List.range ws.length).all fun j =>
    decide (vs.getD i [] ≠ ws.getD j []) ||
      ((decide (i = 0) && decide (j = 0)) ||
        (decide (i = vs.length-1) && decide (j = ws.length-1)))

def validLocal (w : Prepared q) : Bool :=
  let a := w.1.1
  let c := w.1.2
  w.2 && simple a && simple c && cross a c &&
    (decide (a.length ≠ 2) || decide (c.length ≠ 2)) &&
    decide (a.getD 0 [] = c.getD 0 []) &&
    decide (a.getD (a.length-1) [] = c.getD (c.length-1) [])

def pathsDisjoint (vs ws : PathData q) : Bool :=
  (List.range vs.length).all fun i => (List.range ws.length).all fun j =>
    decide (vs.getD i [] ≠ ws.getD j [])

def bubblesDisjoint (a c : Prepared q) : Bool :=
  pathsDisjoint a.1.1 c.1.1 && pathsDisjoint a.1.1 c.1.2 &&
    pathsDisjoint a.1.2 c.1.1 && pathsDisjoint a.1.2 c.1.2

def valid (L : ℕ) (ws : List (BubbleData q)) : Bool :=
  let data := ws.map (prepare L)
  data.all validLocal &&
    (List.range data.length).all fun i => (List.range data.length).all fun j =>
      decide (i = j) || bubblesDisjoint (data.getD i (([],[]),false)) (data.getD j (([],[]),false))

private theorem serialize_vertex (pad : Fin q) (w : QWord q) (L i : ℕ)
    (hw : L ≤ w.length) (hi : i < w.length-L+2) :
    DeletionCode.Explicit.AcceptanceWeights.window (L-1) i w =
      List.ofFn (fun j : Fin (L-1) => w.getD (i+j.val) pad) := by
  by_cases hL : L = 0
  · subst L
    simp [DeletionCode.Explicit.AcceptanceWeights.window]
  have hcap : L-1 ≤ w.length-i := by omega
  apply List.ext_getElem
  · simp [DeletionCode.Explicit.AcceptanceWeights.window,Nat.min_eq_left hcap]
  · intro k hk hj
    have hm : i+k < w.length := by
      simp only [List.length_ofFn] at hj
      omega
    simp [DeletionCode.Explicit.AcceptanceWeights.window,List.getElem?_eq_getElem hm]

@[simp] theorem vertices_length (L : ℕ) (w : QWord q) :
    (vertices L w).length = w.length-L+2 := by simp [vertices]

private theorem vertices_getD (pad : Fin q) (L : ℕ) (w : QWord q)
    (hw : L ≤ w.length) (i : ℕ) (hi : i < w.length-L+2) :
    (vertices L w).getD i [] = List.ofFn (fun j : Fin (L-1) => w.getD (i+j.val) pad) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simpa [vertices] using serialize_vertex pad w L i hw hi

private theorem vertex_at (pad : Fin q) (ws : Fin s → BubbleWord (Fin q) K b L)
    (j : Fin s) (a : Bool) (ha : L ≤ (Catalogue.pathWord (ws j) a).length)
    (i : ℕ) (hi : i < (Catalogue.pathWord (ws j) a).length - L + 2) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    (vertices L (Catalogue.pathWord (ws j) a)).getD i [] =
      List.ofFn (vertex (Catalogue.indexedFamily ws (fun _ => (0 : Fin 1))) L j a i) := by
  exact vertices_getD pad L _ ha i hi

private theorem simple_iff (pad : Fin q) (ws : Fin s → BubbleWord (Fin q) K b L)
    (j : Fin s) (a : Bool) (ha : L ≤ (Catalogue.pathWord (ws j) a).length) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    let F := Catalogue.indexedFamily ws (fun _ => (0 : Fin 1))
    simple (vertices L (Catalogue.pathWord (ws j) a)) = true ↔
      ∀ (i k : Fin (F.extra j a+2)), vertex F L j a i.val = vertex F L j a k.val → i = k := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  dsimp only
  simp only [simple,List.all_eq_true,List.mem_range,vertices_length,Bool.or_eq_true,
    decide_eq_true_eq]
  change (∀ i, i < _ → ∀ k, k < _ → _) ↔ _
  constructor
  · intro h i k eqv
    apply Fin.ext
    have ho := h i.val i.isLt k.val k.isLt
    rw [vertex_at pad ws j a ha i.val i.isLt,vertex_at pad ws j a ha k.val k.isLt] at ho
    exact ho.resolve_right (by rw [eqv]; simp)
  · intro h i hi k hk
    rw [vertex_at pad ws j a ha i hi,vertex_at pad ws j a ha k hk]
    by_cases e : vertex (Catalogue.indexedFamily ws (fun _ => (0 : Fin 1))) L j a i =
        vertex (Catalogue.indexedFamily ws (fun _ => (0 : Fin 1))) L j a k
    · exact Or.inl (congrArg Fin.val (h ⟨i,hi⟩ ⟨k,hk⟩ e))
    · exact Or.inr (fun hh => e (List.ofFn_injective hh))

private theorem cross_iff (pad : Fin q) (ws : Fin s → BubbleWord (Fin q) K b L)
    (j : Fin s) (hf : L ≤ (Catalogue.pathWord (ws j) false).length)
    (ht : L ≤ (Catalogue.pathWord (ws j) true).length) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    let F := Catalogue.indexedFamily ws (fun _ => (0 : Fin 1))
    cross (vertices L (Catalogue.pathWord (ws j) false)) (vertices L (Catalogue.pathWord (ws j) true)) = true ↔
      ∀ (i : Fin (F.extra j false+2)) (k : Fin (F.extra j true+2)),
        vertex F L j false i.val = vertex F L j true k.val →
        (i.val = 0 ∧ k.val = 0) ∨ (i.val = F.extra j false+1 ∧ k.val = F.extra j true+1) := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  dsimp only
  simp only [cross,List.all_eq_true,List.mem_range,vertices_length,Bool.or_eq_true,
    Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · intro h i k eqv
    have ho := h i.val i.isLt k.val k.isLt
    rw [vertex_at pad ws j false hf i.val i.isLt,vertex_at pad ws j true ht k.val k.isLt] at ho
    exact ho.resolve_left (by rw [eqv]; simp)
  · intro h i hi k hk
    rw [vertex_at pad ws j false hf i hi,vertex_at pad ws j true ht k hk]
    by_cases e : vertex (Catalogue.indexedFamily ws (fun _ => (0 : Fin 1))) L j false i =
        vertex (Catalogue.indexedFamily ws (fun _ => (0 : Fin 1))) L j true k
    · exact Or.inr (h ⟨i,hi⟩ ⟨k,hk⟩ e)
    · exact Or.inl (fun hh => e (List.ofFn_injective hh))

private theorem disjoint_iff (pad : Fin q) (ws : Fin s → BubbleWord (Fin q) K b L)
    (i j : Fin s) (a c : Bool) (ha : L ≤ (Catalogue.pathWord (ws i) a).length)
    (hc : L ≤ (Catalogue.pathWord (ws j) c).length) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    let F := Catalogue.indexedFamily ws (fun _ => (0 : Fin 1))
    pathsDisjoint (vertices L (Catalogue.pathWord (ws i) a)) (vertices L (Catalogue.pathWord (ws j) c)) =
      true ↔ ∀ (k : Fin (F.extra i a+2)) (m : Fin (F.extra j c+2)), vertex F L i a k.val ≠ vertex F L j c m.val := by
  dsimp only
  simp only [pathsDisjoint,List.all_eq_true,List.mem_range,vertices_length,decide_eq_true_eq]
  constructor
  · intro h k m he
    have hne := h k.val k.isLt m.val m.isLt
    rw [vertex_at pad ws i a ha k.val k.isLt,vertex_at pad ws j c hc m.val m.isLt,he] at hne
    exact hne rfl
  · intro h k hk m hm he
    rw [vertex_at pad ws i a ha k hk,vertex_at pad ws j c hc m hm] at he
    exact h ⟨k,hk⟩ ⟨m,hm⟩ (List.ofFn_injective he)

private theorem validLocal_iff (pad : Fin q) (ws : Fin s → BubbleWord (Fin q) K b L) (j : Fin s) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    validLocal (prepare L (bubbleData (ws j))) = true ↔
      (decide (∀ a : Bool, L ≤ (Catalogue.pathWord (ws j) a).length) &&
        localValid (Catalogue.indexedFamily ws (fun _ => (0 : Fin 1))) L j) = true := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  let F := Catalogue.indexedFamily ws (fun _ => (0 : Fin 1))
  let a := Catalogue.pathWord (ws j) false
  let c := Catalogue.pathWord (ws j) true
  have hlen : (∀ a : Bool, L ≤ (Catalogue.pathWord (ws j) a).length) ↔ L ≤ a.length ∧ L ≤ c.length := by
    constructor
    · exact fun h => ⟨h false,h true⟩
    · intro h b
      cases b
      · exact h.1
      · exact h.2
  simp only [validLocal,prepare,side_eq,localValid,Bool.and_eq_true,decide_eq_true_eq,hlen]
  by_cases ha : L ≤ a.length
  · by_cases hc : L ≤ c.length
    · have hs : (∀ a : Bool, ∀ (i k : Fin (F.extra j a+2)),
          vertex F L j a i.val = vertex F L j a k.val → i = k) ↔
          (simple (vertices L a) = true ∧ simple (vertices L c) = true) := by
        have hneg := simple_iff pad ws j false ha
        have hpos := simple_iff pad ws j true hc
        dsimp only at hneg hpos
        rw [hneg,hpos]
        constructor
        · exact fun h => ⟨h false,h true⟩
        · intro h b
          cases b
          · exact h.1
          · exact h.2
      have hna : (vertices L a).length ≠ 2 ↔ F.extra j false ≠ 0 := by
        simp [F,Catalogue.indexedFamily,Catalogue.family,vertices_length,a]
      have hnc : (vertices L c).length ≠ 2 ↔ F.extra j true ≠ 0 := by
        simp [F,Catalogue.indexedFamily,Catalogue.family,vertices_length,c]
      have h0a : 0 < a.length-L+2 := by omega
      have h0c : 0 < c.length-L+2 := by omega
      have h1a : a.length-L+1 < a.length-L+2 := by omega
      have h1c : c.length-L+1 < c.length-L+2 := by omega
      rw [vertex_at pad ws j false ha 0 h0a,vertex_at pad ws j true hc 0 h0c]
      have hsub (k : ℕ) : k+2-1 = k+1 := by omega
      simp only [vertices_length,hsub]
      rw [vertex_at pad ws j false ha _ h1a,vertex_at pad ws j true hc _ h1c]
      have hcross := cross_iff pad ws j ha hc
      dsimp only at hcross
      rw [hcross]
      simp only [Bool.or_eq_true,decide_eq_true_eq,List.ofFn_inj]
      have hs' := hs
      have hna' := hna
      have hnc' := hnc
      dsimp only [a,c,F] at hs' hna' hnc'
      simp only [vertices_length] at hna' hnc'
      rw [hna',hnc',hs']
      have hnaEnd : a.length-L+1 = (Catalogue.indexedFamily ws (fun _ => (0 : Fin 1))).extra j false+1 := rfl
      have hncEnd : c.length-L+1 = (Catalogue.indexedFamily ws (fun _ => (0 : Fin 1))).extra j true+1 := rfl
      rw [hnaEnd,hncEnd]
      simp only [and_assoc]
      rfl
    · simp [a,c,ha,hc]
  · simp [a,c,ha]

private theorem preparedDisjoint_iff (pad : Fin q) (ws : Fin s → BubbleWord (Fin q) K b L)
    (i j : Fin s) (hw : ∀ j a, L ≤ (Catalogue.pathWord (ws j) a).length) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    let F := Catalogue.indexedFamily ws (fun _ => (0 : Fin 1))
    bubblesDisjoint (prepare L (bubbleData (ws i))) (prepare L (bubbleData (ws j))) = true ↔
      ∀ a c, ∀ (k : Fin (F.extra i a+2)) (m : Fin (F.extra j c+2)), vertex F L i a k.val ≠ vertex F L j c m.val := by
  dsimp only
  simp only [bubblesDisjoint,prepare,side_eq,Bool.and_eq_true,disjoint_iff pad ws i j _ _ (hw i _) (hw j _)]
  constructor
  · intro h a c
    cases a <;> cases c
    · exact h.1.1.1
    · exact h.1.1.2
    · exact h.1.2
    · exact h.2
  · intro h
    exact ⟨⟨⟨h false false,h false true⟩,h true false⟩,h true true⟩

private theorem all_ofFn {α : Type} (f : Fin s → α) (p : α → Bool) :
    (List.ofFn f).all p = true ↔ ∀ j, p (f j) = true := by
  simp [List.all_eq_true,List.mem_ofFn]

theorem valid_eq (pad : Fin q) (ws : Fin s → BubbleWord (Fin q) K b L) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    valid L (List.ofFn (fun i => bubbleData (ws i))) =
      Catalogue.validCheck ws (fun _ => (0 : Fin 1)) := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  apply Bool.eq_iff_iff.mpr
  unfold valid Catalogue.validCheck
  simp only [List.map_ofFn,Function.comp_def,Bool.and_eq_true_iff]
  rw [all_ofFn]
  simp only [validLocal_iff pad ws,Bool.and_eq_true_iff]
  simp only [List.all_eq_true,List.mem_finRange,true_implies,Bool.and_eq_true_iff]
  apply and_congr_right
  intro h
  have hw : ∀ j a, L ≤ (Catalogue.pathWord (ws j) a).length :=
    fun j a => (of_decide_eq_true (h j).1) a
  simp only [List.mem_range,List.length_ofFn,Bool.or_eq_true,decide_eq_true_eq,
    disjointValid]
  constructor
  · intro hd i j _ hne
    have hm := hd i.val i.isLt j.val j.isLt
    rw [BooleanFibres.ofFn_getD _ i,BooleanFibres.ofFn_getD _ j] at hm
    exact (preparedDisjoint_iff pad ws i j hw).mp (hm.resolve_left fun h => hne (Fin.ext h))
  · intro hd i hi j hj
    by_cases he : i = j
    · exact Or.inl he
    · rw [BooleanFibres.ofFn_getD _ (⟨i,hi⟩ : Fin s),BooleanFibres.ofFn_getD _ (⟨j,hj⟩ : Fin s)]
      exact Or.inr ((preparedDisjoint_iff pad ws ⟨i,hi⟩ ⟨j,hj⟩ hw).mpr
        (hd _ _ trivial (fun h => he (congrArg Fin.val h))))

def rulesAt (_pad : Fin q) (K b L t : ℕ) : List (List (BubbleData q)) :=
  (ExceptionalWeight.tuples (localRows q K b L) (2*t)).filter (valid L)

private theorem tuples_map {α β : Type} (f : α → β) (xs : List α) (n : ℕ) :
    ExceptionalWeight.tuples (xs.map f) n = (tuples xs n).map (List.map f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ExceptionalWeight.tuples,tuples,ih,List.map_flatMap,List.flatMap_map,
      List.map_map,Function.comp_def]

private theorem tuple_length {α : Type} (xs : List α) {n : ℕ} {ys : List α} (hy : ys ∈ tuples xs n) :
    ys.length = n := by
  induction n generalizing ys with
  | zero => simpa [tuples] using hy
  | succ n ih =>
    rw [tuples] at hy
    obtain ⟨x,_,hx⟩ := List.mem_flatMap.mp hy
    obtain ⟨zs,hz,rfl⟩ := List.mem_map.mp hx
    simp [ih hz]

private theorem ofFn_after_eq {α : Type} (ws : List α) (h : ws.length = s) :
    List.ofFn (fun i : Fin s => ws.get (Fin.cast h.symm i)) = ws := by
  subst s
  simp

theorem rulesAt_eq (pad : Fin q) (K b L t : ℕ) :
    rulesAt pad K b L t =
      (CatalogueEnumeration.rules q K b L (2*t) pad).map (fun r => List.ofFn (bubbleData ∘ r)) := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  unfold rulesAt CatalogueEnumeration.rules
  rw [local_eq,tuples_map,List.filter_map,← List.filterMap_eq_filter,List.map_filterMap,List.map_filterMap]
  apply List.filterMap_congr
  intro ws hw
  have hl := tuple_length _ hw
  let f := fun i : Fin (2*t) => ws.get (Fin.cast hl.symm i)
  have hmap : List.ofFn (bubbleData ∘ f) = ws.map bubbleData := by
    rw [← List.map_ofFn,ofFn_after_eq ws hl]
  simp only [Function.comp_def,Option.guard]
  have hh : valid L (ws.map bubbleData) = Catalogue.validCheck f (fun _ => (0 : Fin 1)) :=
    (congrArg (valid L) hmap).symm.trans (valid_eq pad f)
  simp only [hl,↓reduceDIte]
  change (Option.map (List.map bubbleData) (if valid L (ws.map bubbleData) = true then some ws else none)) =
    Option.map (fun r => List.ofFn (bubbleData ∘ r))
      (if Catalogue.validCheck f (fun _ => (0 : Fin 1)) = true then some f else none)
  by_cases h : Catalogue.validCheck f (fun _ => (0 : Fin 1)) = true
  · simp [hh,h,hmap]
  · simp [hh,h]

def rules (pad : Fin q) (b t ℓ : ℕ) : List (List (BubbleData q)) :=
  rulesAt pad (UniformParameters.windowLength q ℓ) b (UniformParameters.gram q b t ℓ) t

theorem rules_eq (pad : Fin q) (b t ℓ : ℕ) :
    rules pad b t ℓ = (CatalogueEnumeration.rules q (UniformParameters.windowLength q ℓ) b
      (UniformParameters.gram q b t ℓ) (2*t) pad).map (fun r => List.ofFn (bubbleData ∘ r)) :=
  rulesAt_eq pad _ _ _ _

private theorem shapes_polyTime (q b : ℕ) :
    ComputableInPolyTime (shapes q b) encUnary (encList (shapeEncoding q)) := by
  unfold shapes
  apply flatMapWithInput (encIn := encUnary) (encA := encUnary)
    (f := fun L a => (List.range L).flatMap fun r => (shortWords q b).flatMap fun u =>
      (shortWords q b).map fun v => ((a,r),(u,v))) range
  apply flatMapWithInput (encIn := encPair encUnary encUnary) (encA := encUnary)
    (f := fun x r => (shortWords q b).flatMap fun u =>
      (shortWords q b).map fun v => ((x.2,r),(u,v))) (range.comp (fst encUnary encUnary))
  apply flatMapConst
  intro u _
  apply mapConst
  intro v _
  exact (((snd encUnary encUnary).comp (fst (encPair encUnary encUnary) encUnary)).prod
    (snd (encPair encUnary encUnary) encUnary)).prod (const (u,v))

private abbrev localInputEncoding (q : ℕ) := encPair (encPair encUnary encUnary) (bubbleEncoding q)

theorem localCheck_polyTime (q b : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × BubbleData q => localCheck x.1.1 b x.1.2 x.2)
      (localInputEncoding q) encBool := by
  have hp := fst (encPair encUnary encUnary) (bubbleEncoding q)
  have hw := snd (encPair encUnary encUnary) (bubbleEncoding q)
  have hlen := length_list (ExceptionalRecords.letterEncoding q)
  have hu := hlen.comp hw.snd'.fst'
  have hv := hlen.comp hw.snd'.snd'
  have ha := hlen.comp hw.fst'.fst'
  have hr := hlen.comp hw.fst'.snd'
  have hL := unary_sub' hp.snd' (const 1)
  have lo := unary_sub' (unary_sub' hL hp.fst') (const b)
  exact bool_and'
    (bool_and' (bool_and' (bool_and' (bool_and'
      (bool_and' (unary_le' hu (const b)) (unary_le' hv (const b)))
      (bool_not.comp (hw.snd'.fst'.decide_eq' hw.snd'.snd'))) (unary_le' lo ha))
      (unary_le' ha hL)) (unary_le' lo hr)) (unary_le' hr hL)

def cappedExpansions (q b t : ℕ) (x : ℕ × ShapeData q) : List (BubbleData q) :=
  let L := UniformParameters.gram q b t x.1
  expansions q ((min x.2.1.1 L,min x.2.1.2 L),x.2.2)

private theorem capped_count (q b t : ℕ) (hq : 2 ≤ q) (f : ShapeData q → ℕ) :
    PolyBounded (fun x : ℕ × ShapeData q => ((encPair encUnary (shapeEncoding q)) x).length)
      (fun x => q ^ min (f x.2) (UniformParameters.gram q b t x.1)) := by
  apply ((SourceHashChoice.width_polyTime q b t hq).comp
    (fst encUnary (shapeEncoding q))).polyBounded_length.mono
  intro x
  simp only [encUnary_apply,List.length_replicate]
  exact Nat.pow_le_pow_right (by omega) (Nat.min_le_right _ _)

theorem cappedExpansions_polyTime (q b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (cappedExpansions q b t)
      (encPair encUnary (shapeEncoding q)) (encList (bubbleEncoding q)) := by
  let e := encPair encUnary (shapeEncoding q)
  let w := wordEncoding q
  have hl := (Machine.UniformParameters.gram_machine q b t).comp (fst encUnary (shapeEncoding q))
  have hs := snd encUnary (shapeEncoding q)
  have hlft := wordsOfLength_polyTime hq (unary_min' hs.fst'.fst' hl) (capped_count q b t hq (·.1.1))
  have hrgt := wordsOfLength_polyTime hq (unary_min' hs.fst'.snd' hl) (capped_count q b t hq (·.1.2))
  unfold cappedExpansions expansions
  dsimp only
  apply flatMapWithInput (encIn := e) (encA := w)
    (f := fun x a => (wordsOfLength q (min x.2.1.2 (UniformParameters.gram q b t x.1))).map
      (fun r => ((a,r),x.2.2))) hlft
  apply mapWithInput (encIn := encPair e w) (encA := w) (encB := bubbleEncoding q)
    (f := fun x r => ((x.2,r),x.1.2.2)) (hrgt.comp (fst e w))
  have h := fst (encPair e w) w
  exact (((snd e w).comp h).prod (snd (encPair e w) w)).prod (hs.snd'.comp ((fst e w).comp h))

def localUniform (q b t ℓ : ℕ) : List (BubbleData q) :=
  let L := UniformParameters.gram q b t ℓ
  let K := UniformParameters.windowLength q ℓ
  (shapes q b L).flatMap fun s => (cappedExpansions q b t (ℓ,s)).filter (localCheck K b L)

theorem localUniform_eq (q b t ℓ : ℕ) :
    localUniform q b t ℓ = localRows q (UniformParameters.windowLength q ℓ) b
      (UniformParameters.gram q b t ℓ) := by
  unfold localUniform localRows
  dsimp only
  apply List.flatMap_congr
  intro x hx
  have hl : x.1.1 < UniformParameters.gram q b t ℓ := by
    unfold shapes at hx
    obtain ⟨a,ha,hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨r,_,hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨u,_,hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mp ha
  have hr : x.1.2 < UniformParameters.gram q b t ℓ := by
    unfold shapes at hx
    obtain ⟨a,_,hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨r,hr,hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨u,_,hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mp hr
  simp [cappedExpansions,Nat.min_eq_left (Nat.le_of_lt hl),Nat.min_eq_left (Nat.le_of_lt hr)]

theorem localUniform_polyTime (q b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (localUniform q b t) encUnary (encList (bubbleEncoding q)) := by
  let e := encPair encUnary (shapeEncoding q)
  let w := bubbleEncoding q
  have hl := Machine.UniformParameters.gram_machine q b t
  have hk := Machine.UniformParameters.window_machine q
  unfold localUniform
  dsimp only
  apply flatMapWithInput (encIn := encUnary) (encA := shapeEncoding q)
    (f := fun ℓ s => (cappedExpansions q b t (ℓ,s)).filter
      (localCheck (UniformParameters.windowLength q ℓ) b (UniformParameters.gram q b t ℓ)))
    ((shapes_polyTime q b).comp hl)
  have hx := (fst encUnary (shapeEncoding q)).comp (fst e w)
  exact filterWithInput (encIn := e) (encA := w)
    (test := fun x w => localCheck (UniformParameters.windowLength q x.1) b
      (UniformParameters.gram q b t x.1) w) (cappedExpansions_polyTime q b t hq)
    (by
      have h := (localCheck_polyTime q b).comp
        (encIn := encPair e w) (encMid := localInputEncoding q)
        (((hk.comp hx).prod (hl.comp hx)).prod (snd e w))
      exact h.of_enc_eq (fun _ => rfl))

private theorem grid_polyTime {α : Type} {e : α ↪ List Bool} {a c : α → ℕ}
    {test : α → ℕ → ℕ → Bool} (ha : ComputableInPolyTime a e encUnary)
    (hc : ComputableInPolyTime c e encUnary)
    (ht : ComputableInPolyTime (fun x : (α × ℕ) × ℕ => test x.1.1 x.1.2 x.2)
      (encPair (encPair e encUnary) encUnary) encBool) :
    ComputableInPolyTime (fun x => (List.range (a x)).all fun i => (List.range (c x)).all
      (test x i)) e encBool :=
  allWithInput (encIn := e) (encA := encUnary) (test := fun x i => (List.range (c x)).all (test x i))
    (unary_range' ha) (allWithInput (encIn := encPair e encUnary) (encA := encUnary)
      (test := fun x j => test x.1 x.2 j) (unary_range' (hc.comp (fst e encUnary))) ht)

theorem side_polyTime (q : ℕ) (a : Bool) :
    ComputableInPolyTime (fun w : BubbleData q => side w a) (bubbleEncoding q) (wordEncoding q) := by
  let e := wordPairEncoding q
  have h := fst e e
  have hr := snd e e
  cases a
  · exact listAppend' (listAppend' h.fst' hr.fst') h.snd'
  · exact listAppend' (listAppend' h.fst' hr.snd') h.snd'

private theorem vertices_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : ℕ × QWord q => vertices x.1 x.2)
      (encPair encUnary (wordEncoding q)) (encList (wordEncoding q)) := by
  let e := encPair encUnary (wordEncoding q)
  have hL := fst encUnary (wordEncoding q)
  have hw := snd encUnary (wordEncoding q)
  have hlen := (length_list (ExceptionalRecords.letterEncoding q)).comp hw
  unfold vertices
  apply mapWithInput (encIn := e) (encA := encUnary) (encB := wordEncoding q) (f := fun x i =>
      DeletionCode.Explicit.AcceptanceWeights.window (x.1-1) i x.2)
    (unary_range' (unary_add' (unary_sub' hlen hL) (const 2)))
  have hi := snd e encUnary
  have hx := fst e encUnary
  exact (Machine.AcceptanceWeights.window_polyTime q).comp
    ((unary_sub' (hL.comp hx) (const 1) |>.prod hi).prod (hw.comp hx))

abbrev pathsEncoding (q : ℕ) := encList (wordEncoding q)
abbrev pathPairEncoding (q : ℕ) := encPair (pathsEncoding q) (pathsEncoding q)
abbrev preparedEncoding (q : ℕ) := encPair (pathPairEncoding q) encBool

private theorem prepare_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : ℕ × BubbleData q => prepare x.1 x.2)
      (encPair encUnary (bubbleEncoding q)) (preparedEncoding q) := by
  let e := encPair encUnary (bubbleEncoding q)
  have hl := fst encUnary (bubbleEncoding q)
  have hw := snd encUnary (bubbleEncoding q)
  have hneg := (side_polyTime q false).comp hw
  have hpos := (side_polyTime q true).comp hw
  have hlen := length_list (ExceptionalRecords.letterEncoding q)
  have hn := (vertices_polyTime q).comp (encIn := e) (hl.prod hneg)
  have hp := (vertices_polyTime q).comp (encIn := e) (hl.prod hpos)
  exact (hn.prod hp).prod (bool_and' (unary_le' hl (hlen.comp hneg)) (unary_le' hl (hlen.comp hpos)))

private theorem simple_polyTime (q : ℕ) :
    ComputableInPolyTime (simple (q := q)) (pathsEncoding q) encBool := by
  let e := pathsEncoding q
  let p := encPair e encUnary
  have hi := (snd e encUnary).comp (fst p encUnary)
  have hj := snd p encUnary
  have hs := (fst e encUnary).comp (fst p encUnary)
  have ha := listGetDWithInput hs hi ([] : QWord q)
  have hc := listGetDWithInput hs hj ([] : QWord q)
  exact grid_polyTime (length_list (wordEncoding q)) (length_list (wordEncoding q))
    (test := fun vs i j => decide (i = j) || decide (vs.getD i [] ≠ vs.getD j []))
    (bool_or' (hi.decide_eq' hj) (bool_not.comp (ha.decide_eq' hc)))

private theorem pathsCompare_polyTime (q : ℕ) (allowEndpoints : Bool) :
    ComputableInPolyTime (if allowEndpoints then fun x : PathData q × PathData q => cross x.1 x.2
      else fun x => pathsDisjoint x.1 x.2) (pathPairEncoding q) encBool := by
  let e := pathPairEncoding q
  let p := encPair e encUnary
  let w := pathsEncoding q
  have hlen := length_list (wordEncoding q)
  have ha := hlen.comp (fst w w)
  have hc := hlen.comp (snd w w)
  have hx := (fst e encUnary).comp (fst p encUnary)
  have hi := (snd e encUnary).comp (fst p encUnary)
  have hj := snd p encUnary
  have h0 := listGetDWithInput ((fst w w).comp hx) hi ([] : QWord q)
  have h1 := listGetDWithInput ((snd w w).comp hx) hj ([] : QWord q)
  have hne := bool_not.comp (h0.decide_eq' h1)
  cases allowEndpoints
  · exact grid_polyTime ha hc
      (test := fun x i j => decide (x.1.getD i [] ≠ x.2.getD j [])) hne
  · have hz := bool_and' (hi.decide_eq' (const 0)) (hj.decide_eq' (const 0))
    have he := bool_and' (hi.decide_eq' (unary_sub' (ha.comp hx) (const 1)))
      (hj.decide_eq' (unary_sub' (hc.comp hx) (const 1)))
    exact grid_polyTime ha hc
      (test := fun x i j => decide (x.1.getD i [] ≠ x.2.getD j []) ||
        ((decide (i = 0) && decide (j = 0)) ||
          (decide (i = x.1.length-1) && decide (j = x.2.length-1))))
      (by
        have h := bool_or' hne (bool_or' hz he)
        exact h.of_enc_eq (fun _ => rfl))

private theorem validLocal_polyTime (q : ℕ) :
    ComputableInPolyTime (validLocal (q := q)) (preparedEncoding q) encBool := by
  have hp := fst (pathPairEncoding q) encBool
  have hlen := length_list (wordEncoding q)
  have hna := hlen.comp hp.fst'
  have hnc := hlen.comp hp.snd'
  have hsa := (simple_polyTime q).comp hp.fst'
  have hsc := (simple_polyTime q).comp hp.snd'
  have hcr := (pathsCompare_polyTime q true).comp hp
  have ha0 := listGetDWithInput hp.fst' (const 0) ([] : QWord q)
  have hc0 := listGetDWithInput hp.snd' (const 0) ([] : QWord q)
  have ha1 := listGetDWithInput hp.fst' (unary_sub' hna (const 1)) ([] : QWord q)
  have hc1 := listGetDWithInput hp.snd' (unary_sub' hnc (const 1)) ([] : QWord q)
  exact bool_and'
    (bool_and' (bool_and' (bool_and' (bool_and' (bool_and' (snd (pathPairEncoding q) encBool)
      hsa) hsc) hcr) (bool_or' (bool_not.comp (hna.decide_eq' (const 2)))
        (bool_not.comp (hnc.decide_eq' (const 2))))) (ha0.decide_eq' hc0)) (ha1.decide_eq' hc1)

private theorem bubblesDisjoint_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : Prepared q × Prepared q => bubblesDisjoint x.1 x.2)
      (encPair (preparedEncoding q) (preparedEncoding q)) encBool := by
  let e := preparedEncoding q
  have h0 := (fst e e).fst'
  have h1 := (snd e e).fst'
  have h := pathsCompare_polyTime q false
  exact bool_and' (bool_and' (bool_and'
    (h.comp (h0.fst'.prod h1.fst')) (h.comp (h0.fst'.prod h1.snd')))
    (h.comp (h0.snd'.prod h1.fst'))) (h.comp (h0.snd'.prod h1.snd'))

private def checkPrepared (data : List (Prepared q)) : Bool :=
  data.all validLocal &&
    (List.range data.length).all fun i => (List.range data.length).all fun j =>
      decide (i = j) || bubblesDisjoint (data.getD i (([],[]),false)) (data.getD j (([],[]),false))

private theorem checkPrepared_polyTime (q : ℕ) :
    ComputableInPolyTime (checkPrepared (q := q)) (encList (preparedEncoding q)) encBool := by
  let u := preparedEncoding q
  let e := encList u
  let p := encPair e encUnary
  have h := (fst e encUnary).comp (fst p encUnary)
  have hi := (snd e encUnary).comp (fst p encUnary)
  have hj := snd p encUnary
  have ha := listGetDWithInput h hi ((([],[]),false) : Prepared q)
  have hc := listGetDWithInput h hj ((([],[]),false) : Prepared q)
  have hlen := length_list u
  have hc' := (bubblesDisjoint_polyTime q).comp
    (encIn := encPair p encUnary) (encMid := encPair u u) (ha.prod hc)
  have hpair := bool_or' (hi.decide_eq' hj) hc'
  have hgrid := grid_polyTime hlen hlen (test := fun data i j => decide (i = j) ||
    bubblesDisjoint (data.getD i (([],[]),false)) (data.getD j (([],[]),false)))
    (hpair.of_enc_eq (fun _ => rfl))
  have hsingle := (validLocal_polyTime q).comp (encIn := encPair e u) (snd e u)
  have hall := allWithInput (encIn := e) (encA := u) (test := fun _ w => validLocal w) id'
    (hsingle.of_enc_eq (fun _ => rfl))
  exact (bool_and' hall hgrid).of_enc_eq (fun _ => rfl)

theorem valid_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : ℕ × List (BubbleData q) => valid x.1 x.2)
      (encPair encUnary (ruleEncoding q)) encBool := by
  let u := bubbleEncoding q
  let e := encPair encUnary (ruleEncoding q)
  have hl := (fst encUnary (ruleEncoding q)).comp (fst e u)
  have hp := (prepare_polyTime q).comp (encIn := encPair e u) (encMid := encPair encUnary u)
    (hl.prod (snd e u))
  have h := mapWithInput (encIn := e) (encA := u) (encB := preparedEncoding q)
    (f := fun x w => prepare x.1 w) (snd encUnary (ruleEncoding q))
    (hp.of_enc_eq (fun _ => rfl))
  have hc := (checkPrepared_polyTime q).comp (encIn := e) (encMid := encList (preparedEncoding q)) h
  exact hc.of_enc_eq (fun _ => rfl)

theorem rules_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (rules pad b t) encUnary (encList (ruleEncoding q)) := by
  let u := ruleEncoding q
  have htuples := (ExceptionalRecords.tuples_polyTime (bubbleEncoding q) (2*t)).comp
    (encIn := encUnary) (localUniform_polyTime q b t hq)
  have hl := (Machine.UniformParameters.gram_machine q b t).comp (fst encUnary u)
  have htest := (valid_polyTime q).comp (encIn := encPair encUnary u)
    (encMid := encPair encUnary u) (hl.prod (snd encUnary u))
  have h := filterWithInput (encIn := encUnary) (encA := u)
    (test := fun ℓ ws => valid (UniformParameters.gram q b t ℓ) ws) htuples
    (htest.of_enc_eq (fun _ => rfl))
  apply h.of_enc_eq
  intro ℓ
  congr 1
  simp only [rules,rulesAt,Function.comp_def,localUniform_eq]

theorem ruleCount_polyBounded (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    PolyBounded (fun l : ℕ => l) (fun l => (CatalogueEnumeration.rules q
      (UniformParameters.windowLength q l) b (UniformParameters.gram q b t l) (2*t) pad).length) := by
  simpa only [encUnary_apply,List.length_replicate] using
    (rules_polyTime pad b t hq).polyBounded_length.mono (fun l => by
      have h := length_le_length_encList (ruleEncoding q) (rules pad b t l)
      simpa only [rules_eq,List.length_map] using h)

#print axioms rules_eq
#print axioms rules_polyTime
#print axioms ruleCount_polyBounded

end DeletionCode.Explicit.Machine.OrderedCatalogue
