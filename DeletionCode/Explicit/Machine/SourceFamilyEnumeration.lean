import DeletionCode.Explicit.Machine.SourceBuckets
import DeletionCode.Explicit.FamilyEnumeration

/-! Enumerate the coded fresh patterns and deduplicate shapes in catalogue order. -/
namespace DeletionCode.Explicit.Machine.SourceFamilyEnumeration

open SourceFamilyMembers SourceLists BubbleFamilies
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open private shortWords patterns patternOfMarks shortWords_spec from DeletionCode.Explicit.FamilyEnumeration

variable {α : Type} {q : ℕ}

abbrev numbersEncoding := encList encUnary
abbrev tuplesEncoding := encList numbersEncoding
abbrev tuplesInputEncoding := encPair (encPair encUnary encUnary) encUnary

def prepend (base : ℕ) (xs : List (List ℕ)) : List (List ℕ) :=
  (List.range base).flatMap (fun a => xs.map (a::·))

def tuplesStep (args : ℕ × ℕ) (xs : List (List ℕ)) : List (List ℕ) :=
  (prepend args.1 xs).take args.2

def tuples (base cap count : ℕ) : List (List ℕ) :=
  (tuplesStep (base,cap))^[count] [[]]

private theorem prepend_eq (base count : ℕ) :
    prepend base ((wordsOfLength base count).map (List.map Fin.val)) =
      (wordsOfLength base (count+1)).map (List.map Fin.val) := by
  unfold prepend
  change _ = ((List.finRange base).flatMap (fun a => (wordsOfLength base count).map (a::·))).map (List.map Fin.val)
  rw [show List.range base = (List.finRange base).map Fin.val by simp,List.flatMap_map,List.map_flatMap]
  simp [List.map_map,Function.comp_def]

theorem tuples_eq (base cap count : ℕ) (hc : 1 ≤ cap) (hcount : base^count ≤ cap) :
    tuples base cap count = (wordsOfLength base count).map (List.map Fin.val) := by
  have hb (i : ℕ) (hi : i ≤ count) : base^i ≤ cap := by
    by_cases h : base = 0
    · subst base
      cases i <;> simp [hc]
    · exact (Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr h) hi).trans hcount
  unfold tuples
  have go (i : ℕ) (hi : i ≤ count) :
      (tuplesStep (base,cap))^[i] ([[]] : List (List ℕ)) =
        (wordsOfLength base i).map (List.map Fin.val) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply',ih (by omega)]
      unfold tuplesStep
      dsimp only
      rw [prepend_eq,List.take_of_length_le]
      simpa [length_wordsOfLength] using hb (i+1) hi
  exact go count le_rfl

private theorem prepend_polyTime :
    ComputableInPolyTime (fun x : ℕ × List (List ℕ) => prepend x.1 x.2)
      (encPair encUnary tuplesEncoding) tuplesEncoding := by
  let e := encPair encUnary tuplesEncoding
  let a := encPair e encUnary
  let p := encPair a numbersEncoding
  have hx := (snd encUnary tuplesEncoding).comp (fst e encUnary)
  have hi := (snd e encUnary).comp (fst a numbersEncoding)
  have hf := mapWithInput (encIn := a) (encA := numbersEncoding) (encB := numbersEncoding)
    (f := fun x w => x.2::w) hx (cons' hi (snd a numbersEncoding))
  exact flatMapWithInput (encIn := e) (encA := encUnary) (encB := numbersEncoding)
    (f := fun x i => x.2.map (i::·)) (unary_range' (fst encUnary tuplesEncoding)) hf

private theorem tuplesStep_polyTime :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × List (List ℕ) => tuplesStep x.1 x.2)
      (encPair (encPair encUnary encUnary) tuplesEncoding) tuplesEncoding := by
  have hf := fst (encPair encUnary encUnary) tuplesEncoding
  have h := prepend_polyTime.comp (hf.fst'.prod (snd (encPair encUnary encUnary) tuplesEncoding))
  exact listTakeWithInput h hf.snd'

theorem tuples_polyTime :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × ℕ => tuples x.1.1 x.1.2 x.2)
      tuplesInputEncoding tuplesEncoding := by
  let n := encPair encUnary encUnary
  let e := tuplesInputEncoding
  have hx := fst n encUnary
  have hy := snd n encUnary
  let inv (x : (ℕ × ℕ) × ℕ) (i : ℕ) (xs : List (List ℕ)) :=
    xs.length ≤ x.1.2+1 ∧ ∀ w ∈ xs, w.length ≤ i ∧ ∀ d ∈ w, d ≤ x.1.1
  have hc : PolyBounded (fun x : (ℕ × ℕ) × ℕ => (e x).length) (fun x => x.1.2+1) := by
    simpa only [encUnary_apply,List.length_replicate] using (unary_add' hx.snd' (const 1)).polyBounded_length
  have hb : PolyBounded (fun x : (ℕ × ℕ) × ℕ => (e x).length) (fun x => 2*x.1.1+1) := by
    simpa only [encUnary_apply,List.length_replicate] using
      (unary_add' (unary_mul' (const 2) hx.fst') (const 1)).polyBounded_length
  have ht : PolyBounded (fun x : (ℕ × ℕ) × ℕ => (e x).length) (fun x => x.2) := by
    simpa only [encUnary_apply,List.length_replicate] using hy.polyBounded_length
  have hs := hc.mul (((PolyBounded.const 2).mul (ht.mul hb)).add (PolyBounded.const 1))
  refine (iterateWith_spec (step := tuplesStep) hx hy (const [[]]) tuplesStep_polyTime inv
    (fun _ => by simp [inv]) ?_ hs ?_).1
  · intro x i xs _ h
    refine ⟨(List.length_take_le ..).trans (Nat.le_succ _),?_⟩
    intro w hw
    obtain ⟨a,ha,hw⟩ := List.mem_flatMap.mp (List.mem_of_mem_take hw)
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    have ha := (List.mem_range.mp ha).le
    refine ⟨by simpa using Nat.succ_le_succ (h.2 _ hv).1,?_⟩
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact ha
    · exact (h.2 _ hv).2 _ hk
  · intro x i xs hi h
    apply (length_encList_le numbersEncoding xs (b := x.2*(2*x.1.1+1)) ?_).trans
      (Nat.mul_le_mul_right _ h.1)
    intro w hw
    exact (length_encList_le encUnary w (b := x.1.1) (fun d hd => by
      simpa [encUnary_apply] using (h.2 _ hw).2 _ hd)).trans (Nat.mul_le_mul_right _ ((h.2 _ hw).1.trans hi))

def markPattern (pad : Fin q) (n : ℕ) (marks : List ℕ) : List (Option (Fin q)) :=
  (List.range n).map (fun i => (marks.find? (fun a => decide (a/q = i))).map
    (fun a => (List.finRange q).getD (a%q) pad))

theorem markPattern_eq (pad : Fin q) (n : ℕ) (marks : QWord (n*q)) :
    markPattern pad n (marks.map Fin.val) = patternOfMarks q n marks := by
  unfold markPattern patternOfMarks
  rw [show List.range n = (List.finRange n).map Fin.val by simp,List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_def,List.find?_map]
  have hf (a : Fin (n*q)) : decide (a.val/q = i.val) =
      ((finProdFinEquiv.symm a).1 == i) := by
    apply Bool.eq_iff_iff.mpr
    simp [Fin.ext_iff,finProdFinEquiv,Fin.divNat]
  simp only [hf,Option.map_map,Function.comp_def]
  cases marks.find? (fun a => (finProdFinEquiv.symm a).1 == i) with
  | none => rfl
  | some a =>
    simp only [Option.map_some,Option.some.injEq]
    have hq : 0 < q := Nat.zero_lt_of_lt pad.isLt
    have hl : a.val%q < (List.finRange q).length := by simpa using Nat.mod_lt a.val hq
    rw [List.getD_eq_getElem _ _ hl,List.getElem_finRange]
    rfl

def patternList (pad : Fin q) (cap n Λ : ℕ) : List (List (Option (Fin q))) :=
  (List.range (Λ+1)).flatMap (fun k => (tuples (n*q) cap k).map (markPattern pad n))

theorem patternList_eq (pad : Fin q) (cap n Λ : ℕ) (hc : 1 ≤ cap)
    (hb : ∀ k ≤ Λ, (n*q)^k ≤ cap) :
    patternList pad cap n Λ = patterns q n Λ := by
  unfold patternList patterns
  apply List.flatMap_congr
  intro k hk
  rw [tuples_eq _ _ _ hc (hb k (Nat.le_of_lt_succ (List.mem_range.mp hk))),List.map_map]
  exact List.map_congr_left (fun a _ => markPattern_eq pad n a)

abbrev marksInputEncoding := encPair encUnary numbersEncoding

theorem markPattern_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : ℕ × List ℕ => markPattern pad x.1 x.2)
      marksInputEncoding (patternEncoding q) := by
  let e := marksInputEncoding
  let a := encPair e encUnary
  let p := encPair a encUnary
  let c := alphabetEncoding q
  have hw := (snd encUnary numbersEncoding).comp (fst e encUnary)
  have hz := (snd e encUnary).comp (fst a encUnary)
  have hv := snd a encUnary
  have ht := (unary_div' hv (const q)).decide_eq' hz
  have hf := findWithInput (encIn := a) (encA := encUnary)
    (test := fun x a => decide (a/q = x.2)) hw ht
  have hsym := listGetDWithInput (const (encOut := encList c) (List.finRange q))
    (unary_mod' (snd a encUnary) (const q)) pad
  have h := optionMapWithInput (encA := a) (encB := encUnary) (encC := c)
    (f := fun _ k => (List.finRange q).getD (k%q) pad) hf hsym
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := encOption c)
    (f := fun x i => (x.2.find? (fun a => decide (a/q = i))).map
      (fun a => (List.finRange q).getD (a%q) pad)) (unary_range' (fst encUnary numbersEncoding)) h

abbrev patternInputEncoding := encPair (encPair encUnary encUnary) encUnary

theorem patternList_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × ℕ => patternList pad x.1.1 x.1.2 x.2)
      patternInputEncoding (encList (patternEncoding q)) := by
  let e := patternInputEncoding
  let a := encPair e encUnary
  let p := encPair a numbersEncoding
  have hx := fst (encPair encUnary encUnary) encUnary
  have hy := snd (encPair encUnary encUnary) encUnary
  have hz := hx.comp (fst e encUnary)
  have hi := snd e encUnary
  have hbase := unary_mul' hz.snd' (const q)
  have ht := tuples_polyTime.comp ((hbase.prod hz.fst').prod hi)
  have hw := (markPattern_polyTime pad).comp ((hz.snd'.comp (fst a numbersEncoding)).prod (snd a numbersEncoding))
  have h := mapWithInput (encIn := a) (encA := numbersEncoding) (encB := patternEncoding q)
    (f := fun x m => markPattern pad x.1.1.2 m) ht hw
  exact flatMapWithInput (encIn := e) (encA := encUnary) (encB := patternEncoding q)
    (f := fun x k => (tuples (x.1.2*q) x.1.1 k).map (markPattern pad x.1.2))
    (unary_range' (unary_add' hy (const 1))) h

def flankShapes (pad : Fin q) (b cap items left right : ℕ) : List (Shape q) :=
  (shortWords q b).flatMap fun u =>
    (shortWords q b).flatMap fun v =>
      (patternList pad cap (left+u.length+right) items).map (fun p => ⟨left,right,u,v,p⟩)

def allShapes (pad : Fin q) (b cap L Λ : ℕ) : List (Shape q) :=
  (List.range L).flatMap fun a =>
    (List.range L).flatMap fun r =>
      flankShapes pad b cap Λ a r

theorem allShapes_eq (pad : Fin q) (b cap L Λ : ℕ) (hc : 1 ≤ cap)
    (hb : (3*q*(L+b+1))^Λ ≤ cap) :
    allShapes pad b cap L Λ = BubbleFamilies.allShapes q L b Λ := by
  unfold allShapes BubbleFamilies.allShapes
  apply List.flatMap_congr
  intro a ha
  apply List.flatMap_congr
  intro r hr
  unfold flankShapes
  apply List.flatMap_congr
  intro u hu
  apply List.flatMap_congr
  intro v _
  rw [patternList_eq _ _ _ _ hc]
  intro k hk
  have hq : 0 < q := Nat.zero_lt_of_lt pad.isLt
  have ha := List.mem_range.mp ha
  have hr := List.mem_range.mp hr
  have hu := shortWords_spec.mp hu
  have hle : (a+u.length+r)*q ≤ 3*q*(L+b+1) := by
    calc
      _ ≤ (3*(L+b+1))*q := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  exact ((Nat.pow_le_pow_left hle _).trans (Nat.pow_le_pow_right (by positivity) hk)).trans hb

abbrev flankEncoding := encPair (encPair encUnary encUnary) (encPair encUnary encUnary)

theorem flankShapes_polyTime (pad : Fin q) (b : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × (ℕ × ℕ) => flankShapes pad b x.1.1 x.1.2 x.2.1 x.2.2)
      flankEncoding (encList (familyShapeEncoding q)) := by
  let w := wordEncoding q
  let e := flankEncoding
  let a := encPair e w
  let p := encPair a w
  let f := encPair p (patternEncoding q)
  let d := familyShapeEncoding q
  have he := (fst e w).comp (fst a w)
  have hx := (fst (encPair encUnary encUnary) (encPair encUnary encUnary)).comp he
  have hy := (snd (encPair encUnary encUnary) (encPair encUnary encUnary)).comp he
  have hu := (snd e w).comp (fst a w)
  have hv := snd a w
  have hw := (length_list (alphabetEncoding q)).comp hu
  have hn := unary_add' (unary_add' hy.fst' hw) hy.snd'
  have hpat := (patternList_polyTime pad).comp (encIn := p) ((hx.fst'.prod hn).prod hx.snd')
  have hp := fst p (patternEncoding q)
  have hs := familyShapeEncoding_mk_polyTime q (hy.fst'.comp hp) (hy.snd'.comp hp)
    (hu.comp hp) (hv.comp hp) (snd p (patternEncoding q))
  have hm := mapWithInput (encIn := p) (encA := patternEncoding q) (encB := d)
    (f := fun x mark => ⟨x.1.1.2.1,x.1.1.2.2,x.1.2,x.2,mark⟩) hpat hs
  have h := flatMapWithInput (encIn := a) (encA := w) (encB := d)
    (f := fun x v => (patternList pad x.1.1.1 (x.1.2.1+x.2.length+x.1.2.2) x.1.1.2).map
      (fun p => ⟨x.1.2.1,x.1.2.2,x.2,v,p⟩))
    (const (shortWords q b)) hm
  exact flatMapWithInput (encIn := e) (encA := w) (encB := d)
    (f := fun x u => (shortWords q b).flatMap (fun v =>
      (patternList pad x.1.1 (x.2.1+u.length+x.2.2) x.1.2).map
        (fun p => ⟨x.2.1,x.2.2,u,v,p⟩))) (const (shortWords q b)) h

abbrev shapesEncoding := encPair encUnary (encPair encUnary encUnary)

theorem allShapes_polyTime (pad : Fin q) (b : ℕ) :
    ComputableInPolyTime (fun x : ℕ × (ℕ × ℕ) => allShapes pad b x.1 x.2.1 x.2.2)
      shapesEncoding (encList (familyShapeEncoding q)) := by
  let e := shapesEncoding
  let f := encPair e encUnary
  let d := familyShapeEncoding q
  have hE := fst e encUnary
  have hi := snd e encUnary
  have hcap := (fst encUnary (encPair encUnary encUnary)).comp hE
  have hdata := (snd encUnary (encPair encUnary encUnary)).comp hE
  have hcfg := hcap.prod hdata.snd'
  have hn := unary_range' (snd encUnary (encPair encUnary encUnary)).fst'
  have hr := (flankShapes_polyTime pad b).comp
    ((hcfg.comp (fst f encUnary)).prod ((hi.comp (fst f encUnary)).prod (snd f encUnary)))
  have h := flatMapWithInput (encIn := f) (encA := encUnary) (encB := d)
    (f := fun x j => flankShapes pad b x.1.1 x.1.2.2 x.2 j) (hn.comp hE) hr
  exact flatMapWithInput (encIn := e) (encA := encUnary) (encB := d)
    (f := fun x i => (List.range x.2.1).flatMap (fun j => flankShapes pad b x.1 x.2.2 i j)) hn h

def uniformShapes (pad : Fin q) (b t ℓ : ℕ) : List (Shape q) :=
  allShapes pad b (ℓ+1) (UniformParameters.gram q b t ℓ) (UniformParameters.omittedLetters q b t ℓ)

theorem uniformShapes_eq (pad : Fin q) (b t ℓ : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : UniformParameters.minLength q b t ≤ ℓ) :
    uniformShapes pad b t ℓ = BubbleFamilies.allShapes q (UniformParameters.gram q b t ℓ) b
      (UniformParameters.omittedLetters q b t ℓ) := by
  let L := UniformParameters.gram q b t ℓ
  let Λ := UniformParameters.omittedLetters q b t ℓ
  unfold uniformShapes
  apply allShapes_eq _ _ _ _ _ (by omega)
  have hc := (UniformParameters.enumerationBounds hq hb ht hstart).2.1
  have hv : 1 ≤ UniformParameters.families q b t ℓ := by
    unfold UniformParameters.families UniformParameters.familyBound
    have ho : 0 < q := by omega
    exact Nat.succ_le_of_lt (by positivity)
  have hpow : UniformParameters.families q b t ℓ ≤ (UniformParameters.families q b t ℓ)^8 := by
    simpa only [pow_one] using (Nat.pow_le_pow_right hv (show 1 ≤ 8 by decide))
  have he := hpow.trans hc
  have hmul : (3*q*(L+b+1))^Λ ≤ UniformParameters.families q b t ℓ := by
    change _ ≤ (12*(L+b+1)^3*q^(2*b)*(Λ+1))*_
    have hq' : 0 < q := by omega
    exact Nat.le_mul_of_pos_left _ (by positivity)
  exact hmul.trans (he.trans (Nat.le_succ _))

set_option maxHeartbeats 800000 in
theorem uniformShapes_polyTime (pad : Fin q) (b t : ℕ) :
    ComputableInPolyTime (uniformShapes pad b t) encUnary (encList (familyShapeEncoding q)) := by
  have h := (allShapes_polyTime pad b).comp
    ((unary_add' (id' (encIn := encUnary)) (const 1)).prod
      ((Machine.UniformParameters.gram_machine q b t).prod (Machine.UniformParameters.omitted_machine q b t)))
  exact h.of_enc_eq (fun _ => rfl)

def dedupStep [DecidableEq α] (acc : List α) (v : α) : List α :=
  if v ∈ acc then acc else v::acc

def dedup [DecidableEq α] (xs : List α) : List α := xs.reverse.foldl dedupStep []

theorem dedup_eq [DecidableEq α] (xs : List α) : dedup xs = xs.dedup := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    unfold dedup at ih ⊢
    rw [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,ih,List.dedup_cons]
    simp [dedupStep,List.mem_dedup]

theorem dedup_polyTime [DecidableEq α] (e : α ↪ List Bool) :
    ComputableInPolyTime (dedup (α := α)) (encList e) (encList e) := by
  let a := encList e
  let p := encPair a e
  have hx := fst a e
  have hy := snd a e
  have hmem := contains hx hy
  have hf := hmem.ite' hx (cons' hy hx)
  have hs : ComputableInPolyTime (fun x : List α × α => dedupStep x.1 x.2) p a :=
    hf.of_enc_eq (fun x => by simp [dedupStep,List.contains_iff_mem] <;> rfl)
  have h := foldlWith_of_bounded_growth (encA := e) (encL := a) (encB := a)
    (step := fun _ : Bool => dedupStep) (const false) (listReverse e) (const [])
    (hs.comp ((fst (encPair encBool a) e).snd'.prod (snd (encPair encBool a) e)))
    (growth := fun xs => 2*(a xs).length+1) (((PolyBounded.const 2).mul PolyBounded.self).add (PolyBounded.const 1))
    (fun xs acc v hv => by
      have hv' : v ∈ xs := by simpa only [List.mem_reverse] using hv
      have hp := length_le_encList_of_mem e hv'
      unfold dedupStep
      split
      · omega
      · simp only [a,encList_cons,List.length_append,length_frame]
        omega)
  exact h

abbrev familyTableEncoding (q : ℕ) := encList (encPair (familyShapeEncoding q) Ternary.rowsEncoding)

def families (pad : Fin q) (b t ℓ : ℕ) : List (Shape q × Ternary.Rows) :=
  (dedup (uniformShapes pad b t ℓ)).filterMap fun s =>
    let r := SourceBuckets.rows pad b t ℓ s
    if r.isEmpty then none else some (s,r)

theorem familyRows_toFinset (pad : Fin q) (b t ℓ : ℕ) (hq : 2 ≤ q) (s : Shape q) :
    (SourceBuckets.rows pad b t ℓ s).toFinset =
      (s.vectors (UniformParameters.windowLength q ℓ) b (UniformParameters.gram q b t ℓ)
        (UniformParameters.omittedLetters q b t ℓ) pad).image List.ofFn := by
  rw [SourceBuckets.rows_eq pad b t ℓ hq,Shape.vectors]
  ext r
  simp only [List.mem_toFinset,Finset.mem_image,List.mem_map]
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨BubbleFamilies.vector pad x.2,⟨x,hx,rfl⟩,rfl⟩
  · rintro ⟨v,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨x,hx,rfl⟩

theorem families_eq (pad : Fin q) (b t ℓ : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : UniformParameters.minLength q b t ≤ ℓ) :
    (families pad b t ℓ).map (fun p => (p.1,p.2.toFinset)) =
      (BubbleFamilies.families q (UniformParameters.windowLength q ℓ) b (UniformParameters.gram q b t ℓ)
        (UniformParameters.omittedLetters q b t ℓ) pad).map (fun p => (p.1,p.2.image List.ofFn)) := by
  unfold families BubbleFamilies.families
  rw [uniformShapes_eq pad b t ℓ hq hb ht hstart,dedup_eq,List.map_filterMap,List.map_filterMap]
  apply List.filterMap_congr
  intro s _
  have hset := familyRows_toFinset pad b t ℓ hq s
  have hm : (s.vectors (UniformParameters.windowLength q ℓ) b (UniformParameters.gram q b t ℓ)
      (UniformParameters.omittedLetters q b t ℓ) pad).Nonempty ↔
      (SourceBuckets.rows pad b t ℓ s).isEmpty = false := by
    rw [← Finset.image_nonempty (f := List.ofFn),← hset]
    simp
  by_cases h : (SourceBuckets.rows pad b t ℓ s).isEmpty = true
  · simp [h,show ¬ (SourceBuckets.rows pad b t ℓ s).isEmpty = false by simp [h],hm]
  · have h' : (SourceBuckets.rows pad b t ℓ s).isEmpty = false := Bool.eq_false_iff.mpr h
    simp [h,h',hm,hset]

theorem families_length (pad : Fin q) (b t ℓ : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : UniformParameters.minLength q b t ≤ ℓ) :
    (families pad b t ℓ).length ≤ UniformParameters.families q b t ℓ := by
  have he := congrArg List.length (families_eq pad b t ℓ hq hb ht hstart)
  simp only [List.length_map] at he
  rw [he]
  exact BubbleFamilies.families_count _ _ _ _ _ pad hq

theorem families_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (families pad b t) encUnary (familyTableEncoding q) := by
  let s := familyShapeEncoding q
  let a := encPair encUnary s
  let r := Ternary.rowsEncoding
  let p := encPair s r
  have hd := (dedup_polyTime s).comp (uniformShapes_polyTime pad b t)
  have h := SourceBuckets.rows_polyTime pad b t hq
  have hm := (length_list Ternary.rowEncoding).comp h
  have hr := (unary_lt' (const 0) hm).ite'
    (cons' ((snd encUnary s).prod h) (const [])) (const [])
  have hf := flatMapWithInput (encIn := encUnary) (encA := s) (encB := p)
    (f := fun x sh => let r := SourceBuckets.rows pad b t x sh
      if 0 < r.length then [(sh,r)] else []) hd (hr.of_enc_eq (fun _ => by simp [Function.comp_def,p] <;> rfl))
  exact hf.of_enc_eq (fun x => by
    unfold families
    apply congrArg (familyTableEncoding q)
    simp only [Function.comp_def]
    induction dedup (uniformShapes pad b t x) with
    | nil => rfl
    | cons sh xs ih =>
      simp only [List.flatMap_cons,List.filterMap_cons,← ih]
      cases h : SourceBuckets.rows pad b t x sh <;> simp [h])

#print axioms families_eq
#print axioms families_length
#print axioms families_polyTime

#print axioms uniformShapes_eq
#print axioms uniformShapes_polyTime

#print axioms tuples_eq
#print axioms tuples_polyTime
#print axioms patternList_eq

end DeletionCode.Explicit.Machine.SourceFamilyEnumeration
