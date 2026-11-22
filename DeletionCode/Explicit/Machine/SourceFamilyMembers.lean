import DeletionCode.Explicit.Machine.SourceRuleRows
import DeletionCode.Explicit.Machine.SourceGrammar
import DeletionCode.Explicit.FamilyBuckets

/-! Bounded enumeration of the ordered assignments and bubbles in a shape family. -/
namespace DeletionCode.Explicit.Machine.SourceFamilyMembers

open BubbleFamilies Borrowed SourceLists OrderedCatalogue
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {q K b L t Λ : ℕ}

abbrev alphabetEncoding := ExceptionalRecords.letterEncoding
abbrev patternEncoding (q : ℕ) := encList (encOption (alphabetEncoding q))

enc_structure familyShapeEncoding (q : ℕ) : Shape q where
  left : encUnary, right : encUnary, removed : (wordEncoding q), replacement : (wordEncoding q),
  fresh : (patternEncoding q)

abbrev memberDataEncoding (q : ℕ) := encPair (wordEncoding q) (bubbleEncoding q)
abbrev membersEncoding (q : ℕ) := encList (memberDataEncoding q)

def originals (s : List (Option (Fin q))) : ℕ := (s.filter Option.isNone).length

def filledAt (pad : Fin q) (s : List (Option (Fin q))) (w : QWord q) (i : ℕ) : Fin q :=
  (s.getD i none).getD (w.getD (originals (s.take i)) pad)

def filled (pad : Fin q) (s : List (Option (Fin q))) (w : QWord q) : QWord q :=
  (List.range s.length).map (filledAt pad s w)

def fill (pad : Fin q) (s : List (Option (Fin q))) (w : QWord q) : Option (QWord q) :=
  if originals s = w.length then some (filled pad s w) else none

private theorem filled_cons_some (pad a : Fin q) (s : List (Option (Fin q))) (w : QWord q) :
    filled pad (some a::s) w = a :: filled pad s w := by
  unfold filled
  rw [List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map]
  congr 1

private theorem filled_cons_none (pad a : Fin q) (s : List (Option (Fin q))) (w : QWord q) :
    filled pad (none::s) (a::w) = a :: filled pad s w := by
  unfold filled
  rw [List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map]
  congr 1

theorem fill_eq (pad : Fin q) (s : List (Option (Fin q))) (w : QWord q) :
    fill pad s w = BubbleFamilies.fill s w := by
  induction s generalizing w with
  | nil => cases w <;> simp [fill,BubbleFamilies.fill,originals,filled]
  | cons v s ih =>
    cases v with
    | none =>
      cases w with
      | nil => simp [fill,BubbleFamilies.fill,originals]
      | cons a w =>
        simp only [fill,BubbleFamilies.fill,originals,List.filter_cons,Option.isNone_none,↓reduceIte,
          List.length_cons,Nat.add_right_cancel_iff,filled_cons_none,← ih]
        split <;> simp_all
    | some a =>
      simp only [fill,BubbleFamilies.fill,originals,List.filter_cons,Option.isNone_some,Bool.false_eq_true,
        ↓reduceIte,filled_cons_some,← ih]
      split <;> simp_all

def localBubble (K b L a : ℕ) (u v neg : QWord q) : Option (BubbleData q) :=
  let w := ((neg.take a,neg.drop (a+u.length)),(u,v))
  if localCheck K b L w && decide (side w false = neg) then some w else none

theorem local_eq (a : ℕ) (u v neg : QWord q) :
    localBubble K b L a u v neg = (BubbleFamilies.localWord K b L a u v neg).map bubbleData := by
  unfold localBubble BubbleFamilies.localWord
  let l := neg.take a
  let r := neg.drop (a+u.length)
  have hspec : localCheck K b L ((l,r),(u,v)) = true ↔
      u.length ≤ b ∧ v.length ≤ b ∧ u ≠ v ∧
      L-1-K-b ≤ l.length ∧ l.length ≤ L-1 ∧ L-1-K-b ≤ r.length ∧ r.length ≤ L-1 := by
    simp only [localCheck,Bool.and_eq_true_iff,decide_eq_true_eq]
    tauto
  by_cases hs : u.length ≤ b ∧ v.length ≤ b ∧ u ≠ v ∧
      L-1-K-b ≤ l.length ∧ l.length ≤ L-1 ∧ L-1-K-b ≤ r.length ∧ r.length ≤ L-1
  · have hc := hspec.mpr hs
    simp only [show localCheck K b L ((neg.take a,neg.drop (a+u.length)),(u,v)) = true from hc,
      Bool.true_and,decide_eq_true_eq,side,↓reduceIte,Bool.false_eq_true]
    rw [dite_eq_left hs]
    simp [l,r,BubbleWord.negativeWord,bubbleData,Option.map_ite]
  · have hc : localCheck K b L ((neg.take a,neg.drop (a+u.length)),(u,v)) = false :=
      Bool.eq_false_iff.mpr (fun he => hs (hspec.mp he))
    rw [dite_eq_right hs]
    simp only [hc,Bool.false_and,Bool.false_eq_true,↓reduceIte,Option.map_none]

def member (pad : Fin q) (K b L Λ : ℕ) (s : Shape q) (w : QWord q) : Option (BubbleData q) :=
  if s.freshCount ≤ Λ ∧ s.fresh.length = s.left+s.removed.length+s.right then do
    let neg ← fill pad s.fresh w
    let p ← localBubble K b L s.left s.removed s.replacement neg
    if OrderedCatalogue.valid L [p] then some p else none
  else none

theorem member_eq (pad : Fin q) (s : Shape q) (w : QWord q) :
    member pad K b L Λ s w = (s.member K b L Λ pad w).map bubbleData := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  unfold member Shape.member
  rw [fill_eq pad]
  split
  · cases BubbleFamilies.fill s.fresh w with
    | none => rfl
    | some neg =>
      simp only [Option.bind_some,bind,Option.bind,local_eq]
      cases BubbleFamilies.localWord K b L s.left s.removed s.replacement neg with
      | none => rfl
      | some p =>
        have h := OrderedCatalogue.valid_eq pad (fun _ : Fin 1 => p)
        rw [List.ofFn_succ,List.ofFn_zero] at h
        simp only [h,Option.map_some,Option.map_ite,Option.map_none]
  · rfl

def assignments (pad : Fin q) (K b L Λ : ℕ) (s : Shape q) (words : List (QWord q)) :
    List (QWord q × BubbleData q) :=
  words.filterMap (fun w => (member pad K b L Λ s w).map (fun p => (w,p)))

theorem assignments_eq (pad : Fin q) (s : Shape q) :
    assignments pad K b L Λ s (wordsOfLength q s.originalCount) =
      (s.members K b L Λ pad).map (fun p => (p.1,bubbleData p.2)) := by
  unfold assignments Shape.members
  rw [List.map_filterMap]
  apply List.filterMap_congr
  intro w _
  simp [member_eq,Option.map_map,Function.comp_def]

private theorem member_length_le (pad : Fin q) (s : Shape q)
    {w : QWord q × BubbleWord (Fin q) K b L} (h : w ∈ s.members K b L Λ pad) :
    s.originalCount ≤ 2*L+b := by
  have hh := ((mem_members s K b L Λ pad w.1 w.2).mp h).2
  have he := fill_length (member_data s K b L Λ pad hh).1
  have hpat := shapeCounts_add s
  have hleft := w.2.left_upper
  have hright := w.2.right_upper
  have hrem := w.2.removed_bound
  simp only [BubbleWord.negativeWord,List.length_append] at he
  omega

def members (pad : Fin q) (b t ℓ : ℕ) (s : Shape q) : List (QWord q × BubbleData q) :=
  let L := UniformParameters.gram q b t ℓ
  if s.originalCount ≤ 2*L+b then
    assignments pad (UniformParameters.windowLength q ℓ) b L
      (UniformParameters.omittedLetters q b t ℓ) s (wordsOfLength q s.originalCount)
  else []

theorem members_eq (pad : Fin q) (b t ℓ : ℕ) (s : Shape q) :
    members pad b t ℓ s =
      (s.members (UniformParameters.windowLength q ℓ) b (UniformParameters.gram q b t ℓ)
        (UniformParameters.omittedLetters q b t ℓ) pad).map (fun p => (p.1,bubbleData p.2)) := by
  dsimp only [members]
  split
  · exact assignments_eq pad s
  · rename_i nh
    symm
    simp only [List.map_eq_nil_iff]
    by_contra n
    obtain ⟨w,hw⟩ := List.exists_mem_of_ne_nil _ n
    exact nh (member_length_le pad s hw)

theorem members_length_le (pad : Fin q) (b t ℓ : ℕ) (s : Shape q) :
    (members pad b t ℓ s).length ≤ q^(2*UniformParameters.gram q b t ℓ+b) := by
  dsimp only [members]
  split
  · apply (List.length_filterMap_le ..).trans
    rw [length_wordsOfLength]
    by_cases hq : q = 0
    · subst q
      exact Fin.elim0 pad
    · exact Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr hq) (by assumption)
  · simp

theorem count_polyTime (q : ℕ) (fresh : Bool) :
    ComputableInPolyTime (fun l : List (Option (Fin q)) =>
      (l.filter (fun a => if fresh then a.isSome else a.isNone)).length) (patternEncoding q) encUnary := by
  let a := encOption (alphabetEncoding q)
  let e := patternEncoding q
  have h := optionIsSome (snd e a)
  have hp := (const (encOut := encBool) fresh).ite' h (bool_not.comp h)
  have hf := filterWithInput (encIn := e) (encA := a) (test := fun _ a => if fresh then a.isSome else a.isNone)
    id' (hp.of_enc_eq (fun x => by rcases x with ⟨xs,v⟩; cases fresh <;> cases v <;> rfl))
  exact (length_list a).comp hf

theorem originalCount_polyTime (q : ℕ) :
    ComputableInPolyTime (Shape.originalCount (q := q)) (familyShapeEncoding q) encUnary :=
  (count_polyTime q false).comp (familyShapeEncoding_fresh_polyTime q id')

abbrev fillEncoding (q : ℕ) := encPair (patternEncoding q) (wordEncoding q)

theorem fill_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : List (Option (Fin q)) × QWord q => fill pad x.1 x.2)
      (fillEncoding q) (encOption (wordEncoding q)) := by
  let a := alphabetEncoding q
  let p := patternEncoding q
  let w := wordEncoding q
  let e := fillEncoding q
  let d := encPair e encUnary
  have hp := fst p w
  have hw := snd p w
  have hi := snd e encUnary
  have hx := fst e encUnary
  have hs := hp.comp hx
  have ha := listGetDWithInput hs hi (none : Option (Fin q))
  have hn := (count_polyTime q false).comp (listTakeWithInput hs hi)
  have hd := listGetDWithInput (hw.comp hx) hn pad
  have hf := optionElimWithInput (encA := d) (encB := a) (encC := a) (body := fun _ v => v) ha hd (snd d a)
  have hv := mapWithInput (encIn := e) (encA := encUnary) (encB := a)
    (f := fun x i => filledAt pad x.1 x.2 i) (unary_range' ((length_list (encOption a)).comp hp))
    (hf.of_enc_eq (fun x => by
      simp only [filledAt,Function.comp_def,originals,Bool.false_eq_true,↓reduceIte]
      cases x.1.1.getD x.2 none <;> rfl))
  have hlen := ((count_polyTime q false).comp hp).decide_eq' ((length_list a).comp hw)
  exact (hlen.ite' ((optionSome w).comp hv) (const none)).of_enc_eq (fun _ => by simp [fill,originals,Function.comp_def,w] <;> rfl)

abbrev localInputEncoding (q : ℕ) :=
  encPair (encPair encUnary encUnary) (encPair encUnary
    (encPair (OrderedCatalogue.wordPairEncoding q) (wordEncoding q)))

theorem localBubble_polyTime (q b : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × (ℕ × ((QWord q × QWord q) × QWord q)) =>
        localBubble x.1.1 b x.1.2 x.2.1 x.2.2.1.1 x.2.2.1.2 x.2.2.2)
      (localInputEncoding q) (encOption (bubbleEncoding q)) := by
  let w := wordEncoding q
  let ws := OrderedCatalogue.wordPairEncoding q
  let args := encPair encUnary (encPair ws w)
  let e := localInputEncoding q
  have hp := fst (encPair encUnary encUnary) args
  have hx := snd (encPair encUnary encUnary) args
  have hneg := hx.snd'.snd'
  have hrem := hx.snd'.fst'.fst'
  have hleft := listTakeWithInput hneg hx.fst'
  have hright := listDropWithInput hneg
    (unary_add' hx.fst' ((length_list (alphabetEncoding q)).comp hrem))
  have hb := (hleft.prod hright).prod hx.snd'.fst'
  have hc := (OrderedCatalogue.localCheck_polyTime q b).comp (hp.prod hb)
  have hs := ((side_polyTime q false).comp hb).decide_eq' hneg
  exact ((bool_and' hc hs).ite' ((optionSome (bubbleEncoding q)).comp hb) (const none)).of_enc_eq
    (fun _ => by simp [localBubble,Function.comp_def])

abbrev memberParamsEncoding := encPair encUnary (encPair encUnary encUnary)
abbrev memberInputEncoding (q : ℕ) :=
  encPair memberParamsEncoding (encPair (familyShapeEncoding q) (wordEncoding q))

theorem member_polyTime (pad : Fin q) (b : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × (ℕ × ℕ)) × (Shape q × QWord q) =>
        member pad x.1.1 b x.1.2.1 x.1.2.2 x.2.1 x.2.2)
      (memberInputEncoding q) (encOption (bubbleEncoding q)) := by
  let e := memberInputEncoding q
  let w := wordEncoding q
  let y := bubbleEncoding q
  let s := familyShapeEncoding q
  let a := encPair e w
  let v := encPair a y
  have hp := fst memberParamsEncoding (encPair s w)
  have hx := snd memberParamsEncoding (encPair s w)
  have hd := hx.fst'
  have hfresh := familyShapeEncoding_fresh_polyTime q hd
  have hleft := familyShapeEncoding_left_polyTime q hd
  have hright := familyShapeEncoding_right_polyTime q hd
  have hu := familyShapeEncoding_removed_polyTime q hd
  have hv := familyShapeEncoding_replacement_polyTime q hd
  have hL := hp.snd'.fst'
  have hK := hp.fst'
  have hΛ := hp.snd'.snd'
  have hcounts := unary_le' ((count_polyTime q true).comp hfresh) hΛ
  have hlen := (length_list (encOption (alphabetEncoding q))).comp hfresh
  have hn := unary_add' (unary_add' hleft ((length_list (alphabetEncoding q)).comp hu)) hright
  have htest := bool_and' hcounts (hlen.decide_eq' hn)
  have hfill := (fill_polyTime pad).comp (hfresh.prod hx.snd')
  have hf := fst e w
  have hneg := snd e w
  have hloc := (localBubble_polyTime q b).comp (encIn := a) (((hK.prod hL).comp hf).prod
    ((hleft.comp hf).prod (((hu.prod hv).comp hf).prod hneg)))
  have hsh := snd a y
  have hgr := (hL.comp hf).comp (fst a y)
  have hvalid := (OrderedCatalogue.valid_polyTime q).comp (encIn := v) (hgr.prod (cons' hsh (const [])))
  have hpass := hvalid.ite' ((optionSome y).comp hsh) (const none)
  have hafter := optionBindWithInput (ea := a) (eb := y) (ec := y)
    (f := fun x p => if OrderedCatalogue.valid x.1.1.2.1 [p] then some p else none)
    (hloc.of_enc_eq (fun _ => rfl)) (hpass.of_enc_eq (fun _ => rfl))
  have hr := optionBindWithInput (ea := e) (eb := w) (ec := y)
    (f := fun x neg => (localBubble x.1.1 b x.1.2.1 x.2.1.left x.2.1.removed x.2.1.replacement neg).bind
      (fun p => if OrderedCatalogue.valid x.1.2.1 [p] then some p else none))
    hfill hafter
  exact (htest.ite' hr (const none)).of_enc_eq
    (fun _ => by simp [member,Shape.freshCount,Function.comp_def,Bool.and_eq_true_iff,bind,Option.bind] <;> rfl)

abbrev uniformInputEncoding (q : ℕ) := encPair encUnary (familyShapeEncoding q)

theorem members_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : ℕ × Shape q => members pad b t x.1 x.2)
      (uniformInputEncoding q) (membersEncoding q) := by
  let e := uniformInputEncoding q
  let s := familyShapeEncoding q
  let w := wordEncoding q
  let m := memberDataEncoding q
  let a := encPair e w
  let p := encPair a (bubbleEncoding q)
  have hl := fst encUnary s
  have hS := snd encUnary s
  have hL := (Machine.UniformParameters.gram_machine q b t).comp hl
  have hK := (Machine.UniformParameters.window_machine q).comp hl
  have hΛ := (Machine.UniformParameters.omitted_machine q b t).comp hl
  have hO := (originalCount_polyTime q).comp hS
  have hcap := unary_add' (unary_mul' (const 2) hL) (const b)
  have hm := unary_min' hO hcap
  have hwidth := ((SourceHashChoice.width_polyTime q b t hq).comp hl).polyBounded_length
  have hb : PolyBounded (fun x : ℕ × Shape q => (e x).length)
      (fun x => q ^ min x.2.originalCount (2*UniformParameters.gram q b t x.1+b)) := by
    apply ((PolyBounded.const (q^b)).mul (hwidth.pow 2)).mono
    intro x
    simp only [SourceHashChoice.width,Function.comp_def,encUnary_apply,List.length_replicate]
    exact (Nat.pow_le_pow_right (by omega) (Nat.min_le_right _ _)).trans_eq (by
      rw [pow_add,Nat.mul_comm 2,pow_mul,mul_comm])
  have hwords := wordsOfLength_polyTime hq hm hb
  have hp := ((hK.prod (hL.prod hΛ)).comp (fst e w)).prod ((hS.comp (fst e w)).prod (snd e w))
  have hf := (member_polyTime pad b).comp (encIn := a) hp
  have hs := ((snd e w).comp (fst a (bubbleEncoding q))).prod (snd a (bubbleEncoding q))
  have hpair := optionMapWithInput (encA := a) (encB := bubbleEncoding q) (encC := m)
    (f := fun x p => (x.2,p)) (hf.of_enc_eq (fun _ => rfl)) hs
  have ho := (optionToList_polyTime m).comp hpair
  have h := flatMapWithInput (encIn := e) (encA := w) (encB := m)
    (f := fun x v => ((member pad (UniformParameters.windowLength q x.1) b
      (UniformParameters.gram q b t x.1) (UniformParameters.omittedLetters q b t x.1)
      x.2 v).map (fun p => (v,p))).toList) hwords ho
  exact ((unary_le' hO hcap).ite' h (const [])).of_enc_eq (fun x => by
    have he (f : QWord q → Option (QWord q × BubbleData q)) (xs : List (QWord q)) :
        xs.flatMap (fun x => (f x).toList) = xs.filterMap f := by
      induction xs with
      | nil => rfl
      | cons x xs ih => cases hh : f x <;> simp [hh,ih]
    unfold members assignments
    simp only [Function.comp_def,decide_eq_true_eq,he]
    split
    · rename_i h
      rw [Nat.min_eq_left h]
    · rfl)

#print axioms fill_polyTime
#print axioms localBubble_polyTime
#print axioms member_polyTime
#print axioms members_polyTime
#print axioms fill_eq
#print axioms local_eq
#print axioms member_eq
#print axioms members_eq
#print axioms members_length_le

end DeletionCode.Explicit.Machine.SourceFamilyMembers
