import DeletionCode.Explicit.AffineSolution
import DeletionCode.Explicit.Machine.TernaryProbability
import DeletionCode.Explicit.Machine.CataloguePrefix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import Batteries.Tactic.OpenPrivate

/-! The last-coordinate-first affine solver on explicitly encoded rows. -/
namespace DeletionCode.Explicit.Machine.CanonicalAffine

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open FieldHash Ternary CataloguePrefix
open private feasible assign choices from DeletionCode.Explicit.AffineSolution

variable {m n : ℕ}

abbrev FeasibleInput := AffineInput × PartialRow
abbrev feasibleEncoding := encPair affineEncoding partialRowEncoding

def targetPart (m : ℕ) (y : Row) : Row :=
  (List.range m).map (fun i => y.getD i 0)

def jointAffine (x : FeasibleInput) : AffineInput :=
  let P := joint (x.1.1,x.2)
  (P.1,targetPart x.1.1.2.length x.1.2 ++ P.2.drop x.1.1.2.length)

def isFeasible (x : FeasibleInput) : Bool :=
  let p := jointAffine x
  decide (rank (augmented p) = rank p.1)

theorem jointAffine_target (x : FeasibleInput) :
    (fun i : Fin (x.1.1.2.length+x.1.1.1) => (jointAffine x).2.getD i.val 0) =
      Fin.append (fun i : Fin x.1.1.2.length => x.1.2.getD i.val 0)
        (FieldHash.fixedTarget (fun i : Fin x.1.1.1 => partialValue x.2 i.val)) := by
  have hdrop : (joint (x.1.1,x.2)).2.drop x.1.1.2.length = (fixed x.1.1.1 x.2).2 := by
    simp [joint]
  funext i
  change (targetPart x.1.1.2.length x.1.2 ++
    (joint (x.1.1,x.2)).2.drop x.1.1.2.length).getD i.val 0 = _
  rw [hdrop]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hj : j.val < (targetPart x.1.1.2.length x.1.2).length := by simp [targetPart]
    simp only [Fin.val_castAdd,Fin.append_left,List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hj]
    simp [targetPart,j.isLt]
  · simp [targetPart,fixed,fixedTarget,List.getD_eq_getElem?_getD,j.isLt]

theorem isFeasible_eq (x : FeasibleInput) :
    isFeasible x = feasible (matrixOf x.1.1) (rowOf x.1.1.2.length x.1.2)
      (fun i : Fin x.1.1.1 => partialValue x.2 i.val) := by
  let p := jointAffine x
  let B := jointMatrix (matrixOf x.1.1) (fun i : Fin x.1.1.1 => partialValue x.2 i.val)
  let y := Fin.append (rowOf x.1.1.2.length x.1.2)
    (fixedTarget (fun i : Fin x.1.1.1 => partialValue x.2 i.val))
  have hA : asMatrix p.1.2 (x.1.1.2.length+x.1.1.1) x.1.1.1 = B :=
    joint_matrix x.1.1 x.2
  have hm : p.1.2.length = x.1.1.2.length+x.1.1.1 := tabRows_length ..
  have hbase := rank_represents hm rfl hA
  have haug {m n : ℕ} (h : p.1.2.length = m) (hn : p.1.1 = n) :
      rank (augmented p) = ternaryRank (augment (asMatrix p.1.2 m n) (rowOf m p.2)) := by
    subst m n
    exact augmented_eq p
  have ht : rowOf (x.1.1.2.length+x.1.1.1) p.2 = y := jointAffine_target x
  unfold isFeasible feasible
  dsimp only
  rw [haug hm (show p.1.1 = x.1.1.1 from rfl),hbase,hA,ht]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,beq_iff_eq]
  rfl

def select (A : AffineInput) (i : ℕ) (p : PartialRow) : Option PartialRow :=
  (choices.find? fun a => isFeasible (A,p.set i (some a))).map (fun a => p.set i (some a))

def assignStep (A : AffineInput) (p : Option PartialRow) (i : ℕ) : Option PartialRow :=
  p.bind (select A i)

def solve (A : AffineInput) : Option Row :=
  let empty : PartialRow := List.replicate A.1.1 none
  if isFeasible (A,empty) then
    (((List.range A.1.1).reverse.foldl (assignStep A) (some empty)).map
      (List.map (fun r => r.getD 0)))
  else none

private theorem partialValue_set (i : Fin n) (p : PartialRow) (hl : p.length = n) (a : F₃) :
    (fun j : Fin n => partialValue (p.set i.val (some a)) j.val) =
      Function.update (fun j : Fin n => partialValue p j.val) i (some a) := by
  funext j
  unfold partialValue
  have hj : j.val < p.length := hl ▸ j.isLt
  have hj' : j.val < (p.set i.val (some a)).length := by simpa
  by_cases h : j = i
  · subst j
    rw [Function.update_self,List.getD_eq_getElem _ _ hj',List.getElem_set_self]
  · rw [Function.update_of_ne h,List.getD_eq_getElem _ _ hj',
      List.getElem_set_ne (fun he => h (Fin.ext he.symm)),List.getD_eq_getElem _ _ hj]

private theorem fold_none (A : AffineInput) (js : List ℕ) :
    js.foldl (assignStep A) none = none := by
  induction js with
  | nil => rfl
  | cons j js ih => exact ih

private theorem folded_assign (A : AffineInput) (js : List (Fin A.1.1))
    (p : PartialRow) (hl : p.length = A.1.1) :
    let A' := matrixOf A.1
    let y := rowOf A.1.2.length A.2
    (((js.map Fin.val).foldl (assignStep A) (some p)).map fun r i => partialValue r i.val) =
      assign A' y js (fun i => partialValue p i.val) := by
  induction js generalizing p with
  | nil => rfl
  | cons i js ih =>
    have hc (a : F₃) : isFeasible (A,p.set i.val (some a)) =
        feasible (matrixOf A.1) (rowOf A.1.2.length A.2)
          (Function.update (fun j => partialValue p j.val) i (some a)) := by
      rw [isFeasible_eq,partialValue_set i p hl]
    simp only [List.map_cons,List.foldl_cons,assignStep,Option.bind_some,select,assign, hc]
    cases h : choices.find? (fun a => feasible (matrixOf A.1) (rowOf A.1.2.length A.2)
        (Function.update (fun j => partialValue p j.val) i (some a))) with
    | none =>
      simp only [Option.map_none,fold_none]
      rfl
    | some a =>
      simp only [h,Option.map_some,Option.bind_some]
      have hlen : (p.set i.val (some a)).length = A.1.1 := by simp [hl]
      change (((js.map Fin.val).foldl (assignStep A) (some (p.set i.val (some a)))).map
        fun r j => partialValue r j.val) =
        assign (matrixOf A.1) (rowOf A.1.2.length A.2) js
          (Function.update (fun j => partialValue p j.val) i (some a))
      rw [ih _ hlen,partialValue_set i p hl]

private theorem folded_length (A : AffineInput) (js : List ℕ) (p r : PartialRow)
    (h : js.foldl (assignStep A) (some p) = some r) : r.length = p.length := by
  induction js generalizing p with
  | nil => simpa using (congrArg (Option.map List.length) h).symm
  | cons i js ih =>
    simp only [List.foldl_cons,assignStep,Option.bind_some,select] at h
    cases hh : choices.find? (fun a => isFeasible (A,p.set i (some a))) with
    | none =>
      simp only [hh,Option.map_none,fold_none] at h
      contradiction
    | some a =>
      simp only [hh,Option.map_some] at h
      have hlen := ih (p.set i (some a)) h
      simpa using hlen

theorem solve_eq (A : AffineInput) :
    solve A = (solveAffine (matrixOf A.1) (rowOf A.1.2.length A.2)).map List.ofFn := by
  let e : PartialRow := List.replicate A.1.1 none
  let js := (List.finRange A.1.1).reverse
  have hjs : js.map Fin.val = (List.range A.1.1).reverse := by simp [js,List.map_reverse]
  have hel : e.length = A.1.1 := by simp [e]
  have he0 : (fun i : Fin A.1.1 => partialValue e i.val) = fun _ => none := by
    funext i
    simp [e,partialValue,List.getD_eq_getElem?_getD]
  unfold solve solveAffine
  dsimp only
  rw [show List.replicate A.1.1 none = e from rfl, isFeasible_eq,he0]
  split
  next h =>
    have ha := folded_assign A js e hel
    dsimp only at ha
    rw [he0,hjs] at ha
    rw [← ha]
    cases hh : (List.range A.1.1).reverse.foldl (assignStep A) (some e) with
    | none => rfl
    | some r =>
      have hlen := (folded_length A _ e r hh).trans hel
      simp only [Option.map_some]
      congr 1
      apply List.ext_getElem (by simp [hlen])
      intro i hi hj
      have hri : i < r.length := by simpa using hi
      simp [partialValue,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hri]
  next h => rfl

theorem solve_represents (x : AffineInput) (hm : x.1.2.length = m) (hn : x.1.1 = n)
    {A : TernaryMatrix m n} {y : Fin m → F₃} (hA : asMatrix x.1.2 m n = A)
    (hy : rowOf m x.2 = y) :
    solve x = (solveAffine A y).map List.ofFn := by
  subst m n A y
  exact solve_eq x

theorem targetPart_polyTime :
    ComputableInPolyTime (fun p : ℕ × Row => targetPart p.1 p.2)
      (encPair encUnary rowEncoding) rowEncoding := by
  let e := encPair encUnary rowEncoding
  unfold targetPart
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := tritEncoding)
    (f := fun p i => p.2.getD i 0) (range.comp (fst encUnary rowEncoding))
    (listGetDWithInput ((snd encUnary rowEncoding).comp (fst e encUnary)) (snd e encUnary) 0)

theorem jointAffine_polyTime :
    ComputableInPolyTime jointAffine feasibleEncoding affineEncoding := by
  let e := feasibleEncoding
  have hx := fst affineEncoding partialRowEncoding
  have hp := snd affineEncoding partialRowEncoding
  have hm := (length_list rowEncoding).comp hx.fst'.snd'
  have hJ := joint_polyTime.comp (encIn := e) (encMid := encPair matrixEncoding partialRowEncoding)
    (hx.fst'.prod hp)
  have hy := targetPart_polyTime.comp (encIn := e) (encMid := encPair encUnary rowEncoding)
    (hm.prod hx.snd')
  exact (hJ.fst'.prod (listAppend' hy (listDropWithInput hJ.snd' hm))).of_enc_eq (fun _ => rfl)

theorem isFeasible_polyTime :
    ComputableInPolyTime isFeasible feasibleEncoding encBool := by
  have hp := jointAffine_polyTime
  have ht := augmented_polyTime.comp (encIn := feasibleEncoding) hp
  exact ((rank_polyTime.comp ht).decide_eq' (rank_polyTime.comp hp.fst')).of_enc_eq (fun _ => rfl)

abbrev SelectInput := (AffineInput × ℕ) × PartialRow
abbrev selectEncoding := encPair (encPair affineEncoding encUnary) partialRowEncoding
abbrev partialOptionEncoding := encOption partialRowEncoding

theorem select_polyTime :
    ComputableInPolyTime (fun x : SelectInput => select x.1.1 x.1.2 x.2)
      selectEncoding partialOptionEncoding := by
  let e := selectEncoding
  let p := encPair e tritEncoding
  have hx := fst e tritEncoding
  have hcfg := (fst (encPair affineEncoding encUnary) partialRowEncoding).comp hx
  have hpart := (snd (encPair affineEncoding encUnary) partialRowEncoding).comp hx
  have hv := (optionSome tritEncoding).comp (snd e tritEncoding)
  have hs := listSetWithInput (encOption tritEncoding) hpart hcfg.snd' hv
  have hf := isFeasible_polyTime.comp (encIn := p) (encMid := feasibleEncoding) (hcfg.fst'.prod hs)
  have h := findWithInput (encIn := e) (encA := tritEncoding)
    (test := fun x a => isFeasible (x.1.1,x.2.set x.1.2 (some a)))
      (const choices) (hf.of_enc_eq (fun _ => rfl))
  unfold select
  exact optionMapWithInput (f := fun x a => x.2.set x.1.2 (some a)) h hs

abbrev StepInput := (AffineInput × Option PartialRow) × ℕ
abbrev stepEncoding := encPair (encPair affineEncoding partialOptionEncoding) encUnary

theorem assignStep_polyTime :
    ComputableInPolyTime (fun x : StepInput => assignStep x.1.1 x.1.2 x.2)
      stepEncoding partialOptionEncoding := by
  let e := stepEncoding
  let p := encPair e partialRowEncoding
  have hA := fst (encPair affineEncoding partialOptionEncoding) encUnary
  have hx := fst e partialRowEncoding
  have hp := snd e partialRowEncoding
  have hi := (snd (encPair affineEncoding partialOptionEncoding) encUnary).comp hx
  have harg := (((hA.comp hx).fst').prod hi).prod hp
  have hh := select_polyTime.comp (encIn := p) (encMid := selectEncoding) harg
  have h := optionElimWithInput (encA := e) (encB := partialRowEncoding)
    (encC := partialOptionEncoding) (body := fun x p => select x.1.1 x.2 p)
    hA.snd' (const none) (hh.of_enc_eq (fun _ => rfl))
  refine h.of_enc_eq ?_
  intro x
  change partialOptionEncoding (x.1.2.bind (select x.1.1 x.2)) = _
  cases x.1.2 <;> rfl

private theorem partial_encoding_size (p : Option PartialRow) (n : ℕ)
    (h : ∀ r, p = some r → r.length ≤ n) :
    (partialOptionEncoding p).length ≤ 12*n+1 := by
  cases p with
  | none => simp [partialOptionEncoding, encOption]
  | some r =>
    have hr := h r rfl
    have hsize := length_encList_le (encOption tritEncoding) r (b := 5) (by
      intro a _
      exact (show ∀ a : Option F₃, (encOption tritEncoding a).length ≤ 5 from by decide) a)
    change ((encList (encOption tritEncoding) r).length+1) ≤ 12 * n+1
    omega

private theorem solveFold_polyTime :
    ComputableInPolyTime (fun A : AffineInput => (List.range A.1.1).reverse.foldl
      (assignStep A) (some (List.replicate A.1.1 none))) affineEncoding partialOptionEncoding := by
  let e := affineEncoding
  let p := encPair e partialOptionEncoding
  have hn := (fst matrixEncoding rowEncoding).fst'
  have hempty : ComputableInPolyTime (fun A : AffineInput => List.replicate A.1.1 none) e partialRowEncoding :=
    replicate hn (const none)
  have hindex := (listReverse encUnary).comp (unary_range' hn)
  have hinit := id'.prod ((optionSome partialRowEncoding).comp hempty)
  have hstate := ((fst e partialOptionEncoding).comp (fst p encUnary)).prod assignStep_polyTime
  have hb : PolyBounded (fun A : AffineInput => (e A).length)
      (fun A => 2 * (e A).length + 1 + (12*A.1.1+1)) := by
    have hn' : PolyBounded (fun A : AffineInput => (e A).length) (fun A => A.1.1) := by
      simpa only [encUnary_apply,List.length_replicate] using hn.polyBounded_length
    exact (((PolyBounded.const 2).mul .self).add (.const 1)).add
      (((PolyBounded.const 12).mul hn').add (.const 1))
  have hstate_eq (A : AffineInput) (js : List ℕ) (s : Option PartialRow) :
      js.foldl (fun z j => (z.1,assignStep z.1 z.2 j)) (A,s) =
        (A,js.foldl (assignStep A) s) := by
    induction js generalizing s with
    | nil => rfl
    | cons j js ih => exact ih (assignStep A s j)
  have hf := foldl' (encIn := e) (encA := encUnary) (encB := p)
    (list := fun A => (List.range A.1.1).reverse)
    (init := fun A => (A,some (List.replicate A.1.1 none)))
    (step := fun z i => (z.1,assignStep z.1 z.2 i))
    (hindex.of_enc_eq (fun _ => rfl)) (hinit.of_enc_eq (fun _ => rfl))
    (hstate.of_enc_eq (fun _ => rfl)) hb (by
      intro A i _
      rw [hstate_eq,length_encPair]
      refine Nat.add_le_add_left (partial_encoding_size _ _ ?_) _
      intro r h
      have hl := folded_length A _ _ r h
      simp [hl])
  have hm := (snd e partialOptionEncoding).comp (encIn := e) (encMid := p) hf
  refine hm.of_enc_eq ?_
  intro A
  simp only [Function.comp_def,hstate_eq]

theorem solve_polyTime : ComputableInPolyTime solve affineEncoding (encOption rowEncoding) := by
  let e := affineEncoding
  let p := encPair e partialRowEncoding
  let o := encOption tritEncoding
  have hA := fst e partialRowEncoding
  have hn := (fst matrixEncoding rowEncoding).fst'
  have hempty : ComputableInPolyTime (fun A : AffineInput => List.replicate A.1.1 none) e partialRowEncoding :=
    replicate hn (const none)
  have hc := isFeasible_polyTime.comp (encIn := e) (encMid := feasibleEncoding) (id'.prod hempty)
  have hm := ComputableInPolyTime.map (optionGetDWithInput (id' (encIn := o)) (const (0 : F₃)))
  have hout := optionMapWithInput (f := fun _ r => r.map (fun a => a.getD 0)) solveFold_polyTime
    (hm.comp (encIn := p) (encMid := partialRowEncoding) (snd e partialRowEncoding))
  exact (hc.ite' hout (const none)).of_enc_eq (fun _ => rfl)

#print axioms solve_eq
#print axioms solve_polyTime

end DeletionCode.Explicit.Machine.CanonicalAffine
