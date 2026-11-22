import DeletionCode.Explicit.Machine.CataloguePrefix
import DeletionCode.Explicit.FamilyBuckets
import DeletionCode.Explicit.FibreListing
import DeletionCode.Explicit.CoreReplay

/-! The hash selector on row-major family and core catalogue tables. -/
namespace DeletionCode.Explicit.Machine.SourceHashChoice

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open FieldHash Ternary CataloguePrefix ConditionalChoice ExceptionalRecords
open scoped BigOperators

variable {q ℓ n θ : ℕ}

abbrev CoreTable (q : ℕ) := List (EntryData q)
abbrev coreTableEncoding (q : ℕ) := encList (entryEncoding q)
abbrev CoreConditionalInput (q : ℕ) := (ℕ × PartialRows) × CoreTable q
abbrev coreConditionalEncoding (q : ℕ) := encPair partialHashEncoding (coreTableEncoding q)

def coreTerm (x : (ℕ × PartialRows) × EntryData q) : ℚ :=
  Ternary.conditional ((x.1.1,x.2.1),x.1.2) / (q : ℚ)^x.2.2.length

def coreConditional (x : CoreConditionalInput q) : ℚ := (x.2.map (fun o => coreTerm (x.1,o))).sum

private theorem coreTerm_polyTime (q : ℕ) :
    ComputableInPolyTime (coreTerm (q := q)) (encPair partialHashEncoding (entryEncoding q)) encRat := by
  have hh := fst partialHashEncoding (entryEncoding q)
  have ho := snd partialHashEncoding (entryEncoding q)
  have hm := hh.fst'.prod ho.fst'
  have hs := (length_list (encPair encUnary (letterEncoding q))).comp ho.snd'
  have hn := ratOfNat_polyTime.comp (binary_pow.comp ((const (encOut := encNat) q).prod hs))
  have hp : ComputableInPolyTime (fun x : (ℕ × PartialRows) × EntryData q => (q : ℚ)^x.2.2.length)
      (encPair partialHashEncoding (entryEncoding q)) encRat := by
    simpa only [Function.comp_def,Nat.cast_pow] using hn
  exact rat_div' (conditional_polyTime.comp (hm.prod hh.snd')) hp

theorem coreConditional_polyTime (q : ℕ) :
    ComputableInPolyTime (coreConditional (q := q)) (coreConditionalEncoding q) encRat := by
  let e := coreConditionalEncoding q
  let a := entryEncoding q
  have hs := fst e a
  have hterm := (coreTerm_polyTime q).comp (hs.fst'.prod (snd e a))
  exact ratSum_polyTime.comp (mapWithInput (encIn := e) (encA := a)
    (f := fun x o => coreTerm (x.1,o)) (snd partialHashEncoding (coreTableEncoding q)) hterm)

private theorem kernelProbability_rows {m : ℕ} (A : TernaryMatrix m n) (p : PartialHash θ n) :
    conditionalKernelProbability (matrixOf (n,matrixRows A)) p = conditionalKernelProbability A p := by
  have h : (matrixRows A).length = m := List.length_ofFn
  have ha (i : Fin (matrixRows A).length) : matrixOf (n,matrixRows A) i = A (Fin.cast h i) := by
    funext j
    change ((List.ofFn fun i => List.ofFn (A i)).getD i.val []).getD j.val 0 = _
    exact (congrArg (fun row : Row => row.getD j.val 0)
      (BooleanFibres.ofFn_getD (fun k => List.ofFn (A k)) (Fin.cast h i) [])).trans
      (BooleanFibres.ofFn_getD (A (Fin.cast h i)) j 0)
  suffices ∀ k (B : TernaryMatrix k n) (hk : k = m),
      (∀ i, B i = A (Fin.cast hk i)) → conditionalKernelProbability B p = conditionalKernelProbability A p by
    exact this _ _ h ha
  intro k B hk hB
  subst k
  exact congrArg (fun A => conditionalKernelProbability A p) (funext hB)

theorem coreConditional_eq {m : ℕ} (C : Fin m → CoreWeight.Object ℓ q n) (p : PartialRows) :
    coreConditional ((n,p),List.ofFn (fun i => objectData (C i))) = CoreWeight.conditionalMass C (hashOf n p) := by
  unfold coreConditional CoreWeight.conditionalMass
  simp only [List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  change Ternary.conditional ((n,matrixRows (C i).rules),p) /
    (q : ℚ)^(serializeAssignment (C i).assignment).length = _
  rw [conditional_eq,kernelProbability_rows]
  simp [serializeAssignment]

abbrev CoreOnPrefix (q : ℕ) := ((ℕ × ℕ) × CoreTable q) × ConditionalChooser.Prefix
abbrev coreOnPrefixEncoding (q : ℕ) := encPair (encPair dimensionEncoding (coreTableEncoding q)) prefixEncoding

def coreOnPrefix (x : CoreOnPrefix q) : ℚ :=
  coreConditional ((x.1.1.2,partialRows (x.1.1,x.2)),x.1.2)

theorem coreOnPrefix_polyTime (q : ℕ) :
    ComputableInPolyTime (coreOnPrefix (q := q)) (coreOnPrefixEncoding q) encRat := by
  have hd := fst (encPair dimensionEncoding (coreTableEncoding q)) prefixEncoding
  have hp := snd (encPair dimensionEncoding (coreTableEncoding q)) prefixEncoding
  have hh := partialRows_polyTime.comp (hd.fst'.prod hp)
  exact (coreConditional_polyTime q).comp ((hd.fst'.snd'.prod hh).prod hd.snd')

theorem coreOnPrefix_eq {m : ℕ} (C : Fin m → CoreWeight.Object ℓ q n) (p : ConditionalChooser.Prefix) :
    coreOnPrefix (((θ,n),List.ofFn (fun i => objectData (C i))),p) =
      CoreWeight.conditionalMass C (ConditionalChooser.prefixHash θ n p) := by
  let P := partialRows ((θ,n),p)
  change coreConditional ((n,P),List.ofFn (fun i => objectData (C i))) = _
  rw [coreConditional_eq]
  have h := partialRows_length ((θ,n),p)
  suffices ∀ k (hk : P.length = k) (r : PartialHash k n),
      (∀ i j, hashOf n P i j = r (Fin.cast hk i) j) →
      CoreWeight.conditionalMass C (hashOf n P) = CoreWeight.conditionalMass C r by
    exact this θ h _ (partialRows_hash θ n p)
  intro k hk r he
  subst k
  exact congrArg (CoreWeight.conditionalMass C) (funext fun i => funext fun j => he i j)

/-- The list representation of one main-session bubble family. -/
def familyRows (s : BubbleFamilies.Shape q) (K b L Λ : ℕ) (pad : Fin q) : Rows :=
  (s.members K b L Λ pad).map (fun m => List.ofFn (BubbleFamilies.vector pad m.2))

theorem familyRows_decoded (s : BubbleFamilies.Shape q) (K b L Λ : ℕ) (pad : Fin q) :
    (familyRows s K b L Λ pad).map (rowOf (q^L)) =
      (s.members K b L Λ pad).map (fun m => BubbleFamilies.vector pad m.2) := by
  rw [familyRows,List.map_map]
  apply List.map_congr_left
  intro m _
  funext j
  exact BooleanFibres.ofFn_getD _ j 0

theorem familyRows_nodup (s : BubbleFamilies.Shape q) (K b L Λ : ℕ) (pad : Fin q) (hL : 1 ≤ L) :
    ((familyRows s K b L Λ pad).map (rowOf (q^L))).Nodup := by
  rw [familyRows_decoded]
  let xs := (s.members K b L Λ pad).map (fun m => BubbleFamilies.vector pad m.2)
  have h : xs.toFinset.card = xs.length := by
    rw [List.length_map]
    exact BubbleFamilies.vectors_card s K b L Λ pad hL
  exact Multiset.toFinset_card_eq_card_iff_nodup.mp h

theorem familyRows_eq (s : BubbleFamilies.Shape q) (K b L Λ : ℕ) (pad : Fin q) :
    familyOf (q^L) (familyRows s K b L Λ pad) = s.vectors K b L Λ pad := by
  unfold familyOf BubbleFamilies.Shape.vectors
  rw [familyRows_decoded]

abbrev Tables (q : ℕ) := List Rows × CoreTable q
abbrev tablesEncoding (q : ℕ) := encPair (encList rowsEncoding) (coreTableEncoding q)
abbrev Input (q : ℕ) := ChooserData (Tables q)
abbrev inputEncoding (q : ℕ) := encPair dimensionEncoding (tablesEncoding q)
abbrev prefixArgsEncoding (q : ℕ) := encPair (inputEncoding q) prefixEncoding

def width (q b t l : ℕ) : ℕ := q^UniformParameters.gram q b t l

theorem width_polyTime (q b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (width q b t) encUnary encUnary :=
  ((length_list (wordEncoding q)).comp (gramList_polyTime q b t hq)).of_enc_eq
    (fun _ => congrArg encUnary (length_wordsOfLength ..).symm)

def familyEvaluator (q b t : ℕ) (x : Input q × ConditionalChooser.Prefix) : ℚ :=
  potentialOnPrefix (((x.1.1.2,width q b t x.1.1.1),x.1.2.1),x.2)

def coreEvaluator (q b t : ℕ) (x : Input q × ConditionalChooser.Prefix) : ℚ :=
  coreOnPrefix (((x.1.1.2,width q b t x.1.1.1),x.1.2.2),x.2)

private theorem familyEvaluator_polyTime (q b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (familyEvaluator q b t) (prefixArgsEncoding q) encRat := by
  have hp := fst (inputEncoding q) prefixEncoding
  have hw := (width_polyTime q b t hq).comp hp.fst'.fst'
  exact potentialOnPrefix_polyTime.comp (((hp.fst'.snd'.prod hw).prod hp.snd'.fst').prod
    (snd (inputEncoding q) prefixEncoding))

private theorem coreEvaluator_polyTime (q b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (coreEvaluator q b t) (prefixArgsEncoding q) encRat := by
  have hp := fst (inputEncoding q) prefixEncoding
  have hw := (width_polyTime q b t hq).comp hp.fst'.fst'
  exact (coreOnPrefix_polyTime q).comp (((hp.fst'.snd'.prod hw).prod hp.snd'.snd').prod
    (snd (inputEncoding q) prefixEncoding))

def otherEvaluators (q b t : ℕ) (x : Input q) : ConditionalChooser.Evaluator :=
  fun i p => if i = 0 then familyEvaluator q b t (x,p) else coreEvaluator q b t (x,p)

def otherScales (q b t : ℕ) (x : Input q) (i : Fin 3) : ℚ :=
  if i = 0 then (x.2.1.length : ℚ) else coreEvaluator q b t (x,[])

/-- A complete row-major hash from the three exact evaluators. -/
def choosePrefix (pad : Fin q) (b t : ℕ) (x : Input q) : ConditionalChooser.Prefix :=
  ConditionalChooser.choose (ConditionalChooser.score
    (withExceptional pad b t (otherEvaluators q b t) x)
    (withExceptionalScale pad b t (otherScales q b t) x)) (x.1.2 * width q b t x.1.1)

set_option maxHeartbeats 500000 in
theorem choosePrefix_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (choosePrefix pad b t) (inputEncoding q) prefixEncoding := by
  let src := inputEncoding q
  let out := encPair src encUnary
  have hf := familyEvaluator_polyTime q b t hq
  have hc := coreEvaluator_polyTime q b t hq
  have hs := ((length_list rowsEncoding).comp (snd dimensionEncoding (tablesEncoding q)).fst')
  have hJ : ComputableInPolyTime (fun x : Input q => (x.2.1.length : ℚ)) src encRat :=
    ratOfNat_polyTime.comp (unary_to_binary.comp hs)
  have hroot : ComputableInPolyTime (fun x : Input q => coreEvaluator q b t (x,[])) src encRat :=
    hc.comp (encIn := src) (encMid := prefixArgsEncoding q) (id'.prod (const []))
  have hE (i : Fin 3) : ComputableInPolyTime (fun x : Input q × ConditionalChooser.Prefix =>
      otherEvaluators q b t x.1 i x.2) (prefixArgsEncoding q) encRat := by
    by_cases hi : i = 0
    · simpa only [otherEvaluators,hi,↓reduceIte] using hf
    · simpa only [otherEvaluators,hi,↓reduceIte] using hc
  have hμ (i : Fin 3) : ComputableInPolyTime (fun x : Input q => otherScales q b t x i) src encRat := by
    by_cases hi : i = 0
    · simpa only [otherScales,hi,↓reduceIte] using hJ
    · simpa only [otherScales,hi,↓reduceIte] using hroot
  have h := choose_withExceptional_polyTime (enc := tablesEncoding q) pad b t hq
    (otherEvaluators q b t) (otherScales q b t) (fun i _ => hE i) (fun i _ => hμ i)
  have hd := fst dimensionEncoding (tablesEncoding q)
  have hn := (width_polyTime q b t hq).comp hd.fst'
  have harg : ComputableInPolyTime (fun x : Input q => (x,x.1.2 * width q b t x.1.1)) src out :=
    id'.prod (unary_mul' hd.snd' hn)
  exact (h.comp (encIn := src) (encMid := out) harg).of_enc_eq (fun _ => rfl)

/-- Interpret the supplied main-session families in the potential's finite sum. -/
theorem familyEvaluator_eq (q b t ℓ θ : ℕ) (shapes : List (BubbleFamilies.Shape q))
    (pad : Fin q) (cores : CoreTable q) (p : ConditionalChooser.Prefix) :
    let L := UniformParameters.gram q b t ℓ
    let K := UniformParameters.windowLength q ℓ
    let Λ := UniformParameters.omittedLetters q b t ℓ
    let fs := shapes.map (fun s => familyRows s K b L Λ pad)
    1 ≤ L → familyEvaluator q b t (((ℓ,θ),(fs,cores)),p) =
      BucketBalance.conditionalPotential
        (fun i : Fin fs.length => shapes[i.val]'(by simpa [fs] using i.isLt) |>.vectors K b L Λ pad)
        (ConditionalChooser.prefixHash θ (q^L) p) := by
  dsimp only
  intro hL
  let L := UniformParameters.gram q b t ℓ
  let K := UniformParameters.windowLength q ℓ
  let Λ := UniformParameters.omittedLetters q b t ℓ
  let matrix (s : BubbleFamilies.Shape q) := familyRows s K b L Λ pad
  change potentialOnPrefix (((θ,q^L),shapes.map matrix),p) = _
  rw [potentialOnPrefix_eq]
  · congr 1
    funext i
    have hi : i.val < (shapes.map matrix).length := i.isLt
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,List.getElem_map,Option.getD_some]
    exact familyRows_eq _ K b L Λ pad
  · intro xs hx
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp hx
    exact familyRows_nodup s K b L Λ pad hL

theorem coreEvaluator_eq {m : ℕ} (q b t ℓ θ : ℕ)
    (C : Fin m → CoreWeight.Object ℓ q (width q b t ℓ)) (families : List Rows)
    (p : ConditionalChooser.Prefix) :
    coreEvaluator q b t (((ℓ,θ),(families,List.ofFn fun i => objectData (C i))),p) =
      CoreWeight.conditionalMass C (ConditionalChooser.prefixHash θ (width q b t ℓ) p) :=
  coreOnPrefix_eq C p

def chosenRows (pad : Fin q) (b t : ℕ) (x : Input q) : Rows :=
  let p := choosePrefix pad b t x
  let n := width q b t x.1.1
  tabRows x.1.2 n (fun i j => p.getD (j+n*i) 0)

theorem chosenRows_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (chosenRows pad b t) (inputEncoding q) rowsEncoding := by
  let e := inputEncoding q
  let a := encPair e encUnary
  let d := encPair a encUnary
  have hx := fst dimensionEncoding (tablesEncoding q)
  have hn := (width_polyTime q b t hq).comp hx.fst'
  have hp := choosePrefix_polyTime pad b t hq
  have hu := (fst e encUnary).comp (fst a encUnary)
  have hi := (snd e encUnary).comp (fst a encUnary)
  have hj := snd a encUnary
  unfold chosenRows
  exact tabRows_polyTime (enc := e) hx.snd' hn
    (listGetDWithInput (hp.comp hu) (unary_add' hj (unary_mul' (hn.comp hu) hi)) 0)

theorem chosenRows_eq (pad : Fin q) (b t : ℕ) (x : Input q) :
    chosenRows pad b t x = matrixRows (ConditionalChooser.totalHash x.1.2
      (width q b t x.1.1) (choosePrefix pad b t x)) := by
  unfold chosenRows matrixRows tabRows
  dsimp only
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  apply List.ext_getElem (by simp)
  intro j hj hj'
  simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  change (choosePrefix pad b t x).getD (j+width q b t x.1.1*i) 0 = _
  rw [List.getD_eq_getElem?_getD]
  rfl

#print axioms coreConditional_eq
#print axioms coreOnPrefix_eq
#print axioms coreOnPrefix_polyTime
#print axioms familyRows_nodup
#print axioms familyRows_eq
#print axioms familyEvaluator_eq
#print axioms coreEvaluator_eq
#print axioms choosePrefix_polyTime
#print axioms chosenRows_eq
#print axioms chosenRows_polyTime

end DeletionCode.Explicit.Machine.SourceHashChoice
