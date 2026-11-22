import DeletionCode.Explicit.Machine.OrderedCatalogue
import DeletionCode.Explicit.Machine.SourceExposure
import DeletionCode.Explicit.LabelRecognition

/-! Materialize the ternary rows of the ordered rule catalogue. -/
namespace DeletionCode.Explicit.Machine.SourceRuleRows

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open FieldHash Ternary OrderedCatalogue
open scoped BigOperators

variable {q b t K L s : ℕ}

abbrev RuleData (q : ℕ) := List (BubbleData q)
abbrev RuleRow (q : ℕ) := Row × RuleData q
abbrev rowEncoding (q : ℕ) := encPair Ternary.rowEncoding (ruleEncoding q)
abbrev tableEncoding (q : ℕ) := encList (rowEncoding q)

def delta (g : QWord q) (u : BubbleData q) : F₃ :=
  (ExceptionalWeight.gramCount (side u true) g : F₃) -
    (ExceptionalWeight.gramCount (side u false) g : F₃)

def rowWith (gs : List (QWord q)) (ws : RuleData q) : Row :=
  gs.map (fun g => (ws.map (delta g)).sum)

def row (pad : Fin q) (L : ℕ) (ws : RuleData q) : Row :=
  rowWith (GramOrder.mainWords pad L) ws

private theorem delta_eq (pad : Fin q) (w : Borrowed.BubbleWord (Fin q) K b L)
    (j : Fin (q^L)) :
    delta (List.ofFn (finFunctionFinEquiv.symm j)) (bubbleData w) = BubbleFamilies.vector pad w j := by
  unfold delta BubbleFamilies.vector
  rw [side_eq,side_eq]
  change (ExceptionalWeight.gramCount w.positiveWord
      (List.ofFn (finFunctionFinEquiv.symm j)) : F₃) -
    (ExceptionalWeight.gramCount w.negativeWord (List.ofFn (finFunctionFinEquiv.symm j)) : F₃) = _
  rw [ExceptionalWeight.gramCount_field,ExceptionalWeight.gramCount_field]

theorem row_eq (pad : Fin q) (hq : 2 ≤ q) (ws : Fin s → Borrowed.BubbleWord (Fin q) K b L) :
    row pad L (List.ofFn (bubbleData ∘ ws)) = List.ofFn (CatalogueEnumeration.row pad ws) := by
  rw [row,rowWith,GramOrder.mainWords_eq pad hq,List.map_ofFn]
  congr 1
  funext j
  unfold CatalogueEnumeration.row
  simp only [List.map_ofFn,Function.comp_def,delta_eq pad,List.sum_ofFn]

def attachRows (pad : Fin q) (b t ℓ : ℕ) (rules : List (RuleData q)) : List (RuleRow q) :=
  rules.map (fun r => (row pad (UniformParameters.gram q b t ℓ) r,r))

def table (pad : Fin q) (b t ℓ : ℕ) : List (RuleRow q) :=
  attachRows pad b t ℓ (OrderedCatalogue.rules pad b t ℓ)

theorem table_eq (pad : Fin q) (b t ℓ : ℕ) (hq : 2 ≤ q) :
    table pad b t ℓ =
      (CatalogueEnumeration.rules q (UniformParameters.windowLength q ℓ) b (UniformParameters.gram q b t ℓ)
        (2*t) pad).map (fun r => (List.ofFn (CatalogueEnumeration.row pad r),List.ofFn (bubbleData ∘ r))) := by
  unfold table attachRows
  rw [OrderedCatalogue.rules_eq,List.map_map]
  apply List.map_congr_left
  intro r _
  exact Prod.ext (row_eq pad hq r) rfl

theorem delta_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : QWord q × BubbleData q => delta x.1 x.2)
      (encPair (wordEncoding q) (bubbleEncoding q)) tritEncoding := by
  let e := encPair (wordEncoding q) (bubbleEncoding q)
  have hg := fst (wordEncoding q) (bubbleEncoding q)
  have hw := snd (wordEncoding q) (bubbleEncoding q)
  have hn := (side_polyTime q false).comp (encIn := e) hw
  have hp := (side_polyTime q true).comp (encIn := e) hw
  have hcount := ExceptionalRecords.gramCount_machine q
  have hf := ExceptionalRecords.tritOfUnary
  have ht := hf.comp (hcount.comp (hp.prod hg))
  have hu := hf.comp (hcount.comp (hn.prod hg))
  have hs : ComputableInPolyTime (fun x : F₃ × F₃ => x.1-x.2)
      (encPair tritEncoding tritEncoding) tritEncoding := of_finite _
  exact (hs.comp (encIn := e) (ht.prod hu)).of_enc_eq (fun _ => rfl)

theorem rowWith_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : List (QWord q) × RuleData q => rowWith x.1 x.2)
      (encPair (encList (wordEncoding q)) (ruleEncoding q)) Ternary.rowEncoding := by
  let ws := encList (wordEncoding q)
  let r := ruleEncoding q
  let u := bubbleEncoding q
  let e := encPair ws r
  let p := encPair e (wordEncoding q)
  let e' := encPair p u
  have hr := (snd ws r).comp (fst e (wordEncoding q))
  have h := (delta_polyTime q).comp (encIn := e')
    (((snd e (wordEncoding q)).comp (fst p u)).prod (snd p u))
  have hd := mapWithInput (encIn := p) (encA := u) (encB := tritEncoding)
    (f := fun x u => delta x.2 u) hr (h.of_enc_eq (fun _ => rfl))
  exact mapWithInput (encIn := e) (encA := wordEncoding q) (encB := tritEncoding)
    (f := fun x g => (x.2.map (delta g)).sum) (fst ws r)
    ((CataloguePrefix.tritSum_polyTime.comp (encIn := p) hd).of_enc_eq (fun _ => rfl))

theorem table_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (table pad b t) encUnary (tableEncoding q) := by
  let w := wordEncoding q
  let e := ruleEncoding q
  let p := encPair encUnary e
  have hg := (SourceSpectrum.mainWords_polyTime pad b t hq).comp (fst encUnary e)
  have hs := snd encUnary e
  have hr := (rowWith_polyTime q).comp (encIn := p) (encMid := encPair (encList w) e) (hg.prod hs)
  have h := mapWithInput (encIn := encUnary) (encA := e) (encB := rowEncoding q)
    (f := fun ℓ r => (row pad (UniformParameters.gram q b t ℓ) r,r))
    (OrderedCatalogue.rules_polyTime pad b t hq) ((hr.prod hs).of_enc_eq (fun _ => rfl))
  exact h.of_enc_eq (fun _ => rfl)

#print axioms row_eq
#print axioms table_eq
#print axioms table_polyTime

end DeletionCode.Explicit.Machine.SourceRuleRows
