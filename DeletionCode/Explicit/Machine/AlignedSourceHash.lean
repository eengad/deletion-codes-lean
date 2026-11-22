import DeletionCode.Explicit.Machine.SourceHashChoice
import DeletionCode.Explicit.Machine.GramOrder
import DeletionCode.Explicit.Machine.AcceptanceWeights

/-! Assemble the chooser and its consumers in the recognizer's gram order. -/
namespace DeletionCode.Explicit.Machine.AlignedSourceHash

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open FieldHash Ternary SourceHashChoice GramOrder CataloguePrefix
open _root_.DeletionCode.Explicit.AcceptanceWeights (exceptional exceptional_iff_admitted)

set_option maxHeartbeats 350000

variable {q ℓ L θ b t K : ℕ}

def lexHash (H : TernaryMatrix θ (q^L)) : TernaryMatrix θ (q^L) :=
  fun i j => H i (columns q L j)

def lexObject (o : CoreWeight.Object ℓ q (q^L)) : CoreWeight.Object ℓ q (q^L) :=
  {o with rules := lexHash o.rules}

theorem kept_columns (o : CoreWeight.Object ℓ q (q^L)) (H : TernaryMatrix θ (q^L)) :
    CoreWeight.Kept (lexObject o) (lexHash H) ↔ CoreWeight.Kept o H := by
  change (∀ j, Matrix.mulVec (fun i k => o.rules i (columns q L k)) ((H j) ∘ columns q L) = 0) ↔ _
  simp only [mulVec_columns]

def lexTables (indices : List ℕ) (tables : Tables q) : Tables q :=
  (tables.1.map (toLexRows indices), tables.2.map (fun e => (toLexRows indices e.1,e.2)))

theorem lexCoreTable_eq {m : ℕ} (C : Fin m → CoreWeight.Object ℓ q (q^L)) (rs : List Rows) :
    (lexTables (lexIndices q L) (rs,List.ofFn (fun j => objectData (C j)))).2 =
      List.ofFn (fun j => objectData (lexObject (C j))) := by
  simp only [lexTables,List.map_ofFn]
  congr 1
  funext j
  change (toLexRows _ (matrixRows (C j).rules),_) = (matrixRows (lexHash (C j).rules),_)
  rw [toLexRows_eq]
  rfl

theorem lexFamilyTable_eq {m : ℕ} (C : Fin m → Rows) (r : CoreTable q) :
    (lexTables (lexIndices q L) (List.ofFn C,r)).1 =
      List.ofFn (fun j => toLexRows (lexIndices q L) (C j)) := by
  simp only [lexTables,List.map_ofFn]
  rfl

abbrev lexTablesEncoding (q : ℕ) := encPair indexEncoding (tablesEncoding q)

theorem lexTables_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : List ℕ × Tables q => lexTables x.1 x.2)
      (lexTablesEncoding q) (tablesEncoding q) := by
  let e := lexTablesEncoding q
  have hi := fst indexEncoding (tablesEncoding q)
  have hp := snd indexEncoding (tablesEncoding q)
  have hf := mapWithInput (encIn := e) (encA := rowsEncoding) (f := fun x r => toLexRows x.1 r)
    hp.fst' (toLexRows_polyTime.comp ((hi.comp (fst e rowsEncoding)).prod (snd e rowsEncoding)))
  let a := entryEncoding q
  have hr : ComputableInPolyTime (fun x : (List ℕ × Tables q) × EntryData q => (x.1.1,x.2.1))
      (encPair e a) rowsPermutationEncoding := (hi.comp (fst e a)).prod (snd e a).fst'
  have ho := mapWithInput (encIn := e) (encA := a) (f := fun x entry => (toLexRows x.1 entry.1,entry.2))
    hp.snd' ((toLexRows_polyTime.comp hr).prod (snd e a).snd')
  exact hf.prod ho

def alignedInput (b t : ℕ) (x : SourceHashChoice.Input q) : SourceHashChoice.Input q :=
  (x.1,lexTables (lexIndices q (UniformParameters.gram q b t x.1.1)) x.2)

def chooseMainRows (pad : Fin q) (b t : ℕ) (x : SourceHashChoice.Input q) : Rows :=
  let is := lexIndices q (UniformParameters.gram q b t x.1.1)
  toMainRows is (chosenRows pad b t (alignedInput b t x))

theorem chooseMainRows_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (chooseMainRows pad b t) (SourceHashChoice.inputEncoding q) rowsEncoding := by
  let src := SourceHashChoice.inputEncoding q
  let ds := ConditionalChoice.dimensionEncoding
  let ts := tablesEncoding q
  have hd := fst ds ts
  have ht := snd ds ts
  have hi : ComputableInPolyTime (fun x : SourceHashChoice.Input q =>
      lexIndices q (UniformParameters.gram q b t x.1.1)) src indexEncoding :=
    (lexIndices_polyTime q b t hq).comp (encIn := src) hd.fst'
  have ha : ComputableInPolyTime (fun x : SourceHashChoice.Input q =>
      (lexIndices q (UniformParameters.gram q b t x.1.1),x.2)) src (lexTablesEncoding q) :=
    hi.prod ht
  have htable : ComputableInPolyTime (fun x : SourceHashChoice.Input q =>
      lexTables (lexIndices q (UniformParameters.gram q b t x.1.1)) x.2) src ts := by
    have htable := (lexTables_polyTime q).comp (encIn := src) (encMid := lexTablesEncoding q) ha
    exact htable.of_enc_eq (fun _ => rfl)
  have hh : ComputableInPolyTime (alignedInput (q := q) b t) src src := by
    unfold alignedInput
    exact hd.prod htable
  have H : ComputableInPolyTime (fun x => chosenRows pad b t (alignedInput b t x)) src rowsEncoding :=
    (chosenRows_polyTime pad b t hq).comp (encIn := src) (encMid := src) hh
  have hfinal : ComputableInPolyTime (fun x => (lexIndices q (UniformParameters.gram q b t x.1.1),
      chosenRows pad b t (alignedInput b t x)))
      src rowsPermutationEncoding := hi.prod H
  exact (toMainRows_polyTime.comp (encIn := src) (encMid := rowsPermutationEncoding) hfinal).of_enc_eq
    (fun _ => rfl)

theorem chooseMainRows_eq (pad : Fin q) (b t : ℕ) (x : SourceHashChoice.Input q) :
    chooseMainRows pad b t x = matrixRows (fun i j =>
      ConditionalChooser.totalHash x.1.2 ((q^UniformParameters.gram q b t x.1.1)) (choosePrefix pad b t (alignedInput b t x))
        i ((columns q (UniformParameters.gram q b t x.1.1)).symm j)) := by
  unfold chooseMainRows
  rw [chosenRows_eq]
  exact toMainRows_eq _ _ _

private theorem exceptional_columns (pad : Fin q) (H : TernaryMatrix θ (q^L)) (x : Fin ℓ → Fin q) :
    ExceptionalWeight.Exceptional pad (ExceptionalWeight.dictionary q L) (lexHash H) b t K x ↔
      ExceptionalWeight.Exceptional pad finFunctionFinEquiv.symm H b t K x := by
  have he (w : QWord q) : ExceptionalWeight.spectrum pad (ExceptionalWeight.dictionary q L) w =
      ExceptionalWeight.spectrum pad finFunctionFinEquiv.symm w ∘ columns q L := by
    funext j
    simp [ExceptionalWeight.spectrum,columns,Function.comp_def]
  have hh (r : Fin (q^L) → F₃) : (lexHash H).mulVec (r ∘ columns q L) = H.mulVec r :=
    mulVec_columns q L H r
  unfold ExceptionalWeight.Exceptional
  simp only [he,hh]

def exceptionalMain (pad : Fin q) (b t : ℕ) (x : ℕ × (Rows × QWord q)) : Bool :=
  exceptional pad b t x.1 (toLexRows (lexIndices q (UniformParameters.gram q b t x.1)) x.2.1) x.2.2

theorem exceptionalMain_polyTime (pad : Fin q) (hq : 2 ≤ q) :
    ComputableInPolyTime (exceptionalMain pad b t) (exceptionalPrefixEncoding q) encBool := by
  have hl := fst encUnary (encPair rowsEncoding (wordEncoding q))
  have hw := snd encUnary (encPair rowsEncoding (wordEncoding q))
  have hi := (lexIndices_polyTime q b t hq).comp hl
  have hh := toLexRows_polyTime.comp (hi.prod hw.fst')
  exact (Machine.AcceptanceWeights.exceptional_polyTime (b := b) (t := t) pad hq).comp
    (hl.prod (hh.prod hw.snd'))

theorem exceptionalMain_iff (pad : Fin q) (b t : ℕ) (x : Fin ℓ → Fin q)
    (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) (hl : UniformParameters.minLength q b t ≤ ℓ)
    (H : TernaryMatrix θ (q^UniformParameters.gram q b t ℓ)) :
    exceptionalMain pad b t (ℓ,matrixRows H,List.ofFn x) = true ↔
      ExceptionalWeight.Exceptional pad finFunctionFinEquiv.symm H b t (UniformParameters.windowLength q ℓ) x := by
  unfold exceptionalMain
  dsimp only
  rw [toLexRows_eq q (UniformParameters.gram q b t ℓ) H]
  exact (exceptional_iff_admitted pad b t x hq hb ht hl (lexHash H)).trans (exceptional_columns pad H x)

#print axioms lexCoreTable_eq
#print axioms chooseMainRows_eq
#print axioms chooseMainRows_polyTime
#print axioms exceptionalMain_iff
#print axioms exceptionalMain_polyTime

end DeletionCode.Explicit.Machine.AlignedSourceHash
