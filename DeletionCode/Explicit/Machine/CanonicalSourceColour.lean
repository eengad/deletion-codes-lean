import DeletionCode.Explicit.ParityLabel
import DeletionCode.Explicit.Machine.CanonicalAffine
import DeletionCode.Explicit.Machine.ClosureRank
import DeletionCode.Explicit.Machine.SourceSpectrum

/-! The ordered span basis, colour and packed label with row-major data. -/
namespace DeletionCode.Explicit.Machine.CanonicalSourceColour

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open FieldHash Ternary CataloguePrefix GramOrder
open private collect solveRows from DeletionCode.Explicit.CanonicalColour
open private trit from DeletionCode.Explicit.ParityLabel

variable {q θ n : ℕ}

def inSpan (p : Adjunction) : Bool := !independentAdjunction p

private theorem range_rowOf (n : ℕ) (xs : Rows) :
    Set.range (matrixOf (n,xs)).row = {v | v ∈ xs.map (rowOf n)} := by
  ext v
  change (∃ i : Fin xs.length, (matrixOf (n,xs)).row i = v) ↔ _
  constructor
  · rintro ⟨i,rfl⟩
    refine List.mem_map.mpr ⟨xs.get i,List.get_mem _ _,?_⟩
    funext j
    change (xs.get i).getD j.val 0 = cell xs i.val j.val
    unfold cell
    rw [List.getD_eq_getElem _ _ i.isLt]
    rfl
  · rintro h
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp h
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hw
    refine ⟨i,?_⟩
    funext j
    change cell xs i.val j.val = _
    unfold cell
    rw [List.getD_eq_getElem _ _ i.isLt]
    rfl

theorem inSpan_eq (n : ℕ) (xs : Rows) (v : Row) :
    inSpan ((n,xs),v) = CanonicalColour.inSpan (xs.map (rowOf n)) (rowOf n v) := by
  have h := independentAdjunction_eq_true ((n,xs),v)
  rw [range_rowOf] at h
  apply Bool.eq_iff_iff.mpr
  rw [CanonicalColour.inSpan_iff]
  change (!independentAdjunction ((n,xs),v)) = true ↔ _
  have he : vector n v = rowOf n v := rfl
  rw [he] at h
  by_cases hs : independentAdjunction ((n,xs),v) = true
  · have hn := h.mp hs
    simp [hs,hn]
  · have hn : rowOf n v ∈ CanonicalColour.span (xs.map (rowOf n)) := by
      by_contra hh
      exact hs (h.mpr hh)
    simp [Bool.eq_false_iff.mpr hs,hn]

private theorem readRow (r : Fin n → F₃) : rowOf n (List.ofFn r) = r := by
  funext i
  exact BooleanFibres.ofFn_getD r i 0

private theorem readRows (rs : List (Fin n → F₃)) :
    (rs.map List.ofFn).map (rowOf n) = rs := by simp [List.map_map,Function.comp_def,readRow]

theorem inSpan_rows (rs : List (Fin n → F₃)) (v : Fin n → F₃) :
    inSpan ((n,rs.map List.ofFn),List.ofFn v) = CanonicalColour.inSpan rs v := by
  rw [inSpan_eq,readRows,readRow]

def step (n : ℕ) (r : Rows) (v : Row) : Rows :=
  if inSpan ((n,r),v) then r else v :: r

def keep (n : ℕ) (catalogue old : Rows) : Rows :=
  catalogue.filter (fun v => inSpan ((n,old),v))

def basisRows (n : ℕ) (catalogue old : Rows) : Rows :=
  (keep n catalogue old).foldl (step n) []

private theorem keep_eq (catalogue old : List (Fin n → F₃)) :
    keep n (catalogue.map List.ofFn) (old.map List.ofFn) =
      (catalogue.filter (CanonicalColour.inSpan old)).map List.ofFn := by
  unfold keep
  rw [List.filter_map]
  congr 1
  exact List.filter_congr (fun v _ => inSpan_rows old v)

private theorem scan_eq (xs old : List (Fin n → F₃)) :
    (xs.map List.ofFn).foldl (step n) (old.map List.ofFn) =
      (collect xs old).map List.ofFn := by
  induction xs generalizing old with
  | nil => rfl
  | cons v xs ih =>
    simp only [List.map_cons,List.foldl_cons,step,inSpan_rows,collect]
    split
    · exact ih old
    · exact ih (v::old)

theorem basisRows_eq (catalogue old : List (Fin n → F₃)) :
    basisRows n (catalogue.map List.ofFn) (old.map List.ofFn) =
      (CanonicalColour.basisRows catalogue old).map List.ofFn := by
  unfold basisRows CanonicalColour.basisRows
  rw [keep_eq]
  exact scan_eq _ []

def alpha (n : ℕ) (catalogue old : Rows) : Option Row :=
  let rs := basisRows n catalogue old
  CanonicalAffine.solve ((n,rs),List.replicate rs.length 1)

private theorem alpha_basis_eq (rs : List (Fin n → F₃)) :
    CanonicalAffine.solve ((n,rs.map List.ofFn),List.replicate rs.length 1) =
      (solveRows rs).map List.ofFn := by
  unfold solveRows
  refine CanonicalAffine.solve_represents (m := rs.length) (n := n)
    ((n,rs.map List.ofFn),List.replicate rs.length 1) (by simp) rfl
    (A := CanonicalColour.matrix rs) (y := fun _ => 1) ?_ ?_
  · funext i j
    have hi : i.val < (rs.map List.ofFn).length := by simpa using i.isLt
    change cell (rs.map List.ofFn) i.val j.val = _
    unfold cell
    rw [List.getD_eq_getElem _ _ hi,List.getElem_map]
    exact congrFun (readRow (rs.get i)) j
  · funext i
    simp [rowOf,List.getD_eq_getElem?_getD,i.isLt]

theorem alpha_eq (catalogue old : List (Fin n → F₃)) :
    alpha n (catalogue.map List.ofFn) (old.map List.ofFn) =
      (CanonicalColour.alpha catalogue old).map List.ofFn := by
  unfold alpha CanonicalColour.alpha
  rw [basisRows_eq]
  dsimp only
  rw [List.length_map]
  exact alpha_basis_eq _

def packLabel (x : Row × F₃) : ℕ :=
  x.2.val + 3 * wordRank ((x.1.map trit).reverse)

theorem packLabel_eq (z : (Fin θ → F₃) × F₃) :
    packLabel (List.ofFn z.1,z.2) = (CanonicalColour.packLabel z).val := by
  unfold packLabel CanonicalColour.packLabel
  rw [List.map_ofFn]
  change z.2.val + 3 * wordRank (List.ofFn (fun i => trit (z.1 i))).reverse =
    z.2.val + 3 * (finFunctionFinEquiv (fun i => trit (z.1 i))).val
  rw [reversed_rank]

abbrev PublicRows := (ℕ × Rows) × (Rows × Rows)

def labelPair (d : PublicRows) (v : Row) : Option (Row × F₃) :=
  (alpha d.1.1 d.2.1 d.2.2).map fun a =>
    (SourceSpectrum.applyRows d.1.1 d.1.2 v, dot d.1.1 v a)

def label (d : PublicRows) (v : Row) : Option ℕ :=
  (labelPair d v).map packLabel

theorem label_eq (H : TernaryMatrix θ n) (catalogue old : List (Fin n → F₃)) (v : Fin n → F₃) :
    label ((n,matrixRows H),(catalogue.map List.ofFn,old.map List.ofFn)) (List.ofFn v) =
      (CanonicalColour.labelPair H catalogue old v).map (fun z => (CanonicalColour.packLabel z).val) := by
  unfold label labelPair CanonicalColour.labelPair
  rw [alpha_eq]
  cases CanonicalColour.alpha catalogue old with
  | none => rfl
  | some a =>
    simp only [Option.map_some,Option.some.injEq,SourceSpectrum.applyRows_matrix_eq,dot_eq]
    exact packLabel_eq (H.mulVec v,dotProduct v a)

theorem inSpan_polyTime : ComputableInPolyTime inSpan adjunctionEncoding encBool := by
  have h := bool_not.comp independentAdjunction_polyTime
  exact h.of_enc_eq (fun _ => rfl)

theorem step_polyTime :
    ComputableInPolyTime (fun x : Adjunction => step x.1.1 x.1.2 x.2)
      adjunctionEncoding rowsEncoding := by
  have hr := (fst matrixEncoding rowEncoding).snd'
  have ha := snd matrixEncoding rowEncoding
  exact (inSpan_polyTime.ite' hr (cons' ha hr)).of_enc_eq (fun _ => rfl)

abbrev BasisInput := ℕ × (Rows × Rows)
abbrev basisEncoding := encPair encUnary (encPair rowsEncoding rowsEncoding)

theorem keep_polyTime :
    ComputableInPolyTime (fun x : BasisInput => keep x.1 x.2.1 x.2.2)
      basisEncoding rowsEncoding := by
  let e := basisEncoding
  let r := encPair rowsEncoding rowsEncoding
  let p := encPair e rowEncoding
  have hx := fst e rowEncoding
  have hg := fst encUnary r
  have hr := snd encUnary r
  have hf := inSpan_polyTime.comp (encIn := p) (encMid := adjunctionEncoding)
    ((((hg.comp hx).prod (hr.snd'.comp hx))).prod (snd e rowEncoding))
  exact filterWithInput (encIn := e) (encA := rowEncoding)
    (test := fun x v => inSpan ((x.1,x.2.2),v)) hr.fst' (hf.of_enc_eq (fun _ => rfl))

theorem basisRows_polyTime :
    ComputableInPolyTime (fun x : BasisInput => basisRows x.1 x.2.1 x.2.2)
      basisEncoding rowsEncoding := by
  let e := basisEncoding
  let r := encPair rowsEncoding rowsEncoding
  have hb := (((PolyBounded.const 2).mul keep_polyTime.polyBounded_length).add (.const 1))
  have h := foldlWith_of_bounded_growth
    (step := fun n old v => step n old v)
    (fst encUnary r) keep_polyTime (const []) step_polyTime hb (by
      intro x state v hv
      unfold step
      split
      · omega
      · have hh := SizedListEncoding.length_elem_le (encA := rowEncoding) (encL := rowsEncoding)
          (keep x.1 x.2.1 x.2.2) v hv
        rw [encList_cons,List.length_append,length_frame]
        change 2 * (rowEncoding v).length + 1 + (rowsEncoding state).length ≤ _
        omega)
  exact h.of_enc_eq (fun _ => rfl)

theorem alpha_polyTime :
    ComputableInPolyTime (fun x : BasisInput => alpha x.1 x.2.1 x.2.2)
      basisEncoding (encOption rowEncoding) := by
  have hn := fst encUnary (encPair rowsEncoding rowsEncoding)
  have hb := basisRows_polyTime
  have hy := replicate ((length_list rowEncoding).comp hb) (const (encOut := tritEncoding) 1)
  have hs := CanonicalAffine.solve_polyTime.comp (encIn := basisEncoding) (encMid := affineEncoding)
    ((hn.prod hb).prod hy)
  exact hs.of_enc_eq (fun _ => rfl)

theorem basisRows_length (catalogue old : List (Fin n → F₃)) :
    (basisRows n (catalogue.map List.ofFn) (old.map List.ofFn)).length ≤ n := by
  rw [basisRows_eq,List.length_map]
  have hi := CanonicalColour.basisRows_independent catalogue old
  simpa [Module.finrank_fintype_fun_eq_card] using hi.fintype_card_le_finrank

theorem packLabel_polyTime :
    ComputableInPolyTime packLabel (encPair rowEncoding tritEncoding) encNat := by
  let e := encPair rowEncoding tritEncoding
  have ht : ComputableInPolyTime trit tritEncoding (ExceptionalRecords.letterEncoding 3) := of_finite _
  have hval : ComputableInPolyTime (fun a : F₃ => a.val) tritEncoding encNat := of_finite _
  have hword := (listReverse (ExceptionalRecords.letterEncoding 3)).comp
    ((ComputableInPolyTime.map ht).comp (fst rowEncoding tritEncoding))
  have hrank := (wordRank_polyTime (q := 3) (by decide)).comp (encIn := e) hword
  have h := binary_add' (hval.comp (snd rowEncoding tritEncoding))
    (binary_mul' (const 3) hrank)
  exact h.of_enc_eq (fun _ => rfl)

abbrev publicRowsEncoding := encPair matrixEncoding (encPair rowsEncoding rowsEncoding)
abbrev labelInputEncoding := encPair publicRowsEncoding rowEncoding
abbrev labelPairEncoding := encPair rowEncoding tritEncoding

theorem labelPair_polyTime :
    ComputableInPolyTime (fun x : PublicRows × Row => labelPair x.1 x.2)
      labelInputEncoding (encOption labelPairEncoding) := by
  let d := publicRowsEncoding
  let e := labelInputEncoding
  let p := encPair e rowEncoding
  let rows := encPair rowsEncoding rowsEncoding
  have hd := fst d rowEncoding
  have hv := snd d rowEncoding
  have hm := (fst matrixEncoding rows).comp hd
  have hn := hm.fst'
  have hrows := (snd matrixEncoding rows).comp hd
  have ha := alpha_polyTime.comp (encIn := e) (encMid := basisEncoding) (hn.prod hrows)
  have hhash := SourceSpectrum.applyRows_polyTime.comp
    (encIn := e) (encMid := SourceSpectrum.applyEncoding) (hm.prod hv)
  have hx := fst e rowEncoding
  have hd' := dot_polyTime.comp (encIn := p) (encMid := dotEncoding)
    ((hn.comp hx).prod ((hv.comp hx).prod (snd e rowEncoding)))
  have hpair := (hhash.comp (encIn := p) hx).prod hd'
  have h := optionMapWithInput (encA := e) (encB := rowEncoding) (encC := labelPairEncoding)
    (f := fun x a => (SourceSpectrum.applyRows x.1.1.1 x.1.1.2 x.2,dot x.1.1.1 x.2 a))
    (ha.of_enc_eq (fun _ => rfl)) (hpair.of_enc_eq (fun _ => rfl))
  exact h.of_enc_eq (fun _ => rfl)

theorem label_polyTime :
    ComputableInPolyTime (fun x : PublicRows × Row => label x.1 x.2)
      labelInputEncoding (encOption encNat) := by
  have hp := packLabel_polyTime.comp (encIn := encPair labelInputEncoding labelPairEncoding)
    (snd labelInputEncoding labelPairEncoding)
  have h := optionMapWithInput (encA := labelInputEncoding) (encB := labelPairEncoding)
    (encC := encNat) (f := fun _ z => packLabel z) labelPair_polyTime (hp.of_enc_eq (fun _ => rfl))
  exact h.of_enc_eq (fun _ => rfl)

abbrev WordLabelInput (q : ℕ) := (ℕ × (Rows × (Rows × Rows))) × QWord q
abbrev wordLabelInputEncoding (q : ℕ) :=
  encPair (encPair encUnary (encPair rowsEncoding (encPair rowsEncoding rowsEncoding))) (wordEncoding q)

def labelWord (pad : Fin q) (b t : ℕ) (x : WordLabelInput q) : Option ℕ :=
  let ℓ := x.1.1
  let n := SourceHashChoice.width q b t ℓ
  label ((n,x.1.2.1),x.1.2.2) (SourceSpectrum.word pad b t (ℓ,x.2))

theorem labelWord_eq (pad : Fin q) (b t ℓ : ℕ) (hq : 2 ≤ q)
    (H : TernaryMatrix θ (q^UniformParameters.gram q b t ℓ))
    (catalogue old : List (Fin (q^UniformParameters.gram q b t ℓ) → F₃))
    (w : Fin ℓ → Fin q) :
    labelWord pad b t ((ℓ,(matrixRows H,(catalogue.map List.ofFn,old.map List.ofFn))),List.ofFn w) =
      (CanonicalColour.labelPair H catalogue old
          (Recognizer.spectrum pad w (UniformParameters.gram q b t ℓ))).map
        (fun z => (CanonicalColour.packLabel z).val) := by
  unfold labelWord SourceSpectrum.word
  dsimp only
  rw [SourceSpectrum.spectrum_recognizer pad hq]
  exact label_eq H catalogue old _

set_option maxHeartbeats 600000 in
theorem labelWord_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (labelWord pad b t) (wordLabelInputEncoding q) (encOption encNat) := by
  let e := wordLabelInputEncoding q
  let bs := encPair rowsEncoding (encPair rowsEncoding rowsEncoding)
  have hd := fst (encPair encUnary bs) (wordEncoding q)
  have hx := snd (encPair encUnary bs) (wordEncoding q)
  have hn := (SourceHashChoice.width_polyTime q b t hq).comp (encIn := e) hd.fst'
  have hv := (SourceSpectrum.word_polyTime pad b t hq).comp (encIn := e)
    (encMid := encPair encUnary (wordEncoding q)) (hd.fst'.prod hx)
  have ha : ComputableInPolyTime (fun x : WordLabelInput q =>
      ((SourceHashChoice.width q b t x.1.1,x.1.2.1),x.1.2.2)) e publicRowsEncoding :=
    (hn.prod hd.snd'.fst').prod hd.snd'.snd'
  have h := label_polyTime.comp (encIn := e) (encMid := labelInputEncoding) (ha.prod hv)
  refine h.of_enc_eq (g := labelWord pad b t) (encD := encOption encNat) ?_
  intro x
  simp only [labelWord,Function.comp_def]

#print axioms basisRows_eq
#print axioms basisRows_polyTime
#print axioms basisRows_length
#print axioms alpha_eq
#print axioms alpha_polyTime
#print axioms packLabel_eq
#print axioms packLabel_polyTime
#print axioms label_eq
#print axioms label_polyTime
#print axioms labelWord_eq
#print axioms labelWord_polyTime

end DeletionCode.Explicit.Machine.CanonicalSourceColour
