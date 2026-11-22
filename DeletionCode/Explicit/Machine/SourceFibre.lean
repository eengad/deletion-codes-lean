import DeletionCode.Explicit.ComponentExposure
import DeletionCode.Explicit.Machine.CanonicalSourceColour
import DeletionCode.Explicit.Machine.FibreClosure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max

/-! The recognizer's ordered fibre enumeration and its unary block-length budget. -/
namespace DeletionCode.Explicit.Machine.SourceFibre

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Ternary FieldHash CataloguePrefix
open private columns chosen restrictedMatrix target from DeletionCode.Explicit.FibreEnumeration

variable {n ℓ : ℕ}

def transposeRows (n : ℕ) (rs : Rows) : Rows :=
  tabRows n rs.length (fun i j => cell rs j i)

@[simp] theorem transposeRows_length (n : ℕ) (rs : Rows) :
    (transposeRows n rs).length = n := tabRows_length ..

theorem transposeRows_columns (rs : List (Fin n → F₃)) :
    transposeRows n (rs.map List.ofFn) = (columns rs).map List.ofFn := by
  unfold columns
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hn : i < n := by simpa using hi
  have hb := tabRows_row_length (List.getElem_mem (l := transposeRows n (rs.map List.ofFn)) hi)
  simp only [List.getElem_map,List.getElem_finRange]
  apply List.ext_getElem (by simpa using hb)
  intro j hj hj'
  have hj' : j < rs.length := by simpa using hj'
  have h := tabRows_cell n (rs.map List.ofFn).length
    (fun i j => cell (rs.map List.ofFn) j i) hn (by simpa using hj')
  change ((transposeRows n (rs.map List.ofFn)).getD i []).getD j 0 =
    ((rs.map List.ofFn).getD j []).getD i 0 at h
  have hrow : j < (rs.map List.ofFn).length := by simpa only [List.length_map] using hj'
  rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj,
    List.getD_eq_getElem _ _ hrow,List.getElem_map] at h
  let k : Fin n := ⟨i,hn⟩
  have hk := BooleanFibres.ofFn_getD (rs.get ⟨j,hj'⟩) k 0
  simp only [List.getElem_ofFn,FibreEnumeration.column]
  exact h.trans hk

def indexOf (cs : Rows) (r : Row) : ℕ := @List.idxOf Row instBEqOfDecidableEq r cs

def separating (cols : Rows) (height : ℕ) : List ℕ :=
  ((CanonicalSourceColour.basisRows height cols cols).map (indexOf cols)).filter (fun i => decide (i < cols.length))

private theorem ofFn_idxOf {k : ℕ} (rs : List (Fin k → F₃)) (v : Fin k → F₃) :
    indexOf (rs.map List.ofFn) (List.ofFn v) = rs.idxOf v := by
  unfold indexOf
  induction rs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons,List.idxOf_cons,beq_iff_eq,List.ofFn_inj,ih]

theorem separating_eq (rs : List (Fin n → F₃)) :
    separating (transposeRows n (rs.map List.ofFn)) rs.length =
      (FibreEnumeration.separating rs).map Fin.val := by
  have hlen : (columns rs).length = n := by simp [columns]
  unfold separating FibreEnumeration.separating chosen
  rw [transposeRows_columns,CanonicalSourceColour.basisRows_eq,List.map_map,List.length_map,hlen,
    ← List.filterMap_eq_filter,List.filterMap_map,List.map_filterMap]
  apply List.filterMap_congr
  intro v _
  simp only [Function.comp_def,ofFn_idxOf,Option.guard]
  split <;> simp_all

def restrictRows (cols : Rows) (js : List ℕ) : Rows := js.map (fun i => cols.getD i [])

def targetRow (js : List ℕ) (v : Row) (bits : QWord 2) : Row :=
  (List.range js.length).map fun i => ((bits.getD i 0).val : F₃) - v.getD (js.getD i 0) 0

def plus (n : ℕ) (a b : Row) : Row :=
  (List.range n).map fun i => a.getD i 0 + b.getD i 0

theorem plus_eq (a b : Fin n → F₃) : plus n (List.ofFn a) (List.ofFn b) = List.ofFn (a+b) := by
  unfold plus
  apply List.ext_getElem (by simp)
  intro i hi hi'
  let j : Fin n := ⟨i,by simpa using hi'⟩
  simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  rw [BooleanFibres.ofFn_getD a j,BooleanFibres.ofFn_getD b j]
  rfl

def allowed (v : F₃) : Bool := decide (v = 0 ∨ v = 1)

def candidate (height : ℕ) (cols : Rows) (js : List ℕ) (v : Row) (bits : QWord 2) :
    Option Row := do
  let a ← CanonicalAffine.solve ((height,restrictRows cols js),targetRow js v bits)
  let u := plus cols.length v (SourceSpectrum.applyRows height cols a)
  if u.all allowed then some u else none

private theorem restrictRows_eq (rs : List (Fin n → F₃)) :
    let cols := transposeRows n (rs.map List.ofFn)
    let js := (FibreEnumeration.separating rs).map Fin.val
    restrictRows cols js = matrixRows (restrictedMatrix rs) := by
  unfold restrictRows
  simp only [transposeRows_columns,List.map_map]
  apply List.ext_getElem (by simp [matrixRows])
  intro i hi hj
  simp only [matrixRows,Function.comp_def,List.getElem_map,List.getElem_ofFn]
  let j := (FibreEnumeration.separating rs)[i]'(by simpa [matrixRows] using hj)
  change ((columns rs).map List.ofFn).getD j.val [] = List.ofFn (FibreEnumeration.column rs j)
  have hr : j.val < ((columns rs).map List.ofFn).length := by simpa [columns] using j.isLt
  rw [List.getD_eq_getElem _ _ hr]
  simp [columns]

private theorem targetRow_eq (rs : List (Fin n → F₃)) (v : Fin n → F₃) (bits : QWord 2) :
    targetRow ((FibreEnumeration.separating rs).map Fin.val) (List.ofFn v) bits =
      List.ofFn (target rs v bits) := by
  unfold targetRow target
  apply List.ext_getElem (by simp)
  intro i hi hj
  let k : Fin (FibreEnumeration.separating rs).length := ⟨i,by simpa using hj⟩
  let j := (FibreEnumeration.separating rs).get k
  have hk : i < ((FibreEnumeration.separating rs).map Fin.val).length := by
    simpa only [List.length_map] using k.isLt
  simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ hk,List.getElem_map]
  change ((bits.getD i 0).val : F₃) - (List.ofFn v).getD j.val 0 = ((bits.getD i 0).val : F₃) - v j
  rw [BooleanFibres.ofFn_getD v j]

private theorem readMatrix (A : TernaryMatrix ℓ n) :
    asMatrix (matrixRows A) ℓ n = A := by
  funext i j
  unfold asMatrix cell matrixRows
  rw [BooleanFibres.ofFn_getD (fun i => List.ofFn (A i)) i,BooleanFibres.ofFn_getD (A i) j]

theorem candidate_eq (rs : List (Fin n → F₃)) (v : Fin n → F₃) (bits : QWord 2) :
    let cols := transposeRows n (rs.map List.ofFn)
    let js := (FibreEnumeration.separating rs).map Fin.val
    candidate rs.length cols js (List.ofFn v) bits =
      (do
        let a ← solveAffine (restrictedMatrix rs) (target rs v bits)
        let u := v + FibreEnumeration.image rs a
        if FibreEnumeration.check u then some u else none).map List.ofFn := by
  dsimp only
  unfold candidate
  rw [restrictRows_eq rs,targetRow_eq]
  have hs := CanonicalAffine.solve_represents
    ((rs.length,matrixRows (restrictedMatrix rs)),List.ofFn (target rs v bits))
    (by simp [matrixRows]) rfl (readMatrix (restrictedMatrix rs))
    (by funext i; exact BooleanFibres.ofFn_getD _ i 0)
  rw [hs]
  cases h : solveAffine (restrictedMatrix rs) (target rs v bits) with
  | none => rfl
  | some a =>
    let A : TernaryMatrix n rs.length := fun i j => FibreEnumeration.column rs i j
    have he : transposeRows n (rs.map List.ofFn) = matrixRows A := by
      rw [transposeRows_columns]
      have hf : List.finRange n = List.ofFn (fun i : Fin n => i) := rfl
      simp [A,columns,matrixRows,hf,List.map_ofFn,Function.comp_def]
    let u := plus n (List.ofFn v) (SourceSpectrum.applyRows rs.length
      (matrixRows A) (List.ofFn a))
    simp only [he,Option.map_some,matrixRows,List.length_ofFn]
    change (if u.all allowed then some u else none) =
      (if FibreEnumeration.check (v+FibreEnumeration.image rs a) then some (v+FibreEnumeration.image rs a)
        else none).map List.ofFn
    have hu : u = List.ofFn (v+FibreEnumeration.image rs a) := by
      unfold u
      rw [SourceSpectrum.applyRows_matrix_eq A a,
        show A.mulVec a = FibreEnumeration.image rs a from rfl,plus_eq]
    rw [hu]
    have hc (u : Fin n → F₃) : (List.ofFn u).all allowed = FibreEnumeration.check u := by
      apply Bool.eq_iff_iff.mpr
      simp [allowed,FibreEnumeration.check,List.all_eq_true,List.mem_ofFn]
    simp [hc]

abbrev EnumerateInput := ℕ × (MatrixInput × Row)

def enumerate (x : EnumerateInput) : Rows :=
  let cols := transposeRows x.2.1.1 x.2.1.2
  let js := separating cols x.2.1.2.length
  if js.length ≤ Nat.log 2 x.1 then
    (wordsOfLength 2 (min js.length (Nat.log 2 x.1))).filterMap
      (candidate x.2.1.2.length cols js x.2.2)
  else []

theorem sufficient_budget {q b t : ℕ} (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : UniformParameters.minLength q b t ≤ ℓ) :
    UniformParameters.componentCutoff q b t ℓ ≤ Nat.log 2 ℓ := by
  have h := UniformParameters.boolean_budget hq hb ht hstart
  have hrec : 1 ≤ UniformParameters.reciprocal q b t := by
    unfold UniformParameters.reciprocal UniformParameters.edits
    have ht' : 0 < t := by omega
    have hpos : 0 < 2^20 * (2*t)^2 * (b+1) * (UniformParameters.alphabetBits q+1) := by positivity
    omega
  have hp : 2^(UniformParameters.componentCutoff q b t ℓ) ≤ ℓ := by
    apply le_trans _ h
    nth_rw 1 [← pow_one (2^(UniformParameters.componentCutoff q b t ℓ))]
    exact Nat.pow_le_pow_right (by positivity) hrec
  exact Nat.le_log_of_pow_le (by decide) hp

theorem enumerate_eq (rs : List (Fin n → F₃)) (v : Fin n → F₃)
    (h : (FibreEnumeration.separating rs).length ≤ Nat.log 2 ℓ) :
    enumerate (ℓ,((n,rs.map List.ofFn),List.ofFn v)) =
      (FibreEnumeration.enumerate rs v).map List.ofFn := by
  unfold enumerate FibreEnumeration.enumerate
  simp only [List.length_map,separating_eq, h, Nat.min_eq_left h,↓reduceIte,List.map_filterMap]
  apply List.filterMap_congr
  intro bits _
  exact candidate_eq rs v bits

theorem enumerate_uniform_eq {q b t : ℕ} (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : UniformParameters.minLength q b t ≤ ℓ) (rs : List (Fin n → F₃))
    (v : Fin n → F₃) (hr : rs.length ≤ UniformParameters.componentCutoff q b t ℓ) :
    enumerate (ℓ,((n,rs.map List.ofFn),List.ofFn v)) =
      (FibreEnumeration.enumerate rs v).map List.ofFn :=
  enumerate_eq rs v ((FibreEnumeration.separating_length rs).trans (hr.trans
    (sufficient_budget hq hb ht hstart)))

theorem transposeRows_polyTime :
    ComputableInPolyTime (fun x : MatrixInput => transposeRows x.1 x.2) matrixEncoding rowsEncoding := by
  let e := matrixEncoding
  let p := encPair e encUnary
  have h := fst encUnary rowsEncoding
  have hs := snd encUnary rowsEncoding
  unfold transposeRows
  exact tabRows_polyTime (f := fun x i j => cell x.2 j i) h
    ((length_list rowEncoding).comp hs)
    (cell_polyTime (hs.comp ((fst e encUnary).comp (fst p encUnary)))
      (snd p encUnary) ((snd e encUnary).comp (fst p encUnary)))

abbrev indicesEncoding := encList encUnary

theorem separating_polyTime :
    ComputableInPolyTime (fun x : MatrixInput => separating x.2 x.1)
      matrixEncoding indicesEncoding := by
  let e := matrixEncoding
  have hn := fst encUnary rowsEncoding
  have hc := snd encUnary rowsEncoding
  have hB := CanonicalSourceColour.basisRows_polyTime.comp (encIn := e)
    (encMid := CanonicalSourceColour.basisEncoding) (hn.prod (hc.prod hc))
  have hj := idxOfWithInput (encA := rowEncoding) (encIn := encPair e rowEncoding)
    (hc.comp (fst e rowEncoding)) (snd e rowEncoding)
  have h := mapWithInput (encIn := e) (encA := rowEncoding) (encB := encUnary)
    (f := fun x v => indexOf x.2 v) hB (by
      simpa only [indexOf,Function.comp_def] using hj)
  have hs := unary_lt' (snd e encUnary)
    ((length_list rowEncoding).comp (hc.comp (fst e encUnary)))
  exact filterWithInput (encIn := e) (encA := encUnary)
    (test := fun x i => decide (i < x.2.length)) h (hs.of_enc_eq (fun _ => rfl))

abbrev restrictionsEncoding := encPair rowsEncoding indicesEncoding

theorem restrictRows_polyTime :
    ComputableInPolyTime (fun x : Rows × List ℕ => restrictRows x.1 x.2)
      restrictionsEncoding rowsEncoding := by
  let e := restrictionsEncoding
  have hg := fst rowsEncoding indicesEncoding
  have hj := snd rowsEncoding indicesEncoding
  unfold restrictRows
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := rowEncoding)
    (f := fun x i => x.1.getD i []) hj
    (listGetDWithInput (hg.comp (fst e encUnary)) (snd e encUnary) ([] : Row))

abbrev targetEncoding := encPair (encPair indicesEncoding rowEncoding) (wordEncoding 2)

theorem targetRow_polyTime :
    ComputableInPolyTime (fun x : (List ℕ × Row) × QWord 2 => targetRow x.1.1 x.1.2 x.2)
      targetEncoding rowEncoding := by
  let e := targetEncoding
  let r := encPair indicesEncoding rowEncoding
  let h := fst r (wordEncoding 2)
  let e' := encPair e encUnary
  have hd := h.comp (fst e encUnary)
  have hi := snd e encUnary
  have hb := (snd r (wordEncoding 2)).comp (fst e encUnary)
  have hz := listGetDWithInput hd.fst' hi 0
  have hv := listGetDWithInput hd.snd' hz 0
  have hf : ComputableInPolyTime (fun a : Fin 2 => (a.val : F₃))
      (ExceptionalRecords.letterEncoding 2) tritEncoding := of_finite _
  have ha := hf.comp (encIn := e') (listGetDWithInput hb hi (0 : Fin 2))
  have hsub : ComputableInPolyTime (fun p : F₃ × F₃ => p.1-p.2)
      (encPair tritEncoding tritEncoding) tritEncoding := of_finite _
  have hs := hsub.comp (encIn := e') (ha.prod hv)
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := tritEncoding)
    (f := fun x i => ((x.2.getD i 0).val : F₃) - x.1.2.getD (x.1.1.getD i 0) 0)
    (unary_range' ((length_list encUnary).comp h.fst')) (hs.of_enc_eq (fun _ => rfl))

abbrev plusEncoding := encPair encUnary (encPair rowEncoding rowEncoding)

theorem plus_polyTime :
    ComputableInPolyTime (fun x : ℕ × (Row × Row) => plus x.1 x.2.1 x.2.2)
      plusEncoding rowEncoding := by
  let e := plusEncoding
  have hn := fst encUnary (encPair rowEncoding rowEncoding)
  have hs := (snd encUnary (encPair rowEncoding rowEncoding)).comp (fst e encUnary)
  have hi := snd e encUnary
  have h := (show ComputableInPolyTime (fun a : F₃ × F₃ => a.1+a.2)
      (encPair tritEncoding tritEncoding) tritEncoding from of_finite _).comp
    ((listGetDWithInput hs.fst' hi 0).prod (listGetDWithInput hs.snd' hi 0))
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := tritEncoding)
    (f := fun x i => x.2.1.getD i 0 + x.2.2.getD i 0) (unary_range' hn)
    (h.of_enc_eq (fun _ => rfl))

theorem allowed_polyTime : ComputableInPolyTime allowed tritEncoding encBool := of_finite _

abbrev CandidateInput := (MatrixInput × (List ℕ × Row)) × QWord 2
abbrev candidateEncoding := encPair (encPair matrixEncoding (encPair indicesEncoding rowEncoding)) (wordEncoding 2)

theorem candidate_polyTime :
    ComputableInPolyTime (fun x : CandidateInput =>
      candidate x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2 x.2) candidateEncoding (encOption rowEncoding) := by
  let e := candidateEncoding
  let m := encPair matrixEncoding (encPair indicesEncoding rowEncoding)
  let p := encPair e rowEncoding
  have hx := fst m (wordEncoding 2)
  have hbits := snd m (wordEncoding 2)
  have hcols := hx.fst'.snd'
  have hheight := hx.fst'.fst'
  have hjs := hx.snd'.fst'
  have hrestr := restrictRows_polyTime.comp (encIn := e) (encMid := restrictionsEncoding)
    (hcols.prod hjs)
  have ht := targetRow_polyTime.comp (encIn := e) (encMid := targetEncoding) (hx.snd'.prod hbits)
  have ha := CanonicalAffine.solve_polyTime.comp (encIn := e) (encMid := affineEncoding)
    ((hheight.prod hrestr).prod ht)
  have h := fst e rowEncoding
  have hi := SourceSpectrum.applyRows_polyTime.comp (encIn := p)
    (encMid := SourceSpectrum.applyEncoding) ((hx.fst'.comp h).prod (snd e rowEncoding))
  have hlen := (length_list rowEncoding).comp (hcols.comp h)
  have hu := plus_polyTime.comp (encIn := p) (encMid := plusEncoding)
    (hlen.prod ((hx.snd'.snd'.comp h).prod hi))
  have hgood : ComputableInPolyTime (fun v : Row => v.all allowed) rowEncoding encBool :=
    allWithInput (encIn := rowEncoding) (encA := tritEncoding) (test := fun _ a => allowed a) id'
      (allowed_polyTime.comp (snd rowEncoding tritEncoding))
  have hout := ((hgood.comp hu).ite' ((optionSome rowEncoding).comp hu) (const none))
  have hop := optionElimWithInput (encA := e) (encB := rowEncoding) (encC := encOption rowEncoding)
    (body := fun x a =>
      let u := plus x.1.1.2.length x.1.2.2 (SourceSpectrum.applyRows x.1.1.1 x.1.1.2 a)
      if u.all allowed then some u else none) (ha.of_enc_eq (fun _ => rfl)) (const none)
    (hout.of_enc_eq (fun _ => rfl))
  refine hop.of_enc_eq ?_
  intro x
  unfold candidate
  simp only [Function.comp_def]
  cases CanonicalAffine.solve ((x.1.1.1,restrictRows x.1.1.2 x.1.2.1),
    targetRow x.1.2.1 x.1.2.2 x.2) <;> rfl

abbrev enumerateEncoding := encPair encUnary affineEncoding

theorem enumerate_polyTime :
    ComputableInPolyTime enumerate enumerateEncoding rowsEncoding := by
  let e := enumerateEncoding
  let out := wordEncoding 2
  let p := encPair e out
  have hℓ := fst encUnary affineEncoding
  have hs := snd encUnary affineEncoding
  have hcols := transposeRows_polyTime.comp (encIn := e) hs.fst'
  have hheight := (length_list rowEncoding).comp hs.fst'.snd'
  have hj := separating_polyTime.comp (encIn := e) (encMid := matrixEncoding) (hheight.prod hcols)
  have hnum := (length_list encUnary).comp hj
  have hlog := unary_log_two.comp hℓ
  have hm := unary_min' hnum hlog
  have hbound : PolyBounded (fun x : EnumerateInput => (e x).length)
      (fun x => 2^(min (separating (transposeRows x.2.1.1 x.2.1.2) x.2.1.2.length).length (Nat.log 2 x.1))) := by
    apply (hℓ.polyBounded_length.add (.const 1)).mono
    intro x
    rw [encUnary_apply,List.length_replicate]
    apply (Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _)).trans
    by_cases h0 : x.1 = 0
    · simp [h0]
    · have hp := Nat.pow_log_le_self 2 h0
      omega
  have hwords := wordsOfLength_polyTime (q := 2) (by decide) hm hbound
  have hx := fst e out
  have hconfig := (hheight.prod hcols).prod (hj.prod hs.snd')
  have happ := candidate_polyTime.comp (encIn := p) (encMid := candidateEncoding)
    ((hconfig.comp hx).prod (snd e out))
  have hlist : ComputableInPolyTime (Option.toList (α := Row)) (encOption rowEncoding) rowsEncoding := by
    have h := optionElimWithInput (encA := encOption rowEncoding) (encB := rowEncoding)
      (encC := rowsEncoding) (body := fun _ v => [v]) id' (const [])
      (cons' (snd (encOption rowEncoding) rowEncoding) (const []))
    exact h.of_enc_eq (fun x => by cases x <;> rfl)
  have hpass := hlist.comp (encIn := p) happ
  have hf := flatMapWithInput (encIn := e) (encA := out) (encB := rowEncoding)
    (f := fun x w => (candidate x.2.1.2.length (transposeRows x.2.1.1 x.2.1.2)
      (separating (transposeRows x.2.1.1 x.2.1.2) x.2.1.2.length) x.2.2 w).toList)
    hwords (hpass.of_enc_eq (fun _ => rfl))
  have h := (unary_le' hnum hlog).ite' hf (const [])
  refine h.of_enc_eq ?_
  intro x
  simp only [Function.comp_def,enumerate,List.filterMap_eq_flatMap_toList,decide_eq_true_eq]

#print axioms enumerate_eq
#print axioms enumerate_uniform_eq
#print axioms enumerate_polyTime

end DeletionCode.Explicit.Machine.SourceFibre
