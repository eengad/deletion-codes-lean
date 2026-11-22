import DeletionCode.Explicit.Machine.SourceFibre

/-! Component exposure on the serialized rule rows used by the recognizer. -/
namespace DeletionCode.Explicit.Machine.SourceExposure

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open FieldHash Ternary
open SourceFibre (allowed enumerate)

variable {m n ℓ q b t : ℕ}

abbrev Components := List Rows
abbrev ExposureInput := (ℕ × (ℕ × Components)) × (Row × Row)

def occupied (rs : Rows) (j : ℕ) : Bool :=
  rs.any (fun r => decide (r.getD j 0 ≠ 0))

def outside (n : ℕ) (ps : Components) (v δ : Row) : Bool :=
  (List.range n).all fun j => ps.any (fun rows => occupied rows j) ||
    allowed (v.getD j 0 + δ.getD j 0)

def inside (n : ℕ) (rs : Rows) (u δ : Row) : Bool :=
  (List.range n).all fun j => !occupied rs j || allowed (u.getD j 0 + δ.getD j 0)

def check (x : ExposureInput) : Bool :=
  let ℓ := x.1.1
  let n := x.1.2.1
  let ps := x.1.2.2
  let v := x.2.1
  let δ := x.2.2
  outside n ps v δ && ps.all (fun rs =>
    (enumerate (ℓ,((n,rs),v))).any (fun u => inside n rs u δ))

private theorem occupied_eq (rs : List (Fin n → F₃)) (j : Fin n) :
    occupied (rs.map List.ofFn) j.val = ComponentExposure.occupies rs j := by
  apply Bool.eq_iff_iff.mpr
  rw [ComponentExposure.occupies_iff]
  simp only [occupied,List.any_map,Function.comp_def,List.any_eq_true,decide_eq_true_eq]
  simp only [BooleanFibres.ofFn_getD]

private theorem outside_eq (ps : Fin m → List (Fin n → F₃)) (v δ : Fin n → F₃) :
    outside n (List.ofFn (fun i => (ps i).map List.ofFn)) (List.ofFn v) (List.ofFn δ) =
      (List.finRange n).all (fun j =>
        (List.finRange m).any (fun i => ComponentExposure.occupies (ps i) j) ||
        (v j+δ j == 0 || v j+δ j == 1)) := by
  unfold outside
  rw [show List.range n = (List.finRange n).map Fin.val from by simp,List.all_map]
  apply congrArg ((List.finRange n).all)
  funext j
  have he : (List.ofFn (fun i => (ps i).map List.ofFn)).any (fun rs => occupied rs j.val) =
      (List.finRange m).any (fun i => ComponentExposure.occupies (ps i) j) := by
    have hr : List.finRange m = List.ofFn (fun i : Fin m => i) := rfl
    have hparts : List.ofFn (fun i => (ps i).map List.ofFn) =
        (List.finRange m).map (fun i => (ps i).map List.ofFn) := by
      simp [hr,List.map_ofFn,Function.comp_def]
    rw [hparts,List.any_map]
    apply congrArg ((List.finRange m).any)
    funext i
    exact occupied_eq (ps i) j
  simp only [Function.comp_def,he,BooleanFibres.ofFn_getD]
  congr 1

private theorem inside_eq (rs : List (Fin n → F₃)) (u δ : Fin n → F₃) :
    inside n (rs.map List.ofFn) (List.ofFn u) (List.ofFn δ) =
      (List.finRange n).all (fun j =>
        !ComponentExposure.occupies rs j || (u j+δ j == 0 || u j+δ j == 1)) := by
  unfold inside
  rw [show List.range n = (List.finRange n).map Fin.val from by simp,List.all_map]
  apply congrArg ((List.finRange n).all)
  funext j
  simp only [Function.comp_def,occupied_eq,BooleanFibres.ofFn_getD]
  congr 1

theorem check_eq (ps : Fin m → List (Fin n → F₃)) (v δ : Fin n → F₃)
    (hr : ∀ i, (FibreEnumeration.separating (ps i)).length ≤ Nat.log 2 ℓ) :
    check ((ℓ,(n,List.ofFn (fun i => (ps i).map List.ofFn))),(List.ofFn v,List.ofFn δ)) =
      ComponentExposure.check ps v δ := by
  unfold check ComponentExposure.check
  dsimp only
  rw [outside_eq]
  have he : List.finRange m = List.ofFn (fun i : Fin m => i) := rfl
  have hparts : List.ofFn (fun i => (ps i).map List.ofFn) =
      (List.finRange m).map (fun i => (ps i).map List.ofFn) := by
    simp [he,List.map_ofFn,Function.comp_def]
  rw [hparts,List.all_map]
  congr 1
  apply congrArg ((List.finRange m).all)
  funext i
  simp only [Function.comp_def,SourceFibre.enumerate_eq _ _ (hr i),List.any_map,inside_eq]
  rfl

theorem check_uniform_eq (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : UniformParameters.minLength q b t ≤ ℓ)
    (ps : Fin m → List (Fin n → F₃)) (v δ : Fin n → F₃)
    (hr : ∀ i, (ps i).length ≤ UniformParameters.componentCutoff q b t ℓ) :
    check ((ℓ,(n,List.ofFn (fun i => (ps i).map List.ofFn))),(List.ofFn v,List.ofFn δ)) =
      ComponentExposure.check ps v δ :=
  check_eq ps v δ (fun i => (FibreEnumeration.separating_length _).trans
    ((hr i).trans (SourceFibre.sufficient_budget hq hb ht hstart)))

theorem candidates_uniform_count (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : UniformParameters.minLength q b t ≤ ℓ) (rs : List (Fin n → F₃)) (v : Fin n → F₃)
    (hr : rs.length ≤ UniformParameters.componentCutoff q b t ℓ) :
    ((enumerate (ℓ,((n,rs.map List.ofFn),List.ofFn v))).length)^(UniformParameters.reciprocal q b t) ≤ ℓ := by
  rw [SourceFibre.enumerate_uniform_eq hq hb ht hstart rs v hr,List.length_map]
  exact (Nat.pow_le_pow_left ((FibreEnumeration.enumerate_length rs v).trans
    (Nat.pow_le_pow_right (by decide) hr)) _).trans (UniformParameters.boolean_budget hq hb ht hstart)

abbrev occupiedEncoding := encPair rowsEncoding encUnary
abbrev componentsEncoding := encList rowsEncoding
abbrev rowPairEncoding := encPair rowEncoding rowEncoding

theorem occupied_polyTime :
    ComputableInPolyTime (fun x : Rows × ℕ => occupied x.1 x.2)
      occupiedEncoding encBool := by
  let e := occupiedEncoding
  let p := encPair e rowEncoding
  have hj := (snd rowsEncoding encUnary).comp (fst e rowEncoding)
  have hv := listGetDWithInput (snd e rowEncoding) hj 0
  exact anyWithInput (encIn := e) (encA := rowEncoding)
    (test := fun x r => decide (r.getD x.2 0 ≠ 0)) (fst rowsEncoding encUnary)
    ((bool_not.comp (hv.decide_eq' (const 0))).of_enc_eq (fun _ => rfl))

private theorem allowedSum_polyTime :
    ComputableInPolyTime (fun x : (Row × Row) × ℕ =>
      allowed (x.1.1.getD x.2 0+x.1.2.getD x.2 0))
      (encPair rowPairEncoding encUnary) encBool := by
  let e := encPair rowPairEncoding encUnary
  have hx := fst rowPairEncoding encUnary
  have hj := snd rowPairEncoding encUnary
  have hp : ComputableInPolyTime (fun a : F₃ × F₃ => a.1+a.2)
      (encPair tritEncoding tritEncoding) tritEncoding := of_finite _
  have h := hp.comp (encIn := e)
    ((listGetDWithInput hx.fst' hj 0).prod (listGetDWithInput hx.snd' hj 0))
  exact (SourceFibre.allowed_polyTime.comp (encIn := e) h).of_enc_eq (fun _ => rfl)

abbrev outsideEncoding := encPair (encPair encUnary componentsEncoding) rowPairEncoding
abbrev insideEncoding := encPair (encPair encUnary rowsEncoding) rowPairEncoding

theorem outside_polyTime :
    ComputableInPolyTime (fun x : (ℕ × Components) × (Row × Row) =>
      outside x.1.1 x.1.2 x.2.1 x.2.2) outsideEncoding encBool := by
  let e := outsideEncoding
  let p := encPair e encUnary
  have h := fst (encPair encUnary componentsEncoding) rowPairEncoding
  have hx := fst e encUnary
  have hi := snd e encUnary
  have hp := h.snd'.comp hx
  have hwhere := occupied_polyTime.comp (encIn := encPair p rowsEncoding)
    (encMid := occupiedEncoding) ((snd p rowsEncoding).prod (hi.comp (fst p rowsEncoding)))
  have hocc := anyWithInput (encIn := p) (encA := rowsEncoding)
    (test := fun x rs => occupied rs x.2) hp (hwhere.of_enc_eq (fun _ => rfl))
  have hsum := allowedSum_polyTime.comp (encIn := p) (encMid := encPair rowPairEncoding encUnary)
    (((snd (encPair encUnary componentsEncoding) rowPairEncoding).comp hx).prod hi)
  exact allWithInput (encIn := e) (encA := encUnary)
    (test := fun x j => x.1.2.any (fun r => occupied r j) ||
      allowed (x.2.1.getD j 0 + x.2.2.getD j 0))
    (unary_range' h.fst') ((bool_or' hocc hsum).of_enc_eq (fun _ => rfl))

theorem inside_polyTime :
    ComputableInPolyTime (fun x : (ℕ × Rows) × (Row × Row) =>
      inside x.1.1 x.1.2 x.2.1 x.2.2) insideEncoding encBool := by
  let e := insideEncoding
  let p := encPair e encUnary
  have h := fst (encPair encUnary rowsEncoding) rowPairEncoding
  have hx := fst e encUnary
  have hi := snd e encUnary
  have hocc := occupied_polyTime.comp (encIn := p) (encMid := occupiedEncoding)
    ((h.snd'.comp hx).prod hi)
  have hsum := allowedSum_polyTime.comp (encIn := p) (encMid := encPair rowPairEncoding encUnary)
    (((snd (encPair encUnary rowsEncoding) rowPairEncoding).comp hx).prod hi)
  exact allWithInput (encIn := e) (encA := encUnary) (test := fun x j =>
    !occupied x.1.2 j || allowed (x.2.1.getD j 0 + x.2.2.getD j 0))
    (unary_range' h.fst') ((bool_or' (bool_not.comp hocc) hsum).of_enc_eq (fun _ => rfl))

abbrev exposureEncoding := encPair (encPair encUnary (encPair encUnary componentsEncoding)) rowPairEncoding

theorem check_polyTime : ComputableInPolyTime check exposureEncoding encBool := by
  let e := exposureEncoding
  let p := encPair e rowsEncoding
  let r := encPair p rowEncoding
  let d := encPair encUnary (encPair encUnary componentsEncoding)
  have hd := fst d rowPairEncoding
  have hv := snd d rowPairEncoding
  have hout := outside_polyTime.comp (encIn := e) (encMid := outsideEncoding) (hd.snd'.prod hv)
  have hx := fst e rowsEncoding
  have hn := hd.snd'.fst'.comp hx
  have hh := SourceFibre.enumerate_polyTime.comp (encIn := p) (encMid := SourceFibre.enumerateEncoding)
    ((hd.fst'.comp hx).prod ((hn.prod (snd e rowsEncoding)).prod (hv.fst'.comp hx)))
  have hi := inside_polyTime.comp (encIn := r) (encMid := insideEncoding)
    (((hn.prod (snd e rowsEncoding)).comp (fst p rowEncoding)).prod
      ((snd p rowEncoding).prod (hv.snd'.comp (hx.comp (fst p rowEncoding)))))
  have he := anyWithInput (encIn := p) (encA := rowEncoding) (test := fun x u =>
    inside x.1.1.2.1 x.2 u x.1.2.2) hh (hi.of_enc_eq (fun _ => rfl))
  have hall := allWithInput (encIn := e) (encA := rowsEncoding)
    (test := fun x rs => (enumerate (x.1.1,((x.1.2.1,rs),x.2.1))).any
      (fun u => inside x.1.2.1 rs u x.2.2))
    hd.snd'.snd' (he.of_enc_eq (fun _ => rfl))
  exact (bool_and' hout hall).of_enc_eq (fun _ => rfl)

#print axioms check_uniform_eq
#print axioms candidates_uniform_count
#print axioms check_polyTime

end DeletionCode.Explicit.Machine.SourceExposure
