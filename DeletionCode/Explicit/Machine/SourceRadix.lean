import DeletionCode.Explicit.MixedRadix
import DeletionCode.Explicit.Machine.SourceLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.ListProd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeRadix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder

/-! Binary mixed-radix arithmetic and fixed-width digit tables. -/
namespace DeletionCode.Explicit.Machine.SourceRadix

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open SourceLists

abbrev numbersEncoding := encList encNat
abbrev pairEncoding := encPair encNat encNat
abbrev rankEncoding := encPair numbersEncoding numbersEncoding
abbrev unrankEncoding := encPair numbersEncoding encNat

def rankStep (acc : Option ℕ) (p : ℕ × ℕ) : Option ℕ :=
  if p.2 < p.1 then acc.map (fun a => a*p.1+p.2) else none

def rank (rs vs : List ℕ) : Option ℕ :=
  if rs.length = vs.length then (rs.zip vs).foldl rankStep (some 0) else none

private theorem rank_fold_none (xs : List (ℕ × ℕ)) : xs.foldl rankStep none = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, show rankStep none x = none by simp [rankStep],ih]

private theorem rank_fold_eq (rs vs : List ℕ) (a : ℕ) (h : rs.length = vs.length) :
    (rs.zip vs).foldl rankStep (some a) =
      (MixedRadix.rank rs vs).map (fun k => a*rs.prod+k.val) := by
  induction rs generalizing vs a with
  | nil =>
    cases vs with
    | nil => simp [MixedRadix.rank]
    | cons v vs => simp at h
  | cons r rs ih =>
    cases vs with
    | nil => simp at h
    | cons v vs =>
      have hh : rs.length = vs.length := by simpa using h
      by_cases hv : v < r
      · simp only [List.zip_cons_cons,List.foldl_cons,rankStep,hv,↓reduceIte,Option.map_some,
          MixedRadix.rank,↓reduceDIte]
        rw [ih _ _ hh]
        cases MixedRadix.rank rs vs with
        | none => rfl
        | some k =>
          change some ((a*r+v)*rs.prod+k.val) = some (a*(r*rs.prod)+(k.val+rs.prod*v))
          congr 1
          ring
      · simp [List.zip_cons_cons,List.foldl_cons,rankStep,hv,MixedRadix.rank,rank_fold_none]

private theorem rank_length {rs vs : List ℕ} {k : Fin rs.prod}
    (h : MixedRadix.rank rs vs = some k) : rs.length = vs.length := by
  induction rs generalizing vs with
  | nil => cases vs <;> simp_all [MixedRadix.rank]
  | cons r rs ih =>
    cases vs with
    | nil => simp [MixedRadix.rank] at h
    | cons v vs =>
      simp only [MixedRadix.rank] at h
      split at h
      · obtain ⟨w,he,_⟩ := Option.map_eq_some_iff.mp h
        simpa using ih he
      · contradiction

theorem rank_eq (rs vs : List ℕ) : rank rs vs = (MixedRadix.rank rs vs).map Fin.val := by
  unfold rank
  split
  · rename_i h
    simpa [rank_fold_eq rs vs 0 h]
  · rename_i h
    cases e : MixedRadix.rank rs vs with
    | none => rfl
    | some k => exact (h (rank_length e)).elim

private theorem rankStep_polyTime :
    ComputableInPolyTime (fun x : Option ℕ × (ℕ × ℕ) => rankStep x.1 x.2)
      (encPair (encOption encNat) pairEncoding) (encOption encNat) := by
  let e := encPair (encOption encNat) pairEncoding
  let s := encPair e encNat
  have h := snd (encOption encNat) pairEncoding
  have hpar := h.comp (fst e encNat)
  have hr := binary_add' (binary_mul' (snd e encNat) hpar.fst') hpar.snd'
  have hcalc := optionMapWithInput (encA := e) (encB := encNat) (encC := encNat)
    (f := fun x a => a*x.2.1+x.2.2) (fst (encOption encNat) pairEncoding) hr
  exact ((binary_lt' h.snd' h.fst').ite' hcalc (const none)).of_enc_eq
    (fun _ => by simp [rankStep,Function.comp_def])

theorem rank_polyTime :
    ComputableInPolyTime (fun x : List ℕ × List ℕ => rank x.1 x.2) rankEncoding (encOption encNat) := by
  let e := rankEncoding
  let p := pairEncoding
  let o := encOption encNat
  let b := encList p
  have hz := Turing.MultiTapeTM.ComputableInPolyTime.zip encNat encNat
  have hg (x : List ℕ × List ℕ) (a : Option ℕ) (v : ℕ × ℕ) (hv : v ∈ x.1.zip x.2) :
      (o (rankStep a v)).length ≤ (o a).length + (b (x.1.zip x.2)).length + 1 := by
    have he := length_le_encList_of_mem p hv
    change (encPair encNat encNat v).length ≤ (b (x.1.zip x.2)).length at he
    simp only [length_encPair,encNat_apply,Nat.size_eq_bits_len] at he
    unfold rankStep
    split
    · cases a with
      | none => simp [o]
      | some a =>
        have hs := Nat.size_add_le (a*v.1) v.2
        have hm := Nat.size_mul_le a v.1
        simp only [Option.map_some,o,encOption_some,List.length_cons,encNat_apply,Nat.size_eq_bits_len]
        omega
    · simp [o]
  have h := foldlWith_of_bounded_growth (encA := p) (encL := b) (encB := o)
    (par := fun _ : List ℕ × List ℕ => false) (step := fun _ => rankStep)
    (const false) hz (const (some 0))
    (rankStep_polyTime.comp (((fst (encPair encBool o) p).snd').prod (snd (encPair encBool o) p)))
    (hz.polyBounded_length.add (PolyBounded.const 1)) (fun x a v hv => by
      simpa [Nat.add_assoc] using hg x a v hv)
  have hl := (length_list encNat).comp (fst numbersEncoding numbersEncoding)
  have hr := (length_list encNat).comp (snd numbersEncoding numbersEncoding)
  exact ((hl.decide_eq' hr).ite' h (const none)).of_enc_eq (fun _ => by simp [rank,o])

def divisors (rs : List ℕ) : List ℕ :=
  (List.range rs.length).map (fun i => (rs.drop (i+1)).prod)

private theorem divisors_cons (r : ℕ) (rs : List ℕ) :
    divisors (r::rs) = rs.prod :: divisors rs := by
  simp [divisors,List.range_succ_eq_map,List.map_map,Function.comp_def,Nat.succ_eq_add_one]

abbrev UnrankState := ℕ × List ℕ
abbrev unrankStateEncoding := encPair encNat numbersEncoding

def strip (st : UnrankState) (d : ℕ) : UnrankState := (st.1%d,st.1/d::st.2)

def unrank (rs : List ℕ) (k : ℕ) : List ℕ :=
  ((divisors rs).foldl strip (k,[])).2.reverse

private theorem unrank_fold_eq (rs : List ℕ) (k : Fin rs.prod) (st : List ℕ) :
    ((divisors rs).foldl strip (k.val,st)).2.reverse = st.reverse++MixedRadix.unrank rs k := by
  induction rs generalizing st with
  | nil => simp [divisors,MixedRadix.unrank]
  | cons r rs ih =>
    have hp : 0 < rs.prod := by
      have hk := k.isLt
      simp only [List.prod_cons] at hk
      exact Nat.pos_of_ne_zero (fun hc =>
        (Nat.ne_of_gt ((Nat.zero_le k.val).trans_lt hk)) (by simp [hc]))
    let p : Fin rs.prod := ⟨k.val%rs.prod,Nat.mod_lt _ hp⟩
    rw [divisors_cons,List.foldl_cons]
    change ((divisors rs).foldl strip (p.val,k.val/rs.prod::st)).2.reverse = _
    rw [ih p]
    rw [MixedRadix.unrank,List.reverse_cons,List.append_assoc]
    rfl

theorem unrank_eq (rs : List ℕ) (k : Fin rs.prod) : unrank rs k.val = MixedRadix.unrank rs k := by
  simpa only [unrank,List.reverse_nil,List.nil_append] using unrank_fold_eq rs k []

theorem divisors_polyTime : ComputableInPolyTime divisors numbersEncoding numbersEncoding := by
  let e := numbersEncoding
  let a := encPair e encUnary
  have h := binary_prod.comp (listDropWithInput (fst e encUnary) (unary_add' (snd e encUnary) (const 1)))
  exact mapWithInput (encIn := e) (encA := encUnary) (encB := encNat)
    (f := fun rs i => (rs.drop (i+1)).prod) (unary_range' (length_list encNat)) h

private theorem strip_polyTime :
    ComputableInPolyTime (fun x : UnrankState × ℕ => strip x.1 x.2)
      (encPair unrankStateEncoding encNat) unrankStateEncoding := by
  have hx := fst unrankStateEncoding encNat
  have hd := snd unrankStateEncoding encNat
  exact (binary_mod' hx.fst' hd).prod (cons' (binary_div' hx.fst' hd) hx.snd')

set_option maxHeartbeats 1000000 in
theorem unrank_polyTime :
    ComputableInPolyTime (fun x : List ℕ × ℕ => unrank x.1 x.2) unrankEncoding numbersEncoding := by
  let e := unrankEncoding
  let p := unrankStateEncoding
  have hx := fst numbersEncoding encNat
  have hk := snd numbersEncoding encNat
  have hl := divisors_polyTime.comp hx
  have hn := (length_list encNat).comp hl
  have hinit := hk.prod (const (encOut := numbersEncoding) [])
  let inv (x : List ℕ × ℕ) (ds : List ℕ) (s : UnrankState) :=
    s.1 ≤ x.2 ∧ s.2.length ≤ ds.length ∧ ∀ a ∈ s.2, a ≤ x.2
  have hs := (PolyBounded.const 2).mul hk.polyBounded_length |>.add (PolyBounded.const 1) |>.add
    ((show PolyBounded (fun x : List ℕ × ℕ => (e x).length)
      (fun x => (divisors x.1).length) by
        simpa only [encUnary_apply,List.length_replicate,Function.comp_def] using hn.polyBounded_length).mul
      (((PolyBounded.const 2).mul hk.polyBounded_length).add (PolyBounded.const 1)))
  have ho := (foldlWith_spec (encA := encNat) (encL := numbersEncoding) (encB := p)
    (step := fun _ : Bool => strip) (const false) hl hinit
    (strip_polyTime.comp (((fst (encPair encBool p) encNat).snd').prod (snd (encPair encBool p) encNat)))
    inv (fun _ => by simp [inv]) (by
      intro x ds s d _ h
      rcases h with ⟨h₁,h₂,h₃⟩
      refine ⟨(Nat.mod_le ..).trans h₁,by simpa [strip] using Nat.succ_le_succ h₂,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact (Nat.div_le_self ..).trans h₁
      · exact h₃ _ ha) hs (by
      intro x ds s hp h
      rcases h with ⟨h₁,h₂,h₃⟩
      have hk : (encNat s.1).length ≤ (encNat x.2).length := by
        simpa only [encNat_apply,← Nat.size_eq_bits_len] using Nat.size_le_size h₁
      have hl : (numbersEncoding s.2).length ≤ (divisors x.1).length*(2*(encNat x.2).length+1) :=
        (length_encList_le encNat s.2 (fun a ha => by
          simpa only [encNat_apply,← Nat.size_eq_bits_len] using Nat.size_le_size (h₃ a ha))).trans
          (Nat.mul_le_mul_right _ (h₂.trans hp.length_le))
      change (p s).length ≤ _
      simp only [p,unrankStateEncoding,length_encPair,Function.comp_def]
      omega)).1
  exact ((listReverse encNat).comp ((snd encNat numbersEncoding).comp ho)).of_enc_eq (fun _ => rfl)

def littleValue (base : ℕ) (ds : List ℕ) : ℕ :=
  ds.reverse.foldl (fun a d => base*a+d) 0

theorem littleValue_eq (base : ℕ) (ds : List ℕ) : littleValue base ds = Nat.ofDigits base ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    unfold littleValue at ih ⊢
    rw [List.reverse_cons,List.foldl_append]
    change base*(ds.reverse.foldl (fun a d => base*a+d) 0)+d = Nat.ofDigits base (d::ds)
    rw [ih,Nat.ofDigits_cons,Nat.add_comm]

set_option maxHeartbeats 850000 in
theorem littleValue_polyTime :
    ComputableInPolyTime (fun x : ℕ × List ℕ => littleValue x.1 x.2)
      (encPair encNat numbersEncoding) encNat := by
  let e := encPair encNat numbersEncoding
  have hb := fst encNat numbersEncoding
  have hd := snd encNat numbersEncoding
  have hr := (listReverse encNat).comp hd
  have hf := fst (encPair encNat encNat) encNat
  have hstep := binary_add' (binary_mul' hf.fst' hf.snd') (snd (encPair encNat encNat) encNat)
  exact foldlWith_of_bounded_growth (encB := encNat)
    (step := fun base a d => base*a+d) hb hr (const 0) hstep
    (hb.polyBounded_length.add hd.polyBounded_length |>.add (PolyBounded.const 1)) (by
      intro x acc d hmem
      have hm : d ∈ x.2 := by simpa only [List.mem_reverse,Function.comp_def] using hmem
      have he := length_le_encList_of_mem encNat hm
      have hp := Nat.size_mul_le x.1 acc
      have hs := Nat.size_add_le (x.1*acc) d
      change (encNat (x.1*acc+d)).length ≤ (encNat acc).length +
        ((encNat x.1).length + (numbersEncoding x.2).length + 1)
      simp only [encNat_apply,Nat.size_eq_bits_len]
      change d.bits.length ≤ (numbersEncoding x.2).length at he
      rw [Nat.size_eq_bits_len] at he
      omega)

def digits (base count value : ℕ) : List ℕ :=
  (List.range count).map (Cslib.Radix.digit base value)

theorem digits_length (base count value : ℕ) : (digits base count value).length = count := by
  simp [digits]

theorem digits_eq {m n : ℕ} (i : Fin (m^n)) :
    digits m n i.val = List.ofFn (fun j => (finFunctionFinEquiv.symm i j).val) := by
  rw [digits,SourceLists.range_map_eq]
  congr 1
  funext j
  exact Cslib.Radix.digit_eq_div_pow_mod _ _ _

theorem digits_polyTime :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × ℕ => digits x.1.1 x.2 x.1.2)
      (encPair (encPair encNat encNat) encUnary) numbersEncoding := by
  let e := encPair (encPair encNat encNat) encUnary
  have hr := unary_range' (snd (encPair encNat encNat) encUnary)
  have hf := (fst (encPair encNat encNat) encUnary).comp (fst e encUnary)
  have hd := radix_digit.comp (hf.prod (snd e encUnary))
  exact mapWithInput (encIn := e) (encA := encUnary)
    (f := fun x i => Cslib.Radix.digit x.1.1 x.1.2 i) hr hd

def smallDigits (base count value : ℕ) : List ℕ :=
  (digits base count value).map (min base)

theorem smallDigits_eq {m n : ℕ} (i : Fin (m^n)) :
    smallDigits m n i.val = List.ofFn (fun j => (finFunctionFinEquiv.symm i j).val) := by
  rw [smallDigits,digits_eq,List.map_ofFn]
  congr 1
  funext j
  exact Nat.min_eq_right (finFunctionFinEquiv.symm i j).isLt.le

theorem smallDigits_polyTime :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × ℕ => smallDigits x.1.1 x.2 x.1.2)
      (encPair (encPair encUnary encNat) encUnary) (encList encUnary) := by
  let c := encPair encUnary encNat
  let e := encPair c encUnary
  let a := encPair e encNat
  have hb := (fst c encUnary).fst'
  have hdata := (((unary_to_binary.comp hb).prod (fst c encUnary).snd').prod (snd c encUnary))
  have hd := digits_polyTime.comp hdata
  have hB := hb.comp (fst e encNat)
  have hf := binary_to_unary_bounded
    (binary_min' (unary_to_binary.comp hB) (snd e encNat)) hB (fun _ => Nat.min_le_left ..)
  exact mapWithInput (encIn := e) (encA := encNat) (encB := encUnary)
    (f := fun x d => min x.1.1 d) hd (hf.of_enc_eq (fun _ => rfl))

#print axioms rank_eq
#print axioms unrank_eq
#print axioms rank_polyTime
#print axioms unrank_polyTime
#print axioms littleValue_eq
#print axioms littleValue_polyTime
#print axioms smallDigits_eq
#print axioms smallDigits_polyTime

end DeletionCode.Explicit.Machine.SourceRadix
