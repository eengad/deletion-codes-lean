import DeletionCode.Explicit.Machine.SourceGrammar
import DeletionCode.Explicit.Machine.SourceRadix
import DeletionCode.Explicit.Machine.GramOrder

/-! The numeric index of a compact replay description, in the manuscript field order. -/
namespace DeletionCode.Explicit.Machine.SourceDescriptionIndex

open SourceGrammar SourceRadix
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open private entryEquiv entryCount codeCount from DeletionCode.Explicit.ReplayGrammar
open private ofDigits_ofFn from DeletionCode.Explicit.Machine.GramOrder

variable {q E L b : ℕ}

def entryCapacity (q E L b : ℕ) : ℕ :=
  ReplayGrammar.radix E L^11 * (q^b*q^b)

def capacity (q E L b : ℕ) : ℕ := (E+1)*entryCapacity q E L b^E

def packEntry (E L b : ℕ) (c : Code q) : ℕ :=
  let B := q^b
  littleValue (ReplayGrammar.radix E L) c.1*(B*B)+wordRank c.2.1.reverse*B+wordRank c.2.2.reverse

def pack (E L b : ℕ) (d : Description q) : ℕ :=
  let C := entryCapacity q E L b
  d.1*C^E+littleValue C (d.2.map (packEntry E L b))

private theorem packEntry_eq (c : ReplayGrammar.EntryCode E L b q) :
    packEntry E L b (codeData c) = (entryEquiv E L b q c).val := by
  unfold packEntry codeData
  simp only [littleValue_eq,GramOrder.reversed_rank,ofDigits_ofFn,← finFunctionFinEquiv_apply]
  change (finFunctionFinEquiv c.1).val*(q^b*q^b)+(finFunctionFinEquiv c.2.1).val*q^b+
      (finFunctionFinEquiv c.2.2).val =
    (finFunctionFinEquiv c.2.2).val+q^b*(finFunctionFinEquiv c.2.1).val+
      (q^b*q^b)*(finFunctionFinEquiv c.1).val
  ring

theorem pack_eq (d : ReplayGrammar.DescriptionCode E L b q) :
    pack E L b (descriptionData d) = (ReplayGrammar.packDescription d).val := by
  unfold pack descriptionData
  simp only [List.map_ofFn,Function.comp_def,packEntry_eq,littleValue_eq,ofDigits_ofFn]
  change d.1.val*entryCapacity q E L b^E+
      (∑ i : Fin E, (entryEquiv E L b q (d.2 i)).val*entryCapacity q E L b^i.val) =
    (∑ i : Fin E, (entryEquiv E L b q (d.2 i)).val*entryCount E L b q^i.val)+
      entryCount E L b q^E*d.1.val
  simp [entryCapacity,Nat.mul_comm,Nat.add_comm]

def unpackEntry (pad : Fin q) (E L b idx : ℕ) : Code q :=
  let B := q^b
  (smallDigits (ReplayGrammar.radix E L) 11 (idx/(B*B)),
    (RareAddress.fixedDigits pad b (idx%(B*B)/B)).reverse,
    (RareAddress.fixedDigits pad b (idx%(B*B)%B)).reverse)

def unpack (pad : Fin q) (E L b idx : ℕ) : Option (Description q) :=
  let C := entryCapacity q E L b
  if idx < capacity q E L b then
    some (idx/C^E,(digits C E (idx%C^E)).map (unpackEntry pad E L b))
  else none

private theorem unpackEntry_eq (pad : Fin q) (hq : 2 ≤ q) (i : Fin (entryCount E L b q)) :
    unpackEntry pad E L b i.val = codeData ((entryEquiv E L b q).symm i) := by
  let B := q^b
  let f := (finProdFinEquiv (m := ReplayGrammar.radix E L^11) (n := B*B)).symm i
  let g := (finProdFinEquiv (m := B) (n := B)).symm f.2
  change (smallDigits (ReplayGrammar.radix E L) 11 f.1.val,
    (RareAddress.fixedDigits pad b g.1.val).reverse,(RareAddress.fixedDigits pad b g.2.val).reverse) =
    (List.ofFn (fun j => (finFunctionFinEquiv.symm f.1 j).val),
      List.ofFn (finFunctionFinEquiv.symm g.1),List.ofFn (finFunctionFinEquiv.symm g.2))
  rw [smallDigits_eq f.1,GramOrder.mainWord_eq pad hq b g.1,GramOrder.mainWord_eq pad hq b g.2]

theorem unpack_eq (pad : Fin q) (hq : 2 ≤ q)
    (i : Fin (ReplayGrammar.descriptionBound E L b q)) :
    unpack pad E L b i.val = (ReplayGrammar.unpackDescription i).map descriptionData := by
  unfold unpack ReplayGrammar.unpackDescription
  change (if i.val < codeCount E L b q then _ else none) = _
  split
  · rename_i h
    simp only [h,↓reduceDIte,Option.map_some]
    let j : Fin (codeCount E L b q) := ⟨i.val,h⟩
    let f := (finProdFinEquiv (m := E+1) (n := entryCount E L b q^E)).symm j
    change some (f.1.val,(digits (entryCount E L b q) E f.2.val).map (unpackEntry pad E L b)) =
      some (f.1.val,List.ofFn (fun k => codeData ((entryEquiv E L b q).symm (finFunctionFinEquiv.symm f.2 k))))
    simp only [digits_eq f.2,List.map_ofFn,Function.comp_def,unpackEntry_eq pad hq]
  · rename_i h
    simp [h]

theorem entryCapacity_polyTime (q : ℕ) :
    ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) => entryCapacity q p.1 p.2.1 p.2.2) sizesEncoding encNat := by
  let e := sizesEncoding
  have hE := fst encUnary (encPair encUnary encUnary)
  have hv := snd encUnary (encPair encUnary encUnary)
  have hrad := unary_to_binary.comp (radix_polyTime.comp (hE.prod hv.fst'))
  have hword := binary_pow' (const q) hv.snd'
  exact binary_mul' (binary_pow' hrad (const 11)) (binary_mul' hword hword)

theorem packEntry_polyTime (q : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : (ℕ × (ℕ × ℕ)) × Code q => packEntry x.1.1 x.1.2.1 x.1.2.2 x.2)
      (encPair sizesEncoding (codeEncoding q)) encNat := by
  let c := codeEncoding q
  let e := encPair sizesEncoding c
  have hx := fst sizesEncoding c
  have hy := snd sizesEncoding c
  have hrad := unary_to_binary.comp (radix_polyTime.comp (hx.fst'.prod hx.snd'.fst'))
  have hb := binary_pow' (const q) hx.snd'.snd'
  have hf := (ComputableInPolyTime.map unary_to_binary).comp hy.fst'
  have hnum := littleValue_polyTime.comp (hrad.prod hf)
  have hw := (wordRank_polyTime hq).comp (listReverse (ExceptionalRecords.letterEncoding q))
  have hu := hw.comp hy.snd'.fst'
  have hv := hw.comp hy.snd'.snd'
  have h := binary_add' (binary_add' (binary_mul' hnum (binary_mul' hb hb)) (binary_mul' hu hb)) hv
  exact h.of_enc_eq (fun _ => by simp [packEntry,Function.comp_def] <;> rfl)

theorem pack_polyTime (q : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : (ℕ × (ℕ × ℕ)) × Description q => pack x.1.1 x.1.2.1 x.1.2.2 x.2)
      (encPair sizesEncoding (descriptionEncoding q)) encNat := by
  let d := descriptionEncoding q
  let e := encPair sizesEncoding d
  let c := codeEncoding q
  let p := encPair e c
  have hx := fst sizesEncoding d
  have hd := snd sizesEncoding d
  have hc := (entryCapacity_polyTime q).comp hx
  have hn := unary_to_binary.comp hd.fst'
  have ha := binary_mul' hn (binary_pow' hc hx.fst')
  have hf := (packEntry_polyTime q hq).comp (encIn := p)
    ((hx.comp (fst e c)).prod (snd e c))
  have htable := mapWithInput (encIn := e) (encA := c) (encB := encNat)
    (f := fun x c => packEntry x.1.1 x.1.2.1 x.1.2.2 c) hd.snd' (hf.of_enc_eq (fun _ => rfl))
  exact binary_add' ha (littleValue_polyTime.comp (hc.prod htable))

theorem unpackEntry_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : (ℕ × (ℕ × ℕ)) × ℕ => unpackEntry pad x.1.1 x.1.2.1 x.1.2.2 x.2)
      (encPair sizesEncoding encNat) (codeEncoding q) := by
  let e := encPair sizesEncoding encNat
  have hx := fst sizesEncoding encNat
  have hi := snd sizesEncoding encNat
  have hrad := radix_polyTime.comp (hx.fst'.prod hx.snd'.fst')
  have hb := hx.snd'.snd'
  have hB := binary_pow' (const q) hb
  have hBB := binary_mul' hB hB
  have hnum := smallDigits_polyTime.comp ((hrad.prod (binary_div' hi hBB)).prod (const 11))
  have hi := binary_mod' hi hBB
  have hw := (listReverse (ExceptionalRecords.letterEncoding q)).comp (Machine.RareAddress.fixedDigits_polyTime pad)
  have hu := hw.comp (hb.prod (binary_div' hi hB))
  have hv := hw.comp (hb.prod (binary_mod' hi hB))
  exact hnum.prod (hu.prod hv)

theorem unpack_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : (ℕ × (ℕ × ℕ)) × ℕ => unpack pad x.1.1 x.1.2.1 x.1.2.2 x.2)
      (encPair sizesEncoding encNat) (encOption (descriptionEncoding q)) := by
  let e := encPair sizesEncoding encNat
  let c := codeEncoding q
  let p := encPair e encNat
  have hx := fst sizesEncoding encNat
  have hE := hx.fst'
  have hi := snd sizesEncoding encNat
  have hc := (entryCapacity_polyTime q).comp hx
  have hpow := binary_pow' hc hE
  have hcap := binary_mul' (unary_to_binary.comp (unary_add' hE (const 1))) hpow
  have hk := binary_div' hi hpow
  have hkey := binary_to_unary_bounded (binary_min' hk (unary_to_binary.comp hE)) hE
    (fun _ => Nat.min_le_right ..)
  have hd := digits_polyTime.comp ((hc.prod (binary_mod' hi hpow)).prod hE)
  have hf := (unpackEntry_polyTime pad).comp (encIn := p) ((hx.comp (fst e encNat)).prod (snd e encNat))
  have ht := mapWithInput (encIn := e) (encA := encNat) (encB := c)
    (f := fun x i => unpackEntry pad x.1.1 x.1.2.1 x.1.2.2 i) hd (hf.of_enc_eq (fun _ => rfl))
  have hgood := (optionSome (descriptionEncoding q)).comp (hkey.prod ht)
  have h := (binary_lt' hi hcap).ite' hgood (const none)
  refine h.of_enc_eq (g := fun x => unpack pad x.1.1 x.1.2.1 x.1.2.2 x.2) ?_
  intro x
  let C := entryCapacity q x.1.1 x.1.2.1 x.1.2.2^x.1.1
  by_cases he : x.2 < (x.1.1+1)*C
  · have hk : x.2/C < x.1.1+1 := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using he)
    have hmin : min (x.2/C) x.1.1 = x.2/C := Nat.min_eq_left (Nat.le_of_lt_succ hk)
    dsimp only [C] at he hmin
    simp only [unpack,Function.comp_def,capacity,decide_eq_true_eq,show x.2 < capacity q x.1.1 x.1.2.1 x.1.2.2 from he,
      he,↓reduceIte,hmin]
    try rfl
  · simp [unpack,capacity,Function.comp_def,he,C]

#print axioms pack_eq
#print axioms unpack_eq
#print axioms pack_polyTime
#print axioms unpack_polyTime

end DeletionCode.Explicit.Machine.SourceDescriptionIndex
