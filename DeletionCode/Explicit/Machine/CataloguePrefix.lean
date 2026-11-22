import DeletionCode.Explicit.Machine.ExceptionalCatalogue
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! Prefix masses of finite rule catalogues on serialized words and matrices. -/
namespace DeletionCode.Explicit.Machine.CataloguePrefix

open FieldHash CoreWeight ExceptionalWeight Ternary Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime
open ExceptionalRecords (Prescriptions prescriptionsEncoding serializeAssignment letterEncoding)
open scoped BigOperators

variable {q ℓ n θ : ℕ}

abbrev EntryData (q : ℕ) := Rows × Prescriptions q
abbrev entryEncoding (q : ℕ) := encPair rowsEncoding (prescriptionsEncoding q)

def matrixRows {m n : ℕ} (A : TernaryMatrix m n) : Rows := List.ofFn fun i => List.ofFn (A i)

def objectData (o : CoreWeight.Object ℓ q n) : EntryData q :=
  (matrixRows o.rules, serializeAssignment o.assignment)

/-- All positions read by either the prefix or the assignment. -/
def occupied (len : ℕ) (p : QWord q) (xs : Prescriptions q) : ℕ :=
  (List.range len).countP (fun i => decide (i < p.length) || xs.any (fun a => decide (a.1 = i)))

def agrees (pad : Fin q) (p : QWord q) (xs : Prescriptions q) : Bool :=
  xs.all fun a => decide (p.length ≤ a.1) || decide (p.getD a.1 pad = a.2)

def dot (n : ℕ) (r h : Row) : F₃ :=
  ((List.range n).map fun j => r.getD j 0 * h.getD j 0).sum

def kept (n : ℕ) (hs rs : Rows) : Bool :=
  hs.all fun h => rs.all fun r => decide (dot n r h = 0)

abbrev PrefixData (q : ℕ) := ℕ × (MatrixInput × QWord q)
abbrev prefixDataEncoding (q : ℕ) := encPair encUnary (encPair matrixEncoding (wordEncoding q))

abbrev Input (q : ℕ) := PrefixData q × List (EntryData q)
abbrev inputEncoding (q : ℕ) := encPair (prefixDataEncoding q) (encList (entryEncoding q))

def term (pad : Fin q) (x : PrefixData q) (e : EntryData q) : ℕ :=
  if kept x.2.1.1 x.2.1.2 e.1 && agrees pad x.2.2 e.2 then
    q^(x.1 - occupied x.1 x.2.2 e.2)
  else 0

def prefixMass (pad : Fin q) (x : Input q) : ℕ :=
  if x.1.2.2.length ≤ x.1.1 then (x.2.map (term pad x.1)).sum else 0

private theorem serialized_mem (a : Assignment ℓ q) (j : ℕ) (c : Fin q) :
    (j,c) ∈ serializeAssignment a ↔ ∃ i : ↥a.support, i.val.val = j ∧ a.letter i = c := by
  unfold serializeAssignment
  constructor
  · rintro h
    obtain ⟨i, _, hi⟩ := List.mem_map.mp h
    exact ⟨⟨i.val, mem_supportList.mp i.2⟩, congrArg Prod.fst hi, congrArg Prod.snd hi⟩
  · rintro ⟨i,rfl,rfl⟩
    exact List.mem_map.mpr ⟨⟨i.val,mem_supportList.mpr i.2⟩, by simp, rfl⟩

private theorem occupied_eq {k : ℕ} (a : Assignment ℓ q) (u : Fin k → Fin q) :
    occupied ℓ (List.ofFn u) (serializeAssignment a) = (a.support ∪ (initial u).support).card := by
  have hmem (i : Fin ℓ) :
      (decide (i.val < (List.ofFn u).length) || (serializeAssignment a).any
        (fun a => decide (a.1 = i.val))) = true ↔ i ∈ a.support ∪ (initial u).support := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.length_ofFn, List.any_eq_true,
      Finset.mem_union, initial, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [or_comm]
    apply or_congr_left
    constructor
    · rintro ⟨⟨j,c⟩, hj, he⟩
      obtain ⟨a', ha', _⟩ := (serialized_mem a j c).mp hj
      exact Fin.ext (ha'.trans he) ▸ a'.property
    · intro hi
      exact ⟨(i.val,a.letter ⟨i,hi⟩), (serialized_mem ..).mpr ⟨⟨i,hi⟩,rfl,rfl⟩,rfl⟩
  let test (j : ℕ) := decide (j < (List.ofFn u).length) ||
    (serializeAssignment a).any (fun a => decide (a.1 = j))
  change (List.range ℓ).countP test = _
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  have hset : ((List.range ℓ).filter test).toFinset =
      (a.support ∪ (initial u).support).map Fin.valEmbedding := by
    ext j
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_map, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨hj, ht⟩
      exact ⟨⟨j,hj⟩, (hmem ⟨j,hj⟩).mp ht, rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨i.isLt, (hmem i).mpr hi⟩
  rw [hset, Finset.card_map]

private theorem ofFn_getD {α : Type*} (f : Fin k → α) (d : α) (i : ℕ) (hi : i < k) :
    (List.ofFn f).getD i d = f ⟨i,hi⟩ := by
  have hlen : i < (List.ofFn f).length := by simpa using hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, List.getElem_ofFn,
    Option.getD_some]

private theorem agrees_iff {k : ℕ} (pad : Fin q) (a : Assignment ℓ q) (u : Fin k → Fin q) :
    agrees pad (List.ofFn u) (serializeAssignment a) = true ↔ Compatible a (initial u) := by
  simp only [agrees, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.length_ofFn]
  constructor
  · intro h i hi
    have hk := (Finset.mem_filter.mp hi).2
    have hm := (serialized_mem a i.val.val (a.letter i)).mpr ⟨i,rfl,rfl⟩
    have he := (h _ hm).resolve_left (Nat.not_le.mpr hk)
    rw [ofFn_getD _ _ _ hk] at he
    exact he.symm
  · rintro h ⟨j,c⟩ hj
    obtain ⟨i, rfl, rfl⟩ := (serialized_mem a j c).mp hj
    by_cases hk : k ≤ i.val.val
    · exact Or.inl hk
    · have hm : i.val ∈ (initial (ℓ := ℓ) u).support :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_of_not_ge hk⟩
      right
      rw [ofFn_getD _ _ _ (Nat.lt_of_not_ge hk)]
      exact (h i hm).symm

theorem dot_eq (r h : Fin n → F₃) :
    dot n (List.ofFn r) (List.ofFn h) = r ⬝ᵥ h := by
  unfold dot dotProduct
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem (by simp)
  intro j hj hk
  have hl : j < n := by simpa using hk
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [ofFn_getD _ _ _ hl, ofFn_getD _ _ _ hl]

private theorem kept_iff (o : CoreWeight.Object ℓ q n) (H : TernaryMatrix θ n) :
    kept n (matrixRows H) (objectData o).1 = true ↔ CoreWeight.Kept o H := by
  simp only [kept, objectData, matrixRows, List.all_eq_true, List.mem_ofFn, decide_eq_true_eq,
    CoreWeight.Kept, funext_iff, Pi.zero_apply, Matrix.mulVec]
  constructor
  · intro h i j
    simpa only [dot_eq] using h _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
  · rintro h _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    rw [dot_eq]
    exact h i j

private theorem term_eq {k : ℕ} (pad : Fin q) (H : TernaryMatrix θ n) (u : Fin k → Fin q)
    (o : CoreWeight.Object ℓ q n) :
    term pad (ℓ, (n,matrixRows H), List.ofFn u) (objectData o) =
      if CoreWeight.Kept o H then jointCount o.assignment (initial u) else 0 := by
  change (if kept n (matrixRows H) (objectData o).1 &&
      agrees pad (List.ofFn u) (serializeAssignment o.assignment) then
      q^(ℓ - occupied ℓ (List.ofFn u) (serializeAssignment o.assignment)) else 0) = _
  simp only [Bool.and_eq_true, kept_iff, agrees_iff, occupied_eq, jointCount]
  split_ifs <;> simp_all

theorem prefixMass_eq {m k : ℕ} (pad : Fin q) (C : Fin m → CoreWeight.Object ℓ q n)
    (H : TernaryMatrix θ n) (u : Fin k → Fin q) :
    prefixMass pad ((ℓ,(n,matrixRows H),List.ofFn u), List.ofFn (fun i => objectData (C i))) =
      CoreWeight.prefixMass C H u := by
  simp only [prefixMass, CoreWeight.prefixMass, List.length_ofFn, List.map_ofFn, List.sum_ofFn]
  split_ifs with h
  · exact Finset.sum_congr rfl fun i _ => term_eq pad H u (C i)
  · rfl

theorem tritSum_polyTime :
    ComputableInPolyTime (List.sum (α := F₃)) rowEncoding tritEncoding := by
  have ha : ComputableInPolyTime (fun p : F₃ × F₃ => p.1 + p.2)
      (encPair tritEncoding tritEncoding) tritEncoding := of_finite _
  have hb : ∀ a : F₃, (tritEncoding a).length ≤ 10 := by decide
  have hf := foldlWith_of_bounded_growth (step := fun (_ : Bool) (a b : F₃) => a + b)
    (const false) (id' (encIn := rowEncoding)) (const 0)
    (ha.comp ((fst (encPair encBool tritEncoding) tritEncoding).snd'.prod (snd _ _)))
    (growth := fun _ => 10) (PolyBounded.const 10)
    (fun _ _ _ _ => (hb _).trans (Nat.le_add_left _ _))
  exact hf.of_enc_eq (fun xs => congrArg tritEncoding (by
    have h (a : F₃) (ys : List F₃) : ys.foldl (· + ·) a = a + ys.sum := by
      induction ys generalizing a with
      | nil => simp
      | cons x ys ih => simp [ih, add_assoc]
    simp [h]))

abbrev DotInput := ℕ × (Row × Row)
abbrev dotEncoding := encPair encUnary (encPair rowEncoding rowEncoding)

theorem dot_polyTime : ComputableInPolyTime (fun x : DotInput => dot x.1 x.2.1 x.2.2)
    dotEncoding tritEncoding := by
  have hleft := (snd encUnary (encPair rowEncoding rowEncoding)).fst'.comp (fst dotEncoding encUnary)
  have hright := (snd encUnary (encPair rowEncoding rowEncoding)).snd'.comp (fst dotEncoding encUnary)
  have hi := snd dotEncoding encUnary
  have hmul : ComputableInPolyTime (fun x : F₃ × F₃ => x.1 * x.2)
      (encPair tritEncoding tritEncoding) tritEncoding := of_finite _
  unfold dot
  exact tritSum_polyTime.comp (mapWithInput (encA := encUnary)
    (f := fun x j => x.2.1.getD j 0 * x.2.2.getD j 0)
    (range.comp (fst encUnary (encPair rowEncoding rowEncoding)))
    (hmul.comp ((listGetDWithInput hleft hi 0).prod (listGetDWithInput hright hi 0))))

private abbrev KeptInput := MatrixInput × Rows
private abbrev keptEncoding := encPair matrixEncoding rowsEncoding

private theorem kept_polyTime :
    ComputableInPolyTime (fun x : KeptInput => kept x.1.1 x.1.2 x.2) keptEncoding encBool := by
  let src := encPair keptEncoding rowEncoding
  have hx := fst keptEncoding rowEncoding
  have hp := fst src rowEncoding
  have hn := (fst matrixEncoding rowsEncoding).fst'.comp (hx.comp hp)
  have hh := (snd keptEncoding rowEncoding).comp hp
  have hr := snd src rowEncoding
  let arg := encPair src rowEncoding
  have hpack : ComputableInPolyTime (fun x : (KeptInput × Row) × Row =>
      (x.1.1.1.1,(x.2,x.1.2))) arg dotEncoding := hn.prod (hr.prod hh)
  have hd := dot_polyTime.comp (encIn := arg) (encMid := dotEncoding) hpack
  have hrow : ComputableInPolyTime (fun x : KeptInput × Row =>
      x.1.2.all (fun r => decide (dot x.1.1.1 r x.2 = 0))) src encBool :=
    allWithInput (encIn := src) (encA := rowEncoding)
      (test := fun x r => decide (dot x.1.1.1 r x.2 = 0))
      ((snd matrixEncoding rowsEncoding).comp hx) (hd.decide_eq' (const 0))
  unfold kept
  exact allWithInput (encIn := keptEncoding) (encA := rowEncoding)
    (test := fun x h => x.2.all fun r => decide (dot x.1.1 r h = 0))
    (fst matrixEncoding rowsEncoding).snd' hrow

private abbrev letterPairEncoding (q : ℕ) := encPair encUnary (letterEncoding q)
private abbrev PrefixTest (q : ℕ) := QWord q × Prescriptions q
private abbrev prefixTestEncoding (q : ℕ) := encPair (wordEncoding q) (prescriptionsEncoding q)

private theorem agrees_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : PrefixTest q => agrees pad x.1 x.2)
      (prefixTestEncoding q) encBool := by
  let e := prefixTestEncoding q
  let a := letterPairEncoding q
  have hw := (fst (wordEncoding q) (prescriptionsEncoding q)).comp (fst e a)
  have hp := snd e a
  have hlen := (length_list (letterEncoding q)).comp hw
  have hval := listGetDWithInput hw hp.fst' pad
  exact allWithInput (test := fun w p => decide (w.1.length ≤ p.1) || decide (w.1.getD p.1 pad = p.2))
    (snd (wordEncoding q) (prescriptionsEncoding q))
    (bool_or' (unary_le' hlen hp.fst') (hval.decide_eq' hp.snd'))

private theorem occupied_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : ℕ × PrefixTest q => occupied x.1 x.2.1 x.2.2)
      (encPair encUnary (prefixTestEncoding q)) encUnary := by
  let e := encPair encUnary (prefixTestEncoding q)
  let p := encPair e encUnary
  let a := letterPairEncoding q
  have hd := (snd encUnary (prefixTestEncoding q)).comp (fst e encUnary)
  have hi := snd e encUnary
  have hl := (length_list (letterEncoding q)).comp hd.fst'
  have ha := anyWithInput (test := fun x (r : ℕ × Fin q) => decide (r.1 = x.2)) hd.snd'
    ((snd p a).fst'.decide_eq' (hi.comp (fst p a)))
  exact countPWithInput (test := fun x j => decide (j < x.2.1.length) ||
    x.2.2.any (fun r => decide (r.1 = j)))
    (range.comp (fst encUnary (prefixTestEncoding q))) (bool_or' (unary_lt' hi hl) ha)

theorem term_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : PrefixData q × EntryData q => term pad x.1 x.2)
      (encPair (prefixDataEncoding q) (entryEncoding q)) encNat := by
  have hp := fst (prefixDataEncoding q) (entryEncoding q)
  have he := snd (prefixDataEncoding q) (entryEncoding q)
  have hkeep := kept_polyTime.comp (hp.snd'.fst'.prod he.fst')
  have htest := hp.snd'.snd'.prod he.snd'
  have hagree := (agrees_polyTime pad).comp htest
  have hocc := (occupied_polyTime q).comp (hp.fst'.prod htest)
  have hpow := binary_pow.comp ((const (encOut := encNat) q).prod (unary_sub' hp.fst' hocc))
  exact ite (bool_and' hkeep hagree) hpow (const 0)

theorem prefixMass_polyTime (pad : Fin q) :
    ComputableInPolyTime (prefixMass pad) (inputEncoding q) encNat := by
  let e := inputEncoding q
  let a := entryEncoding q
  have hp := fst (prefixDataEncoding q) (encList a)
  have hr := snd (prefixDataEncoding q) (encList a)
  let arg := encPair e a
  let params := encPair (prefixDataEncoding q) a
  have hpack : ComputableInPolyTime (fun x : Input q × EntryData q => (x.1.1,x.2))
      arg params := (hp.comp (fst e a)).prod (snd e a)
  have hterm := (term_polyTime pad).comp (encIn := arg) (encMid := params) hpack
  have hlen := (length_list (letterEncoding q)).comp hp.snd'.snd'
  have hterms := mapWithInput (encIn := e) (encA := a)
    (f := fun (x : Input q) o => term pad x.1 o) hr hterm
  exact ite_decide (unary_le' hlen hp.fst') (binary_sum.comp hterms) (const 0)

/-- Evaluate the exceptional prefix mass using its length-generated catalogue. -/
def exceptionalPrefixMass (pad : Fin q) (b t : ℕ) (x : ℕ × (Rows × QWord q)) : ℕ :=
  prefixMass pad ((x.1, (q ^ UniformParameters.gram q b t x.1, x.2.1), x.2.2),
    (ExceptionalRecords.serialized pad b t x.1).map (fun e => ([e.1],e.2)))

abbrev exceptionalPrefixEncoding (q : ℕ) := encPair encUnary (encPair rowsEncoding (wordEncoding q))

theorem exceptionalPrefixMass_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (exceptionalPrefixMass pad b t) (exceptionalPrefixEncoding q) encNat := by
  have hl := fst encUnary (encPair rowsEncoding (wordEncoding q))
  have hp := snd encUnary (encPair rowsEncoding (wordEncoding q))
  have hn := ((length_list (wordEncoding q)).comp (ExceptionalRecords.gramList_polyTime q b t hq)).comp hl
  have hw : ComputableInPolyTime (fun x : ℕ × (Rows × QWord q) =>
      q ^ UniformParameters.gram q b t x.1) (exceptionalPrefixEncoding q) encUnary :=
    hn.of_enc_eq (fun _ => congrArg encUnary (length_wordsOfLength ..).symm)
  have he : ComputableInPolyTime (fun e : ExceptionalRecords.SerialEntry q => ([e.1],e.2))
      (ExceptionalRecords.serialEntryEncoding q) (entryEncoding q) :=
    (cons' (fst rowEncoding (prescriptionsEncoding q)) (const [])).prod
      (snd rowEncoding (prescriptionsEncoding q))
  have hcat := (ComputableInPolyTime.map he).comp ((ExceptionalRecords.serialized_polyTime pad b t hq).comp hl)
  exact (prefixMass_polyTime pad).comp ((hl.prod ((hw.prod hp.fst').prod hp.snd')).prod hcat)

theorem exceptionalPrefixMass_eq {k : ℕ} (pad : Fin q) (b t : ℕ)
    (H : TernaryMatrix θ (q ^ UniformParameters.gram q b t ℓ)) (u : Fin k → Fin q) :
    exceptionalPrefixMass pad b t (ℓ,matrixRows H,List.ofFn u) =
      ExceptionalWeight.prefixMass
        (ExceptionalWeight.family pad (ExceptionalWeight.dictionary q (UniformParameters.gram q b t ℓ)) b t ℓ) H u := by
  let C := ExceptionalWeight.family pad (ExceptionalWeight.dictionary q (UniformParameters.gram q b t ℓ)) b t ℓ
  have hc : List.ofFn C = ExceptionalWeight.catalogue pad
      (ExceptionalWeight.dictionary q (UniformParameters.gram q b t ℓ)) b t ℓ := List.ofFn_get _
  have hlist : ((List.ofFn C).map ExceptionalRecords.serialize).map (fun e => ([e.1],e.2)) =
      List.ofFn (fun j => objectData (C j).object) := by
    simp only [List.map_ofFn]
    rfl
  have hs := (congrArg (fun xs => (xs.map ExceptionalRecords.serialize).map (fun e => ([e.1],e.2))) hc).symm.trans hlist
  unfold exceptionalPrefixMass
  rw [ExceptionalRecords.serialized_eq, hs, prefixMass_eq]
  rfl

#print axioms prefixMass_polyTime
#print axioms exceptionalPrefixMass_polyTime
#print axioms exceptionalPrefixMass_eq

#print axioms prefixMass_eq

end DeletionCode.Explicit.Machine.CataloguePrefix
