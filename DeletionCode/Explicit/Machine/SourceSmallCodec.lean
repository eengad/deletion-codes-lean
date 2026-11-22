import DeletionCode.Explicit.Machine.SourceMixedRadix
import DeletionCode.Explicit.Machine.SourceReplayFamily
import DeletionCode.Explicit.Machine.SourceCompact

/-! Rank, write, and read the small-family payload with a binary literal radix. -/
namespace DeletionCode.Explicit.Machine.SourceSmallCodec

open SourceLists SourceRadix SourceMixedRadix
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {q ℓ : ℕ}

def names (s : Finset (Fin ℓ)) : List ℕ := s.sort.map Fin.val

theorem names_eq (s : Finset (Fin ℓ)) :
    names s = List.ofFn (fun i => (s.orderIsoOfFin rfl i).val.val) := by
  unfold names
  rw [← Finset.listMap_orderEmbOfFin_finRange s rfl]
  change ((List.ofFn (fun i : Fin s.card => i)).map _).map _ = _
  rw [List.map_map,List.map_ofFn]
  rfl

theorem names_length (s : Finset (Fin ℓ)) : (names s).length = s.card := by
  simp [names_eq]

theorem names_mem_iff (s : Finset (Fin ℓ)) (i : Fin ℓ) : i.val ∈ names s ↔ i ∈ s := by
  simp only [names,List.mem_map,Finset.mem_sort]
  exact ⟨fun ⟨j,hj,h⟩ => Fin.ext h ▸ hj,fun h => ⟨i,h,rfl⟩⟩

def outside (ℓ : ℕ) (active : List ℕ) : List ℕ :=
  (List.range ℓ).filter fun i => !active.contains i

private theorem names_filter (s : Finset (Fin ℓ)) :
    names s = ((List.finRange ℓ).filter (· ∈ s)).map Fin.val := by
  have hn := (List.nodup_finRange ℓ).filter (fun i => decide (i ∈ s))
  have hs : ((List.finRange ℓ).filter (· ∈ s)).Pairwise (· ≤ ·) :=
    ((List.pairwise_lt_finRange ℓ).imp le_of_lt).filter _
  have hp : s.sort = (List.finRange ℓ).filter (· ∈ s) := by
    apply List.Perm.eq_of_pairwise' (s.pairwise_sort _) hs
    apply (List.perm_ext_iff_of_nodup (s.sort_nodup _) hn).mpr
    simp
  exact congrArg (List.map Fin.val) hp

theorem outside_eq (s : Finset (Fin ℓ)) : outside ℓ (names s) = names sᶜ := by
  rw [outside,names_filter sᶜ,show List.range ℓ = (List.finRange ℓ).map Fin.val by simp,List.filter_map]
  congr 1
  apply List.filter_congr
  intro i _
  simp [Function.comp_def,names_mem_iff]

def select (pad : Fin q) (keys : List ℕ) (word : QWord q) : QWord q :=
  keys.map fun i => word.getD i pad

theorem select_eq (pad : Fin q) (s : Finset (Fin ℓ)) (x : Fin ℓ → Fin q) :
    select pad (names s) (List.ofFn x) = List.ofFn (SmallFamilyCodec.select s x) := by
  rw [select,names_eq,List.map_ofFn]
  congr 1
  funext i
  exact BooleanFibres.ofFn_getD x ((s.orderIsoOfFin rfl) i).val pad

def assemble (pad : Fin q) (ℓ : ℕ) (keys : List ℕ) (active literal : QWord q) : QWord q :=
  (List.range ℓ).map fun i =>
    match keys.idxOf? i with
    | some a => active.getD a pad
    | none => literal.getD (SourceCompact.index (outside ℓ keys) i) pad

private theorem idxOf?_eq (keys : List ℕ) (i : ℕ) (h : i ∈ keys) :
    keys.idxOf? i = some (SourceCompact.index keys i) := by
  cases hi : keys.idxOf? i with
  | none => exact False.elim ((List.idxOf?_eq_none_iff.mp hi) h)
  | some j => simp [SourceCompact.index,hi]

theorem assemble_eq (pad : Fin q) (s : Finset (Fin ℓ))
    (active : Fin s.card → Fin q) (literal : Fin sᶜ.card → Fin q) :
    assemble pad ℓ (names s) (List.ofFn active) (List.ofFn literal) =
      List.ofFn (SmallFamilyCodec.assemble s active literal) := by
  unfold assemble SmallFamilyCodec.assemble
  rw [show List.range ℓ = (List.finRange ℓ).map Fin.val by simp,List.map_map]
  change (List.ofFn (fun i : Fin ℓ => i)).map _ = _
  rw [List.map_ofFn]
  congr 1
  funext i
  have index_eq (s : Finset (Fin ℓ)) (h : i ∈ s) :
      SourceCompact.index (names s) i.val = ((s.orderIsoOfFin rfl).symm ⟨i,h⟩).val := by
    rw [names,SourceCompact.index_eq,ReplayEntry.compactIndex,dite_eq_left i.isLt,dite_eq_left h]
    rfl
  by_cases hi : i ∈ s
  · rw [dite_eq_left hi]
    simp only [Function.comp_apply,idxOf?_eq _ _ ((names_mem_iff s i).mpr hi)]
    rw [index_eq s hi]
    exact BooleanFibres.ofFn_getD active _ pad
  · rw [dite_eq_right hi]
    have hn : (names s).idxOf? i.val = none := List.idxOf?_eq_none_iff.mpr (mt (names_mem_iff s i).mp hi)
    simp only [Function.comp_apply,hn,outside_eq]
    rw [index_eq sᶜ (Finset.mem_compl.mpr hi)]
    exact BooleanFibres.ofFn_getD literal _ pad

def bound (q ℓ : ℕ) (keys : List ℕ) (members : List (QWord q)) : ℕ :=
  q^((outside ℓ keys).length)*members.length

def encode (pad : Fin q) (keys : List ℕ) (members : List (QWord q)) (word : QWord q) :
    Option (QWord q) :=
  let literal := select pad (outside word.length keys) word
  let width := Nat.clog q (bound q word.length keys members)
  (members.idxOf? (select pad keys word)).map fun member =>
    (RareAddress.fixedDigits pad width (wordRank literal.reverse*members.length+member)).reverse

theorem encode_eq (pad : Fin q) (hq : 2 ≤ q) (s : Finset (Fin ℓ))
    (members : List (Fin s.card → Fin q)) (x : Fin ℓ → Fin q) :
    encode pad (names s) (members.map List.ofFn) (List.ofFn x) =
      (SmallFamilyCodec.encode (by omega : 1 < q) s members x).map List.ofFn := by
  have hi : (members.map List.ofFn).idxOf? (List.ofFn (SmallFamilyCodec.select s x)) =
      members.idxOf? (SmallFamilyCodec.select s x) := by
    unfold List.idxOf?
    rw [List.findIdx?_map]
    congr 1
    funext a
    simp [Function.comp_def,List.ofFn_inj]
  unfold encode SmallFamilyCodec.encode SmallFamilyCodec.rank
  simp only [List.length_ofFn,outside_eq,select_eq,GramOrder.reversed_rank,hi,List.length_map,
    bound,names_length,SmallFamilyCodec.payloadLength]
  let i := members.idxOf (SmallFamilyCodec.select s x)
  have hidx : members.idxOf? (SmallFamilyCodec.select s x) =
      if i < members.length then some i else none := by
    rw [List.idxOf?,List.findIdx?_eq_guard_findIdx_lt]
    simp [i,List.idxOf,Option.guard]
  rw [hidx]
  by_cases h : i < members.length
  · rw [if_pos h,dite_eq_left h]
    simp only [Option.map_some]
    apply congrArg some
    let k : Fin (q^(Nat.clog q (q^sᶜ.card*members.length))) :=
      Fin.castLE (Nat.le_pow_clog (by omega) _) (finProdFinEquiv (finFunctionFinEquiv (SmallFamilyCodec.select sᶜ x),⟨i,h⟩))
    change _ = List.ofFn (finFunctionFinEquiv.symm k)
    rw [← GramOrder.mainWord_eq pad hq _ k]
    simp [k,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  · rw [if_neg h,dite_eq_right h]
    rfl

def decode (pad : Fin q) (ℓ : ℕ) (keys : List ℕ) (members : List (QWord q))
    (word : QWord q) : Option (QWord q) :=
  let r := wordRank word.reverse
  if r < bound q ℓ keys members then
    (members[r%members.length]?).map fun active =>
      assemble pad ℓ keys active
        (RareAddress.fixedDigits pad (outside ℓ keys).length (r/members.length)).reverse
  else none

theorem decode_eq (pad : Fin q) (hq : 2 ≤ q) (s : Finset (Fin ℓ))
    (members : List (Fin s.card → Fin q)) (word : Fin (SmallFamilyCodec.payloadLength s members) → Fin q) :
    decode pad ℓ (names s) (members.map List.ofFn) (List.ofFn word) =
      (SmallFamilyCodec.decode s members word).map List.ofFn := by
  unfold decode SmallFamilyCodec.decode
  simp only [GramOrder.reversed_rank,bound,outside_eq,names_length,List.length_map]
  by_cases h : (finFunctionFinEquiv word).val < q^sᶜ.card*members.length
  · rw [if_pos h,dite_eq_left h]
    let i : Fin (q^sᶜ.card*members.length) := ⟨_,h⟩
    let d := finProdFinEquiv.symm i
    change (((members.map List.ofFn)[i.val%members.length]?).map _) =
      some (List.ofFn (SmallFamilyCodec.assemble s (members.get d.2) (finFunctionFinEquiv.symm d.1)))
    rw [show i.val%members.length = d.2.val from rfl,
      List.getElem?_map,List.getElem?_eq_getElem d.2.isLt,Option.map_some,Option.map_some]
    change some (assemble pad ℓ (names s) (List.ofFn (members.get d.2))
      (RareAddress.fixedDigits pad sᶜ.card d.1.val).reverse) = _
    rw [GramOrder.mainWord_eq pad hq _ d.1,assemble_eq]
  · rw [if_neg h,dite_eq_right h]
    rfl

abbrev keyEncoding := PatchGraph.rowEncoding
abbrev membersEncoding (q : ℕ) := encList (wordEncoding q)

theorem outside_polyTime :
    ComputableInPolyTime (fun x : ℕ × List ℕ => outside x.1 x.2)
      (encPair encUnary keyEncoding) keyEncoding := by
  let e := encPair encUnary keyEncoding
  let a := encPair e encUnary
  have hr := unary_range' (fst encUnary keyEncoding)
  have hi := (idxOf?_polyTime 0 encUnary).comp
    (((snd encUnary keyEncoding).comp (fst e encUnary)).prod (snd e encUnary))
  have ht := hi.decide_eq' (const none)
  exact filterWithInput (encIn := e) (encA := encUnary)
    (test := fun x i => !x.2.contains i) hr (ht.of_enc_eq (fun x => by
      simp [Function.comp_def,List.idxOf?_eq_none_iff,List.contains_iff_mem]))

theorem select_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : List ℕ × QWord q => select pad x.1 x.2)
      (encPair keyEncoding (wordEncoding q)) (wordEncoding q) := by
  let e := encPair keyEncoding (wordEncoding q)
  exact mapWithInput (encIn := e) (encA := encUnary)
    (f := fun x i => x.2.getD i pad) (fst keyEncoding (wordEncoding q))
    (listGetDWithInput ((snd keyEncoding (wordEncoding q)).comp (fst e encUnary)) (snd e encUnary) pad)

abbrev assembleEncoding (q : ℕ) :=
  encPair (encPair encUnary keyEncoding) (encPair (wordEncoding q) (wordEncoding q))

theorem assemble_polyTime (pad : Fin q) :
    ComputableInPolyTime (fun x : (ℕ × List ℕ) × (QWord q × QWord q) =>
      assemble pad x.1.1 x.1.2 x.2.1 x.2.2) (assembleEncoding q) (wordEncoding q) := by
  let e := assembleEncoding q
  let a := encPair e encUnary
  let w := wordEncoding q
  have hp := fst (encPair encUnary keyEncoding) (encPair w w)
  have hw := snd (encPair encUnary keyEncoding) (encPair w w)
  have hx := fst e encUnary
  have hi := snd e encUnary
  have hkeys := hp.snd'.comp hx
  have hf := (idxOf?_polyTime 0 encUnary).comp (hkeys.prod hi)
  have hO := outside_polyTime.comp (hp.comp hx)
  have hindex := SourceCompact.index_polyTime.comp (hO.prod hi)
  have hl := listGetDWithInput (hw.snd'.comp hx) hindex pad
  have ha := listGetDWithInput (hw.fst'.comp (hx.comp (fst a encUnary))) (snd a encUnary) pad
  have hb := optionElimWithInput (encA := a) (encB := encUnary) (encC := ExceptionalRecords.letterEncoding q)
    (body := fun x i => x.1.2.1.getD i pad) hf hl ha
  exact mapWithInput (encIn := e) (encA := encUnary)
    (f := fun x i => match x.1.2.idxOf? i with
      | some j => x.2.1.getD j pad
      | none => x.2.2.getD (SourceCompact.index (outside x.1.1 x.1.2) i) pad)
    (encB := ExceptionalRecords.letterEncoding q) (unary_range' hp.fst')
    (hb.of_enc_eq (fun x => by
      simp only [Function.comp_def]
      cases x.1.1.2.idxOf? x.2 <;> rfl))

abbrev boundEncoding (q : ℕ) := encPair (encPair encUnary keyEncoding) (membersEncoding q)

theorem bound_polyTime (q : ℕ) :
    ComputableInPolyTime (fun x : (ℕ × List ℕ) × List (QWord q) =>
      bound q x.1.1 x.1.2 x.2) (boundEncoding q) encNat := by
  let e := boundEncoding q
  have hlen := (length_list encUnary).comp
    (outside_polyTime.comp (fst (encPair encUnary keyEncoding) (membersEncoding q)))
  have hsize := (length_list (wordEncoding q)).comp (snd (encPair encUnary keyEncoding) (membersEncoding q))
  exact binary_mul' (binary_pow' (const q) hlen) (unary_to_binary.comp hsize)

abbrev encodeEncoding (q : ℕ) := encPair (encPair keyEncoding (membersEncoding q)) (wordEncoding q)

theorem encode_polyTime (pad : Fin q) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : (List ℕ × List (QWord q)) × QWord q =>
      encode pad x.1.1 x.1.2 x.2) (encodeEncoding q) (encOption (wordEncoding q)) := by
  let e := encodeEncoding q
  let a := encPair e encUnary
  let w := wordEncoding q
  let m := membersEncoding q
  have hp := fst (encPair keyEncoding m) w
  have hw := snd (encPair keyEncoding m) w
  have hlen := (length_list (ExceptionalRecords.letterEncoding q)).comp hw
  have hO := outside_polyTime.comp (hlen.prod hp.fst')
  have hb := (bound_polyTime q).comp ((hlen.prod hp.fst').prod hp.snd')
  have hwidth := (widthAt_polyTime q).comp hb
  have hs := (select_polyTime pad).comp (hp.fst'.prod hw)
  have hm := (idxOf?_polyTime ([] : QWord q) w).comp (hp.snd'.prod hs)
  have hl := (select_polyTime pad).comp (hO.prod hw)
  have hv := (wordRank_polyTime hq).comp ((listReverse (ExceptionalRecords.letterEncoding q)).comp hl)
  have hsz := unary_to_binary.comp ((length_list w).comp hp.snd')
  have group := fst e encUnary
  have hi := unary_to_binary.comp (snd e encUnary)
  have hr := binary_add' ((binary_mul' hv hsz).comp group) hi
  have hd := (RareAddress.fixedDigits_polyTime pad).comp (encIn := a) ((hwidth.comp group).prod hr)
  have hrev := (listReverse (ExceptionalRecords.letterEncoding q)).comp hd
  refine optionMapWithInput (encA := e) (encB := encUnary) (encC := w) hm (hrev.of_enc_eq ?_)
  intro x
  simp only [Function.comp_def,widthAt_eq hq]
  rfl

abbrev decodeEncoding (q : ℕ) := encPair (boundEncoding q) (wordEncoding q)

theorem decode_polyTime (pad : Fin q) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : ((ℕ × List ℕ) × List (QWord q)) × QWord q =>
      decode pad x.1.1.1 x.1.1.2 x.1.2 x.2) (decodeEncoding q) (encOption (wordEncoding q)) := by
  let e := decodeEncoding q
  let w := wordEncoding q
  let m := membersEncoding q
  have hp := fst (boundEncoding q) w
  have hw := snd (boundEncoding q) w
  have hm := (snd (encPair encUnary keyEncoding) m).comp hp
  have hs := (fst (encPair encUnary keyEncoding) m).comp hp
  have hb := (bound_polyTime q).comp hp
  have hO := outside_polyTime.comp hs
  have hlen := (length_list encUnary).comp hO
  have hr := (wordRank_polyTime hq).comp ((listReverse (ExceptionalRecords.letterEncoding q)).comp hw)
  have hsz := unary_to_binary.comp ((length_list w).comp hm)
  have hi := binary_mod' hr hsz
  have hl := binary_div' hr hsz
  have hread := listGetD_binary (encA := w) (encL := m) [] hm hi
  have hd := (RareAddress.fixedDigits_polyTime pad).comp (hlen.prod hl)
  have hv := (listReverse (ExceptionalRecords.letterEncoding q)).comp hd
  have ha := (assemble_polyTime pad).comp (hs.prod (hread.prod hv))
  have ht := bool_and' (binary_lt' hr hb) (binary_lt' hi hsz)
  refine (ht.ite' ((optionSome w).comp ha) (const none)).of_enc_eq ?_
  intro x
  apply congrArg (encOption w)
  simp only [Function.comp_def,decode]
  split
  · rename_i h
    by_cases hi : wordRank x.2.reverse % x.1.2.length < x.1.2.length
    · simp [h,hi,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    · simp [h,hi,List.getElem?_eq_none (Nat.le_of_not_gt hi)]
  · rename_i h
    simp [h]

#print axioms select_eq
#print axioms assemble_eq
#print axioms encode_eq
#print axioms decode_eq
#print axioms encode_polyTime
#print axioms decode_polyTime

end DeletionCode.Explicit.Machine.SourceSmallCodec
