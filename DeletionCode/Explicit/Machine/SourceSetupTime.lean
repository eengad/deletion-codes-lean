import DeletionCode.Explicit.Machine.SourceExceptionalTable
import DeletionCode.Explicit.Machine.SourceCoreCatalogue
import DeletionCode.Explicit.Machine.SourceFamilyEnumeration
import DeletionCode.Explicit.SourceSetup

/-! Build the public hashes using the exact conditional expectations of the concrete setup. -/
namespace DeletionCode.Explicit.Machine.SourceSetupTime

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Ternary CataloguePrefix ConditionalChoice
open Machine.SourceHashChoice (CoreTable coreTableEncoding coreOnPrefix coreOnPrefix_eq coreOnPrefix_polyTime)
open _root_.DeletionCode.Explicit.UniformParameters
open _root_.DeletionCode.Explicit.ConditionalChooser
open scoped BigOperators
set_option maxHeartbeats 1700000

variable {q l b t : ℕ}

structure ChooserInput (q : ℕ) where
  length : ℕ
  rows : ℕ
  families : List Rows
  exceptional : CoreTable q
  core : CoreTable q

enc_structure chooserEncoding (q : ℕ) : ChooserInput q where
  length : encUnary, rows : encUnary, families : (encList rowsEncoding),
  exceptional : (coreTableEncoding q), core : (coreTableEncoding q)

abbrev evaluatorEncoding (q : ℕ) := encPair (chooserEncoding q) ConditionalChoice.prefixEncoding

def input (pad : Fin q) (b t l : ℕ) : ChooserInput q :=
  ⟨l, hashWidth q b t l, (SourceFamilyEnumeration.families pad b t l).map Prod.snd,
    SourceExceptionalTable.table pad b t l, SourceCoreCatalogue.table pad b t l⟩

theorem input_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (input pad b t) encUnary (chooserEncoding q) := by
  have hf := (SourceFamilyEnumeration.families_polyTime pad b t hq)
  have hrows := (ComputableInPolyTime.map (snd (SourceFamilyMembers.familyShapeEncoding q) rowsEncoding)).comp hf
  exact chooserEncoding_mk_polyTime q id' (UniformParameters.width_machine q b t) hrows
    (SourceExceptionalTable.table_polyTime pad b t hq) (SourceCoreCatalogue.table_polyTime pad b t hq)

private def dimensions (q b t : ℕ) (x : ChooserInput q) : Dimensions := (x.rows, q^gram q b t x.length)

private theorem dimensions_polyTime (q b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (dimensions q b t) (chooserEncoding q) dimensionEncoding := by
  let e := chooserEncoding q
  have hi := id' (encIn := e)
  have hn := (Machine.SourceHashChoice.width_polyTime q b t hq).comp (chooserEncoding_length_polyTime q hi)
  exact (chooserEncoding_rows_polyTime q hi).prod hn

def evaluate (q b t : ℕ) (x : ChooserInput q) (i : Fin 3) (p : Prefix) : ℚ :=
  ![potentialOnPrefix ((dimensions q b t x, x.families), p),
    coreOnPrefix ((dimensions q b t x, x.exceptional), p),
    coreOnPrefix ((dimensions q b t x, x.core), p)] i

def scale (q b t : ℕ) (x : ChooserInput q) (i : Fin 3) : ℚ :=
  ![(x.families.length : ℚ), evaluate q b t x 1 [], evaluate q b t x 2 []] i

private theorem evaluate_polyTime (q b t : ℕ) (hq : 2 ≤ q) (i : Fin 3) :
    ComputableInPolyTime (fun p : ChooserInput q × Prefix => evaluate q b t p.1 i p.2)
      (evaluatorEncoding q) encRat := by
  let e := chooserEncoding q
  let p := ConditionalChoice.prefixEncoding
  have hx := fst e p
  have hn := (dimensions_polyTime q b t hq).comp hx
  have hp := snd e p
  fin_cases i
  · exact potentialOnPrefix_polyTime.comp ((hn.prod (chooserEncoding_families_polyTime q hx)).prod hp)
  · exact (coreOnPrefix_polyTime q).comp ((hn.prod (chooserEncoding_exceptional_polyTime q hx)).prod hp)
  · exact (coreOnPrefix_polyTime q).comp ((hn.prod (chooserEncoding_core_polyTime q hx)).prod hp)

private theorem scale_polyTime (q b t : ℕ) (hq : 2 ≤ q) (i : Fin 3) :
    ComputableInPolyTime (fun p : ChooserInput q => scale q b t p i) (chooserEncoding q) encRat := by
  let e := chooserEncoding q
  have hi := id' (encIn := e)
  have h := hi.prod (const (encOut := ConditionalChoice.prefixEncoding) [])
  fin_cases i
  · have hc := ratOfNat_polyTime.comp (unary_to_binary.comp ((length_list rowsEncoding).comp
      (chooserEncoding_families_polyTime q hi)))
    exact hc.of_enc_eq (fun _ => rfl)
  · have hc := (evaluate_polyTime q b t hq 1).comp h
    exact hc.of_enc_eq (fun _ => rfl)
  · have hc := (evaluate_polyTime q b t hq 2).comp h
    exact hc.of_enc_eq (fun _ => rfl)

def chosenPrefix (q b t : ℕ) (x : ChooserInput q) : Prefix :=
  choose (score (evaluate q b t x) (scale q b t x)) (x.rows * (dimensions q b t x).2)

private theorem chosenPrefix_polyTime (q b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (chosenPrefix q b t) (chooserEncoding q) ConditionalChoice.prefixEncoding := by
  let e := chooserEncoding q
  have hi := id' (encIn := e)
  have hn := dimensions_polyTime q b t hq
  have hf := unary_mul' (chooserEncoding_rows_polyTime q hi) hn.snd'
  have h := choose_three_polyTime (enc := e) (evaluate q b t) (scale q b t)
    (evaluate_polyTime q b t hq) (scale_polyTime q b t hq)
  have hc := h.comp (encIn := e) (hi.prod hf)
  exact hc.of_enc_eq (fun _ => rfl)

def chosenRows (q b t : ℕ) (x : ChooserInput q) : Rows :=
  let width := (dimensions q b t x).2
  tabRows x.rows width (fun i j => (chosenPrefix q b t x).getD (j + width*i) 0)

private theorem chosenRows_polyTime (q b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (chosenRows q b t) (chooserEncoding q) rowsEncoding := by
  let e := chooserEncoding q
  let a := encPair e encUnary
  have hi := id' (encIn := e)
  have hrows := chooserEncoding_rows_polyTime q hi
  have hn := (dimensions_polyTime q b t hq).snd'
  have hp := chosenPrefix_polyTime q b t hq
  have hx := (fst e encUnary).comp (fst a encUnary)
  have hi := (snd e encUnary).comp (fst a encUnary)
  have hj := snd a encUnary
  exact tabRows_polyTime (enc := e) (f := fun x i j => (chosenPrefix q b t x).getD (j + (dimensions q b t x).2*i) 0)
    hrows hn (listGetDWithInput (hp.comp hx) (unary_add' hj (unary_mul' (hn.comp hx) hi)) 0)

private theorem chosenRows_eq (q b t : ℕ) (x : ChooserInput q) :
    chosenRows q b t x = matrixRows (totalHash x.rows (dimensions q b t x).2 (chosenPrefix q b t x)) := by
  unfold chosenRows tabRows matrixRows
  dsimp only
  rw [SourceLists.range_map_eq]
  congr 1
  funext i
  rw [SourceLists.range_map_eq]
  congr 1

private def hashRows (pad : Fin q) (b t l : ℕ) : Rows := chosenRows q b t (input pad b t l)

private theorem hashRows_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (hashRows pad b t) encUnary rowsEncoding :=
  (chosenRows_polyTime q b t hq).comp (input_polyTime pad b t hq)

def setup (pad : Fin q) (b t n : ℕ) : List Bool :=
  encList encBits ((List.range (n+1-minLength q b t)).map fun j =>
    rowsEncoding (hashRows pad b t (minLength q b t+j)))

theorem setup_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (setup pad b t) encUnary encBits := by
  let c := minLength q b t
  have hn := unary_sub' (unary_add' (id' (encIn := encUnary)) (const 1)) (const c)
  have hl := unary_add' (const (encIn := encPair encUnary encUnary) c) (snd encUnary encUnary)
  have hrows := (hashRows_polyTime pad b t hq).comp hl
  have hraw : ComputableInPolyTime (fun p : ℕ × ℕ => rowsEncoding (hashRows pad b t (c+p.2)))
      (encPair encUnary encUnary) encBits := hrows.of_enc_eq (fun _ => rfl)
  have h := mapWithInput (encIn := encUnary) (encA := encUnary) (encB := encBits)
    (f := fun _ j => rowsEncoding (hashRows pad b t (c+j))) (unary_range' hn) hraw
  exact h.of_enc_eq (fun _ => rfl)

private theorem familyRows_member (pad : Fin q) (b t l : ℕ) (r : Rows)
    (hr : r ∈ (input pad b t l).families) : ∃ shape, r = SourceBuckets.rows pad b t l shape := by
  obtain ⟨⟨shape, rs⟩, hs, rfl⟩ := List.mem_map.mp hr
  unfold SourceFamilyEnumeration.families at hs
  obtain ⟨s, _, h⟩ := List.mem_filterMap.mp hs
  dsimp only at h
  split at h
  · contradiction
  · exact ⟨s, (congrArg Prod.snd (Option.some.inj h)).symm⟩

private theorem familiesOf_eq (pad : Fin q) (b t l : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hl : minLength q b t ≤ l) :
    (input pad b t l).families.map (familyOf (q^gram q b t l)) =
      (PeelingFamilyBounds.tables q b t l pad).map Prod.snd := by
  let n := q^gram q b t l
  have hround (r : BucketBalance.Word n) : rowOf n (List.ofFn r) = r := by
    funext i
    exact BooleanFibres.ofFn_getD r i 0
  have h := congrArg (List.map (fun p : BubbleFamilies.Shape q × Finset Row => (p.2).image (rowOf n)))
    (SourceFamilyEnumeration.families_eq pad b t l hq hb ht hl)
  unfold input PeelingFamilyBounds.tables
  simp only [List.map_map, Function.comp_def, Finset.image_image, hround, Finset.image_id'] at h ⊢
  have he (r : Rows) : familyOf n r = r.toFinset.image (rowOf n) := by
    ext z
    simp [familyOf]
  change List.map (fun x : BubbleFamilies.Shape q × Rows => familyOf n x.2) _ = _
  simpa only [he] using h

private theorem conditionalPotential_list {n θ J : ℕ} (p : FieldHash.PartialHash θ n)
    (B : Fin J → BucketBalance.Family n) : BucketBalance.conditionalPotential B p =
      ((List.ofFn B).map fun f =>
        (∑ v ∈ f, ∑ w ∈ f, FieldHash.conditionalKernelProbability (BucketBalance.differenceRow v w) p) /
          f.card - f.card / (3 : ℚ)^θ).sum := by
  simp only [BucketBalance.conditionalPotential, List.map_ofFn, List.sum_ofFn, Function.comp_def]

private theorem potential_eq (pad : Fin q) (b t l : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hl : minLength q b t ≤ l) (p : Prefix) :
    potentialOnPrefix ((dimensions q b t (input pad b t l), (input pad b t l).families), p) =
      BucketBalance.conditionalPotential (PeelingFamilyBounds.vectors q b t l pad)
        (prefixHash (hashWidth q b t l) (q^gram q b t l) p) := by
  let rs := (input pad b t l).families
  let n := q^gram q b t l
  have hL : 1 ≤ gram q b t l := by
    unfold gram gramLength
    apply Nat.mul_pos
    · unfold gramMultiplier
      exact (by decide : 0 < 32).trans_le (Nat.le_max_left ..)
    · omega
  have hn : ∀ r ∈ rs, (r.map (rowOf n)).Nodup := by
    intro r hr
    obtain ⟨s, rfl⟩ := familyRows_member pad b t l r hr
    rw [SourceBuckets.rows_eq pad b t l hq]
    exact Machine.SourceHashChoice.familyRows_nodup s (windowLength q l) b (gram q b t l)
      (omittedLetters q b t l) pad hL
  rw [potentialOnPrefix_eq _ hn, conditionalPotential_list, conditionalPotential_list]
  have h₁ : (List.ofFn (fun j : Fin rs.length => familyOf n (rs.getD j.val []))) = rs.map (familyOf n) := by
    conv_rhs => rw [← List.ofFn_get rs, List.map_ofFn]
    congr 1
    funext i
    exact congrArg (familyOf n) (List.getD_eq_getElem rs [] i.isLt)
  have h₂ : List.ofFn (PeelingFamilyBounds.vectors q b t l pad) =
      (PeelingFamilyBounds.tables q b t l pad).map Prod.snd := by
    conv_rhs => rw [← List.ofFn_get (PeelingFamilyBounds.tables q b t l pad), List.map_ofFn]
    rfl
  change ((List.ofFn (fun j : Fin rs.length => familyOf n (rs.getD j.val []))).map _).sum = _
  rw [h₁, h₂, familiesOf_eq pad b t l hq hb ht hl]
  rfl

private theorem coreOnPrefix_term {n θ : ℕ} (o : CoreWeight.Object l q n) (p : Prefix) :
    Machine.SourceHashChoice.coreTerm ((n, partialRows ((θ, n), p)), objectData o) =
      FieldHash.conditionalKernelProbability o.rules (prefixHash θ n p) / (q : ℚ)^o.assignment.support.card := by
  have he := coreOnPrefix_eq (θ := θ) (fun _ : Fin 1 => o) p
  simpa only [Machine.SourceHashChoice.coreOnPrefix, Machine.SourceHashChoice.coreConditional,
    List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    CoreWeight.conditionalMass, Fin.sum_univ_one] using he

private theorem core_eq (pad : Fin q) (b t l : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hl : minLength q b t ≤ l) (p : Prefix) :
    coreOnPrefix ((dimensions q b t (input pad b t l), (input pad b t l).core), p) =
      CoreWeight.conditionalMass (SourceHashChoice.coreData q b t l pad).object
        (prefixHash (hashWidth q b t l) (q^gram q b t l) p) := by
  let D := SourceHashChoice.coreData q b t l pad
  change coreOnPrefix (((hashWidth q b t l,q^gram q b t l), SourceCoreCatalogue.table pad b t l),p) = _
  rw [SourceCoreCatalogue.table_eq pad hq hb ht hl]
  unfold Machine.SourceHashChoice.coreOnPrefix Machine.SourceHashChoice.coreConditional CoreWeight.conditionalMass
  simp only [CoreWeight.ReplayData.table, List.map_map, Function.comp_def, coreOnPrefix_term]
  exact CoreWeight.ReplayData.sum_indices D _

private theorem evaluator_eq (pad : Fin q) (b t l : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hl : minLength q b t ≤ l) :
    evaluate q b t (input pad b t l) = SourceHashChoice.evaluators q b t l pad := by
  funext i p
  fin_cases i
  · exact potential_eq pad b t l hq hb ht hl p
  · change coreOnPrefix (((hashWidth q b t l,q^gram q b t l), SourceExceptionalTable.table pad b t l),p) = _
    rw [SourceExceptionalTable.table_eq, coreOnPrefix_eq]
    rfl
  · exact core_eq pad b t l hq hb ht hl p

private theorem hashRows_eq (pad : Fin q) (b t l : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hl : minLength q b t ≤ l) :
    hashRows pad b t l = matrixRows (SourceHashChoice.choose q b t l pad) := by
  have hcount := congrArg List.length (familiesOf_eq pad b t l hq hb ht hl)
  simp only [List.length_map] at hcount
  have h := evaluator_eq pad b t l hq hb ht hl
  have hscale : scale q b t (input pad b t l) = catalogueBounds
      (SmallCompression.familyCount q b t l pad) (SourceHashChoice.evaluators q b t l pad) := by
    funext i
    unfold scale catalogueBounds
    rw [h, hcount]
    rfl
  unfold hashRows
  rw [chosenRows_eq]
  unfold chosenPrefix SourceHashChoice.choose chooseHash
  rw [h, hscale]
  rfl

theorem sourceBits_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (SourceSetup.sourceBits q b t pad) encUnary encBits := by
  refine (setup_polyTime pad b t hq).of_enc_eq ?_
  intro n
  apply congrArg encBits
  symm
  unfold setup SourceSetup.sourceBits SourceHashTable.write
  congr 1
  apply List.map_congr_left
  intro j _
  rw [hashRows_eq pad b t _ hq hb ht (by omega)]
  rfl

#print axioms sourceBits_polyTime

end DeletionCode.Explicit.Machine.SourceSetupTime
