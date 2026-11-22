import DeletionCode.Explicit.Machine.SourceFamilyMembers
import DeletionCode.Explicit.Machine.SourceMixedRadix

/-! Compute ordered family buckets and the vectors consumed by the hash chooser. -/
namespace DeletionCode.Explicit.Machine.SourceBuckets

open FieldHash Ternary CataloguePrefix SourceFamilyMembers OrderedCatalogue
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {q ℓ K b L θ : ℕ}

def vector (pad : Fin q) (L : ℕ) (w : BubbleData q) : Row :=
  SourceRuleRows.row pad L [w]

theorem vector_eq (pad : Fin q) (hq : 2 ≤ q) (w : Borrowed.BubbleWord (Fin q) K b L) :
    vector pad L (bubbleData w) = List.ofFn (BubbleFamilies.vector pad w) := by
  have h := SourceRuleRows.row_eq pad hq (fun _ : Fin 1 => w)
  simp only [List.ofFn_succ,List.ofFn_zero,Function.comp_def] at h
  unfold vector
  rw [h]
  congr 1
  funext i
  simp [CatalogueEnumeration.row]

def rows (pad : Fin q) (b t ℓ : ℕ) (s : BubbleFamilies.Shape q) : Rows :=
  (members pad b t ℓ s).map (fun p => vector pad (UniformParameters.gram q b t ℓ) p.2)

theorem rows_eq (pad : Fin q) (b t ℓ : ℕ) (hq : 2 ≤ q) (s : BubbleFamilies.Shape q) :
    rows pad b t ℓ s =
      (s.members (UniformParameters.windowLength q ℓ) b (UniformParameters.gram q b t ℓ)
        (UniformParameters.omittedLetters q b t ℓ) pad).map (fun p => List.ofFn (BubbleFamilies.vector pad p.2)) := by
  rw [rows,members_eq,List.map_map]
  simp [Function.comp_def,vector_eq pad hq]

theorem rows_nodup (pad : Fin q) (b t ℓ : ℕ) (hq : 2 ≤ q)
    (s : BubbleFamilies.Shape q) (hL : 1 ≤ UniformParameters.gram q b t ℓ) :
    (rows pad b t ℓ s).Nodup := by
  rw [rows_eq pad b t ℓ hq]
  apply (BubbleFamilies.members_nodup s _ _ _ _ pad).map_on
  intro x hx y hy he
  have hm := (BubbleFamilies.mem_members s _ _ _ _ pad x.1 x.2).mp hx
  have hn := (BubbleFamilies.mem_members s _ _ _ _ pad y.1 y.2).mp hy
  have h := BubbleFamilies.member_vector_injective s pad hL hm.2 hn.2 (List.ofFn_inj.mp he)
  exact Prod.ext h (Option.some.inj (hm.2.symm.trans (h.symm ▸ hn.2)))

def bucket (pad : Fin q) (b t ℓ : ℕ) (s : BubbleFamilies.Shape q) (H : Rows) (z : Row) :
    List (QWord q × BubbleData q) :=
  let L := UniformParameters.gram q b t ℓ
  (members pad b t ℓ s).filter (fun p => decide (SourceSpectrum.applyRows (q^L) H (vector pad L p.2) = z))

theorem bucket_eq (pad : Fin q) (b t ℓ : ℕ) (hq : 2 ≤ q) (s : BubbleFamilies.Shape q)
    (H : TernaryMatrix θ (q^UniformParameters.gram q b t ℓ)) (z : Fin θ → F₃) :
    bucket pad b t ℓ s (matrixRows H) (List.ofFn z) =
      (BubbleFamilies.bucket s (UniformParameters.windowLength q ℓ) b (UniformParameters.gram q b t ℓ)
        (UniformParameters.omittedLetters q b t ℓ) pad H z).map (fun p => (p.1,bubbleData p.2)) := by
  unfold bucket BubbleFamilies.bucket
  rw [members_eq,List.filter_map]
  congr 1
  apply List.filter_congr
  intro x hx
  simp [Function.comp_def,vector_eq pad hq,SourceSpectrum.applyRows_matrix_eq,List.ofFn_inj]

theorem bucket_length_le (pad : Fin q) (b t ℓ : ℕ) (s : BubbleFamilies.Shape q) (H : Rows) (z : Row) :
    (bucket pad b t ℓ s H z).length ≤ q^(2*UniformParameters.gram q b t ℓ+b) :=
  (List.length_filter_le ..).trans (members_length_le pad b t ℓ s)

theorem vector_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : ℕ × BubbleData q => vector pad (UniformParameters.gram q b t x.1) x.2)
      (encPair encUnary (bubbleEncoding q)) rowEncoding := by
  let w := bubbleEncoding q
  have hg := (SourceSpectrum.mainWords_polyTime pad b t hq).comp (fst encUnary w)
  have h := (SourceRuleRows.rowWith_polyTime q).comp (hg.prod (cons' (snd encUnary w) (const [])))
  exact h.of_enc_eq (fun _ => rfl)

theorem rows_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : ℕ × BubbleFamilies.Shape q => rows pad b t x.1 x.2)
      (uniformInputEncoding q) rowsEncoding := by
  let e := uniformInputEncoding q
  let w := memberDataEncoding q
  have hg := (fst encUnary (familyShapeEncoding q)).comp (fst e w)
  have hm := members_polyTime pad b t hq
  have h := (vector_polyTime pad b t hq).comp (hg.prod (snd e w).snd')
  exact mapWithInput (encIn := e) (encA := w) (encB := rowEncoding)
    (f := fun x p => vector pad (UniformParameters.gram q b t x.1) p.2) hm h

abbrev bucketEncoding (q : ℕ) := encPair (uniformInputEncoding q) (encPair rowsEncoding rowEncoding)

theorem bucket_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : (ℕ × BubbleFamilies.Shape q) × (Rows × Row) =>
      bucket pad b t x.1.1 x.1.2 x.2.1 x.2.2) (bucketEncoding q) (membersEncoding q) := by
  let e := bucketEncoding q
  let u := uniformInputEncoding q
  let d := encPair rowsEncoding rowEncoding
  let w := memberDataEncoding q
  let p := encPair e w
  have hx := fst u d
  have hy := snd u d
  have hs := (members_polyTime pad b t hq).comp hx
  have ha := fst e w
  have hℓ := hx.fst'.comp ha
  have hvec := (vector_polyTime pad b t hq).comp (hℓ.prod (snd e w).snd')
  have hn := (SourceHashChoice.width_polyTime q b t hq).comp hℓ
  have hb := (hy.fst'.comp ha)
  have hout := SourceSpectrum.applyRows_polyTime.comp ((hn.prod hb).prod hvec)
  exact filterWithInput (encIn := e) (encA := w)
    (test := fun x p => decide (SourceSpectrum.applyRows (q ^ UniformParameters.gram q b t x.1.1)
      x.2.1 (vector pad (UniformParameters.gram q b t x.1.1) p.2) = x.2.2))
    hs (hout.decide_eq' (hy.snd'.comp ha))

#print axioms vector_eq
#print axioms rows_eq
#print axioms rows_nodup
#print axioms bucket_eq
#print axioms bucket_length_le
#print axioms rows_polyTime
#print axioms bucket_polyTime

end DeletionCode.Explicit.Machine.SourceBuckets
