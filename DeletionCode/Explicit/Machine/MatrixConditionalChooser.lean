import DeletionCode.Explicit.MatrixConditionalChooser
import DeletionCode.Explicit.Machine.ConditionalChooser
import DeletionCode.Explicit.Machine.TernaryPotential

/-! Row-major prefix adapter and the certified bucket potential for the chooser. -/
namespace DeletionCode.Explicit.Machine.ConditionalChoice

open FieldHash ConditionalChooser
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

abbrev Dimensions := ℕ × ℕ
abbrev dimensionEncoding := encPair encUnary encUnary
abbrev prefixInputEncoding := encPair dimensionEncoding prefixEncoding

private def partialRow (x : (Dimensions × Prefix) × ℕ) : Ternary.PartialRow :=
  (List.range x.1.1.2).map fun j =>
    (x.1.2.map some).getD (j + x.1.1.2 * x.2) none

def partialRows (x : Dimensions × Prefix) : Ternary.PartialRows :=
  (List.range x.1.1).map fun i => partialRow (x, i)

private theorem partialRow_polyTime :
    ComputableInPolyTime partialRow (encPair prefixInputEncoding encUnary) Ternary.partialRowEncoding := by
  let src := encPair prefixInputEncoding encUnary
  let arg := encPair src encUnary
  have hw := (fst prefixInputEncoding encUnary).fst'.snd'
  have hl := range.comp hw
  have hbase := fst src encUnary
  have hi := (snd prefixInputEncoding encUnary).comp hbase
  have hj := snd src encUnary
  have hlist := (ComputableInPolyTime.map (optionSome Ternary.tritEncoding)).comp
    ((fst prefixInputEncoding encUnary).snd'.comp hbase)
  have hindex := unary_add' hj (unary_mul' (hw.comp hbase) hi)
  exact mapWithInput (f := fun x j => (x.1.2.map some).getD (j + x.1.1.2 * x.2) none)
    hl (listGetDWithInput hlist hindex none)

theorem partialRows_polyTime :
    ComputableInPolyTime partialRows prefixInputEncoding Ternary.partialRowsEncoding :=
  mapWithInput (f := fun x i => partialRow (x, i))
    (range.comp (fst dimensionEncoding prefixEncoding).fst') partialRow_polyTime

@[simp] theorem partialRows_length (x : Dimensions × Prefix) :
    (partialRows x).length = x.1.1 := by simp [partialRows]

private theorem range_map_getD {A : Type*} (m i : ℕ) (f : ℕ → A) (d : A) (hi : i < m) :
    ((List.range m).map f).getD i d = f i := by
  have h : i < ((List.range m).map f).length := by simpa using hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, List.getElem_map,
    List.getElem_range, Option.getD_some]

theorem partialRows_hash (θ n : ℕ) (p : Prefix) (i : Fin (partialRows ((θ, n), p)).length)
    (j : Fin n) :
    Ternary.hashOf n (partialRows ((θ, n), p)) i j =
      prefixHash θ n p (Fin.cast (partialRows_length _) i) j := by
  have hi : i.val < θ :=
    i.isLt.trans_le (partialRows_length ((θ, n), p)).le
  have hrow : (partialRows ((θ, n), p)).getD i.val [] = partialRow (((θ, n), p), i.val) :=
    range_map_getD θ i.val (fun k => partialRow (((θ, n), p), k)) [] hi
  unfold Ternary.hashOf Ternary.partialValue
  rw [hrow]
  change ((List.range n).map (fun k => (p.map some).getD (k + n * i.val) none)).getD j.val none = _
  rw [range_map_getD _ _ _ _ j.isLt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  change (p[j.val + n * i.val]?.map some).getD none = p[j.val + n * i.val]?
  cases p[j.val + n * i.val]? <;> rfl

abbrev PotentialData := Dimensions × List Ternary.Rows
abbrev potentialDataEncoding := encPair dimensionEncoding (encList Ternary.rowsEncoding)

def potentialOnPrefix (x : PotentialData × Prefix) : ℚ :=
  Ternary.potential ((x.1.1.2, partialRows (x.1.1, x.2)), x.1.2)

theorem potentialOnPrefix_polyTime :
    ComputableInPolyTime potentialOnPrefix (encPair potentialDataEncoding prefixEncoding) encRat := by
  have hd := fst potentialDataEncoding prefixEncoding
  have hp := snd potentialDataEncoding prefixEncoding
  exact Ternary.potential_polyTime.comp
    ((hd.fst'.snd'.prod (partialRows_polyTime.comp (hd.fst'.prod hp))).prod hd.snd')

private theorem potential_represents {θ n : ℕ} (rs : List Ternary.Rows)
    (rows : Ternary.PartialRows) (h : rows.length = θ) (p : PartialHash θ n)
    (hr : ∀ i j, Ternary.hashOf n rows i j = p (Fin.cast h i) j)
    (hN : ∀ s ∈ rs, (s.map (Ternary.rowOf n)).Nodup) :
    Ternary.potential ((n, rows), rs) = BucketBalance.conditionalPotential
      (fun j : Fin rs.length => Ternary.familyOf n (rs.getD j.val [])) p := by
  subst θ
  rw [Ternary.potential_eq _ hN]
  congr 1
  exact funext fun i => funext fun j => hr i j

theorem potentialOnPrefix_eq (x : PotentialData × Prefix)
    (hN : ∀ rs ∈ x.1.2, (rs.map (Ternary.rowOf x.1.1.2)).Nodup) :
    potentialOnPrefix x = BucketBalance.conditionalPotential
      (fun j : Fin x.1.2.length => Ternary.familyOf x.1.1.2 (x.1.2.getD j.val []))
      (prefixHash x.1.1.1 x.1.1.2 x.2) := by
  exact potential_represents _ _ (partialRows_length _) _ (partialRows_hash _ _ _) hN

#print axioms partialRows_polyTime
#print axioms partialRows_hash
#print axioms potentialOnPrefix_polyTime
#print axioms potentialOnPrefix_eq

end DeletionCode.Explicit.Machine.ConditionalChoice
