import DeletionCode.Explicit.Machine.RareAddress
import DeletionCode.Explicit.FibreListing
import Mathlib.Data.Nat.Digits.Lemmas

/-! Convert between the exceptional catalogue's lexicographic columns and
Mathlib's little-endian gram indices used by the recognizer. -/
namespace DeletionCode.Explicit.Machine.GramOrder

open Ternary FieldHash Qary.SignedSupport
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open _root_.DeletionCode.Explicit.RareAddress (fixedDigits fixedDigits_length rank_fixedDigits)
open Machine.RareAddress (fixedDigits_polyTime)
open scoped BigOperators

variable {q b t n θ : ℕ}

def columns (q L : ℕ) : Fin (q^L) ≃ Fin (q^L) :=
  (ExceptionalWeight.dictionary q L).trans finFunctionFinEquiv

private theorem ofDigits_ofFn (q : ℕ) (a : Fin n → ℕ) :
    Nat.ofDigits q (List.ofFn a) = ∑ j, a j * q^j.val := by
  induction n with
  | zero => simp [Nat.ofDigits]
  | succ n ih =>
    rw [List.ofFn_succ,Nat.ofDigits_cons,Fin.sum_univ_succ,ih,Finset.mul_sum]
    simp only [Fin.val_zero,pow_zero,mul_one]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.val_succ,pow_succ]
    ring

theorem reversed_rank (g : Fin n → Fin q) : wordRank (List.ofFn g).reverse = (finFunctionFinEquiv g).val := by
  unfold wordRank
  rw [List.map_reverse,List.reverse_reverse,List.map_ofFn,ofDigits_ofFn,finFunctionFinEquiv_apply]
  rfl

theorem mainWord_eq (pad : Fin q) (hq : 2 ≤ q) (L : ℕ) (j : Fin (q^L)) :
    (fixedDigits pad L j.val).reverse = List.ofFn (finFunctionFinEquiv.symm j) := by
  apply List.reverse_injective
  rw [List.reverse_reverse]
  apply wordRank_injective_at_length hq
  · simp
  · rw [rank_fixedDigits pad L j.val j.isLt,reversed_rank,Equiv.apply_symm_apply]

def mainWords (pad : Fin q) (L : ℕ) : List (QWord q) :=
  (List.range (q^L)).map (fun j => (fixedDigits pad L j).reverse)

theorem mainWords_eq (pad : Fin q) (hq : 2 ≤ q) (L : ℕ) :
    mainWords pad L = List.ofFn (fun j : Fin (q^L) => List.ofFn (finFunctionFinEquiv.symm j)) := by
  apply List.ext_getElem (by simp [mainWords])
  intro j hj hj'
  have h : j < q^L := by simpa using hj'
  simp only [mainWords,List.getElem_map,List.getElem_range,List.getElem_ofFn]
  exact mainWord_eq pad hq L ⟨j,h⟩

abbrev indexEncoding := encList encNat

def lexIndices (q L : ℕ) : List ℕ := (wordsOfLength q L).map (fun w => wordRank w.reverse)

theorem lexIndices_eq (q L : ℕ) : lexIndices q L = List.ofFn (fun i => (columns q L i).val) := by
  apply List.ext_getElem (by simp [lexIndices,length_wordsOfLength])
  intro i hi hi'
  let j : Fin (q^L) := ⟨i,by simpa using hi'⟩
  simp only [lexIndices,List.getElem_map,List.getElem_ofFn]
  rw [← ExceptionalWeight.dictionary_at q L j,reversed_rank]
  rfl

theorem lexIndices_polyTime (q b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun l => lexIndices q (UniformParameters.gram q b t l)) encUnary indexEncoding := by
  have hr := (wordRank_polyTime hq).comp (listReverse (MatchingPrefixes.symbolEncoding q))
  exact (ComputableInPolyTime.map hr).comp (ExceptionalRecords.gramList_polyTime q b t hq)

/-- The permutation stores the main column number of each lexicographic gram. -/
def toLex (indices : List ℕ) (r : Row) : Row :=
  indices.map (fun i => r.getD i 0)

def toMain (indices : List ℕ) (r : Row) : Row :=
  (List.range indices.length).map fun i => r.getD (indices.idxOf i) 0

abbrev rowPermutationEncoding := encPair indexEncoding rowEncoding

theorem toLex_polyTime :
    ComputableInPolyTime (fun x : List ℕ × Row => toLex x.1 x.2) rowPermutationEncoding rowEncoding := by
  have hl := fst indexEncoding rowEncoding
  have hr := (snd indexEncoding rowEncoding).comp (fst rowPermutationEncoding encNat)
  exact mapWithInput (encA := encNat) (f := fun x i => x.2.getD i 0) hl
    (listGetD_binary (encA := tritEncoding) (encL := rowEncoding) 0 hr (snd rowPermutationEncoding encNat))

theorem toMain_polyTime :
    ComputableInPolyTime (fun x : List ℕ × Row => toMain x.1 x.2) rowPermutationEncoding rowEncoding := by
  let e := rowPermutationEncoding
  have hl := fst indexEncoding rowEncoding
  have hr := snd indexEncoding rowEncoding
  have ha := fst e encUnary
  have hi := unary_to_binary.comp (snd e encUnary)
  have hj := idxOfWithInput (hl.comp ha) hi
  exact mapWithInput (encA := encUnary) (f := fun x i => x.2.getD (x.1.idxOf i) 0)
    (unary_range' ((length_list encNat).comp hl)) (listGetDWithInput (hr.comp ha) hj 0)

theorem toLex_eq (q L : ℕ) (r : Fin (q^L) → F₃) :
    toLex (lexIndices q L) (List.ofFn r) = List.ofFn (r ∘ columns q L) := by
  rw [toLex,lexIndices_eq,List.map_ofFn]
  congr 1
  funext i
  exact BooleanFibres.ofFn_getD r (columns q L i) 0

private theorem indexOf_main (q L : ℕ) (i : Fin (q^L)) :
    (lexIndices q L).idxOf i.val = ((columns q L).symm i).val := by
  rw [lexIndices_eq]
  let e := columns q L
  have hn : (List.ofFn (fun j => (e j).val)).Nodup :=
    List.nodup_ofFn.mpr (fun _ _ h => e.injective (Fin.ext h))
  let j := e.symm i
  have hj : j.val < (List.ofFn fun k => (e k).val).length := by simp
  have he : (List.ofFn (fun k => (e k).val))[j.val] = i.val := by
    simp only [List.getElem_ofFn]
    exact congrArg Fin.val (e.apply_symm_apply i)
  rw [← he]
  exact hn.idxOf_getElem j.val hj

theorem toMain_eq (q L : ℕ) (r : Fin (q^L) → F₃) :
    toMain (lexIndices q L) (List.ofFn r) = List.ofFn (r ∘ (columns q L).symm) := by
  unfold toMain
  have h : (lexIndices q L).length = q^L := by rw [lexIndices_eq,List.length_ofFn]
  rw [h]
  apply List.ext_getElem (by simp)
  intro j hj hi
  let i : Fin (q^L) := ⟨j,by simpa using hi⟩
  simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  rw [show (lexIndices q L).idxOf j = ((columns q L).symm i).val from indexOf_main q L i]
  exact BooleanFibres.ofFn_getD r ((columns q L).symm i) 0

def toLexRows (indices : List ℕ) (rs : Rows) : Rows := rs.map (toLex indices)
def toMainRows (indices : List ℕ) (rs : Rows) : Rows := rs.map (toMain indices)

abbrev rowsPermutationEncoding := encPair indexEncoding rowsEncoding

theorem toLexRows_polyTime :
    ComputableInPolyTime (fun x : List ℕ × Rows => toLexRows x.1 x.2) rowsPermutationEncoding rowsEncoding := by
  let e := rowsPermutationEncoding
  exact mapWithInput (encIn := e) (encA := rowEncoding) (f := fun x r => toLex x.1 r)
    (snd indexEncoding rowsEncoding) (toLex_polyTime.comp
      (((fst indexEncoding rowsEncoding).comp (fst e rowEncoding)).prod (snd e rowEncoding)))

theorem toMainRows_polyTime :
    ComputableInPolyTime (fun x : List ℕ × Rows => toMainRows x.1 x.2) rowsPermutationEncoding rowsEncoding := by
  let e := rowsPermutationEncoding
  exact mapWithInput (encIn := e) (encA := rowEncoding) (f := fun x r => toMain x.1 r)
    (snd indexEncoding rowsEncoding) (toMain_polyTime.comp
      (((fst indexEncoding rowsEncoding).comp (fst e rowEncoding)).prod (snd e rowEncoding)))

theorem toLexRows_eq (q L : ℕ) (A : TernaryMatrix θ (q^L)) :
    toLexRows (lexIndices q L) (CataloguePrefix.matrixRows A) =
      CataloguePrefix.matrixRows (fun i j => A i (columns q L j)) := by
  unfold toLexRows CataloguePrefix.matrixRows
  rw [List.map_ofFn]
  congr 1
  funext i
  exact toLex_eq q L (A i)

theorem toMainRows_eq (q L : ℕ) (A : TernaryMatrix θ (q^L)) :
    toMainRows (lexIndices q L) (CataloguePrefix.matrixRows A) =
      CataloguePrefix.matrixRows (fun i j => A i ((columns q L).symm j)) := by
  unfold toMainRows CataloguePrefix.matrixRows
  rw [List.map_ofFn]
  congr 1
  funext i
  exact toMain_eq q L (A i)

theorem mulVec_columns (q L : ℕ) (A : TernaryMatrix θ (q^L)) (r : Fin (q^L) → F₃) :
    Matrix.mulVec (fun i j => A i (columns q L j)) (r ∘ columns q L) = A.mulVec r := by
  funext i
  exact Equiv.sum_comp (columns q L) (fun j => A i j * r j)

#print axioms mainWords_eq
#print axioms lexIndices_eq
#print axioms lexIndices_polyTime
#print axioms toLexRows_eq
#print axioms toMainRows_eq
#print axioms toLexRows_polyTime
#print axioms toMainRows_polyTime
#print axioms mulVec_columns

end DeletionCode.Explicit.Machine.GramOrder
