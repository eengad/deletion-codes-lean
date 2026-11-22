import DeletionCode.Explicit.Machine.Labels
import DeletionCode.Explicit.Machine.TagTables
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup

/-! Uniform computation of the wrapper with decoded tag tables and opaque
source bits. The tag table encoding supplies the unary indices used for lookups. -/
namespace DeletionCode.Explicit.Machine

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

abbrev PublicData (q : ℕ) := TagTables q × List Bool
abbrev WrapperInput (q : ℕ) := PublicData q × QWord q

abbrev publicDataEncoding (q : ℕ) : PublicData q ↪ List Bool :=
  encPair (tagTablesEncoding q) encBits

abbrev wrapperInputEncoding (q : ℕ) : WrapperInput q ↪ List Bool :=
  encPair (publicDataEncoding q) (wordEncoding q)

abbrev codeEncoding (q : ℕ) := encList (wordEncoding q)

private abbrev TagView (q : ℕ) :=
  ℕ × ℕ × ℕ × ℕ × List (List (QWord q)) × List (QWord q)

private abbrev viewEncoding (q : ℕ) : TagView q ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary
    (encPair (encList (codeEncoding q)) (codeEncoding q)))))

private theorem view_polyTime (q : ℕ) :
    ComputableInPolyTime (fun T : TagTables q =>
      (T.k, T.m₀, T.mOut, T.labelCount, T.innerCodes, T.outerCode))
      (tagTablesEncoding q) (viewEncoding q) :=
  of_eq fun _ => rfl

section CertifiedProjections

variable {α : Type} {enc : α ↪ List Bool} {q : ℕ}
  {T : α → TagTables q} (hT : ComputableInPolyTime T enc (tagTablesEncoding q))
include hT

theorem tagK_polyTime : ComputableInPolyTime (fun a => (T a).k) enc encUnary :=
  ((view_polyTime q).comp hT).fst'

theorem tagBase_polyTime : ComputableInPolyTime (fun a => (T a).m₀) enc encUnary :=
  ((view_polyTime q).comp hT).snd'.fst'

theorem tagOuterLength_polyTime : ComputableInPolyTime (fun a => (T a).mOut) enc encUnary :=
  ((view_polyTime q).comp hT).snd'.snd'.fst'

theorem tagCount_polyTime : ComputableInPolyTime (fun a => (T a).labelCount) enc encUnary :=
  ((view_polyTime q).comp hT).snd'.snd'.snd'.fst'

theorem tagInnerCodes_polyTime :
    ComputableInPolyTime (fun a => (T a).innerCodes) enc (encList (codeEncoding q)) :=
  ((view_polyTime q).comp hT).snd'.snd'.snd'.snd'.fst'

theorem tagOuterCode_polyTime :
    ComputableInPolyTime (fun a => (T a).outerCode) enc (codeEncoding q) :=
  ((view_polyTime q).comp hT).snd'.snd'.snd'.snd'.snd'

end CertifiedProjections

def tagBin {q : ℕ} (T : TagTables q) (l : ℕ) := Nat.clog q (T.k - l + 1)

def tagInner {q : ℕ} (T : TagTables q) (j l z : ℕ) : QWord q :=
  (T.innerCodes.getD j []).getD ((T.k - l) * T.labelCount + z) []

def tagOuter {q : ℕ} (T : TagTables q) (j : ℕ) : QWord q :=
  T.outerCode.getD j []

section TagCertificates

variable {α : Type} {enc : α ↪ List Bool} {q : ℕ}
  {T : α → TagTables q} {j l z : α → ℕ}

theorem tagBin_polyTime (hT : ComputableInPolyTime T enc (tagTablesEncoding q))
    (hl : ComputableInPolyTime l enc encUnary) :
    ComputableInPolyTime (fun a => tagBin (T a) (l a)) enc encUnary :=
  (unary_clog_const q).comp (unary_add' (unary_sub' (tagK_polyTime hT) hl) (const 1))

theorem tagInner_polyTime (hT : ComputableInPolyTime T enc (tagTablesEncoding q))
    (hj : ComputableInPolyTime j enc encUnary) (hl : ComputableInPolyTime l enc encUnary)
    (hz : ComputableInPolyTime z enc encNat) :
    ComputableInPolyTime (fun a => tagInner (T a) (j a) (l a) (z a)) enc (wordEncoding q) := by
  have hoff := unary_mul' (unary_sub' (tagK_polyTime hT) hl) (tagCount_polyTime hT)
  have hi := binary_add.comp ((unary_to_binary.comp hoff).prod hz)
  exact listGetD_binary [] (listGetDWithInput (tagInnerCodes_polyTime hT) hj []) hi

theorem tagOuter_polyTime (hT : ComputableInPolyTime T enc (tagTablesEncoding q))
    (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun a => tagOuter (T a) (j a)) enc (wordEncoding q) :=
  listGetDWithInput (tagOuterCode_polyTime hT) hj []

end TagCertificates

def encodeWrapped {q : ℕ} (zero : Fin q) (l₀ : ℕ) (F : SourceCallbacks q)
    (p : WrapperInput q) : QWord q :=
  let T := p.1.1
  let bits := p.1.2
  let x := F.repair (bits, p.2)
  let j := tagBin T x.length
  let padding := List.replicate (T.k - x.length - j) zero
  let label := labelAt l₀ (fun y => F.label (bits, y)) x
  padding ++ x ++ tagInner T j x.length label ++ tagOuter T j

theorem encodeWrapped_polyTime {q : ℕ} (hq : 2 ≤ q) (zero : Fin q) (l₀ : ℕ)
    (F : SourceCallbacks q) (H : F.Certified) :
    ComputableInPolyTime (encodeWrapped zero l₀ F)
      (wrapperInputEncoding q) (wordEncoding q) := by
  have hp := fst (publicDataEncoding q) (wordEncoding q)
  have hT := hp.fst'
  have hbits := hp.snd'
  have hw := snd (publicDataEncoding q) (wordEncoding q)
  have hx := (F.repair_polyTime H).comp (hbits.prod hw)
  have hl := (wordLength_polyTime q).comp hx
  have hj := tagBin_polyTime hT hl
  have hpad : ComputableInPolyTime
      (fun p : WrapperInput q => List.replicate
        (p.1.1.k - (F.repair (p.1.2, p.2)).length - tagBin p.1.1 (F.repair (p.1.2, p.2)).length)
        zero) (wrapperInputEncoding q) (wordEncoding q) :=
    replicate (unary_sub' (unary_sub' (tagK_polyTime hT) hl) hj) (const zero)
  have hlabel := (labelAt_polyTime hq F H l₀).comp (hbits.prod hx)
  have hinner := tagInner_polyTime hT hj hl hlabel
  have houter := tagOuter_polyTime hT hj
  unfold encodeWrapped
  unfold wordEncoding at hpad hx hinner houter ⊢
  exact listAppend' (listAppend' (listAppend' hpad hx) hinner) houter

theorem encodeWrapped_eq {q : ℕ} (zero : Fin q) (l₀ : ℕ) (F : SourceCallbacks q)
    (T : TagTables q) {bits : List Bool} (h : F.RepairLaws bits) (u : QWord q) :
    encodeWrapped zero l₀ F ((T, bits), u) =
      (T.wrapper zero (F.repairData bits h) (labelAt l₀ (fun w => F.label (bits, w)))).encode u := by
  simp only [encodeWrapped, F.repair_eq h]
  rfl

#print axioms encodeWrapped_polyTime
#print axioms encodeWrapped_eq

end DeletionCode.Explicit.Machine
