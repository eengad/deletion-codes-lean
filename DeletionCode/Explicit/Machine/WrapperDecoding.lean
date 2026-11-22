import DeletionCode.Explicit.Machine.Wrapper
import DeletionCode.Explicit.Machine.EditBall

/-! Machine certificates for the exact image test and bounded decoding search. -/
namespace DeletionCode.Explicit.Machine

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

private theorem findSome_eq {α β : Type} (f : α → Option β) (xs : List α) :
    xs.findSome? f = ((xs.map f).find? Option.isSome).getD none := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases h : f a <;> simp [h, ih]

theorem findSomeWithInput_polyTime {α β γ : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {enc : γ ↪ List Bool}
    {xs : γ → List α} {f : γ → α → Option β}
    (hxs : ComputableInPolyTime xs enc (encList encA))
    (hf : ComputableInPolyTime (fun p => f p.1 p.2) (encPair enc encA) (encOption encB)) :
    ComputableInPolyTime (fun a => (xs a).findSome? (f a)) enc (encOption encB) := by
  have hmap := mapWithInput (f := f) hxs hf
  have hchoose := findWithInput (test := fun (_ : γ) (value : Option β) => value.isSome)
    hmap (optionIsSome (snd enc (encOption encB)))
  exact (optionGetDWithInput hchoose (const none)).of_enc_eq fun a =>
    congrArg (encOption encB) (findSome_eq (f a) (xs a))

private def splitEnd {q : ℕ} (w : QWord q) (n : ℕ) : QWord q × QWord q :=
  (w.take (w.length - n), w.drop (w.length - n))

private theorem splitEnd_polyTime {α : Type} {q : ℕ} {enc : α ↪ List Bool}
    {w : α → QWord q} {n : α → ℕ}
    (hw : ComputableInPolyTime w enc (wordEncoding q)) (hn : ComputableInPolyTime n enc encUnary) :
    ComputableInPolyTime (fun a => splitEnd (w a) (n a)) enc
      (encPair (wordEncoding q) (wordEncoding q)) := by
  have hi := unary_sub' ((wordLength_polyTime q).comp hw) hn
  unfold splitEnd wordEncoding at *
  exact (listTakeWithInput hw hi).prod (listDropWithInput hw hi)

private abbrev rowEncoding := encPair encUnary encUnary

private def tagRows {q : ℕ} (T : TagTables q) : List (ℕ × ℕ) :=
  (List.range (T.k + 1)).flatMap fun l => (List.range T.labelCount).map fun z => (l, z)

private theorem tagRows_polyTime {α : Type} {q : ℕ} {enc : α ↪ List Bool}
    {T : α → TagTables q} (hT : ComputableInPolyTime T enc (tagTablesEncoding q)) :
    ComputableInPolyTime (fun a => tagRows (T a)) enc (encList rowEncoding) := by
  have hl := unary_range' (unary_add' (tagK_polyTime hT) (const 1))
  have hrows := unary_range' (tagCount_polyTime (hT.comp (fst enc encUnary)))
  have hmk := ((fst (encPair enc encUnary) encUnary).snd').prod
    (snd (encPair enc encUnary) encUnary)
  unfold tagRows
  exact flatMapWithInput hl (mapWithInput hrows hmk)

private def verifyInverse {q : ℕ} (zero : Fin q) (l₀ : ℕ) (F : SourceCallbacks q)
    (p : WrapperInput q × QWord q) : Option (QWord q) :=
  (F.inverse ((p.1.1.2, p.2), p.1.1.1.k)).elim none
    (fun u => if encodeWrapped zero l₀ F (p.1.1, u) = p.1.2 then some u else none)

private theorem verifyInverse_polyTime {q : ℕ} (hq : 2 ≤ q) (zero : Fin q) (l₀ : ℕ)
    (F : SourceCallbacks q) (H : F.Certified) :
    ComputableInPolyTime (verifyInverse zero l₀ F)
      (encPair (wrapperInputEncoding q) (wordEncoding q)) (encOption (wordEncoding q)) := by
  let enc := encPair (wrapperInputEncoding q) (wordEncoding q)
  have hp := fst (wrapperInputEncoding q) (wordEncoding q)
  have hdata := hp.fst'
  have hx := snd (wrapperInputEncoding q) (wordEncoding q)
  have hi := (F.inverse_polyTime H).comp ((hdata.snd'.prod hx).prod (tagK_polyTime hdata.fst'))
  have hparent := fst enc (wordEncoding q)
  have hu := snd enc (wordEncoding q)
  have henc := (encodeWrapped_polyTime hq zero l₀ F H).comp ((hdata.comp hparent).prod hu)
  have hword := hp.snd'.comp hparent
  exact optionElimWithInput hi (const none)
    (ite_decide (henc.decide_eq' hword) ((optionSome _).comp hu) (const none))

private def readTagRow {q : ℕ} (zero : Fin q) (l₀ : ℕ) (F : SourceCallbacks q)
    (p : WrapperInput q × (ℕ × ℕ)) : Option (QWord q) :=
  let T := p.1.1.1
  let l := p.2.1
  let j := tagBin T l
  let a := splitEnd p.1.2 T.mOut
  let b := splitEnd a.1 (T.m₀ + j)
  if a.2 = tagOuter T j ∧ b.2 = tagInner T j l p.2.2 then
    verifyInverse zero l₀ F (p.1, (splitEnd b.1 l).2)
  else none

private theorem readTagRow_polyTime {q : ℕ} (hq : 2 ≤ q) (zero : Fin q) (l₀ : ℕ)
    (F : SourceCallbacks q) (H : F.Certified) :
    ComputableInPolyTime (readTagRow zero l₀ F)
      (encPair (wrapperInputEncoding q) rowEncoding) (encOption (wordEncoding q)) := by
  have hp := fst (wrapperInputEncoding q) rowEncoding
  have hT := hp.fst'.fst'
  have hr := snd (wrapperInputEncoding q) rowEncoding
  have hl := hr.fst'
  have hj := tagBin_polyTime hT hl
  have ha := splitEnd_polyTime hp.snd' (tagOuterLength_polyTime hT)
  have hb := splitEnd_polyTime ha.fst' (unary_add' (tagBase_polyTime hT) hj)
  have ho := tagOuter_polyTime hT hj
  have hin := tagInner_polyTime hT hj hl (unary_to_binary.comp hr.snd')
  have htest := decide_and (ha.snd'.decide_eq' ho) (hb.snd'.decide_eq' hin)
  have hverify := (verifyInverse_polyTime hq zero l₀ F H).comp
    (hp.prod (splitEnd_polyTime hb.fst' hl).snd')
  exact ite_decide htest hverify (const none)

private def transmittedLength {q : ℕ} (T : TagTables q) : ℕ := T.k + T.m₀ + T.mOut

private theorem transmittedLength_polyTime {α : Type} {q : ℕ} {enc : α ↪ List Bool}
    {T : α → TagTables q} (hT : ComputableInPolyTime T enc (tagTablesEncoding q)) :
    ComputableInPolyTime (fun a => transmittedLength (T a)) enc encUnary :=
  unary_add' (unary_add' (tagK_polyTime hT) (tagBase_polyTime hT)) (tagOuterLength_polyTime hT)

def imageTestWrapped {q : ℕ} (zero : Fin q) (l₀ : ℕ) (F : SourceCallbacks q)
    (p : WrapperInput q) : Option (QWord q) :=
  if p.2.length = transmittedLength p.1.1 then
    (tagRows p.1.1).findSome? fun row => readTagRow zero l₀ F (p, row)
  else none

theorem imageTestWrapped_polyTime {q : ℕ} (hq : 2 ≤ q) (zero : Fin q) (l₀ : ℕ)
    (F : SourceCallbacks q) (H : F.Certified) :
    ComputableInPolyTime (imageTestWrapped zero l₀ F)
      (wrapperInputEncoding q) (encOption (wordEncoding q)) := by
  have hT := (fst (publicDataEncoding q) (wordEncoding q)).fst'
  have hlen := (wordLength_polyTime q).comp (snd (publicDataEncoding q) (wordEncoding q))
  have htest := hlen.decide_eq' (transmittedLength_polyTime hT)
  exact ite_decide htest
    (findSomeWithInput_polyTime (f := fun p row => readTagRow zero l₀ F (p, row))
      (tagRows_polyTime hT) (readTagRow_polyTime hq zero l₀ F H)) (const none)

private theorem candidates_polyTime {q : ℕ} (b t : ℕ) :
    ComputableInPolyTime (fun p : ℕ × QWord q => candidates p.1 b t p.2)
      (encPair encUnary (wordEncoding q)) (codeEncoding q) := by
  have hn := fst encUnary (wordEncoding q)
  have hz := snd encUnary (wordEncoding q)
  have hlen := (wordLength_polyTime q).comp hz
  have htest := decide_and (unary_le' (unary_sub' hn (const (t * b))) hlen)
    (unary_le' hlen (unary_add' hn (const (t * b))))
  have hfilt := filterWithInput
    (test := fun (p : ℕ × QWord q) (w : QWord q) => w.length == p.1)
    ((editBall_polyTime b t).comp hz)
    (unary_beq ((wordLength_polyTime q).comp (snd _ _)) (hn.comp (fst _ _)))
  exact ite_decide htest hfilt (const [])

def decodeWrapped {q : ℕ} (zero : Fin q) (l₀ b t : ℕ) (F : SourceCallbacks q)
    (p : WrapperInput q) : Option (QWord q) :=
  (candidates (transmittedLength p.1.1) b t p.2).findSome? fun w =>
    imageTestWrapped zero l₀ F (p.1, w)

theorem decodeWrapped_polyTime {q : ℕ} (hq : 2 ≤ q) (zero : Fin q) (l₀ b t : ℕ)
    (F : SourceCallbacks q) (H : F.Certified) :
    ComputableInPolyTime (decodeWrapped zero l₀ b t F)
      (wrapperInputEncoding q) (encOption (wordEncoding q)) := by
  have hp := fst (publicDataEncoding q) (wordEncoding q)
  have hz := snd (publicDataEncoding q) (wordEncoding q)
  have hcandidates := (candidates_polyTime (q := q) b t).comp
    ((transmittedLength_polyTime hp.fst').prod hz)
  have htest := (imageTestWrapped_polyTime hq zero l₀ F H).comp
    ((fst (wrapperInputEncoding q) (wordEncoding q)).fst'.prod (snd _ _))
  exact findSomeWithInput_polyTime (f := fun (p : WrapperInput q) w => imageTestWrapped zero l₀ F (p.1, w))
    hcandidates htest

private theorem verifyInverse_eq {q : ℕ} (zero : Fin q) (l₀ : ℕ) (F : SourceCallbacks q)
    (T : TagTables q) {bits : List Bool} (h : F.RepairLaws bits) (w x : QWord q) :
    verifyInverse zero l₀ F (((T, bits), w), x) =
      Wrapper.verifyInverse (T.wrapper zero (F.repairData bits h) (labelAt l₀ (fun y => F.label (bits, y)))) w x := by
  unfold verifyInverse Wrapper.verifyInverse
  dsimp only
  rw [F.inverse_eq h]
  simp only [TagTables.wrapper]
  cases (F.repairData bits h).inverse T.k x with
  | none => rfl
  | some u =>
    change (if encodeWrapped zero l₀ F ((T, bits), u) = w then some u else none) = _
    rw [encodeWrapped_eq zero l₀ F T h]
    rfl

theorem imageTestWrapped_eq {q : ℕ} (zero : Fin q) (l₀ : ℕ) (F : SourceCallbacks q)
    (T : TagTables q) {bits : List Bool} (h : F.RepairLaws bits) (w : QWord q) :
    imageTestWrapped zero l₀ F ((T, bits), w) =
      (T.wrapper zero (F.repairData bits h) (labelAt l₀ (fun y => F.label (bits, y)))).imageTest w := by
  have hrow : (fun row => readTagRow zero l₀ F (((T, bits), w), row)) =
      Wrapper.readRow (T.wrapper zero (F.repairData bits h) (labelAt l₀ (fun y => F.label (bits, y)))) w := by
    funext row
    unfold readTagRow Wrapper.readRow
    dsimp only
    rw [verifyInverse_eq zero l₀ F T h]
    rfl
  unfold imageTestWrapped Wrapper.imageTest
  dsimp only
  rw [hrow]
  rfl

theorem decodeWrapped_eq {q : ℕ} (zero : Fin q) (l₀ b t : ℕ) (F : SourceCallbacks q)
    (T : TagTables q) {bits : List Bool} (h : F.RepairLaws bits) (z : QWord q) :
    decodeWrapped zero l₀ b t F ((T, bits), z) =
      (T.wrapper zero (F.repairData bits h) (labelAt l₀ (fun y => F.label (bits, y)))).decode b t z := by
  have heq := funext (imageTestWrapped_eq zero l₀ F T h)
  unfold decodeWrapped Wrapper.decode
  dsimp only
  rw [heq]
  rfl

#print axioms imageTestWrapped_polyTime
#print axioms imageTestWrapped_eq
#print axioms decodeWrapped_polyTime
#print axioms decodeWrapped_eq

end DeletionCode.Explicit.Machine
