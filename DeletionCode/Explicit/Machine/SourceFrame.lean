import DeletionCode.Explicit.Machine.SourcePayloadIndex
import DeletionCode.Explicit.Machine.WrapperDecoding

/-! The public branch identifier and the padded compression frame. -/
namespace DeletionCode.Explicit.Machine.SourceFrame

open SourcePayloadIndex SourceLists
open private frame header parseHeader from DeletionCode.Explicit.CompressorFrame

variable {q : ℕ} {π : Type}

abbrev Encoders (π : Type) (q : ℕ) := ℕ → π → QWord q → Option (QWord q)
abbrev Decoders (π : Type) (q : ℕ) := ℕ → π → ℕ → QWord q → Option (QWord q)

def choose (f : Encoders π q) (data : π) (x : QWord q) : Option (ℕ × QWord q) :=
  (List.range 3).findSome? (fun j => (f j data x).map (j,·))

def write (pad : Fin q) (ℓ j : ℕ) (payload : QWord q) : QWord q :=
  let body := SourcePayloadIndex.writeIndex pad 3 j ++ payload
  body ++ List.replicate (ℓ-1-body.length) pad

theorem write_eq (pad : Fin q) (hq : 2 ≤ q) (ℓ : ℕ) (j : Fin 3) (payload : QWord q) :
    write pad ℓ j.val payload = frame (by omega : 1 < q) pad ℓ j payload := by
  unfold write frame
  rw [writeIndex_eq pad hq]
  rfl

def compress (pad : Fin q) (f : Encoders π q) (data : π) (x : QWord q) : Option (QWord q) :=
  (choose f data x).map (fun (j,payload) => write pad x.length j payload)

def expand (f : Decoders π q) (data : π) (x : QWord q) : Option (QWord q) := do
  let (j,tail) ← SourcePayloadIndex.readIndex q 3 x
  f j data (x.length+1) tail

private theorem findSome_map_input {α β γ : Type} (f : α → β) (g : β → Option γ) (xs : List α) :
    (xs.map f).findSome? g = xs.findSome? (g ∘ f) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons,List.findSome?_cons,Function.comp_apply]
    rw [ih]

private theorem findSome_map_output {α β γ : Type} (f : α → Option β) (g : β → γ) (xs : List α) :
    xs.findSome? (fun a => (f a).map g) = (xs.findSome? f).map g := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.findSome?_cons]
    cases h : f a <;> simp [h,ih]

theorem choose_eq (f : Encoders π q) (data : π) (x : QWord q)
    (branches : Fin 3 → CompressorFrame.Branch q)
    (h : ∀ j : Fin 3, f j.val data x = (branches j).encode x) :
    choose f data x = (CompressorFrame.choose branches x).map (fun (j,p) => (j.val,p)) := by
  unfold choose CompressorFrame.choose
  rw [show List.range 3 = (List.finRange 3).map Fin.val by simp,findSome_map_input,← findSome_map_output]
  congr 1
  funext j
  change (f j.val data x).map (j.val,·) = ((((branches j).encode x).map (j,·)).map _)
  rw [h j,Option.map_map]
  rfl

theorem compress_eq (pad : Fin q) (hq : 2 ≤ q) (f : Encoders π q) (data : π) (x : QWord q)
    (branches : Fin 3 → CompressorFrame.Branch q)
    (h : ∀ j : Fin 3, f j.val data x = (branches j).encode x) :
    compress pad f data x = CompressorFrame.compress (by omega) pad branches x := by
  unfold compress CompressorFrame.compress
  rw [choose_eq f data x branches h]
  cases CompressorFrame.choose branches x with
  | none => rfl
  | some p => exact congrArg some (write_eq pad hq _ p.1 p.2)

private theorem parseHeader_eq (x : QWord q) : parseHeader x = ReplayPayload.readIndex 3 x := by
  unfold parseHeader ReplayPayload.readIndex ReplayPayload.readPrefix
  dsimp only
  split <;> simp_all [bind,Option.bind]

theorem expand_eq (f : Decoders π q) (data : π) (x : QWord q)
    (branches : Fin 3 → CompressorFrame.Branch q)
    (h : ∀ (j : Fin 3) tail, f j.val data (x.length+1) tail =
      (branches j).decode (x.length+1) tail) :
    expand f data x = CompressorFrame.decompress branches x := by
  unfold expand CompressorFrame.decompress
  rw [parseHeader_eq,readIndex_eq]
  cases ReplayPayload.readIndex 3 x with
  | none => rfl
  | some p => exact h p.1 p.2

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

abbrev chooseEncoding (q : ℕ) := encPair encUnary (wordEncoding q)
abbrev frameEncoding (q : ℕ) := encPair encUnary (chooseEncoding q)

theorem write_polyTime (pad : Fin q) (hq : 2 ≤ q) :
    ComputableInPolyTime (fun x : ℕ × ℕ × QWord q => write pad x.1 x.2.1 x.2.2)
      (frameEncoding q) (wordEncoding q) := by
  let a := ExceptionalRecords.letterEncoding q
  let w := wordEncoding q
  let e := frameEncoding q
  have hl := fst encUnary (chooseEncoding q)
  have hp := snd encUnary (chooseEncoding q)
  have hh := (writeIndex_polyTime pad hq).comp (encIn := e)
    ((const (encOut := encNat) 3).prod (unary_to_binary.comp hp.fst'))
  have hbody := listAppend' hh hp.snd'
  have hcount := unary_sub' (unary_sub' hl (const 1)) ((length_list a).comp hbody)
  have hpad := replicate (encA := a) hcount (const pad)
  exact (listAppend' hbody hpad).of_enc_eq (fun _ => rfl)

theorem compress_polyTime (pad : Fin q) (hq : 2 ≤ q) (enc : π ↪ List Bool) (f : Encoders π q)
    (hf : ComputableInPolyTime (fun p : (π × QWord q) × ℕ => f p.2 p.1.1 p.1.2)
      (encPair (encPair enc (wordEncoding q)) encUnary) (encOption (wordEncoding q))) :
    ComputableInPolyTime (fun p : π × QWord q => compress pad f p.1 p.2)
      (encPair enc (wordEncoding q)) (encOption (wordEncoding q)) := by
  let w := wordEncoding q
  let e := encPair enc w
  let a := encPair e encUnary
  let c := chooseEncoding q
  have htag := optionMapWithInput (encA := a) (encB := w) (encC := c)
    (f := fun x p => (x.2,p)) hf (((snd e encUnary).comp (fst a w)).prod (snd a w))
  have hc := findSomeWithInput_polyTime (enc := e) (encA := encUnary) (encB := c)
    (f := fun x j => (f j x.1 x.2).map (j,·)) (const (List.range 3)) htag
  have hl := ((wordLength_polyTime q).comp (snd enc w)).comp (fst e c)
  have hv := (write_polyTime pad hq).comp (hl.prod (snd e c))
  exact optionMapWithInput (encA := e) (encB := c) (encC := w)
    (f := fun x p => write pad x.2.length p.1 p.2) hc hv

theorem expand_polyTime (hq : 2 ≤ q) (enc : π ↪ List Bool) (f : Decoders π q)
    (hf : ComputableInPolyTime (fun p : ((π × QWord q) × ℕ) × ℕ => f p.2 p.1.1.1 p.1.2 p.1.1.2)
      (encPair (encPair (encPair enc (wordEncoding q)) encUnary) encNat)
      (encOption (wordEncoding q))) :
    ComputableInPolyTime (fun p : π × QWord q => expand f p.1 p.2)
      (encPair enc (wordEncoding q)) (encOption (wordEncoding q)) := by
  let w := wordEncoding q
  let e := encPair enc w
  let a := readEncoding q
  have h := (readIndex_polyTime q hq).comp (encIn := e) ((const (encOut := encNat) 3).prod (snd enc w))
  have hx := fst e a
  have hp := (fst enc w).comp hx
  have hf' := snd e a
  have hl := unary_add' ((wordLength_polyTime q).comp ((snd enc w).comp hx)) (const 1)
  have hd := hf.comp (((hp.prod hf'.snd').prod hl).prod hf'.fst')
  exact optionBindWithInput h hd

#print axioms choose_eq
#print axioms compress_eq
#print axioms expand_eq
#print axioms write_polyTime
#print axioms compress_polyTime
#print axioms expand_polyTime

end DeletionCode.Explicit.Machine.SourceFrame
