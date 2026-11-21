import DeletionCode.Qary.ConcreteDecoder
import DeletionCode.Qary.DescriptionCount
import DeletionCode.RecordCodec

/-!
Q-ary letters are serialized separately from the already verified numeric fields.
The binary codec is used only for orientations, indices, offsets, and path-side
flags. Its symbol slot is set to false and ignored when decoding; the actual
alphabet symbols are retained in separate fields and restored exactly.
-/
namespace DeletionCode.Qary.RecordCodec
open DeletionCode.Qary.HeaderRecovery DeletionCode.Qary.ConcreteDecoder DeletionCode.Qary.DescriptionCount
variable {α : Type*} [Inhabited α]

def InstructionBounded (L : ℕ) {B : Type*} : Instruction α B → Prop
  | .start _ _ sourceOffset _ _ destOffset _ => sourceOffset ≤ 2 * L ∧ destOffset ≤ 2 * L
  | .fillBase _ _ seedOffset => seedOffset ≤ 2 * L
  | .fillSupplier _ _ sourceOffset _ _ => sourceOffset ≤ 2 * L

instance (L : ℕ) {B : Type*} (instruction : Instruction α B) :
    Decidable (InstructionBounded L instruction) := by
  cases instruction <;> unfold InstructionBounded <;> infer_instance

def eraseOrientation : Orientation → DeletionCode.HeaderRecovery.Orientation
  | .deletion => .deletion
  | .insertion => .insertion
  | .substitution => .substitution

def restoreOrientation : DeletionCode.HeaderRecovery.Orientation → Orientation
  | .deletion => .deletion
  | .insertion => .insertion
  | .substitution => .substitution

def eraseHeader (h : Header α) : DeletionCode.HeaderRecovery.Header :=
  ⟨eraseOrientation h.orientation, h.rho, false⟩

def encodeHeader (L : ℕ) (h : Header α) (hlo : 1 ≤ h.rho) (hhi : h.rho ≤ L) :
    Fin (6 * L) × α × α :=
  ⟨DeletionCode.RecordCodec.encodeHeader L (eraseHeader h) hlo hhi, h.bit, h.newBit⟩

def decodeHeader {L : ℕ} (code : Fin (6 * L) × α × α) : Header α :=
  let h := DeletionCode.RecordCodec.decodeHeader code.1
  ⟨restoreOrientation h.orientation, h.rho, code.2.1, code.2.2⟩

theorem decode_encodeHeader (L : ℕ) (h : Header α) (hlo : 1 ≤ h.rho) (hhi : h.rho ≤ L) :
    decodeHeader (encodeHeader L h hlo hhi) = h := by
  dsimp only [encodeHeader, decodeHeader]
  rw [DeletionCode.RecordCodec.decode_encodeHeader L (eraseHeader h) hlo hhi]
  cases h with
  | mk orientation rho bit newBit => cases orientation <;> rfl

abbrev Row (α : Type*) (L ν : ℕ) := DeletionCode.RecordCodec.Row L ν × α

def eraseInstruction {B : Type*} : Instruction α B → DeletionCode.ConcreteDecoder.Instruction B
  | .start s ss so d ds doff _ => .start s ss so d ds doff false
  | .fillBase d w off => .fillBase d w off
  | .fillSupplier s ss off d w => .fillSupplier s ss off d w

def instructionLetter {B : Type*} : Instruction α B → α
  | .start _ _ _ _ _ _ extra => extra
  | _ => default

def restoreInstruction {B : Type*} (symbol : α) :
    DeletionCode.ConcreteDecoder.Instruction B → Instruction α B
  | .start s ss so d ds doff _ => .start s ss so d ds doff symbol
  | .fillBase d w off => .fillBase d w off
  | .fillSupplier s ss off d w => .fillSupplier s ss off d w

theorem restore_erase {B : Type*} (i : Instruction α B) :
    restoreInstruction (instructionLetter i) (eraseInstruction i) = i := by cases i <;> rfl

theorem erase_bounded (L : ℕ) {B : Type*} (i : Instruction α B)
    (hi : InstructionBounded L i) :
    DeletionCode.RecordCodec.InstructionBounded L (eraseInstruction i) := by
  cases i <;> exact hi

def encodeInstruction (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν)
    (i : Instruction α (Fin ν)) (hi : InstructionBounded L i) : Row α L ν :=
  ⟨DeletionCode.RecordCodec.encodeInstruction L ν hL hν (eraseInstruction i)
    (erase_bounded L i hi), instructionLetter i⟩

def decodeInstruction (L ν : ℕ) (hν : 1 ≤ ν) (row : Row α L ν) :
    Option (Option (Instruction α (Fin ν))) :=
  (DeletionCode.RecordCodec.decodeInstruction L ν hν row.1).map
    (Option.map (restoreInstruction row.2))

theorem decode_encodeInstruction (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν)
    (i : Instruction α (Fin ν)) (hi : InstructionBounded L i) :
    decodeInstruction L ν hν (encodeInstruction L ν hL hν i hi) = some (some i) := by
  simp only [decodeInstruction, encodeInstruction, DeletionCode.RecordCodec.decode_encodeInstruction,
    Option.map_some, restore_erase]

def zeroRow (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν) : Row α L ν :=
  ⟨DeletionCode.RecordCodec.zeroRow L ν hL hν, default⟩

theorem decode_zeroRow (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν) :
    decodeInstruction L ν hν (zeroRow (α := α) L ν hL hν) = some none := rfl

#print axioms decode_encodeHeader
#print axioms decode_encodeInstruction
end DeletionCode.Qary.RecordCodec
