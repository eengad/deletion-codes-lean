import DeletionCode.Burst.ConcreteDecoder
import DeletionCode.Burst.DescriptionCount
import DeletionCode.Qary.RecordCodec
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic

/-!
Finite burst headers and instructions. Numeric instruction fields reuse the
proved single-edit codec at parameter 2L; extension blocks are kept separately.
The codec retains both substituted blocks, including their exact lengths.
-/
namespace DeletionCode.Burst.RecordCodec
open DeletionCode.Burst.HeaderRecovery DeletionCode.Burst.ConcreteDecoder
open DeletionCode.Burst.DescriptionCount
variable {α : Type*} [Inhabited α]

structure HeaderBounded (L b : ℕ) (h : Header α) : Prop where
  left_lt : h.leftLength < L
  right_lt : h.rightLength < L
  removed_lt : h.removed.length < L
  replacement_lt : h.replacement.length < L
  removed_le : h.removed.length ≤ b
  replacement_le : h.replacement.length ≤ b

theorem header_bounded {k b : ℕ} {h : Header α} (hv : h.Valid k b) :
    HeaderBounded (windowLength k b) b h := by
  have := hv.left_upper
  have := hv.right_upper
  have := hv.removed_le
  have := hv.replacement_le
  constructor <;> unfold windowLength at * <;> omega

def padBlock (b : ℕ) (word : List α) : Fin b → α := fun i => word.getD i.val default

def unpadBlock (len : ℕ) {b : ℕ} (bits : Fin b → α) : List α := (List.ofFn bits).take len

theorem block_roundtrip (b : ℕ) (word : List α) (hlen : word.length ≤ b) :
    unpadBlock word.length (padBlock b word) = word := by
  apply List.ext_getElem
  · simp [unpadBlock, hlen]
  · intro i hi hj
    simp only [unpadBlock, List.getElem_take, List.getElem_ofFn, padBlock]
    simp [List.getD, hj]

def encodeHeader (L b : ℕ) (h : Header α) (hb : HeaderBounded L b h) : HeaderCode α L b :=
  ⟨(fun i => if i.val = 0 then ⟨h.leftLength, hb.left_lt⟩
      else if i.val = 1 then ⟨h.rightLength, hb.right_lt⟩
      else if i.val = 2 then ⟨h.removed.length, hb.removed_lt⟩
      else ⟨h.replacement.length, hb.replacement_lt⟩),
    padBlock b h.removed, padBlock b h.replacement⟩

def decodeHeader {L b : ℕ} (code : HeaderCode α L b) : Header α :=
  ⟨(code.1 0).val, (code.1 1).val,
    unpadBlock (code.1 2).val code.2.1, unpadBlock (code.1 3).val code.2.2⟩

theorem decode_encodeHeader (L b : ℕ) (h : Header α) (hb : HeaderBounded L b h) :
    decodeHeader (encodeHeader L b h hb) = h := by
  simp [decodeHeader, encodeHeader, block_roundtrip b h.removed hb.removed_le,
    block_roundtrip b h.replacement hb.replacement_le]

abbrev Row (α : Type*) (b L ν : ℕ) := Qary.RecordCodec.Row (Fin b → α) (2 * L) ν

def toQary {b : ℕ} {B : Type*} : Instruction α b B → Qary.ConcreteDecoder.Instruction (Fin b → α) B
  | .start s ss so d ds doff extra => .start s ss so d ds doff extra
  | .fillBase d w off => .fillBase d w off
  | .fillSupplier s ss off d w => .fillSupplier s ss off d w

def fromQary {b : ℕ} {B : Type*} : Qary.ConcreteDecoder.Instruction (Fin b → α) B → Instruction α b B
  | .start s ss so d ds doff extra => .start s ss so d ds doff extra
  | .fillBase d w off => .fillBase d w off
  | .fillSupplier s ss off d w => .fillSupplier s ss off d w

theorem from_to {b : ℕ} {B : Type*} (i : Instruction α b B) : fromQary (toQary i) = i := by
  cases i <;> rfl

def InstructionBounded (L : ℕ) {b : ℕ} {B : Type*} (i : Instruction α b B) : Prop :=
  Qary.RecordCodec.InstructionBounded (2 * L) (toQary i)

instance (L : ℕ) {b : ℕ} {B : Type*} (i : Instruction α b B) :
    Decidable (InstructionBounded L i) := by unfold InstructionBounded; infer_instance

def encodeInstruction (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν)
    {b : ℕ} (i : Instruction α b (Fin ν)) (hi : InstructionBounded L i) : Row α b L ν :=
  Qary.RecordCodec.encodeInstruction (2 * L) ν (by omega) hν (toQary i) hi

def decodeInstruction (L ν : ℕ) (hν : 1 ≤ ν) {b : ℕ} (row : Row α b L ν) :
    Option (Option (Instruction α b (Fin ν))) :=
  (Qary.RecordCodec.decodeInstruction (2 * L) ν hν row).map (Option.map fromQary)

theorem decode_encodeInstruction (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν)
    {b : ℕ} (i : Instruction α b (Fin ν)) (hi : InstructionBounded L i) :
    decodeInstruction L ν hν (encodeInstruction L ν hL hν i hi) = some (some i) := by
  unfold decodeInstruction encodeInstruction
  rw [Qary.RecordCodec.decode_encodeInstruction (2 * L) ν (by omega) hν (toQary i) hi]
  simp only [Option.map_some, from_to]

def zeroRow (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν) {b : ℕ} : Row α b L ν :=
  Qary.RecordCodec.zeroRow (2 * L) ν (by omega) hν

theorem decode_zeroRow (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν) {b : ℕ} :
    decodeInstruction L ν hν (zeroRow (α := α) (b := b) L ν hL hν) = some none := rfl

#print axioms decode_encodeHeader
#print axioms decode_encodeInstruction
end DeletionCode.Burst.RecordCodec
