import DeletionCode.ConcreteDecoder
import DeletionCode.DescriptionCount
import Mathlib.Tactic.FinCases

/-!
Finite, executable codecs for headers and individual decoder instructions.
Rows have exactly the field type used by DescriptionCount.Description. Tag 0
is padding, tags 1--3 encode the three instruction constructors. Other tags
are rejected. The encoder round trips on every bounded instruction.
-/

namespace DeletionCode.RecordCodec

open HeaderRecovery ConcreteDecoder DescriptionCount

def InstructionBounded (L : ℕ) {B : Type*} : Instruction B → Prop
  | .start _ _ sourceOffset _ _ destOffset _ =>
      sourceOffset ≤ 2 * L ∧ destOffset ≤ 2 * L
  | .fillBase _ _ seedOffset => seedOffset ≤ 2 * L
  | .fillSupplier _ _ sourceOffset _ _ => sourceOffset ≤ 2 * L

instance (L : ℕ) {B : Type*} (instruction : Instruction B) :
    Decidable (InstructionBounded L instruction) := by
  cases instruction <;> unfold InstructionBounded <;> infer_instance

def bitCode (bit : Bool) : ℕ := if bit then 1 else 0

def orientationCode (orientation : Orientation) : ℕ :=
  match orientation with
  | .deletion => 0
  | .insertion => 1
  | .substitution => 2

theorem bitCode_le (bit : Bool) : bitCode bit ≤ 1 := by cases bit <;> decide

theorem orientationCode_le (orientation : Orientation) : orientationCode orientation ≤ 2 := by
  cases orientation <;> decide

def encodeHeader (L : ℕ) (header : Header)
    (hrho0 : 1 ≤ header.rho) (hrhoL : header.rho ≤ L) : Fin (6 * L) :=
  ⟨6 * (header.rho - 1) + 2 * orientationCode header.orientation + bitCode header.bit, by
    have ho := orientationCode_le header.orientation
    have hb := bitCode_le header.bit
    omega⟩

def decodeOrientation (code : ℕ) : Orientation :=
  if code % 6 < 2 then .deletion else if code % 6 < 4 then .insertion else .substitution

def decodeHeader {L : ℕ} (code : Fin (6 * L)) : Header where
  rho := code.val / 6 + 1
  orientation := decodeOrientation code.val
  bit := code.val % 2 == 1

theorem decode_encodeHeader (L : ℕ) (header : Header)
    (hrho0 : 1 ≤ header.rho) (hrhoL : header.rho ≤ L) :
    decodeHeader (encodeHeader L header hrho0 hrhoL) = header := by
  obtain ⟨orientation, rho, bit⟩ := header
  dsimp at hrho0 hrhoL
  have ho := orientationCode_le orientation
  have hb := bitCode_le bit
  have hmod6 : (6 * (rho - 1) + 2 * orientationCode orientation + bitCode bit) % 6
      = 2 * orientationCode orientation + bitCode bit := by omega
  have hmod2 : (6 * (rho - 1) + 2 * orientationCode orientation + bitCode bit) % 2
      = bitCode bit := by omega
  have hdiv : (6 * (rho - 1) + 2 * orientationCode orientation + bitCode bit) / 6 + 1
      = rho := by omega
  simp only [decodeHeader, Header.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · show decodeOrientation (6 * (rho - 1) + 2 * orientationCode orientation + bitCode bit)
        = orientation
    unfold decodeOrientation
    rw [hmod6]
    cases orientation <;> cases bit <;> rfl
  · exact hdiv
  · show ((6 * (rho - 1) + 2 * orientationCode orientation + bitCode bit) % 2 == 1) = bit
    rw [hmod2]
    cases bit <;> rfl

abbrev Row (L ν : ℕ) := Fin 12 → Fin (fieldBound L ν)

def instructionField {ν : ℕ} (instruction : Instruction (Fin ν)) (i : Fin 12) : ℕ :=
  match instruction with
  | .start source sourceSide sourceOffset dest destSide destOffset extra =>
    match i.val with
    | 0 => 1
    | 1 => source.val
    | 2 => bitCode sourceSide
    | 3 => sourceOffset
    | 4 => dest.val
    | 5 => bitCode destSide
    | 6 => destOffset
    | 7 => bitCode extra
    | _ => 0
  | .fillBase dest window seedOffset =>
    match i.val with
    | 0 => 2
    | 1 => dest.val
    | 2 => window.val
    | 3 => seedOffset
    | _ => 0
  | .fillSupplier source sourceSide sourceOffset dest window =>
    match i.val with
    | 0 => 3
    | 1 => source.val
    | 2 => bitCode sourceSide
    | 3 => sourceOffset
    | 4 => dest.val
    | 5 => window.val
    | _ => 0

theorem instructionField_lt (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν)
    (instruction : Instruction (Fin ν)) (hbound : InstructionBounded L instruction)
    (i : Fin 12) : instructionField instruction i < fieldBound L ν := by
  have hlargeOffset : 2 * L < fieldBound L ν := by unfold fieldBound; nlinarith
  have hlargeName : ν < fieldBound L ν := by unfold fieldBound; nlinarith
  have hlargeTag : 4 < fieldBound L ν := by unfold fieldBound; nlinarith
  cases instruction with
  | start source sourceSide sourceOffset dest destSide destOffset extra =>
    have hsource := source.isLt
    have hdest := dest.isLt
    have hsourceSide := bitCode_le sourceSide
    have hdestSide := bitCode_le destSide
    have hextra := bitCode_le extra
    rcases hbound with ⟨hs, hd⟩
    fin_cases i <;> simp only [instructionField] <;> omega
  | fillBase dest window seedOffset =>
    have hdest := dest.isLt
    have hwindow := window.isLt
    change seedOffset ≤ 2 * L at hbound
    fin_cases i <;> simp only [instructionField] <;> omega
  | fillSupplier source sourceSide sourceOffset dest window =>
    have hsource := source.isLt
    have hdest := dest.isLt
    have hwindow := window.isLt
    have hsourceSide := bitCode_le sourceSide
    change sourceOffset ≤ 2 * L at hbound
    fin_cases i <;> simp only [instructionField] <;> omega

def encodeInstruction (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν)
    (instruction : Instruction (Fin ν)) (hbound : InstructionBounded L instruction) : Row L ν :=
  fun i => ⟨instructionField instruction i, instructionField_lt L ν hL hν instruction hbound i⟩

def nameFromNat (ν : ℕ) (hν : 1 ≤ ν) (value : ℕ) : Fin ν :=
  ⟨value % ν, Nat.mod_lt value (by omega)⟩

def slotFromNat (value : ℕ) : Recovery.Slot := ⟨value % 3, Nat.mod_lt value (by omega)⟩

def bitFromNat (value : ℕ) : Bool := value % 2 == 1

/-- Some none denotes padding; none denotes a malformed tag. -/
def decodeInstruction (L ν : ℕ) (hν : 1 ≤ ν) (row : Row L ν) :
    Option (Option (Instruction (Fin ν))) :=
  match (row 0).val with
  | 0 => some none
  | 1 => some (some (.start
      (nameFromNat ν hν (row 1).val) (bitFromNat (row 2).val) (row 3).val
      (nameFromNat ν hν (row 4).val) (bitFromNat (row 5).val) (row 6).val
      (bitFromNat (row 7).val)))
  | 2 => some (some (.fillBase
      (nameFromNat ν hν (row 1).val) (slotFromNat (row 2).val) (row 3).val))
  | 3 => some (some (.fillSupplier
      (nameFromNat ν hν (row 1).val) (bitFromNat (row 2).val) (row 3).val
      (nameFromNat ν hν (row 4).val) (slotFromNat (row 5).val)))
  | _ => none

theorem decode_encodeInstruction (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν)
    (instruction : Instruction (Fin ν)) (hbound : InstructionBounded L instruction) :
    decodeInstruction L ν hν (encodeInstruction L ν hL hν instruction hbound) =
      some (some instruction) := by
  cases instruction with
  | start source sourceSide sourceOffset dest destSide destOffset extra =>
    cases sourceSide <;> cases destSide <;> cases extra <;>
      simp [decodeInstruction, encodeInstruction, instructionField, bitFromNat, bitCode,
        nameFromNat, Nat.mod_eq_of_lt source.isLt, Nat.mod_eq_of_lt dest.isLt]
  | fillBase dest window seedOffset =>
    simp [decodeInstruction, encodeInstruction, instructionField, nameFromNat, slotFromNat,
      Nat.mod_eq_of_lt dest.isLt, Nat.mod_eq_of_lt window.isLt]
  | fillSupplier source sourceSide sourceOffset dest window =>
    cases sourceSide <;>
      simp [decodeInstruction, encodeInstruction, instructionField, bitFromNat, bitCode,
        nameFromNat, slotFromNat, Nat.mod_eq_of_lt source.isLt,
        Nat.mod_eq_of_lt dest.isLt, Nat.mod_eq_of_lt window.isLt]

def zeroRow (L ν : ℕ) (hL : 1 ≤ L) (_hν : 1 ≤ ν) : Row L ν :=
  fun _ => ⟨0, by unfold fieldBound; nlinarith⟩

theorem decode_zeroRow (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν) :
    decodeInstruction L ν hν (zeroRow L ν hL hν) = some none := rfl

#print axioms decode_encodeHeader
#print axioms instructionField_lt
#print axioms decode_encodeInstruction
#print axioms decode_zeroRow

end DeletionCode.RecordCodec
