import DeletionCode.RecordBounds
import DeletionCode.RecordPacking

/-!
Serialization into the finite Description type, including root vectors and
padding to exactly 4ν instruction rows. The serialized decoder is executable;
its round trip and coverage are derived from the concrete recovery proof.
-/
namespace DeletionCode.RecordSerialization

open Windows HeaderRecovery ConcreteDecoder DescriptionCount RecordCodec
open RecordPacking GeneratingModel

structure RecoveredData (ν : ℕ) where
  header : Fin ν → Header
  words : Fin ν → List Bool

def dataOfOutput {ν : ℕ} (k : ℕ) (header : Fin ν → Header) (output : Output k header) :
    RecoveredData ν := ⟨header, fun b => List.ofFn (output b)⟩

def dataOfFamily {ν k : ℕ} (E : EditedFamily (Fin ν) k) : RecoveredData ν :=
  dataOfOutput k E.header (fun b i => negativePath k (E.header b) (E.long b) i.val)

def encodeTotal (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν)
    (instruction : Instruction (Fin ν)) : Row L ν :=
  if hb : InstructionBounded L instruction then encodeInstruction L ν hL hν instruction hb
  else zeroRow L ν hL hν

theorem decode_encodeTotal (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν)
    (instruction : Instruction (Fin ν)) (hb : InstructionBounded L instruction) :
    decodeInstruction L ν hν (encodeTotal L ν hL hν instruction) = some (some instruction) := by
  simp only [encodeTotal, dite_eq_left hb]
  exact decode_encodeInstruction L ν hL hν instruction hb

def rootVectors (n ν c : ℕ) (roots : List (Fin ν × ℕ))
    (hlen : roots.length = c) (hpos : ∀ b a, (b, a) ∈ roots → a < n) :
    (Fin c → Fin n) × (Fin c → Fin ν) :=
  ⟨fun i =>
      let r := roots.get ⟨i.val, by omega⟩
      ⟨r.2, hpos r.1 r.2 (List.get_mem _ _)⟩,
    fun i => (roots.get ⟨i.val, by omega⟩).1⟩

def rootsOfVectors {n ν c : ℕ} (positions : Fin c → Fin n) (names : Fin c → Fin ν) :
    List (Fin ν × ℕ) := List.ofFn (fun i => (names i, (positions i).val))

theorem roots_roundtrip (n ν c : ℕ) (roots : List (Fin ν × ℕ))
    (hlen : roots.length = c) (hpos : ∀ b a, (b, a) ∈ roots → a < n) :
    rootsOfVectors (rootVectors n ν c roots hlen hpos).1
      (rootVectors n ν c roots hlen hpos).2 = roots := by
  subst c
  change List.ofFn (fun i : Fin roots.length => roots.get i) = roots
  simp

def encodeDescription (n k ν c : ℕ) (hν : 1 ≤ ν)
    (header : Fin ν → Header)
    (hlo : ∀ b, 1 ≤ (header b).rho) (hhi : ∀ b, (header b).rho ≤ windowLength k)
    (roots : List (Fin ν × ℕ)) (hroots : roots.length = c)
    (hpos : ∀ b a, (b, a) ∈ roots → a < n)
    (instructions : List (Instruction (Fin ν))) : Description n (windowLength k) ν c :=
  let hL : 1 ≤ windowLength k := by unfold windowLength; omega
  let rv := rootVectors n ν c roots hroots hpos
  ⟨rv.1, (fun b => encodeHeader (windowLength k) (header b) (hlo b) (hhi b)), rv.2,
    pack (zeroRow (windowLength k) ν hL hν)
      (instructions.map (encodeTotal (windowLength k) ν hL hν)) (4 * ν)⟩

def decodeDescription (x : Letters) (n k ν c : ℕ) (hν : 1 ≤ ν)
    (description : Description n (windowLength k) ν c) : Option (RecoveredData ν) :=
  let header := fun b => decodeHeader (description.2.1 b)
  let roots := rootsOfVectors description.1 description.2.2.1
  (unpack (decodeInstruction (windowLength k) ν hν) (4 * ν) description.2.2.2).bind
    fun instructions => (decode x n k header roots instructions).map (dataOfOutput k header)

/-- Serializing a bounded concrete record preserves its exact decoded result. -/
theorem description_roundtrip (x : Letters) (n k ν c : ℕ) (hν : 1 ≤ ν)
    (header : Fin ν → Header)
    (hlo : ∀ b, 1 ≤ (header b).rho) (hhi : ∀ b, (header b).rho ≤ windowLength k)
    (roots : List (Fin ν × ℕ)) (hroots : roots.length = c)
    (hpos : ∀ b a, (b, a) ∈ roots → a < n)
    (instructions : List (Instruction (Fin ν))) (hcost : instructions.length ≤ 4 * ν)
    (hbounded : ∀ instruction ∈ instructions, InstructionBounded (windowLength k) instruction) :
    decodeDescription x n k ν c hν
      (encodeDescription n k ν c hν header hlo hhi roots hroots hpos instructions) =
      (decode x n k header roots instructions).map (dataOfOutput k header) := by
  let hL : 1 ≤ windowLength k := by unfold windowLength; omega
  have hheader : (fun b => decodeHeader (encodeHeader (windowLength k) (header b) (hlo b) (hhi b))) =
      header := by
    funext b
    exact decode_encodeHeader (windowLength k) (header b) (hlo b) (hhi b)
  have hinstructions := unpack_pack (decodeInstruction (windowLength k) ν hν)
    (encodeTotal (windowLength k) ν hL hν) (zeroRow (windowLength k) ν hL hν)
    (decode_zeroRow (windowLength k) ν hL hν) instructions
    (fun a ha => decode_encodeTotal (windowLength k) ν hL hν a (hbounded a ha))
    (4 * ν) hcost
  unfold decodeDescription encodeDescription
  dsimp only
  rw [hheader, roots_roundtrip n ν c roots hroots hpos, hinstructions]
  rfl

/-- Every generating edited family has a description in the counted finite format. -/
theorem serialized_generating_coverage {ν k : ℕ} (E : EditedFamily (Fin ν) k)
    (x : Letters) (n c : ℕ) (hν : 1 ≤ ν) (hx : KUnique x n k)
    (hg : E.family.Generating x n (windowLength k))
    (hc : Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) = c) :
    ∃ description : Description n (windowLength k) ν c,
      decodeDescription x n k ν c hν description = some (dataOfFamily E) := by
  obtain ⟨roots, instructions, hroots, hcost, hdecode, hpos, hbounded⟩ :=
    RecordBounds.generating_decode_exists_bounded E x n hx hg
  have hhi : ∀ b, (E.header b).rho ≤ windowLength k := by
    intro b
    have := E.rho_upper b
    unfold windowLength
    omega
  have hrootc : roots.length = c := hroots.trans hc
  let description := encodeDescription n k ν c hν E.header E.rho_lower hhi
    roots hrootc hpos instructions
  refine ⟨description, ?_⟩
  rw [description_roundtrip x n k ν c hν E.header E.rho_lower hhi roots hrootc hpos
    instructions (by simpa using hcost) hbounded, hdecode]
  rfl

#print axioms roots_roundtrip
#print axioms description_roundtrip
#print axioms serialized_generating_coverage

end DeletionCode.RecordSerialization
