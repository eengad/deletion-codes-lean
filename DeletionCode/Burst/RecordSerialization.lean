import DeletionCode.Burst.RecordBounds
import DeletionCode.RecordPacking

/-!
Serialization into the finite Description α type, including root vectors and
padding to exactly 4ν instruction rows. The serialized decoder is executable;
its round trip and coverage are derived from the concrete recovery proof.
-/
namespace DeletionCode.Burst.RecordSerialization

variable {α : Type*} [DecidableEq α] [Inhabited α]

open DeletionCode.Qary.Windows DeletionCode.Burst.HeaderRecovery DeletionCode.Burst.ConcreteDecoder DeletionCode.Burst.DescriptionCount DeletionCode.Burst.RecordCodec
open DeletionCode.RecordPacking DeletionCode.Burst.GeneratingModel

structure RecoveredData (α : Type*) (ν : ℕ) where
  header : Fin ν → Header α
  words : Fin ν → List α

def dataOfOutput {ν : ℕ} (k d : ℕ) (header : Fin ν → Header α) (output : Output k d header) :
    RecoveredData α ν := ⟨header, fun b => List.ofFn (output b)⟩

def dataOfFamily {ν k d : ℕ} (E : EditedFamily α (Fin ν) k d) : RecoveredData α ν :=
  dataOfOutput k d E.header (fun b i => negativePath (E.header b) (E.long b) i.val)

def encodeTotal {d : ℕ} (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν)
    (instruction : Instruction α d (Fin ν)) : Row α d L ν :=
  if hb : InstructionBounded L instruction then encodeInstruction L ν hL hν instruction hb
  else zeroRow L ν hL hν

theorem decode_encodeTotal {d : ℕ} (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν)
    (instruction : Instruction α d (Fin ν)) (hb : InstructionBounded L instruction) :
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

def encodeDescription (n k d ν c : ℕ) (hν : 1 ≤ ν)
    (header : Fin ν → Header α)
    (hb : ∀ b, HeaderBounded (windowLength k d) d (header b))
    (roots : List (Fin ν × ℕ)) (hroots : roots.length = c)
    (hpos : ∀ b a, (b, a) ∈ roots → a < n)
    (instructions : List (Instruction α d (Fin ν))) : Description α d n (windowLength k d) ν c :=
  let hL : 1 ≤ windowLength k d := by unfold windowLength; omega
  let rv := rootVectors n ν c roots hroots hpos
  ⟨rv.1, (fun b => encodeHeader (windowLength k d) d (header b) (hb b)), rv.2,
    pack (zeroRow (windowLength k d) ν hL hν)
      (instructions.map (encodeTotal (windowLength k d) ν hL hν)) (4 * ν)⟩

def decodeDescription (x : Letters α) (n k d ν c : ℕ) (hν : 1 ≤ ν)
    (description : Description α d n (windowLength k d) ν c) : Option (RecoveredData α ν) :=
  let header := fun b => decodeHeader (description.2.1 b)
  let roots := rootsOfVectors description.1 description.2.2.1
  (unpack (decodeInstruction (windowLength k d) ν hν) (4 * ν) description.2.2.2).bind
    fun instructions => (decode x n k d header roots instructions).map (dataOfOutput k d header)

/-- Serializing a bounded concrete record preserves its exact decoded result. -/
theorem description_roundtrip (x : Letters α) (n k d ν c : ℕ) (hν : 1 ≤ ν)
    (header : Fin ν → Header α)
    (hb : ∀ b, HeaderBounded (windowLength k d) d (header b))
    (roots : List (Fin ν × ℕ)) (hroots : roots.length = c)
    (hpos : ∀ b a, (b, a) ∈ roots → a < n)
    (instructions : List (Instruction α d (Fin ν))) (hcost : instructions.length ≤ 4 * ν)
    (hbounded : ∀ instruction ∈ instructions, InstructionBounded (windowLength k d) instruction) :
    decodeDescription x n k d ν c hν
      (encodeDescription n k d ν c hν header hb roots hroots hpos instructions) =
      (decode x n k d header roots instructions).map (dataOfOutput k d header) := by
  let hL : 1 ≤ windowLength k d := by unfold windowLength; omega
  have hheader : (fun b => decodeHeader (encodeHeader (windowLength k d) d (header b) (hb b))) =
      header := by
    funext b
    exact decode_encodeHeader (windowLength k d) d (header b) (hb b)
  have hinstructions := unpack_pack (decodeInstruction (windowLength k d) ν hν)
    (encodeTotal (windowLength k d) ν hL hν) (zeroRow (windowLength k d) ν hL hν)
    (decode_zeroRow (windowLength k d) ν hL hν) instructions
    (fun a ha => decode_encodeTotal (windowLength k d) ν hL hν a (hbounded a ha))
    (4 * ν) hcost
  unfold decodeDescription encodeDescription
  dsimp only
  rw [hheader, roots_roundtrip n ν c roots hroots hpos, hinstructions]
  rfl

/-- Every generating edited family has a description in the counted finite format. -/
theorem serialized_generating_coverage {ν k d : ℕ} (E : EditedFamily α (Fin ν) k d)
    (x : Letters α) (n c : ℕ) (hν : 1 ≤ ν) (hx : KUnique x n k)
    (hg : E.family.Generating x n (windowLength k d))
    (hc : Fintype.card (Qary.SupportComponents.GraphComponents E.family (windowLength k d)) = c) :
    ∃ description : Description α d n (windowLength k d) ν c,
      decodeDescription x n k d ν c hν description = some (dataOfFamily E) := by
  obtain ⟨roots, instructions, hroots, hcost, hdecode, hpos, hbounded⟩ :=
    RecordBounds.generating_decode_exists_bounded E x n hx hg
  have hb : ∀ b, HeaderBounded (windowLength k d) d (E.header b) :=
    fun b => header_bounded (E.valid b)
  have hrootc : roots.length = c := hroots.trans hc
  let description := encodeDescription n k d ν c hν E.header hb
    roots hrootc hpos instructions
  refine ⟨description, ?_⟩
  rw [description_roundtrip x n k d ν c hν E.header hb roots hrootc hpos
    instructions (by simpa using hcost) hbounded, hdecode]
  rfl

#print axioms roots_roundtrip
#print axioms description_roundtrip
#print axioms serialized_generating_coverage

end DeletionCode.Burst.RecordSerialization
