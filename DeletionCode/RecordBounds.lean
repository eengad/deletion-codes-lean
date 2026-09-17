import DeletionCode.GeneratingRecovery
import DeletionCode.RecordCodec

/-!
Every successful decoder record has bounded numeric fields. These bounds are
derived from the executable guards, not postulated for the existence theorem.
-/
namespace DeletionCode.RecordBounds

open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec

theorem pathLength_le (k : ℕ) (h : Header) (side : Bool) :
    pathLength k h side ≤ 2 * windowLength k := by
  cases side <;> cases ho : h.orientation <;>
    simp [pathLength, negativeLength, positiveLength, shortLength, longLength, ho] <;> omega

theorem negativeLength_pos (k : ℕ) (h : Header)
    (hlo : 1 ≤ h.rho) (hhi : h.rho ≤ k + 1) : 0 < negativeLength k h := by
  rw [negativeLength_eq k h hlo hhi]
  unfold windowLength
  omega

theorem writeBits_bounds (s t : Memory) (m start len : ℕ) (bits : PartialWords.Bits len)
    (h : writeBits s m start bits = some t) : start + len ≤ m := by
  unfold writeBits at h
  split at h
  · rename_i hb
    exact hb.1
  · contradiction

theorem startNegative_bounds (k : ℕ) (h : Header) (offset : ℕ) (bits : PartialWords.Bits k)
    (s t : Memory) (hs : ConcreteStart.startNegative k h offset bits s = some t) :
    offset + k ≤ negativeLength k h :=
  writeBits_bounds s t (negativeLength k h) offset k bits hs

theorem startPositive_bounds (k : ℕ) (h : Header) (offset : ℕ) (bits : PartialWords.Bits k)
    (extra : Bool) (s t : Memory)
    (hs : ConcreteStart.startPositive k h offset bits extra s = some t) :
    offset + k ≤ positiveLength k h := by
  unfold ConcreteStart.startPositive at hs
  split at hs
  · assumption
  · contradiction

theorem fillFromBase_seed_bound (x : Letters) (n k L : ℕ) (s t : Memory)
    (m start r : ℕ) (h : ConcreteFill.fillFromBase x n k L s m start r = some t) :
    r + k ≤ L := by
  cases hseed : readBits s (start + r) k with
  | none => simp [ConcreteFill.fillFromBase, hseed] at h
  | some seed =>
    cases hwindow : SeedLookup.recoverWindow x n k L r seed with
    | none => simp [ConcreteFill.fillFromBase, hseed, hwindow] at h
    | some bits =>
      obtain ⟨a, ha, _⟩ := SeedLookup.recoverWindow_sound x n k L r seed bits hwindow
      exact ha.1

variable {B : Type*} [DecidableEq B]

/-- Every instruction that actually executes has offsets in the finite code range. -/
theorem execute_bounded (x : Letters) (n k : ℕ) (header : B → Header)
    (mem result : Bank B) (instruction : Instruction B)
    (hs : execute x n k header mem instruction = some result) :
    InstructionBounded (windowLength k) instruction := by
  cases instruction with
  | start source sourceSide sourceOffset dest destSide destOffset extra =>
    cases hread : readPath k (header source) (mem source) sourceSide sourceOffset k with
    | none => simp [execute, hread] at hs
    | some bits =>
      have hsource := readPath_bounds k (header source) (mem source)
        sourceSide sourceOffset k bits hread
      have hsourceLen := pathLength_le k (header source) sourceSide
      constructor
      · omega
      · cases destSide with
        | false =>
          cases hstart : ConcreteStart.startNegative k (header dest) destOffset bits (mem dest) with
          | none => simp [execute, hread, hstart] at hs
          | some t =>
            have hd := startNegative_bounds k (header dest) destOffset bits (mem dest) t hstart
            have hlen : negativeLength k (header dest) ≤ 2 * windowLength k :=
              pathLength_le k (header dest) false
            omega
        | true =>
          cases hstart : ConcreteStart.startPositive k (header dest) destOffset bits extra (mem dest) with
          | none => simp [execute, hread, hstart] at hs
          | some t =>
            have hd := startPositive_bounds k (header dest) destOffset bits extra (mem dest) t hstart
            have hlen : positiveLength k (header dest) ≤ 2 * windowLength k :=
              pathLength_le k (header dest) true
            omega
  | fillBase dest window seedOffset =>
    cases hfill : ConcreteFill.fillFromBase x n k (windowLength k) (mem dest)
      (negativeLength k (header dest)) (SelectedWindows.windowStart (negativeExtra k (header dest)) window)
      seedOffset with
    | none => simp [execute, hfill] at hs
    | some t =>
      have hb := fillFromBase_seed_bound x n k (windowLength k) (mem dest) t
        (negativeLength k (header dest))
        (SelectedWindows.windowStart (negativeExtra k (header dest)) window) seedOffset hfill
      change seedOffset ≤ 2 * windowLength k
      omega
  | fillSupplier source sourceSide sourceOffset dest window =>
    cases hread : readPath k (header source) (mem source) sourceSide sourceOffset (windowLength k) with
    | none => simp [execute, hread] at hs
    | some bits =>
      have hb := readPath_bounds k (header source) (mem source) sourceSide sourceOffset
        (windowLength k) bits hread
      have hlen := pathLength_le k (header source) sourceSide
      change sourceOffset ≤ 2 * windowLength k
      omega

theorem run_bounded (x : Letters) (n k : ℕ) (header : B → Header)
    (instructions : List (Instruction B)) (mem result : Bank B)
    (hs : run x n k header mem instructions = some result) :
    ∀ instruction ∈ instructions, InstructionBounded (windowLength k) instruction := by
  induction instructions generalizing mem with
  | nil => simp
  | cons instruction rest ih =>
    cases hexec : execute x n k header mem instruction with
    | none => simp [run, hexec] at hs
    | some next =>
      have hrest : run x n k header next rest = some result := by simpa [run, hexec] using hs
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact execute_bounded x n k header mem next _ hexec
      · exact ih next hrest q hq

theorem loadRoot_position_bound (x : Letters) (n a len : ℕ) (s t : Memory) (m : ℕ)
    (hlen : 0 < len) (h : ConcreteFill.loadRoot x n a len s m = some t) : a < n := by
  unfold ConcreteFill.loadRoot at h
  split at h
  · omega
  · contradiction

theorem loadRoots_bounded (x : Letters) (n k : ℕ) (header : B → Header)
    (hlo : ∀ b, 1 ≤ (header b).rho) (hhi : ∀ b, (header b).rho ≤ k + 1)
    (roots : List (B × ℕ)) (mem result : Bank B)
    (hs : loadRoots x n k header mem roots = some result) :
    ∀ b a, (b, a) ∈ roots → a < n := by
  induction roots generalizing mem with
  | nil => simp
  | cons root rest ih =>
    rcases root with ⟨b, a⟩
    cases hload : ConcreteFill.loadRoot x n a (negativeLength k (header b))
      (mem b) (negativeLength k (header b)) with
    | none => simp [loadRoots, hload] at hs
    | some t =>
      have hrest : loadRoots x n k header (Function.update mem b t) rest = some result := by
        simpa [loadRoots, hload] using hs
      intro c j hj
      rcases List.mem_cons.mp hj with heq | hj
      · cases heq
        exact loadRoot_position_bound x n a (negativeLength k (header b)) (mem b) t
          (negativeLength k (header b)) (negativeLength_pos k (header b) (hlo b) (hhi b)) hload
      · exact ih (Function.update mem b t) hrest c j hj

theorem decode_bounded [Fintype B] (x : Letters) (n k : ℕ) (header : B → Header)
    (hlo : ∀ b, 1 ≤ (header b).rho) (hhi : ∀ b, (header b).rho ≤ k + 1)
    (roots : List (B × ℕ)) (instructions : List (Instruction B)) (output : Output k header)
    (hs : decode x n k header roots instructions = some output) :
    (∀ b a, (b, a) ∈ roots → a < n) ∧
      ∀ instruction ∈ instructions, InstructionBounded (windowLength k) instruction := by
  cases hload : loadRoots x n k header (fun _ => empty) roots with
  | none => simp [decode, hload] at hs
  | some initial =>
    cases hrun : run x n k header initial instructions with
    | none => simp [decode, hload, hrun] at hs
    | some result =>
      exact ⟨loadRoots_bounded x n k header hlo hhi roots _ initial hload,
        run_bounded x n k header instructions initial result hrun⟩

/-- The successful generating-family record automatically satisfies all field bounds. -/
theorem generating_decode_exists_bounded [Fintype B]
    (E : GeneratingModel.EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k)) :
    ∃ roots instructions,
      roots.length = Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) ∧
      instructions.length ≤ 4 * Fintype.card B ∧
      decode x n k E.header roots instructions =
        some (fun b i => negativePath k (E.header b) (E.long b) i.val) ∧
      (∀ b a, (b, a) ∈ roots → a < n) ∧
      (∀ instruction ∈ instructions, InstructionBounded (windowLength k) instruction) := by
  obtain ⟨roots, instructions, hroots, hcost, hdecode⟩ :=
    GeneratingRecovery.generating_decode_exists E x n hx hg
  have hbounds := decode_bounded x n k E.header E.rho_lower E.rho_upper roots instructions _ hdecode
  exact ⟨roots, instructions, hroots, hcost, hdecode, hbounds⟩

#print axioms execute_bounded
#print axioms run_bounded
#print axioms loadRoots_bounded
#print axioms decode_bounded
#print axioms generating_decode_exists_bounded

end DeletionCode.RecordBounds
