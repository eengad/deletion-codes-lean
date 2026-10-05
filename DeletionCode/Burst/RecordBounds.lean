import DeletionCode.Burst.GeneratingRecovery
import DeletionCode.Burst.RecordCodec

/-!
Every successful decoder record has bounded numeric fields. These bounds are
derived from the executable guards, not postulated for the existence theorem.
-/
namespace DeletionCode.Burst.RecordBounds

variable {α : Type*} [DecidableEq α] [Inhabited α]

open DeletionCode.Qary.Windows DeletionCode.Qary.PartialWords DeletionCode.Burst.HeaderRecovery DeletionCode.Burst.PathMemory DeletionCode.Burst.ConcreteDecoder DeletionCode.Burst.RecordCodec

theorem pathLength_le (k d : ℕ) (h : Header α) (hv : h.Valid k d) (side : Bool) :
    pathLength k d h side ≤ 4 * windowLength k d := by
  have hn := (negativeLength_bounds hv).2
  have hp := (positiveLength_bounds hv).2
  have hd : d ≤ windowLength k d := by unfold windowLength; omega
  cases side <;> dsimp [pathLength] <;> omega

theorem negativeLength_pos (k d : ℕ) (h : Header α) (hv : h.Valid k d) :
    0 < negativeLength h := by
  have := (negativeLength_bounds hv).1
  unfold windowLength at this
  omega

theorem writeBits_bounds (s t : Memory α) (m start len : ℕ) (bits : Qary.PartialWords.Bits α len)
    (h : writeBits s m start bits = some t) : start + len ≤ m := by
  unfold writeBits at h
  split at h
  · rename_i hb
    exact hb.1
  · contradiction

theorem startNegative_bounds (k d : ℕ) (h : Header α) (offset : ℕ) (bits : Qary.PartialWords.Bits α k)
    (s t : Memory α) (hs : ConcreteStart.startNegative k d h offset bits s = some t) :
    offset + k ≤ negativeLength h :=
  writeBits_bounds s t (negativeLength h) offset k bits hs

theorem startPositive_bounds (k d : ℕ) (h : Header α) (offset : ℕ) (bits : Qary.PartialWords.Bits α k)
    (extra : Qary.PartialWords.Bits α d) (s t : Memory α)
    (hs : ConcreteStart.startPositive k d h offset bits extra s = some t) :
    offset + k ≤ positiveLength h := by
  unfold ConcreteStart.startPositive at hs
  split at hs
  · assumption
  · contradiction

theorem fillFromBase_seed_bound (x : Letters α) (n k L : ℕ) (s t : Memory α)
    (m start r : ℕ) (h : Qary.ConcreteFill.fillFromBase x n k L s m start r = some t) :
    r + k ≤ L := by
  cases hseed : readBits s (start + r) k with
  | none => simp [Qary.ConcreteFill.fillFromBase, hseed] at h
  | some seed =>
    cases hwindow : Qary.SeedLookup.recoverWindow x n k L r seed with
    | none => simp [Qary.ConcreteFill.fillFromBase, hseed, hwindow] at h
    | some bits =>
      obtain ⟨a, ha, _⟩ := Qary.SeedLookup.recoverWindow_sound x n k L r seed bits hwindow
      exact ha.1

variable {B : Type*} [DecidableEq B]

/-- Every instruction that actually executes has offsets in the finite code range. -/
theorem execute_bounded (x : Letters α) (n k d : ℕ) (header : B → Header α)
    (hv : ∀ b, (header b).Valid k d) (mem result : Bank α B) (instruction : Instruction α d B)
    (hs : execute x n k d header mem instruction = some result) :
    InstructionBounded (windowLength k d) instruction := by
  cases instruction with
  | start source sourceSide sourceOffset dest destSide destOffset extra =>
    cases hread : readPath k d (header source) (mem source) sourceSide sourceOffset k with
    | none => simp [execute, hread] at hs
    | some bits =>
      have hsource := readPath_bounds k d (header source) (mem source)
        sourceSide sourceOffset k bits hread
      have hsourceLen := pathLength_le k d (header source) (hv source) sourceSide
      constructor
      · omega
      · cases destSide with
        | false =>
          cases hstart : ConcreteStart.startNegative k d (header dest) destOffset bits (mem dest) with
          | none => simp [execute, hread, hstart] at hs
          | some t =>
            have hd := startNegative_bounds k d (header dest) destOffset bits (mem dest) t hstart
            have hlen : negativeLength (header dest) ≤ 4 * windowLength k d :=
              pathLength_le k d (header dest) (hv dest) false
            omega
        | true =>
          cases hstart : ConcreteStart.startPositive k d (header dest) destOffset bits extra (mem dest) with
          | none => simp [execute, hread, hstart] at hs
          | some t =>
            have hd := startPositive_bounds k d (header dest) destOffset bits extra (mem dest) t hstart
            have hlen : positiveLength (header dest) ≤ 4 * windowLength k d :=
              pathLength_le k d (header dest) (hv dest) true
            omega
  | fillBase dest window seedOffset =>
    cases hfill : Qary.ConcreteFill.fillFromBase x n k (windowLength k d) (mem dest)
      (negativeLength (header dest)) (SelectedWindows.windowStart (negativeExtra k d (header dest)) window)
      seedOffset with
    | none => simp [execute, hfill] at hs
    | some t =>
      have hb := fillFromBase_seed_bound x n k (windowLength k d) (mem dest) t
        (negativeLength (header dest))
        (SelectedWindows.windowStart (negativeExtra k d (header dest)) window) seedOffset hfill
      change seedOffset ≤ 2 * (2 * windowLength k d)
      omega
  | fillSupplier source sourceSide sourceOffset dest window =>
    cases hread : readPath k d (header source) (mem source) sourceSide sourceOffset (windowLength k d) with
    | none => simp [execute, hread] at hs
    | some bits =>
      have hb := readPath_bounds k d (header source) (mem source) sourceSide sourceOffset
        (windowLength k d) bits hread
      have hlen := pathLength_le k d (header source) (hv source) sourceSide
      change sourceOffset ≤ 2 * (2 * windowLength k d)
      omega

theorem run_bounded (x : Letters α) (n k d : ℕ) (header : B → Header α)
    (hv : ∀ b, (header b).Valid k d) (instructions : List (Instruction α d B)) (mem result : Bank α B)
    (hs : run x n k d header mem instructions = some result) :
    ∀ instruction ∈ instructions, InstructionBounded (windowLength k d) instruction := by
  induction instructions generalizing mem with
  | nil => simp
  | cons instruction rest ih =>
    cases hexec : execute x n k d header mem instruction with
    | none => simp [run, hexec] at hs
    | some next =>
      have hrest : run x n k d header next rest = some result := by simpa [run, hexec] using hs
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact execute_bounded x n k d header hv mem next _ hexec
      · exact ih next hrest q hq

theorem loadRoot_position_bound (x : Letters α) (n a len : ℕ) (s t : Memory α) (m : ℕ)
    (hlen : 0 < len) (h : Qary.ConcreteFill.loadRoot x n a len s m = some t) : a < n := by
  unfold Qary.ConcreteFill.loadRoot at h
  split at h
  · omega
  · contradiction

theorem loadRoots_bounded (x : Letters α) (n k d : ℕ) (header : B → Header α)
    (hv : ∀ b, (header b).Valid k d)
    (roots : List (B × ℕ)) (mem result : Bank α B)
    (hs : loadRoots x n k d header mem roots = some result) :
    ∀ b a, (b, a) ∈ roots → a < n := by
  induction roots generalizing mem with
  | nil => simp
  | cons root rest ih =>
    rcases root with ⟨b, a⟩
    cases hload : Qary.ConcreteFill.loadRoot x n a (negativeLength (header b))
      (mem b) (negativeLength (header b)) with
    | none => simp [loadRoots, hload] at hs
    | some t =>
      have hrest : loadRoots x n k d header (Function.update mem b t) rest = some result := by
        simpa [loadRoots, hload] using hs
      intro c j hj
      rcases List.mem_cons.mp hj with heq | hj
      · cases heq
        exact loadRoot_position_bound x n a (negativeLength (header b)) (mem b) t
          (negativeLength (header b)) (negativeLength_pos k d (header b) (hv b)) hload
      · exact ih (Function.update mem b t) hrest c j hj

theorem decode_bounded [Fintype B] (x : Letters α) (n k d : ℕ) (header : B → Header α)
    (hv : ∀ b, (header b).Valid k d)
    (roots : List (B × ℕ)) (instructions : List (Instruction α d B)) (output : Output k d header)
    (hs : decode x n k d header roots instructions = some output) :
    (∀ b a, (b, a) ∈ roots → a < n) ∧
      ∀ instruction ∈ instructions, InstructionBounded (windowLength k d) instruction := by
  cases hload : loadRoots x n k d header (fun _ => empty) roots with
  | none => simp [decode, hload] at hs
  | some initial =>
    cases hrun : run x n k d header initial instructions with
    | none => simp [decode, hload, hrun] at hs
    | some result =>
      exact ⟨loadRoots_bounded x n k d header hv roots _ initial hload,
        run_bounded x n k d header hv instructions initial result hrun⟩

/-- The successful generating-family record automatically satisfies all field bounds. -/
theorem generating_decode_exists_bounded [Fintype B]
    (E : GeneratingModel.EditedFamily α B k d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k d)) :
    ∃ roots instructions,
      roots.length = Fintype.card (Qary.SupportComponents.GraphComponents E.family (windowLength k d)) ∧
      instructions.length ≤ 4 * Fintype.card B ∧
      decode x n k d E.header roots instructions =
        some (fun b i => negativePath (E.header b) (E.long b) i.val) ∧
      (∀ b a, (b, a) ∈ roots → a < n) ∧
      (∀ instruction ∈ instructions, InstructionBounded (windowLength k d) instruction) := by
  obtain ⟨roots, instructions, hroots, hcost, hdecode⟩ :=
    GeneratingRecovery.generating_decode_exists E x n hx hg
  have hbounds := decode_bounded x n k d E.header E.valid roots instructions _ hdecode
  exact ⟨roots, instructions, hroots, hcost, hdecode, hbounds⟩

#print axioms execute_bounded
#print axioms run_bounded
#print axioms loadRoots_bounded
#print axioms decode_bounded
#print axioms generating_decode_exists_bounded

end DeletionCode.Burst.RecordBounds
