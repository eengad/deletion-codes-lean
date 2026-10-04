import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
Finite description-space bound checked with Lean 4.34.0.
RecordSerialization implements and verifies this format. GeneratingCount and
SignedRuleCount transfer the bound to decoded words and signed rule sets;
ManuscriptCounting supplies the catalogue-level counting theorem.
-/
namespace DeletionCode.DescriptionCount

def fieldBound (L ν : ℕ) : ℕ := 16 * L * (ν + 1)

/--
Root positions; headers; root names; padded instructions with 12 fields.
RecordCodec verifies the twelve-field instruction serialization.
-/
abbrev Description (n L ν c : ℕ) :=
  (Fin c → Fin n) × (Fin ν → Fin (6 * L)) × (Fin c → Fin ν) ×
  (Fin (4 * ν) → (Fin 12 → Fin (fieldBound L ν)))

theorem description_card (n L ν c : ℕ) :
    Fintype.card (Description n L ν c) =
      n ^ c * (6 * L) ^ ν * ν ^ c * ((fieldBound L ν) ^ 12) ^ (4 * ν) := by
  simp [Description, Fintype.card_prod, Fintype.card_fun]
  <;> ring

/-- Positions alone contribute the factor n^c in this raw record space. -/
theorem description_bound (n L ν c : ℕ)
    (hL : 1 ≤ L) (hν : 1 ≤ ν) (hc : c ≤ ν) :
    Fintype.card (Description n L ν c) ≤
      n ^ c * (fieldBound L ν) ^ (50 * ν) := by
  let B := fieldBound L ν
  have hmul : ν ≤ L * ν := by
    calc
      ν = 1 * ν := (one_mul ν).symm
      _ ≤ L * ν := Nat.mul_le_mul_right ν hL
  have hB : 1 ≤ B := by
    dsimp [B, fieldBound]
    nlinarith
  have hheader : 6 * L ≤ B := by
    dsimp [B, fieldBound]
    nlinarith
  have hname : ν ≤ B := by
    dsimp [B, fieldBound]
    nlinarith
  have hp1 : (6 * L) ^ ν ≤ B ^ ν := by gcongr
  have hp2 : ν ^ c ≤ B ^ ν := by
    calc
      ν ^ c ≤ B ^ c := by gcongr
      _ ≤ B ^ ν := by gcongr
  have hpower : B ^ ν * B ^ ν * (B ^ 12) ^ (4 * ν) = B ^ (50 * ν) := by
    rw [← pow_add, ← pow_mul, ← pow_add]
    congr 1
    omega
  calc
    Fintype.card (Description n L ν c) =
        n ^ c * ((6 * L) ^ ν * ν ^ c * (B ^ 12) ^ (4 * ν)) := by
          rw [description_card]
          dsimp [B]
          ring
    _ ≤ n ^ c * (B ^ ν * B ^ ν * (B ^ 12) ^ (4 * ν)) := by gcongr
    _ = n ^ c * B ^ (50 * ν) := by rw [hpower]

#print axioms description_card
#print axioms description_bound
end DeletionCode.DescriptionCount
