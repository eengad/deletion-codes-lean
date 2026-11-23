import DeletionCode.Explicit.Statement
import DeletionCode.Explicit.DeterministicMathlib

/-- Confirm that `deterministic_mathlib` proves the exact standalone statement. -/
example : DeletionCode.Explicit.DeterministicStatement :=
  @DeletionCode.Explicit.deterministic_mathlib

#print axioms DeletionCode.Explicit.deterministic_mathlib
