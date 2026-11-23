# deletion-codes-lean

[![build](https://github.com/eengad/deletion-codes-lean/actions/workflows/build.yml/badge.svg)](https://github.com/eengad/deletion-codes-lean/actions/workflows/build.yml)

A Lean 4 formalization of the main theorem of

> Eyal En Gad, *Explicit codes correcting t edits with redundancy coefficient
> 2t − 1*, 2026.

The repository also retains the earlier Lean 4 formalization of the existence
bounds of

> Eyal En Gad, *Polynomially larger deletion codes by linear hashing of
> substring counts*, [arXiv:2609.19493](https://arxiv.org/abs/2609.19493),
> 2026.

See [EXISTENCE.md](EXISTENCE.md) for the existence theorems, file locations,
and lemma map (the git tag `existence-only` preserves that snapshot on Lean
4.34.0 with Mathlib as its only dependency).

## Provenance

The formalization was produced with the assistance of large language models
(OpenAI's GPT, Anthropic's Claude, and Google's Gemini), as was the paper.
For the explicit construction, the author read and verified that the formal
theorem statement and encodings
([`Statement.lean`](DeletionCode/Explicit/Statement.lean)) and the channel
definitions ([`Channel.lean`](DeletionCode/Burst/Channel.lean)) — everything
outside Mathlib that the statement depends on — match the corresponding
theorem and definitions in the paper. The author did not review the Lean proof
files, which are checked by the Lean kernel. Only the main theorem is
formalized, not the paper's intermediate exposition, remark estimates,
historical comparisons, or related work.

## Checking the statement

To verify what is proved for the explicit paper, only those two short files
outside Mathlib need to be read (82 lines in total):

- [`DeletionCode/Explicit/Statement.lean`](DeletionCode/Explicit/Statement.lean)
  defines the bit encodings (`unaryCode`, `framed`, `wordCode`, `inputCode`)
  and the theorem statement `DeletionCode.Explicit.DeterministicStatement`,
  using only Mathlib (`Real.logb`, `Turing.TM2ComputableInPolyTime`) and the
  channel file below.
- [`DeletionCode/Burst/Channel.lean`](DeletionCode/Burst/Channel.lean) defines
  the bounded substring-edit channel (`Word`, `Script`, `WithinBursts`),
  importing only `Mathlib.Data.List.Basic`.

The theorem is proved as `DeletionCode.Explicit.deterministic_mathlib :
DeterministicStatement` in
[`DeletionCode/Explicit/DeterministicMathlib.lean`](DeletionCode/Explicit/DeterministicMathlib.lean).
Although the proof uses `cslib` and `cslib-frontier` internally, neither
library appears in the statement;
[`scripts/check-statement-imports.lean`](scripts/check-statement-imports.lean)
checks that import boundary automatically. No file uses `sorry`, and no axioms
are added: [`scripts/verify-explicit-theorem.lean`](scripts/verify-explicit-theorem.lean)
checks that `deterministic_mathlib` has type `DeterministicStatement` and
prints its axioms, and the GitHub Actions workflow
([`.github/workflows/build.yml`](.github/workflows/build.yml)) fails if any
axiom outside Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) — such as `sorryAx` — appears.

## What is proved

For every fixed edit budget `t ≥ 2`, substring-edit bound `b ≥ 1`, and
alphabet size `q ≥ 2`, `DeterministicStatement` asserts the existence of
uniform deterministic polynomial-time procedures `setup`, `encode`, and
`decode` (each certified in Mathlib's `TM2ComputableInPolyTime` model with
finite stack alphabets) for all sufficiently large block lengths `n`. Given
`n` in unary, `setup` produces polynomially many public bits; using them,
`encode` maps length-`k n` messages over `Fin q` to length-`n` codewords with
redundancy at most `(2t − 1) log_q n + C log_q log_q n`, and `decode` recovers
the message after any sequence of at most `t` bounded `b`-substring edits
(including single insertions, deletions, and substitutions when `b = 1`, where
edits may overlap and either block may be empty).

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
`lean-toolchain` (Lean 4.36.0-rc2), and `cslib-frontier` (which brings in
`cslib` and Mathlib) is pinned in `lakefile.toml` and `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean --run scripts/check-statement-imports.lean
lake env lean scripts/verify-explicit-theorem.lean
```

`lake build` builds both the explicit and existence developments (starting from
the root module [`DeletionCode.lean`](DeletionCode.lean)) and runs the
`#print axioms` checks. To build only the explicit theorem and its
dependencies, run `lake build DeletionCode.Explicit.DeterministicMathlib`
followed by the two verification commands above.

## Licence

Copyright 2026 Eyal En Gad. Licensed under the Apache License, Version 2.0;
see [LICENSE](LICENSE).
