# deletion-codes-lean

[![build](https://github.com/eengad/deletion-codes-lean/actions/workflows/build.yml/badge.svg)](https://github.com/eengad/deletion-codes-lean/actions/workflows/build.yml)

A Lean 4 formalization of the main theorem of

> Eyal En Gad, *Polynomially larger deletion codes by linear hashing of
> substring counts*, [arXiv:2609.19493](https://arxiv.org/abs/2609.19493),
> 2026.

The paper proves that binary codes of length n correcting t >= 2 deletions
exist with redundancy (2t-1) log2 n + O_t(log2 log2 n), improving the leading
coefficient 2t of Levenshtein's 1965 bound. This repository checks that proof
in Lean, from the definitions of words and edits up to the final bound.

## The theorem

```lean
theorem DeletionCode.OptimalRedundancy.main (t : ℕ) (ht : 2 ≤ t) :
    ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      optimalRedundancy t n ≤
        ((2 * t - 1 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) +
          (K : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ))
```

Here `optimalRedundancy t n = n - log2 (optimalCodeSize t n)`, and
`optimalCodeSize t n` is the maximum cardinality over all subsets of the
n-bit words in which no two distinct words are confusable. Two words are
confusable when some output can be reached from each of them by at most t
single insertions and deletions in total (`EditAlignment.Script`,
`EditAlignment.WithinEdits`, `FiniteConflictGraph.Confusable`,
`CodeSelection.Corrects`). This is at least as strong as correcting t
deletions. The constant is explicit, with no attempt at optimisation:
K = 6 b_t + 6, where b_t = 4 a_t + 2 (`WitnessCost.exponent`) and
a_t = 100 t (32 t + 17) is the exponent in the count of Lemma 5.1
(`CountExponent.exponent`). The result is an existence statement; no encoder
or decoder is asserted.

## Building

Install [elan](https://github.com/leanprover/elan); the toolchain is pinned
in `lean-toolchain` (Lean 4.34.0) and mathlib is pinned in `lakefile.toml`.

```sh
lake exe cache get
lake build
```

## What is checked

| Paper (arXiv v1) | Lean |
| --- | --- |
| Lemma 2.1, most words are k-unique | `UniqueWordCount.most_words_unique_real`, `UniqueWordCount.half_words_le_card_unique` |
| Lemma 2.2, the spectrum is a simple path and determines the word | `SpectrumPath.spectrum_is_simple_path_and_determines_word` |
| Lemma 2.3, equal-length confusability | `EditAlignment.equal_length_confusability` |
| Lemma 2.4, shared source letters | `EditRigidity.shared_source_letters`, `EditRigidity.one_edit_unique`, `ScriptRigidity.within_one_unique` |
| Lemma 2.6, coverage of separated conflicts | `SeparatedTraceCoverage.catalogueRule`, `VerifiedConflictGraphWitness.separated_coverage` |
| Lemma 3.2, independent differences | `RandomHash.independent_differences`, `RandomHash.real_rules_survival_probability_toReal`, `RandomHash.real_nonzero_test_probability_toReal` |
| Lemma 3.3, the nonseparated family is thin | `NonseparatedFamily.nonseparated_family_thin` |
| Lemma 4.4, connected blocks | `ConnectedBlocks.adjoining_rule_bound`, `ConnectedBlocks.connected_block_bound` |
| Lemma 4.5, savings from a relation | `RelationSavings.savings_from_relation` |
| Lemma 4.6, bounded witness | `VerifiedConflictGraphWitness.bounded_witness` |
| Lemma 5.1, counting generating sets | `ManuscriptCounting.counting_generating_sets` |
| Proposition 6.1, obstructions are rare | `PaperProbability.obstructions_are_rare` |
| Theorems 1.1 and 6.2 | `OptimalRedundancy.main`, with `CodeExistence.main` and `CodeExistence.eventually_exists_code` |

Where a formal statement is not word for word the paper's, it is the more
general one: it drops a hypothesis that the proof turned out not to need, so
the paper's statement follows as a special case. For example, Lemma 4.5 is
proved without the side condition |I| >= 2, Lemma 4.4 for every t >= 1, and
the final theorem for t insertions and deletions in total rather than
deletions only. [VERIFIED_LEMMAS.md](VERIFIED_LEMMAS.md) gives the exact
hypotheses of every row.

## What is not checked

Lean certifies the formal statements. That each formal statement says what
the corresponding statement of the paper says is a matter of reading the
definitions, and is the reader's to check; the table above and
VERIFIED_LEMMAS.md are there to make that easy. The formalization does not
cover the paper's narrative, its historical comparisons, or its related work.

No proof uses `sorry`, and no axioms are added. The axioms reported for the
final theorem are Lean's standard `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The formalization was developed with the assistance of large language
models, as was the paper. Every definition and proof in this repository is
checked by the Lean kernel.

## Licence

Copyright 2026 Eyal En Gad. Licensed under the Apache License, Version 2.0;
see [LICENSE](LICENSE).
