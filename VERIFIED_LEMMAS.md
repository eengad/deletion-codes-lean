# Verification map

Eleven lemmas, one proposition, and the final theorem of the paper are
verified. The target is

> Eyal En Gad, *Polynomially larger deletion codes by linear hashing of
> substring counts*, arXiv preprint, submitted 16 September 2026
> (version 1; identifier pending).

Statements are identified below by the LaTeX labels of the paper's source;
the README gives the corresponding lemma numbers. The introductory
`thm:intro` is the same result restated as `thm:main`. No statement of a
lemma, proposition or theorem has changed since version 1; later revisions
of the paper only clarify the prose.

## Complete manuscript statements

| Paper statement | Lean theorem | Hypotheses and interpretation |
| --- | --- | --- |
| `lem:family`: Most words are k-unique | `UniqueWordCount.most_words_unique_real` and `UniqueWordCount.half_words_le_card_unique` | For positive n and the actual k = 2 ceil(log_2 n) + 2, the cardinality of the finite k-unique family is at least (1 - binomial(n,2)/2^k) times 2^n, at least (7/8) times 2^n, and at least 2^(n-1). Repeated substrings may overlap; their count is derived from a concrete injective encoding. The union bound, pair count, and ceiling-log estimate are proved. The family uses exactly the conflict graph's word and uniqueness definitions. |
| `lem:path`: The spectrum is a simple path, and determines the word | `SpectrumPath.spectrum_is_simple_path_and_determines_word` | A word of length n >= L is (L-1)-unique. L >= 1 is explicit, as ensured by the paper's L = 3(k+1). Actual integer spectrum counts are Boolean; every path vertex and edge is accounted for; any length-n word with equal spectrum has the same letters. No uniqueness assumption on the competing word. |
| `lem:confuse`: Equal-length confusability | `EditAlignment.equal_length_confusability` | Two length-n binary lists reach the same output using at most t single insertions/deletions each. The result constructs actual matched/deletion/insertion alignment columns with d <= t edits of each kind. Distinctness of the two words is unnecessary. |
| `lem:rigidity`: Shared source letters | `EditRigidity.shared_source_letters`, `EditRigidity.one_edit_unique`, and `ScriptRigidity.within_one_unique` | With k >= 1, a k-unique source, and two fixed valid single edits (including no edit), equal in-bounds (L-1)-windows contain a common length-k block of surviving source positions at the same window offset. Every resulting word is (L-1)-unique. Actual-script versions derive the concrete edits from `WithinEdits 1`; no origin map, clean block, or edited-word uniqueness is assumed. The paper's k >= 2 ensures positivity. |
| `lem:coverage`: Coverage of separated conflicts | `SeparatedTraceCoverage.catalogueRule` and `VerifiedConflictGraphWitness.separated_coverage` | An actual trace from a k-unique source with exactly t deletions and t insertions and 4L matched-column separation from other edits and boundaries yields the concrete catalogue rule for its full spectrum difference. All local words, balance, vertex disjointness, and the signed sum are derived. No target uniqueness or supplied catalogue presentation. The finite-word interface also handles k = 0. |
| `lem:hash-independent`: Independent differences | `RandomHash.independent_differences`, `RandomHash.real_rules_survival_probability_toReal`, and `RandomHash.real_nonzero_test_probability_toReal` | For any fixed finite family of rationally independent integer vectors, the actual hash with independent uniform real weights on [0,1) has independent uniform circle outputs. For Q >= 2, all R fixed catalogue members survive with probability (2/Q)^R; any nonzero integer vector passes the strict norm test with probability 2/Q. Surjectivity, normalization, independence, and arc measures are derived. No primitivity or unimodularity assumption. |
| `lem:nonsep`: The nonseparated family is thin | `NonseparatedFamily.nonseparated_family_thin` | For t >= 2, a k-unique length-n source, n >= L = 3(k+1), and Q >= 2, the actual exceptional event has probability at most 2 c_t L n^(2t-1)/Q for an explicit positive constant depending only on t. The finite partner count, reconstruction, separation-failure saving, nonzero spectrum differences, and probability union bound are derived. Partners need not be unique. The n >= L hypothesis is the paper's standing assumption, stated after equation (3) in Section 2.3. |
| `lem:block`: Connected blocks | `ConnectedBlocks.adjoining_rule_bound` and `ConnectedBlocks.connected_block_bound` | Catalogue rules have concrete presentations by 2t bubbles with the paper's geometry and balance. Adjoining an adjacent rule increases the intrinsic component count by at most 2t-1. A nonempty rule set connected by adjacencies within that set satisfies c(B) <= (2t-1) times B.card + 1. The formal result allows t >= 1; the paper assumes t >= 2. |
| `lem:saving`: Savings from a relation | `RelationSavings.savings_from_relation` | An actual finite set I of catalogue rules, another catalogue rule w, and a rational coordinatewise relation w = sum of a(u)u over I, with every a(u) nonzero, imply c(I) <= t times I.card + t. The result does not need the paper's extra independence, generation, or I.card >= 2 restrictions. |
| `lem:witness`: Bounded witness | `VerifiedConflictGraphWitness.bounded_witness` | For t >= 2, Q >= 2, an additive circle hash, and a retained vertex whose component in the actual finite conflict graph is not two-colorable, derives an independent surviving generating witness and the exact counted-set predicate, with all manuscript size and component bounds. The exceptional set, separated edge traces, odd walk, catalogue coverage, and equal-bin survival are derived. No coverage premise remains. |
| `lem:resolve`: Counting generating sets | `ManuscriptCounting.counting_generating_sets` | The concrete catalogue grammar and path restrictions, k-unique base word, R >= 1, and signed generating condition. The bound counts underlying sets of signed vectors with their intrinsic support-component count. Independence may be imposed using `filtered_card_bound`; the unrestricted result is stronger. |
| `prop:obstruction`: Obstructions are rare | `PaperProbability.obstructions_are_rare` | For each fixed t >= 2 and all sufficiently large n, every Q >= 8*n^(2*t-1)*L^b_t and every actual k-unique word have obstruction-event probability at most 1/12. The event requires that the word is a retained graph vertex and its actual component is not two-colorable. Candidate finiteness and counts, exact survival probabilities, the geometric tail, and all logarithmic-parameter side conditions are derived; no conditioning on the random graph. |
| `thm:main`: Optimal redundancy bound | `OptimalRedundancy.main`, with `CodeExistence.main` and `CodeExistence.eventually_exists_code` | For each fixed t >= 2, a constant K depending only on t bounds optimal redundancy by (2*t-1)*log_2(n) + K*log_2(log_2(n)) for all sufficiently large n. The optimum is the attained maximum cardinality over actual correcting subsets of the n-bit word space, with its minimum-redundancy interpretation proved. The code-existence form produces nonempty finite codes correcting at most t genuine insertions/deletions in total, with explicit K = 6*b_t+6 and b_t = 4*a_t+2. No large-code, probability, or asymptotic side condition is an input to these final theorems. |

For the unique-word family lemma, `OverlapCollision.collision_card_le`
proves that agreeing length-k substrings at positions a < b leave at most
2^(n-k) possible words. Its encoding deletes the later interval [b,b+k).
Each missing bit equals an earlier source bit, so strong induction recovers
every bit from the retained ones; no non-overlap or independence premise is used.
`FinitePairUnion.ordered_pair_card` derives binomial(n,2) pairs from a
triangular finite index type, and `ordered_pair_union_bound` counts the union
of their events without multiplying words that have several repeated pairs.

`UniqueWordCount.not_unique_iff_pair` identifies every actual failure of
k-uniqueness with one such in-bounds pair, for k >= 1. Invalid pairs contribute
zero, and k > n makes every word unique. `card_unique_lower_bound` proves the
general bound before any logarithmic parameter is substituted.
`UniqueWordParameters.uniquenessLength_eq_ceil` proves that the computed
parameter equals the paper's ordinary integer ceiling of the real logarithm
when n >= 1; `eight_mul_choose_le_pow` proves the one-eighth allowance.
The final theorem records the entire inequality chain in both rationals and
reals. Positive n is explicit because the manuscript parameter uses log_2 n.

`SpectrumPath.catalogue_window_spectrum` specializes the path lemma to the
paper's L = 3(k+1), deriving the required (L-1)-uniqueness directly from
k-uniqueness. The descriptions and counting proofs use exactly the same
`SignedSupport.wordSpectrum` definition as the path lemma.

For rigidity, `SingleEditOrigins.Edit` implements unchanged words, deletion
at a valid source index, and insertion at a valid gap, including both boundary
gaps. Its `origin` map is computed from the edit: an inserted letter has no
source index, surviving indices are injective, and in-bounds output letters
have in-bounds source indices with the correct bits. These facts are proved
from the edit definitions.

`TwoEditWindows.exists_clean_block_among_three` proves that one of the
length-k blocks starting at offsets 0, k+1, or 2(k+1) avoids both edit cuts
and fits in an (L-1)-window, since L-1 = 3k+2. On this block, source indices
are consecutive in both realizations. Equality of the windows and source
k-uniqueness force the two source starting indices to coincide. This proves
`EditRigidity.shared_source_letters` for every fixed pair of edits, not just
for a specially chosen origin labelling. Source-index injectivity then gives
`EditRigidity.one_edit_unique`.

`SingleEditScripts.within_one_realized` classifies a genuine list edit script
of total cost at most one as unchanged, one deletion, or one insertion at its
actual list split. It derives a valid concrete edit, the exact output length,
and equality of the complete padded letter functions. Consequently
`ScriptRigidity.shared_source_letters` and `ScriptRigidity.within_one_unique`
apply directly to actual scripts. The further Boolean-spectrum and simple
vertex-path corollaries use the same checked spectrum as the counting proof;
the latter includes all endpoint vertices when the output length is at least L.
These results establish `lem:rigidity` and supply the local rigidity used
in the separated multi-edit catalogue construction below.

For the block lemma, both the singleton component bound and the connected
growth order are proved. Neither a component-count inequality nor a spanning
tree ordering is supplied as a hypothesis. Component counts use only incident
vertices of the actual nonzero signed-support union; connecting paths between
rules are restricted to the counted set.

For the savings lemma, `CatalogueFamily.ofCatalogue` constructs the combined
2t times I.card bubble occurrences from the individual rules. Their map to
intrinsic support components is proved surjective. A component with one
occurrence supplies an actual negative gram unique to its owning rule; the
nonzero coefficient forces this gram to survive in w. The relation itself
implies support containment, giving a map from w's components into I's.
Consequently at most 2t components have singleton occurrence fibers, and
`ComponentFibers.component_count_bound` proves the remaining counting step.
No support-containment or component-count conclusion is supplied as a premise.

## Verified separated coverage

`SeparatedTraceCoverage.catalogueRule` proves the entire coverage lemma.
Its local constructions and geometric arguments are as follows.

- `UniqueRuns.constant_length_le` bounds every in-bounds constant substring
  of a k-unique source by k; `no_constant_succ_window` excludes length k+1.
  `insert_constant_length_le` bounds a constant substring after a valid
  insertion by k+1. None of these run bounds requires positive k.
- `MaximalRuns.exists_maximal_run_unique` extracts an actual maximal run
  containing a specified deleted letter. The insertion counterparts extract
  the run containing the inserted bit and prove that shortening it recovers
  the exact source. Existing adjacent bits are opposite to the run bit.
  `eraseIdx_same_in_run` proves that changing the deleted position within
  this run leaves the resulting finite word unchanged.
- `RunBubbleConstruction.exists_deletion_bubble` and `exists_insertion_bubble`
  construct the actual `BubbleWord`, its flanks, boundary bits, and unchanged
  exterior words from a k-unique source and an edit at least 4L from both
  boundaries. The exact source and target concatenations are conclusions.
  The local word's location relative to the actual edit is also bounded.
- `SpectrumLocalization.context_replacement` proves the exact spectrum
  cancellation for arbitrary exterior lists and local words with equal
  first and last L-1 letters. `BubbleLocalSpectrum` derives those equal
  boundary words from the repeated-run grammar; its
  `oriented_context_replacement_vector` proves the positive-minus-negative
  identity for actual integer spectrum vectors. No uniqueness, simple-path,
  or opposite-bit assumption is needed for this identity.
- `BubbleEndpoints.deletion_endpoints` and `insertion_endpoints` derive the
  displacement of equal windows from their shared surviving source letters.
  The two flank-bit mismatches then force the initial or terminal endpoint.
  `BubblePathSimplicity` derives both simple paths from actual substring
  realizations and source uniqueness, including all endpoint vertices.
  `BubbleContextGeometry.context_geometry` combines these for the concrete
  grammar inside unchanged context. Its canonical edit at the run's end
  preserves the exact finite source and target; it does not assert that the
  original edit position or its origin map is unchanged.
- `TraceSeparation` proves monotonicity of the actual trace counters, then
  transfers matched-column gaps and boundary margins to source and target
  positions. The resulting neighborhoods are in bounds and disjoint.
  `EditLocality.origin_in_source_interval` derives containment of surviving
  origins for local unchanged, deletion, and insertion segments. Together
  with rigidity, `local_vertex_sets_disjoint` proves disjointness of their
  actual vertex sets, including endpoints, whenever their source intervals
  are disjoint. It assumes neither an origin map nor path disjointness.

`SingleEditBubbles.deletion_bubble` and `insertion_bubble` combine these
results for an actual edit of a k-unique finite word, assuming k >= 1 and
4L margins at both boundaries. They construct a `LocalBubble` with the
exact source and target concatenations, opposite flank bits, both simple
paths, endpoint-only intersections, and the actual signed spectrum change.
The insertion theorem also proves that the bubble bit is the inserted bit.
`LocalBubble.source_interval_in_neighborhood` puts each constructed source
interval inside its prescribed edit neighborhood;
`source_intervals_disjoint_of_trace` derives disjointness for any pair at
distinct edit columns of a separated trace.

`TraceEditData.EditColumn` consists exactly of the trace's edit-column
indices. Its deletion and insertion subtype cardinalities equal the actual
trace counters; `editEquiv` derives the Fin (2*t) enumeration. `TraceBubbleFamily`
constructs one bubble at each index, with its actual isolated target and
orientation in the type. `LocalBubbleDisjoint.localVertex_ne_of_trace`
derives pairwise disjointness for either side, including every endpoint,
from source uniqueness and separation.

`TraceSpectrumAssembly.spectrum_sum` proves the full signed vector identity.
The intermediate word is the target of the processed prefix followed by the
source of the remaining trace. Its spectrum increments telescope; matched
columns contribute zero. `TraceMatchedSuffix.common_suffix_before_edit`
derives at least L-1 matched letters just before every edit. The proved
`SpectrumPrefixChange.common_suffix_change` cancels the earlier prefix, so
each increment equals that edit performed alone on the original source.
This identity needs no uniqueness or assumed cancellation.

`BubbleCatalogue` identifies actual local-word spectra with path spectra and
converts the proved geometry to the exact finite index ranges in
`ValidCatalogue`. `SeparatedTraceCoverage.catalogueRule` reindexes the signed
sum, applies every local spectrum identity, and supplies the derived t/t
balance and disjointness. Finally,
`VerifiedConflictGraphWitness.separated_coverage` converts finite bit words
and handles k = 0: uniqueness forces an empty word, hence t = 0 and the
empty catalogue. This proves the existing coverage interface without changing it.

## Verified bounded-witness extraction core

`BoundedWitnessWalk.extract` proves the complete extraction from an odd closed
walk of Boolean integer spectrum vectors. Its inputs are t >= 2 and a finite
walk whose every successive difference is an actual catalogue rule belonging
to a specified surviving set K. The walk's length is unrestricted. The theorem
constructs an actual finite rule set U with rational independence, a generating
order at the initial vector, catalogue membership, survival, and

    2 <= U.card <= 1 + 4*t*L^2,
    c(U) <= (2*t-1)*U.card + 1,
    U.card <= L implies c(U) <= (2*t-1)*U.card.

Here L = 3(k+1), and c(U) is the intrinsic component count of the union of
nonzero support edges. These are bounds on the underlying finite rule set,
not on a list of possibly repeated step occurrences.

The following results derive the scan and both stopping cases:

- `WalkSelection.odd_boolean_closed_walk_stops` constructs the finite greedy
  scan and its causal invariant. Selected steps are independent and ordered
  by their actual walk indices. Boolean endpoints imply negative-gram
  provenance. If the scan did not stop, every step would be a signed selected
  rule, contradicting the proved even-length property of such closed walks.
- `FiniteWalkRules.selected_generatingAt` transfers independence and the
  chronological generating order to the actual finite set of integer rules.
  The unique selected occurrence of each rule follows from independence.
- `CatalogueAlgebra.new_relation_support` derives at least two nonzero
  coefficients in the relation case: actual catalogue vectors are nonzero
  signed-unit vectors, and the new rule is different from every selected rule
  and its negative.
- `RelationBlockSupport` and `FiniteRelationBlocks` derive a surviving gram
  in every block meeting these coefficients. Independence makes the restricted
  combination nonzero, and actual adjacency excludes contributions from other
  blocks. `SupportBlockCount` derives that at most 2t such blocks are selected;
  no injection or nonzero restriction is an input.
- `WitnessCases.relation_case_of_span` retains their whole union, preserving
  suppliers and independence. It proves 2 <= U.card <= 2tL and the stronger
  c(U) <= (2t-1)*U.card for every resulting size. The component saving uses
  `RelationBlockSavings.relation_block_hull_bound` and the checked savings lemma.
- `LargeBlockSelection.new_block_large_of_exists` proves that a cutoff failure
  after insertion must occur in the new rule's block: blocks excluding that
  rule are unchanged. `BlockAdjunction` identifies this block with the added
  rule and the old blocks meeting it. `WitnessCases.large_block_case` proves
  L < U.card <= 1+4tL^2 and c(U) <= (2t-1)*U.card + 1, using actual catalogue
  vertex bounds and the old-block size invariant.
- `FiniteGenerating` proves that retaining whole blocks preserves the
  actual generating order and rational independence in both cases.

`BoundedWitnessWalk.extract_counted` identifies the initial vector with
`SignedSupport.wordSpectrum x n L` and produces exactly the
`ManuscriptCounting.GeneratingSet` predicate used in the counting theorem,
while retaining independence, survival, and all witness bounds. The bridge
`GeneratingEnumeration.generatingAt_to_manuscript` derives a rank-sorted
enumeration, chooses the individual concrete catalogue presentations, and
assembles their balanced presentation and signed generating order. No supplied
enumeration or combined presentation is assumed.

`BoundedWitnessWalk.extract_word_walk` specializes this to a closed odd walk
of actual k-unique length-n words. It derives Boolean spectra from the checked
path results. The following connection supplies its graph and hash inputs.

## Complete deterministic conflict-graph connection

`VerifiedConflictGraphWitness.bounded_witness` proves the bounded-witness
conclusion starting from the manuscript's explicitly defined finite conflict
graph. Its assumptions are t >= 2, Q >= 2, a fixed additive hash H into the
unit circle, and a retained vertex x whose component is not two-colorable.
It produces the full `Witness` and the exact
`ManuscriptCounting.GeneratingSet` predicate at x, with the bounds above.

The graph, exceptional set, odd walk, and deterministic hash-survival test
are now defined and proved rather than supplied as additional interfaces:

- `AlignmentTrace.alignment_iff_exists_trace` connects the checked alignment
  proposition to computational matched/deletion/insertion columns, with exact
  source and target words and edit counts. Matched-column anchors count the
  actual preceding prefix; the right boundary anchor is n-d for a length-n
  source and d deletions.
- `FiniteConflictGraph` uses finite n-bit words, k-uniqueness, genuine
  edit-script confusability, and equal labels. Its exceptional set quantifies
  over every distinct equal-label n-bit partner, without requiring that partner
  to be unique or retained. A bad trace either has fewer than t edits of each kind
  or has t of each and fails separation. `edge_separated_trace` derives an
  actual trace with t deletions and t insertions, at least 4L matched columns
  strictly between edits, and at least 4L between each edit and either boundary.
- `OddGraphWalk.component_odd_walk` derives a finite odd closed walk based at
  the specified vertex from non-two-colorability of its own component.
  `WordGraphWitness` transfers this actual walk to the checked word spectra
  and bounded extraction; no supplied odd walk is needed at the graph level.
- `CircleHash` constructs the finite weighted additive hash and identifies
  the real-weight version with the manuscript's sum modulo one. Labels are
  floors of Q times the canonical representative in [0,1), with range
  0 through Q-1. Equal labels imply the strict quotient-norm bound
  `norm(H(p' - p)) < 1/Q`; that norm is the distance to the nearest integer.
  Surviving rules are actual catalogue members passing this test. The argument
  is deterministic and does not assume random or uniform weights.
- `VerifiedConflictGraphWitness.edge_catalogue` applies proved separated
  coverage to the derived trace. `edge_surviving` derives survival from equal labels.
  The final theorem combines these with the based odd walk and extraction.

The modular theorem `ConflictGraphWitness.bounded_witness_of_coverage`
retains its explicit coverage argument. The complete theorem supplies
`VerifiedConflictGraphWitness.separated_coverage` internally, so no earlier
unproved lemma remains among its hypotheses. The table above distinguishes
**eleven complete manuscript lemmas**, including `lem:coverage` and `lem:witness`,
from the separately verified obstruction proposition and final theorem.

## Verified random hash probabilities

`CircleUniform.realWeights` is the finite product of Lebesgue measure
restricted to [0,1); each coordinate and the product are probability measures.
Reduction modulo one is measure preserving into normalized circle Haar
measure. The hash is the same `CircleHash.realWeightedHash` used by the
deterministic conflict-graph connection, equal to the real weighted sum of
the integer coordinates modulo one.

`IntegerTorusMap.rational_right_inverse` obtains a rational right inverse
from rational row independence. Casting that actual matrix equation to the
reals gives real surjectivity; representatives of the target circles give
torus surjectivity. This does not assume that arbitrary rationally independent
real vectors remain independent over the reals, or that an integer minor is
unimodular. `TorusHaar` then derives preservation of normalized Haar measure
and actual `iIndepFun` independence of the output coordinates.

`RandomHash.independent_differences` combines these steps for the real-weight
probability space, with only rational independence as its mathematical input.
`CircleUniform.volume_smallArc` computes the measure of the strict test
`norm z < 1/Q` as 2/Q. At Q = 2 the excluded boundary point has zero measure;
the proof does not equate that open arc with the whole circle.
`real_rules_survival_probability` and its ordinary-real version give (2/Q)^R
for fixed independent catalogue members. `real_finset_survival_probability`
uses the underlying finite rule set and its cardinality without an ordering
or occurrence multiplicity. Empty families have probability one.
The nonzero-vector statement follows by proving independence of its singleton.
The vectors and catalogue are fixed before sampling, as in the paper.

## Verified nonseparated-family bound

`AnchorRecords` records edit columns in chronological order, retaining their
matched-column anchors, orientations, and inserted bits. An executable decoder
copies matched gaps and performs the recorded edits on the source; Lean proves
that it returns the actual trace target. Actual edit columns have distinct
record indices even when their anchors coincide. For a balanced trace with
d >= 1 edits of each kind, all anchors are at most n-d and hence belong to Fin n.
Zero-edit traces have equal source and target and cannot witness an exceptional partner.

`CloseAnchorCount.bad_card_le` counts r-tuples with an anchor near a boundary
or another anchor by omitting the constrained coordinate and reconstructing it
from at most 2B possibilities. Its bound is r(r+2)(2B)n^(r-1), including empty
parameter cases. `TaggedAnchorCount` adds the finite orientation/bit alphabet.
Using four tags per edit overcounts the paper's more economical records but
changes only the constant depending on t.

`ExceptionalPartnerCount.candidatePartners_covered` derives the finite cover
from actual bad alignment traces. It converts negated matched-column separation
into the counted anchor conditions, with right boundary n-t. The decoder image
counts each partner once even when several records produce it. The resulting
bound is `c_t L n^(2t-1)`, with
`c_t = (t + 8*(2*t)*(2*t+2))*4^(2*t)`.

`ExceptionalProbability` removes hash labels to define a fixed finite partner
set. Source uniqueness and n >= L make every distinct partner's spectrum
difference nonzero, without requiring partner uniqueness. Equal labels imply
the verified strict norm test, costing at most 2/Q per partner. A finite union
bound and the derived count yield `NonseparatedFamily.nonseparated_family_thin`
on the actual product of uniform real [0,1) weights. No record-cover, cardinality,
independence, or event-measurability premise is supplied by its callers.

## Verified obstruction proposition

`WitnessCounting.Candidate` describes fixed underlying rule sets satisfying
the actual generating-set predicate, rational independence, and witness size
and component bounds. It does not mention the sampled hash or survival.
`candidate_finite` proves finiteness, and `candidate_card_bound` partitions by
the intrinsic component count and applies the verified generating-set count.
Its bound is

    2^R * (2*t*R+1) * n^((2*t-1)*R) * (L*R)^(a_t*R).

`ObstructionProbability.obstructionEvent` is exactly the existence of a retained
vertex with the specified underlying word and a component that is not
two-colorable. `VerifiedConflictGraphWitness.bounded_witness` covers this event
by survival tests for the fixed candidates, for 2 <= R <= 1+4*t*L^2.
The verified random-hash law gives probability (2/Q)^R for each independent
set. Finite union bounds apply without requiring independence between candidates
or conditioning on the random graph or exceptional set.

`WitnessCost` uses the explicit `b_t = 4*a_t+2`, where
`a_t = 100*t*(32*t+17)`, to absorb the description factors into L^(b_t*R).
`ObstructionBound` then bounds each size contribution by 4^(-R) and proves
the finite geometric-tail bound 1/12. `PaperParameters` derives L >= 4*t+2
eventually and n <= 2^R whenever L < R for the actual logarithmic parameter.
`PaperProbability.obstructions_are_rare` therefore proves the entire
proposition with only fixed t >= 2, sufficiently large n, the stated lower
bound on Q, and source membership in the actual unique-word family.

## Verified final theorem and optimal redundancy

`PaperProbability.total_discard_le` combines the actual exceptional-event
bound 1/4 and obstruction-event bound 1/12. The required threshold depends
only on t; `PaperParameters.eventually_ready` proves the window-fit and growth
conditions for all sufficiently large n.

`FiniteDiscard.exists_half_retained` proves that some outcome retains at least
half the unique words. No independence across words or event-measurability
hypothesis is required: the proof takes measurable supersets with the same
measure and integrates the finite sum of their indicators. The surviving set
for these supersets lies inside the surviving set for the original events.

`GoodWordBridge.card_retainedWords` identifies those retained finite words
exactly with the good vertices of the actual conflict graph. `BipartiteSelection`
chooses a consistent two-coloring on each bipartite component and obtains an
independent set of at least half the good vertices. `CodeSelection` restricts
it to a largest actual hash-label class and projects the vertices to words.
The projection is injective; all counts are of distinct finite words.

The correction predicate is literal edit correction: distinct codewords have
no common output obtainable by scripts with at most t single insertions and
deletions in total from each word. `CodeSelection.Corrects.eq_of_common_output`
states the resulting unique-decoding property. Deletion-only scripts are
included, so no unformalized equivalence with deletion correction is needed.

With the integer Q = 8*n^(2*t-1)*L^b_t, `CodeExistence.exists_large_code` derives

    2^n <= 8*Q*C.card.

Its three factors of two come from the unique-word lower bound, the discard
step, and bipartite selection; Q accounts for the label class. This yields
positive code size and redundancy at most log_2(Q)+3. For n >= 4, the proved
logarithmic estimates absorb the constant term and give remainder coefficient
`6*b_t+6`. `CodeExistence.eventually_exists_code` discharges every finite
threshold and supplies actual nonempty codes; `CodeExistence.main` expresses
the bound with a constant depending only on t.

`OptimalRedundancy.optimalCodeSize` is the maximum cardinality among all
correcting subsets of the finite n-bit word space. Singletons prove positivity,
and `exists_optimal_code` proves attainment. The theorem
`exists_code_redundancy_eq_optimal` identifies this with the least attainable
redundancy. Finally, `OptimalRedundancy.main` gives the paper's bound on red*(n)
itself, not merely on a supplied feasible code.

## Verification boundary

The checked statements have no admitted proofs or added axioms. Their axiom
reports use only `propext`, `Classical.choice`, and `Quot.sound`, or subsets of
these. The build is reproduced from source by this repository's CI workflow.

The correspondence with the manuscript is a mathematical review of definitions
and hypotheses; Lean checks the formal statements themselves. The verified
scope includes the eleven mapped lemmas, the obstruction proposition, and the
final optimal-redundancy theorem. It does not certify every narrative statement,
historical comparison, or related-literature claim in the paper. The final
code selection is an existence proof, with no efficient encoder or decoder
asserted.
