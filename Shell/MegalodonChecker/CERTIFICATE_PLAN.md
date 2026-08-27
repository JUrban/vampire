# Megalodon Certificate Export Plan

Date: 2026-07-15; updated through 2026-08-26

Branch: `vampire/megalodon6`

Post-audit note, 2026-07-16: the July 16 Megalodon audit found that the broad
native preprocessing frontier was non-qualifying because Megalodon dynamically
installed certificate-derived `Known` propositions. Vampire-side work should
therefore prioritize a real primitive certificate builder and live core proofs,
not more benchmark-specific printer fragments or metadata that depends on
Megalodon reconstructing missing proof-search data.

Second post-audit note, 2026-07-16: the `vampire/megalodon5` closed-corpus
frontier found no real non-synthetic hammer certificate that enters the current
native proof-term core. The 23 passing core cases are `core.cnf.*` fixtures;
the 149 real closed hammer certificates first hit `formula_term_input` or
`formula_input`. Vampire-side work must therefore emit first-class
source/preprocessing records, in addition to clausal primitive expansions, so
Megalodon can prove real clausal inputs from original Megalodon source facts.

Third post-audit note, 2026-07-16: Megalodon now has a
`-vampirecertv1sourceaudit` gate and a parallel closed-corpus harness that
counts source obligations as checked THF formulas, unsupported formulas,
missing formulas, generated equalities, `set_reflexivity`, and `$true`
obligations. This does not reduce the Vampire-side obligation: future
source/preprocess records still need to provide enough proof data for
Megalodon to build proof terms, not merely enough labels for source-map
validation.

Fourth post-audit note, 2026-07-16: Megalodon also has an opt-in
`-vampirecertv1sourcecontext` / `-vampirecertv1sourcecontextstrict` audit that
loads the original `.mg` context before certificate checking and resolves
hash-backed `known`/`axiom` source entries through `Known hash`. This makes
global source facts mechanically distinguishable from local/unhashed theorem
hypotheses. Vampire should preserve source hashes and roles accurately because
those fields are now part of the fail-closed original-context boundary.

Fifth post-audit note, 2026-07-16: resolved global source facts are no longer
only audited. Megalodon's native proof-term elaborators can consume successful
`Known hash` source proofs and omit those inputs from the source-assumption
spine. This increases the importance of emitting exact source roles and hashes:
incorrect hashes will now prevent the corresponding source from being
discharged into the original context.

Sixth post-audit note, 2026-07-17: `MegalodonKernelSyntax` now exposes the
supported `kernel_v1` rule vocabulary and distinguishes structural migration
rules from primitive-contract rules. `emitKernelV1` fails before printing if a
caller tries to emit an unsupported rule name. This is not yet the full
primitive proof IR requested by the audit, but it closes the immediate
vocabulary loophole: new kernel metadata cannot be added silently by ad hoc
string emission.

## Decision

The previous `--proof megalodon` rich-export experiment is retained as a
prototype/debug path. The primary implementation target is now a normalized,
small certificate calculus documented in the Megalodon repo at:

```text
reports/vampire-megalodon-certificate-spec.md
```

Vampire should emit that calculus directly, rather than adding more
`megalodon_step_extra` fields for individual failing benchmarks.

The July 15 audit tightened this decision: the existing broad native
S-expression/replay implementation is useful as a regression oracle, but it
must not keep growing as the main reconstruction architecture. New qualifying
work should move detail into Vampire-emitted Prover9/Ivy-style primitive
records while Vampire still has substitutions, literal positions, selected
literals, ordering information, Skolem data, and AVATAR state. Megalodon should
check those explicit records and elaborate the restricted core to native proof
terms, not rediscover large transformations from before/after formulas.

The next qualifying Vampire milestone is an internal certificate IR, for
example `MegalodonKernelStep` for clausal primitives plus matching
source/preprocess transformation records, printed by one canonical printer.
Macro-specific code should build that IR first. Direct string assembly in
individual inference cases is now a legacy migration technique, not the target
architecture.

The branch currently has a rendering-level `MegalodonKernelStep` structure.
The remaining audit gap is to make macro handlers build a normalized list of
primitive steps first, then print that list. The rendering structure alone
does not count as the Prover9/Ivy-style IR until it becomes the required path
for macro lowering.

Post-audit note, 2026-07-20: Skolem branch-choice records now also emit a
`choice_witness_substitution` transport descriptor with the source body
instantiated by Vampire's own witness term.  This is not yet the complete
Skolem/epsilon proof object, but it moves the critical transport proposition
out of Megalodon-side proof inspection and into Vampire-emitted, typed
certificate data.

Post-audit correction, 2026-08-26: `MegalodonKernelSyntax` had incorrectly
retained the constructor for `PrimitiveStep`.  That made the printer module a
second builder and allowed inference code to bypass `MegalodonKernelBuilder`.
The constructor has now been removed from the syntax API, and all twenty live
clausal primitive construction sites route through
`MegalodonKernelBuilder::primitiveClauseStep`.  A 20-worker, 100-case THF run
with ten-second Vampire limits passed strict Megalodon certificate checking,
the primitive-record audit, and the `kernel_v1` metadata audit.

The immediate follow-up added rule-specific builder operations for `resolve`,
`factor`, and `equality_symmetry`.  All seventeen sites that construct typed
`PrimitiveStep` metadata for those rules now pass typed unit references and
clauses plus selected literal indices; the builder produces both the
structured fields and canonical Lisp rendering for those records.  A focused
65-step proof was byte-identical before and after this change, and a second
20-worker 100-case run passed all three audits.  Other legacy native-export
branches still assemble primitive-looking text directly in
`MegalodonChecker.cpp`; they remain migration debt and are not covered by this
claim.

The next follow-up added typed builders for `substitute`,
`equality_resolution`, and `equality_resolution_constraints`, migrated the
remaining nine metadata construction sites, and made `primitiveClauseStep` a
private implementation detail of `MegalodonKernelBuilder`. Neither
`MegalodonChecker` nor `MegalodonKernelSyntax` can invoke a generic primitive
constructor now. The same 65-step proof remained byte-identical, and the fresh
20-worker run at `/project/tmp/vampire_no_generic_builder_100_20260826` passed
100/100 strict checks plus both metadata audits.

This remains incomplete because older native-export branches still assemble
primitive-looking text directly in `MegalodonChecker.cpp` without constructing
typed `PrimitiveStep` metadata. Those branches must either call a rule-specific
builder or be removed from the qualifying export. New primitive rules must not
add another generic construction path.

Builder ownership is now externally checkable for indexed expansion chains.
The private builder marks every constructed `PrimitiveStep`; chain
serialization fails if any step lacks that mark and emits
`primitive_expansion_builder=typed_v1` plus a `typed_v1` marker for each
indexed step. Megalodon qualifying replay checks these fields in its extracted
kernel checker. A fresh 100-case, 20-worker run passed builder-strict checking,
and deleting one marker from a focused certificate is rejected.

This provenance is not yet a claim that the whole exporter is builder-owned.
It covers indexed expansion chains only. Direct legacy records need the same
enforceable ownership boundary before any proof can be classified as fully
Ivy-path.

## Initial Export Fragment

The initial qualifying schedule should avoid AVATAR and higher-order-heavy
proofs where possible. Compound Vampire inferences should be expanded before
export:

- hyper-resolution -> binary resolution,
- unit-resulting resolution -> binary resolution,
- demodulation -> paramodulation,
- duplicate deletion -> factoring,
- empty-clause detection -> contradiction.

The restricted native S-expression certificate milestone should contain only:

- `input`,
- `substitute`,
- `resolve`,
- `factor`,
- `equality_resolution`,
- `equality_factoring`,
- `equality_symmetry`,
- `paramodulate`,
- `subsumption_resolution`,
- `contradiction`.

Skolemization, formula preprocessing, predicate definitions, and AVATAR are
separate layers. They may be emitted for diagnostics and regression auditing,
but they do not extend the restricted clausal core. Real hammer proofs cannot
count until Vampire emits enough explicit data for Megalodon to prove
`formula_input` and `formula_term_input` from the original source context and
from certified Smolka-style transformations.

## Export Requirements

Every emitted step must contain enough information for a target importer to
check the constructor without guessing:

- stable step id,
- rule constructor,
- parent ids,
- normalized conclusion clause,
- selected pivot/equality/position where relevant,
- explicit substitution where relevant,
- source-map reference for inputs,
- sorts for all variables and symbols.

No constructor should depend on pretty-printed de-Bruijn names, hidden Vampire
state, or library-specific Megalodon names.

For `skolem_branch` records, each choice additionally carries an ordered typed
`context_variable` vector. Vampire derives it from the helper edge's leading
binders that remain preserved parent variables. Variables quantified inside
the existential body are not part of this vector. A checker can therefore
close the emitted predicate, body, and witnessed body without rediscovering
scope from printed names or from all variables occurring in the formula.

## Current Export Checkpoint

The old JSON/rich-export path is a diagnostic prototype only. It is not printed
as part of the default `--proof megalodon` artifact and it must not be used for
counted proof reconstruction. Set `VAMPIRE_MEGALODON_LEGACY_JSON=1` only for
explicit legacy diagnostics.

The current branch emits a native S-expression block:

```text
megalodon_certificate_native_sexpr_start.
(certificate vampire-megalodon 1 ...)
megalodon_certificate_native_sexpr_end.
```

Literals use Megalodon's S-expression term syntax, for example:

```text
(TMH "X0")
(TMH "a")
(AP (TMH "f") (TMH "a"))
(pos (AP (TMH "p") (TMH "a")))
(neg (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (SET)) (TMH "a")) (TMH "b")))
```

Vampire HOL lambda terms and existential formula binders are emitted as
`(VLAMV "X" sort body)`. This is a certificate-level spelling for Vampire's
explicit `vLAM`/`dbN` encoding, not a Megalodon kernel lambda. The importer may
accept the older `LAMV` spelling for backward compatibility, but newly emitted
native certificates should use `VLAMV` so FOOL/ENNF/Skolem steps can be checked
without inventing a separate `Lam = vLAM` proof.

Every promoted rule constructor must be emitted directly by Vampire in this
native format and checked by the Megalodon native importer. For counted core
work, the target is a checked `Syntax.tm * Syntax.pf` result, not a generated
proof script. Python and JSON may still be used for corpus statistics or
experiments, but not for accepted proof reconstruction.

Current `kernel_v1` metadata must remain a compatibility/regression layer. If a
macro record is kept, it should carry a `primitive_expansion=prefix` contract
and an exact `primitive_expansion_requires=...` field naming the first-class
primitive record that Megalodon is expected to check. The standalone Megalodon
primitive audit is the guard for this: a kernel macro without its matching
primitive record is not progress toward the small-kernel path.

## Non-Goals

Do not extend the existing rich `printReplayExtra` protocol for the next
failing focused example. Any new output should be part of the versioned
certificate format and should have a corresponding negative test in the
Megalodon importer.

Do not add another broad `kernel_v1` or Megalodon-side textual replay case just
to increase pass counts. The next implementation milestone is:

1. source/preprocess certificate records for `formula_input` and
   `formula_term_input`;
2. proof-producing handling of set-generated equalities, conjecture negation,
   rectification, FOOL/boolean normalization, ENNF/CNF projection, and
   Skolemization where they occur in the real closed corpus;
3. a clausal primitive builder for the later refutation steps;
4. ten real live Vampire proofs whose source/preprocess layer and clausal
   primitive layer both check without certificate-derived `Known` propositions.

## Typed FOOL Leaf Builder, 2026-08-26

Direct FOOL leaves are now part of the builder-owned path.
`MegalodonKernelBuilder::foolAtomLiftStep` accepts typed source and target
formula records, the exact structural path, and the ordered typed lexical
context. It owns the canonical Lisp record and marks it `typed_v1`; inference
code no longer assembles fresh `fool_atom_lift` text directly.

The producer traverses the complete formula structure and emits only atomic
leaf differences. The previous depth, pair-count, and text-size cutoffs were
removed. Equality leaves are canonicalized with Vampire's own HOL
named-to-nameless conversion before comparison. If the canonical certificate
terms are equal, as for a special lambda versus the equivalent
`vLAM`/`db0` term, no identity primitive is emitted. Legacy rich diagnostic
metadata may still describe the pre-canonical pair, but qualifying correctness
is determined by the typed record set.

Megalodon independently computes and checks exact leaf coverage, including
the lexical context, and elaborates the formula proof through its extracted
small-kernel module. A fresh 100-case THF run with 20 workers and ten-second
Vampire limits emitted 177 `fool_formula` macros and 524 builder-owned leaves;
all 100 certificates passed builder-strict structural checking. Removing one
builder marker or one leaf is rejected. Full proof-term replay completes for
98 cases; one later clausal injection failure and one long Megalodon timeout
remain outside this FOOL family.

This does not make the entire exporter Ivy-style. Other direct preprocessing
families and top-level compatibility dispatch remain migration work. The next
builder work should follow the same rule: structured Vampire data first,
canonical serialization once, exact deterministic target checking, and no
benchmark-name or library-name recovery.

## Superposition Substitution Precedence, 2026-08-26

The live `hammer.1009.43` proof exposed a producer-side loss of exact inference
data at superposition step `u141`. Vampire's replayer had recorded the equality
parent substitution

```text
X0 -> X2, X1 -> sK0, X2 -> X0, X3 -> X1
```

but the legacy superposition fallback copied that substitution and then
overwrote it with a later matcher containing the identity binding `X0 -> X0`.
The emitted `substitute` primitive consequently lost `X0 -> X2`, and the
extracted Megalodon clause kernel correctly rejected the resulting side
literals.

The correction is deliberately narrow. The recorded replay substitution is
authoritative; matcher bindings are added only for variables that the replay
substitution does not bind. No target-side guessing or checker relaxation was
added. A broader attempt to compose substitutions throughout the fallback was
rejected after the 20-worker corpus gate immediately found 15 missing
superposition expansions.

The live regression
`run_native_live_superposition_permutation_smoke.sh` checks the exact four
bindings and all 136 strict typed-builder steps. The final source-linked THF
batch at
`/project/tmp/superposition_authoritative_final_100_20260826` passes 100/100
with 20 workers, ten-second Vampire limits, source checks, builder-strict
checking, 533 `paramodulate` records, 430 `substitute` records, and both
certificate audits.

This is not a promotion of `certificateSuperpositionStepSexpr` to the target
architecture. That large fallback remains frozen compatibility code. The next
Vampire-side superposition work must construct exact typed primitive records
from recorded inference data and then delete the corresponding search branch;
it must not add more candidate reconstruction to the fallback.

## Typed Superposition Primitive Chains, 2026-08-26

Superposition output now has enforceable builder ownership. The rule-specific
`MegalodonKernelBuilder::paramodulateStep` owns equality/target parent
references, selected literal indices, rewrite position, source and replacement
terms, result clause, and canonical Lisp rendering. `PrimitiveChain` preserves
the exact successful ordered sequence and refuses to expose a chain containing
a non-builder primitive. Both current superposition emitters route their
`substitute`, `factor`, `equality_symmetry`, and `paramodulate` records through
rule-specific builders.

The already generated native chain is cached by Vampire unit number and added
to that unit's `kernel_v1` record; metadata generation does not rerun
superposition reconstruction. Fresh metadata therefore carries
`primitive_expansion_builder=typed_v1` and per-step typed ownership, while the
selected required primitive remains `paramodulate` even when substitutions
precede it.

The final 20-worker corpus at
`/project/tmp/superposition_typed_builder_refactored_final_100_20260826`
passes 100/100 source-linked THF certificates under ten-second Vampire limits,
builder-strict Megalodon checking, and both audits. It contains 351
superposition macros; all 351 have typed builder chains, comprising 352
`paramodulate` and 394 `substitute` primitives. The live `u141` test now also
requires typed paramodulation ownership.

This completed output ownership but, at that checkpoint, did not complete
extraction ownership. The following checkpoint replaces that state; the
paragraph above is retained as the historical acceptance boundary that drove
the next change.

## Exact Recorded Superposition Lowering, 2026-08-26

Fresh Lisp certificates no longer reconstruct superposition by searching the
conclusion. `Superposition::performSuperposition` now gives the inference
recorder the exact rewritten parent, equality parent, selected literals,
selected target term, oriented equality sides, and simultaneous-rewrite mode.
The recorder validates and stores the two literal indices and preserves the
replayer's parent substitutions and conclusion-variable renaming.

`certificateSuperpositionStepsSexpr` consumes only that record. It emits the
typed parent substitutions, rewrites the recorded occurrence (and, for
Vampire's simultaneous mode, every matching occurrence in deterministic
left-to-right order), factors only duplicate side literals, and uses a final
identity substitution only to assign the exact conclusion order and id. It
does not try alternative parents, equality orientations, target literals,
variable permutations, or candidate normalizations. The former 1,024-line
`certificateSuperpositionStepSexpr` candidate-search implementation and its
fallback call were deleted.

The duplicate clause renderer in the old lowering initially encoded Vampire
equality literals as raw `=` applications, unlike the canonical certificate
renderer. Reusing `safeApplySubstitution` and `certificateLiteralSexpr`
removed that second representation and raised exact coverage from 24/351 to
351/351 superposition macros. Fresh metadata records both
`selection_source=recorder_v1` and
`primitive_lowering_source=recorder_v1`; no compatibility source can satisfy
the exact-lowering gate.

The final 20-worker source-linked THF run is:

```text
/project/tmp/superposition_exact_invariant_final_100_v3_20260826
PASS 100/100
kernel_v1 records 3529
superposition macros 351
paramodulate records 533
substitute records 431
```

Vampire was capped at ten seconds per problem. Megalodon used source checks,
builder-strict checking, and the primitive and metadata audits with
`REQUIRE_SUPERPOSITION_EXACT_LOWERING=1`. A mutation changing one lowering
marker to `legacy_search` is rejected. Focused tests cover the cyclic four-way
renaming at `u141` and the two-occurrence simultaneous rewrite at `u792`.

This closes the superposition producer-extraction gap for the measured corpus;
it does not close the whole project. Other macro families and preprocessing
operations must undergo the same producer-record/builder/extracted-checker
migration, and detached source-linked structural results remain distinct from
original-development E1 proofs.

## Exact Producer-Recorded Rectification, 2026-08-26

Fresh rectification records now follow the same producer-to-small-kernel path.
`Rectify` records the exact source and result formulas, top-level free-variable
map, and every recursive quantified transformation under the actual inference
unit id. Each recursive witness also carries the active outer-variable map,
filtered by Vampire's `FormulaVarIterator` to variables free relative to that
source subformula. This is necessary because an outer binder is represented as
a free name when a nested witness is serialized independently.

`MegalodonKernelBuilder::rectifyFormulaStep` owns the direct Lisp and typed
metadata. Megalodon's extracted checker validates source equality, variable-only
and injective maps, source/result occurrence, recursive ambient maps, alpha
structure, vacuous quantifier removal, and equality symmetry. Its extracted
elaborator transports the proof structurally. The old bounded formula traversal,
guessed variable maps, scoped-renaming candidate checks, and rectification
orientation fallback were deleted from this path.

The final 20-worker run is:

```text
/project/tmp/rectify_ambient_exact_final_100_20260826
PASS 100/100
rectify_formula records 332
superposition macros 351
paramodulate records 533
```

Vampire was capped at ten seconds. The run required source checks,
builder-strict replay, both primitive audits,
`REQUIRE_SUPERPOSITION_EXACT_LOWERING=1`, and
`REQUIRE_RECTIFY_EXACT_LOWERING=1`. Focused mutations of both the top-level
free-variable map and a recursive ambient-variable map are rejected. This is
E2/E3 producer and replay evidence; it is not yet 100 original-development E1
proofs and does not certify the remaining compatibility macro families.

## Exact Producer-Recorded CNF Projection, 2026-08-26

CNF clause extraction now records its complete deterministic projection while
`CNF::clausify` still owns the source formula. The recursive record contains
only producer facts: universal variables and their emitted witnesses,
conjunction branch choices, both sides of each disjunction product, and exact
source-literal pointers. It does not store a creation-time result index because
Vampire may reorder clause literals later. The serializer assigns final indices
once by source-literal pointer identity and requires complete one-to-one result
coverage.

`MegalodonKernelBuilder::cnfFormulaClauseStep` owns the canonical Lisp and
indexed metadata. The direct primitive includes source formula, clause
index/count, projection tree, and result clause. Fresh metadata uses
`selection_source=cnf_v1`, `primitive_lowering_source=cnf_v1`, and typed-builder
provenance. No formula-to-CNF candidate list is computed by the exporter.

Megalodon's extracted checker follows the emitted tree and validates every
source shape, witness, source literal, final result index, and coverage. Its
extracted elaborator applies exactly those universal eliminations, Church
conjunction projections, Church disjunction eliminations, and literal
injections. The former monolithic result-directed universal/branch candidate
search was deleted.

The final source-linked run is:

```text
/project/tmp/cnf_exact_invariant_final_100_20260826
PASS 100/100
cnf_clause records 482
cnf_formula_clause primitives 299
cnf_literal primitives 183
```

It used 20 workers, ten-second Vampire limits, source-map and builder-strict
checks, both primitive audits, and exact gates for superposition,
rectification, and CNF. A focused source-linked 53-step proof term passes, and
mutated result indices and forall witnesses are rejected. This closes the CNF
producer/replay search gap for the measured corpus; it is not a claim of 100
original-development E1 proof terms.

## Corrected Next Gate: Compact Producer-Recorded ENNF

An attempted live-DAG experiment on `and7I` demonstrated why ENNF must be the
next producer-owned transformation. Its certificate contains an ENNF direct
record of roughly 73 KB and a Skolem record of roughly 349 KB because complete
intermediate formulas are repeated in transformation-pair metadata. Replaying
those formulas claim by claim in Megalodon became slower with formula depth;
moving that loop into `megalodon.ml` would repeat the architecture rejected by
the July 20 audit. That experiment was removed rather than committed.

The next qualifying ENNF object must therefore be built while `NNF::ennf`
performs the transformation. It will contain the source and result formulas
once, plus a compact constructor tree recording polarity and complete recursive
coverage. The intended constructors are formula-level operations such as
literal, junction, implication, negation, quantifier, Boolean term, and
constant. Children encode traversal; they do not repeat source/result
subformulas or rely on textual paths reconstructed after the inference.

The ownership boundary is mandatory:

```text
NNF::ennf transformation event
  -> typed ENNF trace
  -> MegalodonKernelBuilder::ennfFormulaStep
  -> canonical Lisp
  -> Vampire_kernel_check trace validation
  -> Vampire_kernel_elab proof constructor
```

`MegalodonChecker::certificateEnnfFormulaStepSexpr` must stop comparing the
finished formulas to synthesize bounded pairs. The current depth-16 and
pair-count-32 collector is compatibility code and must be deleted when the
typed trace lands. No replacement ENNF semantics may be added to
`megalodon.ml` or `vampire_cert_v1.ml`.

Acceptance requires a mutation test for every trace constructor and for
missing children, an exact-lowering metadata gate, the existing 100-case
20-worker run with Vampire capped at ten seconds, and original-source Qed
checks through the qualifying path. Certificate size and replay time must be
reported alongside pass counts so a structurally correct but expansion-heavy
object is not mistaken for the Ivy-style result.

Skolemization follows the same rule. Existing typed branch contexts and
choice substitutions are inputs to a scoped producer object. The consumer
must discharge each witness at a DAG block boundary, and the block conclusion
must be checked not to contain the local witness. Expanding a complete proof
tree to remove Skolem symbols is not an approved qualifying implementation.

## Compact Producer-Recorded ENNF Implemented, 2026-08-26

The producer half of the ENNF gate above is now implemented. `NNF::ennf`
records the actual recursive call tree while it transforms Vampire formulas.
Each node records the source connective, input polarity, and ordered children.
The recorder owns the trace until inference replay associates it with the
corresponding ENNF unit; no printed formula is reparsed to recover the tree.

`MegalodonKernelBuilder::ennfFormulaStep` is the only constructor for fresh
ENNF output. It serializes the source and result formulas once together with
the compact trace and `typed_v1` ownership. The direct collector requires the
producer record and checks that its source and result are the formulas being
serialized. The former bounded source/target-pair reconstruction and its
duplicated ENNF metadata were deleted. Other legacy normal-form records still
use pair metadata and remain migration work.

On the consumer side, `vampire_kernel_syntax.ml` owns the trace type and
`vampire_kernel_check.ml` validates source-connective shape, child arity, and
the polarity recurrence. The compatibility parser only decodes and dispatches
the object. The existing deterministic ENNF result check remains as a second
semantic check. Root-polarity and root-connective mutations are rejected by
the extracted checker.

The focused artifact is:

```text
/project/tmp/ennf-trace-focus-20260826/and7-compact.cert
```

It contains 58 logical trace nodes. Builder-strict checking takes about 0.20
seconds and 59 MB in the measured run. Removing the duplicated ENNF pair
metadata reduced this certificate from 1,226,653 to 1,194,987 bytes. The
maintained fixture and its two mutations are under
`/project/tmp/ennf-trace-fixture-20260826`.

The broad gate used the existing one-time solvability list
`known_solvable_strict_100.list`; Vampire was capped at ten seconds and run
with 20 workers. The generated corpus reported 100/100 builder-strict passes
and 248 `ennf_formula` primitives. Two unit-resulting-resolution substitutions
initially lacked exact instantiation metadata. Vampire now records the full
certificate premise, including AVATAR split literals, for those substitutions.
Only those two known-solvable proofs were regenerated in parallel. The merged
100-certificate audits are:

```text
/project/tmp/ennf-trace-known100-audited-20260826-2
/project/tmp/ennf-trace-known100-metadata-audit-20260826
/project/tmp/ennf-trace-known100-primitive-audit-20260826
```

They pass with 8,916 `kernel_v1` records, 248 ENNF primitives, and complete
metadata for every nonidentity substitution. This remains detached E2/E3
evidence. It neither extends the original-development Qed frontier nor solves
certificate-local Skolem and AVATAR discharge.

The ENNF migration is not yet architecturally complete. ENNF proof-term
construction still lives in compatibility code in `vampire_cert_v1.ml`, and
mutation coverage does not yet exercise every trace constructor. Before ENNF
can be counted on an Ivy-only E1 route, the proof constructor must move to
`vampire_kernel_elab.ml`, the semantic result computation must be exposed
through the extracted boundary, typed traces must be mandatory in qualifying
mode, and constructor-complete mutation tests must pass. The next producer
object after that is scoped Skolemization; no consumer-side proof-tree
expansion is approved as a substitute.

## ENNF Consumer Extraction Complete, 2026-08-26

The four remaining ENNF conditions in the preceding paragraph are now
satisfied. Megalodon's extracted checker owns deterministic ENNF result and
trace validation, and its extracted elaborator owns the proof-term constructor.
The compatibility importer delegates through a thin callback adapter. Qualifying
typed-builder mode requires exact source plus trace and rejects legacy pair
records. The extracted unit suite has positive and mutation coverage for all
twelve trace constructors.

The final gate regenerated all 100 certificates from the source-linked THF
corpus using 20 Vampire workers and a ten-second limit. All 100 passed
builder-strict checking, all 100 then passed Megalodon preprocessing proof-term
checking with 20 workers, and all primitive/metadata audits passed. The corpus
contains 169 ENNF records, all compact traces, with no legacy ENNF pair lists
and no Vampire-derived source assumptions:

```text
/project/tmp/ennf-trace-source-linked-100-20260826
/project/tmp/ennf-trace-source-linked-100-pfcheck-final2-20260826
```

This closes the ENNF E2/E3 gate, not the original-development E1 gate. Work now
moves to the scoped Skolem producer object. Its acceptance condition remains:
the producer records the existential source, dependency context, witness,
choice justification, and continuation boundary; the consumer checks that the
exported block conclusion contains no local witness. AVATAR scope discharge
follows. No additional ENNF semantics or Skolem search may be added to the
Megalodon compatibility monoliths.

### Scoped Skolem checkpoint, 2026-08-26

`Skolem::skolemise` now records a compact typed branch object during the real
transformation. It contains exact branch source/target formulas, a binary
kernel-term path, ambient universal variables, dependency context, and typed
witnesses. `MegalodonKernelBuilder::skolemFormulaStep` is the sole fresh Lisp
constructor. The `typed_v2` version denotes the binary path encoding; no
consumer-side subformula search is permitted.

The extracted OCaml checker and elaborator replay this object directly. A
fresh 100-case source-linked THF gate passes builder-strict checking with 77
Skolem steps, including nested, dependent, and multiple-witness cases. This is
not yet E1 completion: final refutation cleanup still depends on Megalodon's
legacy CPS/proof-object route. The next and only approved Skolem milestone is a
compact block-discharge constructor in `vampire_kernel_elab.ml`, followed by
removal of that legacy route from qualifying mode.

### Checked-claim Skolem discharge, 2026-08-26

That block-discharge milestone is now implemented for qualifying mode.
Producer-justified witness definitions are applied as each local proof claim is
registered; claims remain a checked DAG, and the exported block is rejected if
it contains an introduced witness. Qualifying replay requires `typed_v2`, does
not construct the rich legacy proof object, does not enqueue CPS cleanup, and
removes witness aliases from the returned delta and symbol tables.

The original Megalodon source prefix now passes ten ordinary-Qed commands, each
with a scoped Skolem record and a global-signature invariant. The legacy CPS
path remains in the nonqualifying compatibility implementation and should be
deleted only after its remaining tests are migrated. The next qualifying scope
object is AVATAR split/SAT discharge, whose exported claim must contain no
split name.

### Producer-owned AVATAR scope, 2026-08-26

Fresh AVATAR certificate records now pass through typed builder functions for
components, definitions, dependencies, splits, and refutations. Every native
record is emitted together with a builder-owned `avatar_scope_v1` record that
adds a mandatory `avatar_v1` selection/lowering owner and a
`certificate_local_block_v1` scope, including synthetic SAT-origin steps.
Qualifying Megalodon replay accepts only that builder record and rejects
missing or mutated fields; rich `kernel_v1` diagnostics cannot satisfy the
gate.

The consumer localizes each checked claim with the exact emitted component
proposition and rejects a block whose proposition or proof exports a split or
Skolem alias. The original-source ten-command gate passes with AVATAR enabled;
nine certificates contain real AVATAR refutations. A fresh two-phase
100-problem producer run emitted 100/100 certificates in parallel, including
27 scoped AVATAR refutations. Strict proof-term replay passes 22 of those 27 at
the ten-second checker threshold; three stop earlier at existing preprocessing
type errors and two exceed that threshold. These are retained as frontier
cases, not relabelled as AVATAR successes.

The next producer task is not another consumer-side AVATAR heuristic. Record
the exact SAT/RUP resolution chain that justifies every dependency and final
refutation, serialize it through the typed builder, and move deterministic
chain validation/elaboration into the extracted checker and elaborator
modules. Qualifying replay must fail when the chain is absent or malformed and
must never enumerate candidate pivots, parent orders, or substitutions.

### Exact AVATAR SAT kernel, 2026-08-26

That producer task is complete for the measured AVATAR refutations. Vampire's
typed builder now expands each SAT-layer RUP antecedent list into explicit
`sat_resolve`, `sat_factor`, and `sat_permute` records. Pivot exploration occurs
only during this producer-side proof transformation; the successful parent and
literal indices are serialized. Synthetic operation ids lie above all source
SAT ids, while the last operation keeps the source RUP id. Fresh native output
contains no `sat_rup` macro.

The native scope record marks `sat_proof_format=resolution_v1` and
`sat_lowering_source=rup_resolution_v1`. Typed-builder strict replay requires
both. The extracted OCaml checker validates the exact chain without search,
and the extracted elaborator constructs the full chain proof from source input
proofs and the emitted indices. The compatibility importer is a callback
adapter; exact failures cannot enter its legacy RUP or two-parent fallback.

The original ten-command gate passes with nine exact AVATAR refutations. A
fresh 20-worker producer batch emitted 100/100 source-linked certificates in
one phase, including 27 exact AVATAR certificates. Their 96 resolutions, 13
factors, and 2 permutations all pass strict structural replay; no native RUP
record remains. Cached native proof-term replay is 95 pass, three existing
preprocessing type failures, and two ten-second timeouts. Mutation tests reject
wrong parents, pivots, resolvents, factor/permutation records, residual RUP,
and ownership metadata.

Evidence:

```text
/project/tmp/live-hammer-prefix10-avatar-sat-resolution-v1b-20260826
/project/tmp/avatar-sat-resolution-v1-source-linked-100-produce-20260826
/project/tmp/avatar-sat-resolution-v1-source-linked-100-structural-20260826
/project/tmp/avatar-sat-resolution-v1-source-linked-100-check-extracted-20260826
/project/tmp/avatar-sat-resolution-v1-mutations-extracted-10693-20260826
```

Do not add another Megalodon SAT heuristic. Next, reduce the three saved
preprocessing elaboration failures from their typed producer records and
profile the two timeout cases. Migrate legacy fixtures to exact SAT records,
then delete the nonqualifying RUP-search compatibility branch. The separate
declarative script emitter still has broad formula/Skolem rendering failures;
repair that renderer independently if checked human-readable scripts become a
required output surface.

### Closed native proof-term frontier, 2026-08-26

The saved three failures and two timeout cases are now closed in the qualifying
native checker. No additional producer metadata was needed: the existing
`typed_v2` scoped Skolem records supplied the exact branch path, ambient scope,
typed dependencies, witnesses, and target.

The defect was a consumer scope violation. Megalodon's qualifying witness
expander ignored the ambient depth supplied by the extracted scoped elaborator,
so an earlier epsilon definition was inserted below a later existential or
universal binder without the required de Bruijn shift. The expander now honors
that depth. In addition, every emitted scoped branch is checked and shared as
an intermediate proof-DAG claim before replay continues with the next emitted
branch. This is deterministic expansion of producer records, not consumer path
or substitution search.

The cached five-case frontier passes at 8--86 seconds per case, and a ten-worker
consumer-only run over the already produced source-linked TH0 batch reports:

```text
/project/tmp/avatar-sat-resolution-v1-source-linked-100-proof-final-20260826
PASS 100
```

That batch contains 77 scoped Skolem records and 27 exact AVATAR refutations.
The scoped trace mutation suite and extracted unit suite pass at:

```text
/project/tmp/scoped-skolem-mutation-final-20260826
/project/tmp/kernel-elab-unit-scoped-fix-20260826
```

The largest epsilon-localized proof remains expensive, at roughly 1 GB and
79--86 seconds. A shared normalization-cache experiment did not help and was
removed. This is now a performance frontier, not an admitted inference or a
proof failure. Keep the producer-owned certificate and native checked-claim
path authoritative; do not move this work back into Python or infer missing
Skolem data in OCaml. The separate simple declarative emitter remains a
diagnostic output surface and still has independent rendering failures.

### Live Qed preserves the producer claim graph, 2026-08-26

The cached 100-certificate gate above checks the native proof terms but leaves
unresolved source premises as assumptions. The stronger original-development
bridge must resolve those premises to live Megalodon lemmas and the current
conjecture and then pass ordinary `Qed`. That bridge now preserves the same
producer-owned checked-claim graph instead of beta-normalizing it into a proof
tree.

Megalodon's extracted elaborator performs term-only beta reduction for open
choice/extensionality macros and leaves proof-lambda applications as claim
lets. Bare, partially applied native `dneg` and proposition-extensionality
primitives are translated by extracted proof constructors parameterized by
the live library's `xm`, `FalseE`, `prop_ext`, and `iffI`. Final classical
closure is constructed deterministically and checked once by normal
Megalodon `Qed`; no certificate-local definition is installed globally.

The current live artifact passes twelve original commands through `and6I`:

```text
/project/tmp/live-prefix12-final-branch-20260826
LIVE_HAMMER_PREFIX_AVATAR_REFUTATIONS 11
LIVE_HAMMER_PREFIX_QUALIFYING_PASS 12
```

Separately, the same Megalodon binary passed all 100 fixed producer
certificates with ten parallel consumer workers and no new Vampire runs:

```text
/project/tmp/checked-claim-100-final-branch-20260826
    100 PASS
```

That is a broad certificate-consumer regression, not live E1 evidence, because
its unresolved source premises remain assumptions.

The harness requires a DAG-preservation marker for every reconstructed
command, in addition to the ten-second Vampire bound, exact source checking,
no-fallback guards, signature isolation, and final `Qed`. At this checkpoint
the E1 frontier was 12 theorems; it was not a reclassification of the cached
100 certificates. Future certificate evolution must keep atomic producer
records shareable; the consumer may type-check and elaborate them but must not
flatten the graph or rediscover a proof tree.

### Single authoritative live check, 2026-08-27

The live consumer previously checked every prepared DAG claim during replay
and checked the complete nested claim term again at ordinary `Qed`. This was a
duplicate traversal, not missing producer detail: the retained `and7I`
certificate spent about 34 seconds in each traversal. Qualifying compact-DAG
registration now defers the individual proposition checks to the final
ordinary `Qed`; standalone preprocessing retains immediate checks. Claim
closing, reference resolution, and certificate-`Known` rejection still occur
before registration, and every claim proof remains in the final term.

A mutation unit registers an invalid deferred claim and requires final kernel
rejection. The unchanged producer certificates then pass 13 source-linked
commands in 72.9 seconds instead of 111.3 seconds, with lower peak memory. One
new ten-second-bounded producer run extends the original-development gate to
14 commands through `not_or_and_demorgan`:

```text
/project/tmp/live-prefix13-deferred-final-20260827
/project/tmp/live-prefix14-demorgan-20260827
/project/tmp/checked-claim-100-deferred-regression-20260827 (100 PASS, 10 workers)
```

This does not add or weaken a certificate rule, and it does not move any
Smolka transformation back into the OCaml compatibility layer. The producer
calculus, exact ENNF/Skolem/AVATAR records, and small-kernel ownership remain
unchanged. The remaining `and7I` cost is the real final kernel traversal and
must remain an acceptance check.
