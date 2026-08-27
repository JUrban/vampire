# Vampire to Megalodon Certificate Plan

Date: 2026-08-27

Branch: `vampire/megalodon6`

This is the authoritative Vampire-side design. It replaces the cumulative
July/August implementation log previously stored in this file. The external
review in Megalodon `reports/audit-REPORT-2026-07-20.md` is binding: the
qualifying path is a Prover9/Ivy-style producer expansion, not a large
Megalodon-side reconstructor.

## Objective

Vampire must emit enough exact typed information for Megalodon to check and
elaborate a THF refutation deterministically into a native proof term linked to
the original Megalodon theorem.

```text
Vampire inference and preprocessing state
  -> rule-specific MegalodonKernelBuilder operation
  -> small typed primitive/transformation records
  -> one canonical Lisp certificate printer
  -> deterministic OCaml checker and proof-term elaborator
```

Python and JSON are not part of the accepted proof path. They may be used for
statistics only. The qualifying certificate is the versioned native Lisp
S-expression emitted by `--proof megalodon`.

## Producer Ownership

Vampire owns all data that would otherwise require guessing:

- exact typed parents and result;
- substitutions and their variable sorts;
- selected literals and equality sides;
- rewrite orientation and term position;
- proof-order primitive expansion;
- formula source/result and recursive transformation trace;
- free variables versus ambient typing variables;
- Skolem witness symbols, replaced binders, dependencies, and witness terms;
- refutation-wide Skolem scope and discharge order;
- AVATAR split scope and SAT proof evidence;
- original TPTP source names and roles.

Megalodon may normalize representations and verify these records. It must not
recover omitted proof-search state by enumerating candidates.

## Builder Boundary

`MegalodonKernelBuilder` is the only constructor for qualifying typed records.
`MegalodonKernelSyntax` owns immutable data/rendering types and may not expose a
generic public primitive constructor. Inference handlers call rule-specific
builder operations.

Every qualifying record carries builder provenance. Serialization fails when a
record expected to be builder-owned lacks that provenance. A new inference
family is not migrated merely because its old metadata resembles a primitive
record.

Migration of a rule is complete only when:

1. the rule-specific builder accepts typed Vampire data;
2. the builder emits a normalized primitive/transformation object;
3. Megalodon's extracted checker has a mutation test for the object;
4. Megalodon's extracted elaborator constructs `Syntax.pf` without search;
5. the legacy direct emitter or consumer reconstruction route is deleted;
6. cached broad replay has no result-vector regression.

Do not add another `megalodon_step_extra` field to fix one benchmark.

## Certificate Layers

### Source inputs

Input records retain the exact TPTP source name and role. Megalodon combines
them with the source map produced during THF export. Name demangling and live
lemma/definition lookup are consumer source-context operations, but Vampire
must preserve names and formulas exactly.

### Formula transformations

Formula preprocessing is not hidden behind a trusted clause input. It uses
typed records such as:

- rectification with explicit variable maps;
- FOOL atom and boolean transformations;
- ENNF with the exact recursive connective/polarity trace;
- CNF with the exact projection from formula to result clause;
- scoped Skolemization with explicit branch paths and witnesses.

These are a separate Smolka-style proof layer. They establish that the clausal
refutation follows from the original formulas.

### Clausal primitives

Compound proof-search inferences lower to a restricted calculus. The current
vocabulary includes:

- `substitute`;
- `resolve`;
- `factor`;
- `equality_resolution`;
- `equality_factoring`;
- `equality_symmetry`;
- `paramodulate`;
- `contradiction` and checked copy/normalization boundaries.

Hyper-resolution, unit-resulting resolution, superposition, demodulation,
subsumption resolution, and similar macros must lower into these explicit
records where possible. Macro labels may remain diagnostic metadata but cannot
replace the primitive chain.

### AVATAR

AVATAR remains a separate layer. A qualifying refutation needs explicit split
definitions, scope, clause dependencies, and SAT evidence such as resolution
or RUP. Megalodon must not trust an `avatar_refutation` label.

## Scoped Skolem Contract

Each typed `skolem_formula` record gives the local formula transformation:

- exact source and result;
- branch index and formula path;
- ambient and dependency contexts;
- witness symbol, replaced variable, type, and applied witness term;
- normalization contract;
- typed builder provenance.

The complete certificate additionally contains exactly one producer-owned
scope block when any Skolem steps occur:

```lisp
(skolem_scope_block "smolka_refutation_v1"
  (final "u372")
  (entries
    (entry (index 0) (step "u216") (symbols "sK0"))
    (entry (index 1) (step "u218") (symbols "sK1")))
  (discharge_order "u218" "u216"))
```

The builder derives entries by walking the typed primitive proof order and
recording `certificateLocalSymbols` on each Skolem primitive. The final step is
the actual empty-clause root. Discharge order is exact reverse proof order.

The consumer validates that every entry names a typed Skolem step and exactly
its introduced symbols. It then uses this block as the replay scope: every
epsilon replacement is registered against its declared `(step, symbol)`, and
all declarations must be discharged before returning a proof. The block is
therefore semantic certificate data, not an audit annotation.

Future scope versions must be explicit. Do not silently change the meaning of
`smolka_refutation_v1`.

## Canonical Rendering

The native block has one versioned root:

```lisp
(certificate vampire-megalodon 1 ...)
```

Terms, types, literals, clauses, substitutions, positions, traces, and scope
records are rendered by canonical syntax helpers. Inference code must not
assemble alternate primitive-looking Lisp strings.

The rich historical output may remain behind an explicit diagnostic switch
until migration is complete. It is not counted proof evidence and must not be
consulted by qualifying Megalodon replay.

## Current Implementation Status

Implemented and retained:

- private rule-specific primitive builder operations;
- typed builder provenance and cross-repository vocabulary checks;
- exact substitutions, selected literals, equality positions, and free-variable
  records for migrated clausal families;
- exact recursive ENNF producer trace;
- exact CNF projection records;
- typed scoped Skolem branch traces;
- proof-order `skolem_scope_block` emission;
- explicit AVATAR scope and SAT/RUP records for the current migrated path;
- ten-second Vampire and cached parallel corpus workflow.

Still incomplete:

- some direct legacy record construction remains in
  `MegalodonChecker.cpp`;
- not every Vampire inference family has a rule-specific primitive lowering;
- the current first-order/THF preprocessing certificate is larger than the
  desired minimal endpoint;
- broad detached replay does not itself close 100 original Megalodon theorems.

The current files are approximately:

```text
MegalodonChecker.cpp       25,344 lines
MegalodonKernelBuilder.cpp  1,225 lines
MegalodonKernelBuilder.hpp    177 lines
MegalodonKernelSyntax.hpp     848 lines
```

These numbers are architectural warnings, not progress metrics. New work should
move construction out of `MegalodonChecker.cpp` and delete the old path.

## Test Discipline

1. Export all THF problems once.
2. Run Vampire once per corpus with `-t 10` and 10-20 workers.
3. Store all generated outputs below `/project/tmp`.
4. Iterate on Megalodon with cached certificates.
5. Regenerate only affected certificates when producer/schema code changes.
6. Run focused mutation tests before broad replay.
7. Keep structural, detached proof-term, source-target, and original-source
   `Qed` results in separate evidence categories.

The current producer scope batch is:

```text
/project/tmp/skolem-scope-block-source-linked-100-produce-20260827
100 certificates
44 certificates with Skolem steps
135 typed Skolem steps
44 exact scope blocks
```

The corresponding cached semantic-discharge subset reports 41 pass, 0 fail,
and 3 wall-limit timeouts with 10 workers. This validates the current contract;
it is not a 100-theorem completion claim.

## Immediate Producer Work

1. Audit every remaining direct primitive-looking emitter in
   `MegalodonChecker.cpp` and migrate one coherent frequent family at a time.
2. Make qualifying serialization reject any remaining unowned record in that
   family.
3. Delete duplicated rich metadata after the typed record has equivalent
   mutation and replay coverage.
4. Extend scoped producer objects only where the current exact record is
   insufficient for deterministic proof-term construction, never to encode a
   consumer guess.
5. Preserve stable schema versions and compare broad cached result vectors
   after every migration.

The goal is a smaller producer-normalized certificate and a smaller consumer,
not maximum metadata volume or benchmark-specific pass counts.
