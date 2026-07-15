# Megalodon Certificate Export Plan

Date: 2026-07-15

Branch: `vampire/megalodon4`

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
- `equality_symmetry`,
- `paramodulate`,
- `subsumption_resolution`,
- `contradiction`.

Skolemization, formula preprocessing, predicate definitions, and AVATAR are
deferred layers. They may be emitted for diagnostics and regression auditing,
but they do not extend the restricted core unless Vampire expands them into
small primitive records with a corresponding Megalodon native proof-term check.

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
(neg (AP (AP (TMH "=") (TMH "a")) (TMH "b")))
```

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
to increase pass counts. The next implementation milestone is ten committed
original-context or source-bound proofs through the restricted native proof-term
path, followed by a held-out corpus run.
