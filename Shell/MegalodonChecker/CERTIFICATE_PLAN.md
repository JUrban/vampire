# Megalodon Certificate Export Plan

Date: 2026-07-12

Branch: `vampire/megalodon1`

## Decision

The previous `--proof megalodon` rich-export experiment is retained as a
prototype/debug path. The primary implementation target is now a normalized,
small certificate calculus documented in the Megalodon repo at:

```text
reports/vampire-megalodon-certificate-spec.md
```

Vampire should emit that calculus directly, rather than adding more
`megalodon_step_extra` fields for individual failing benchmarks.

## Initial Export Fragment

The initial qualifying schedule should avoid AVATAR and higher-order-heavy
proofs where possible. Compound Vampire inferences should be expanded before
export:

- hyper-resolution -> binary resolution,
- unit-resulting resolution -> binary resolution,
- demodulation -> paramodulation,
- duplicate deletion -> factoring,
- empty-clause detection -> contradiction.

The first native S-expression certificate version should contain only:

- `input`,
- `rename`,
- `substitute`,
- `resolve`,
- `factor`,
- `equality_resolution`,
- `paramodulate`,
- `reflexive_simplify`,
- `contradiction`.

Skolemization is the first deferred macro constructor. AVATAR is explicitly not
part of the initial fragment.

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

The old JSON/rich-export path is a diagnostic prototype only. It should not be
printed as part of the default `--proof megalodon` artifact and it must not be
used for counted proof reconstruction.

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
native format and checked by the Megalodon OCaml importer. Python and JSON may
still be used for corpus statistics or experiments, but not for accepted proof
reconstruction.

## Non-Goals

Do not extend the existing rich `printReplayExtra` protocol for the next
failing focused example. Any new output should be part of the versioned
certificate format and should have a corresponding negative test in the
Megalodon importer.
