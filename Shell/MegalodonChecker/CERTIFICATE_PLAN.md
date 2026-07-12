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

The first JSON certificate version should contain only:

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

The `vampire/megalodon1` branch now emits a transitional
`megalodon_certificate_clause(step,[...]).` record for every first-order clause
whose literals can be rendered in the structured JSON term format used by the
Megalodon importer:

```text
{"var":"X0"}
{"const":"a"}
{"app":"f","args":[...]}
{"polarity":true,"atom":{"pred":"p","args":[...]}}
{"polarity":false,"atom":{"eq":[...,...]}}
```

This is not yet the full certificate object: rule constructors, pivots,
substitutions, positions, and source-map references still have to be emitted as
versioned JSON steps. The point of this checkpoint is to stop relying only on
Megalodon proof-script strings and to make Vampire expose the same structured
clause representation that the new Megalodon-side certificate checker consumes.

## Non-Goals

Do not extend the existing rich `printReplayExtra` protocol for the next
failing focused example. Any new output should be part of the versioned
certificate format and should have a corresponding negative test in the
Megalodon importer.
