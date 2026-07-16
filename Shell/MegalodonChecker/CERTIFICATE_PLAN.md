# Megalodon Certificate Export Plan

Date: 2026-07-15

Branch: `vampire/megalodon5`

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
