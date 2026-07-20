# Audit Response, 2026-07-20

This branch accepts the audit's architectural criticism: the qualifying proof
object must come primarily from Vampire as a small explicit certificate, not
from a large Megalodon-side search procedure that guesses how to replay
high-level inferences.

## Direction

The target certificate shape is Prover9/Ivy-style:

```text
Vampire high-level proof inference
  -> expanded sequence of small primitive clause transformations
  -> explicit source, substitution, selected literal, and rewrite metadata
  -> deterministic Megalodon elaboration
```

The existing `--proof megalodon` mode is useful, but it is still too close to
Vampire's high-level inference objects.  Work on this branch should therefore
prioritize emitting primitive replay data for all frequent inference classes
before extending Megalodon-side heuristics.

## Immediate Freeze

Until the first audited Megalodon qualifying examples pass, do not treat new
high-level inference coverage as success unless the output can be replayed by
the no-fallback Megalodon qualifying mode.

In particular, successes that require any of the following are diagnostic only:

- Megalodon constructive proof search;
- source-audit fallback proof search;
- unchecked final refutation finishing;
- globally installed certificate-local definitions;
- library-name-specific repairs.

## Vampire-Side Work Items

The next useful Vampire changes should be in the certificate emitter and proof
metadata path, especially around:

- `Shell/InferenceRecorder.cpp`, where Megalodon-specific metadata is already
  being recorded;
- equality and demodulation metadata, including actual rewritten sides,
  substitutions, and orientation;
- subsumption and resolution metadata, including pivot literals and parent
  literal positions;
- Skolemization/preprocessing metadata, including the source formula,
  introduced symbol type, witness dependency list, and transformation kind;
- an eventual small primitive certificate layer separate from the current
  high-level `megalodon` proof outline.

This document is not a replacement for implementation.  It records the branch
policy so later commits can be judged against the audit rather than against
incidental proof-count improvements.
