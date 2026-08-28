# Vampire to Megalodon Certificate Plan

Date: 2026-08-28

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
- every typed Skolem application in the emitted proof DAG, including its proof
  unit and exact dependency arguments;
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

Direct `resolve` and duplicate-deleting `factor` records carry an
`ivy_nd_v1` proof block (`ivy_resolve_v2` and `ivy_factor_v2`). Vampire applies
every quantified parent variable explicitly, in the order of the producer
free-variable contract, before eliminating or rebuilding the clause. This is
the Prover9/Ivy `instantiate` discipline: Megalodon validates parent references
and elaborates the supplied proof tree, but does not infer parent
instantiations, pivots, duplicate mappings, or disjunction cases. Synthetic
parents created while lowering unit-resulting and subsumption resolution must
therefore enter the same producer variable-contract table before their proof
blocks are built.

Direct `paramodulate` records follow the same contract in
`ivy_paramodulate_v2`. Vampire validates the selected typed Megalodon equality,
the exact target position, rewrite direction, direct result, and optional
canonical-orientation symmetry. It then emits clause elimination, explicit
Leibniz transport through a two-argument motive, optional equality symmetry,
and result-literal injection as an `ivy_nd_v1` tree. Every parent is explicitly
instantiated in producer contract order. Megalodon may check the structural
action list and replay the attached proof tree, but it must not reconstruct the
transport or synthesize helper claims on this v2 path.

Direct reflexive `equality_resolution` records carry the same proof contract in
`ivy_equality_resolution_v2`. After applying the explicit producer substitution,
Vampire checks that the selected literal is a negative typed equality whose two
sides are identical. It instantiates the parent, eliminates the selected
disequality with an explicit Leibniz-reflexivity term, and copies the remaining
literals into the declared result clause. Megalodon only checks the declared
parent boundary and elaborates that proof. Higher-order
`equality_resolution_constraints` and compound trivial-inequality cleanup are
not covered by this direct object yet and must not be relabeled as v2.

### AVATAR

AVATAR remains a separate layer. A qualifying refutation has explicit split
definitions, scope, clause dependencies, and an exact SAT trace. In addition,
Vampire emits one ordinary `ivy_nd_v1` program for every SAT input, permutation,
factor, and resolution node. Input programs refer to the originating AVATAR
clause; derived programs refer only to earlier `sat_<id>` proof nodes. The final
program proves the empty clause.

The exact SAT trace is audit and dependency information, not a request for the
consumer to synthesize a clause proof. Megalodon checks that node ids and parent
references agree with the trace, then sends every program through the same
generic Ivy checker and elaborator used elsewhere. It must not run RUP search,
recover a clause ordering, synthesize assignment cases, or contain a separate
SAT proof-term generator. Megalodon must not trust an `avatar_refutation` label.

## Scoped Skolem Contract

Each typed `skolem_formula` record gives the local formula transformation:

- exact source and result;
- branch index and formula path;
- ambient and dependency contexts;
- witness symbol, replaced variable, type, and applied witness term;
- normalization contract;
- typed builder provenance.

Current `typed_v5` records additionally contain one mandatory direct proof:

```lisp
(producer_proof
  (program "ivy_nd_v1"
    (proof ... (parent "u214") ...)))
```

The program proves the exact `skolem_formula` result from its single declared
formula parent. Vampire constructs the complete choice, formula transport, and
branch-context lifting term. Its only `known` leaves are the five fixed,
type-specific choice theorems already present in the Megalodon logical prelude.
Conjunction, disjunction, implication, quantifier transport, and positive or
negative equality symmetry are expanded to ordinary Ivy lambdas and
applications. Equality is Megalodon's polymorphic equality, not a
certificate-local relation.

The witness and context traces remain typed audit data and support the later
refutation-wide unherbrandization pass. They are not instructions for the
consumer to synthesize the local proof. For `typed_v5`, Megalodon checks parent
and `known` references and sends the program through the generic Ivy parser and
elaborator. It must fail if the program is absent or cannot be emitted; it must
not run substitution candidates, rebuild transport terms, interpret branch
paths, or introduce a bridge assumption. Older typed versions remain only as
explicit compatibility paths.

The complete certificate additionally contains exactly one producer-owned
scope block when any Skolem steps occur:

```lisp
(skolem_scope_block "smolka_refutation_v2"
  (final "u372")
  (entries
    (entry (index 0) (step "u216") (symbols "sK0"))
    (entry (index 1) (step "u218") (symbols "sK1")))
  (discharge_order "u218" "u216"))

(skolem_use_block "smolka_uses_v1"
  (final "u372")
  (entries
    (entry (index 0) (step "u216") (symbol "sK0")
      (dependency_count 1)
      (uses
        (use (index 0) (unit "u216")
          (term (AP (TMH "sK0") (TMH "X0"))))))))
```

The builder derives entries by walking the typed primitive proof order and
recording `certificateLocalSymbols` on each Skolem primitive. The final step is
the actual empty-clause root. Discharge order is exact reverse proof order. The
use builder walks Vampire's typed formula and clause terms in emitted proof
units and records applications at exactly the declared dependency arity. It
uses Vampire function identities rather than recognizing printed `sK` names.

The consumer validates that every entry names a typed Skolem step and exactly
its introduced symbols. It then uses this block as the replay scope: every
epsilon replacement is registered against its declared `(step, symbol)`, and
all declarations must be discharged before returning a proof. The block is
therefore semantic certificate data, not an audit annotation.

Version 2 scopes require the use block; deleting it is a hard error. The
consumer checks its root, exact scope coverage, typed declaration and arity,
indices, uniqueness, application heads, and referenced proof units. Version 1
scope blocks remain readable only so frozen cached certificates can still be
measured. They are not newly emitted.

The use block is an inventory, not yet an unherbrandization proof. In
particular, it does not authorize Megalodon to synthesize a choice function.
The next producer pass must first expose explicit instantiated parent clauses,
then derive a finite unherbrandization plan from the exact applications. The
consumer must finally compare the complete occurrence multiset and reject any
Skolem alias that survives proof-term construction.

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
- direct `typed_v5` Skolem `ivy_nd_v1` programs generated by Vampire, including
  choice, all observed transport connectives, equality symmetry, and branch
  context lifting;
- proof-order `skolem_scope_block` emission and typed `skolem_use_block`
  application inventory;
- explicit AVATAR scope and exact SAT records, with producer-expanded
  `ivy_nd_v1` programs for component definitions, split results,
  contradictions, and every SAT refutation node;
- generic Megalodon replay of those AVATAR programs, with the displaced
  consumer-side assignment-case, RUP, resolution, factor, permutation, and
  clause-order proof synthesis deleted;
- ten-second Vampire and cached parallel corpus workflow.

Still incomplete:

- some direct legacy record construction remains in
  `MegalodonChecker.cpp`;
- not every Vampire inference family has a rule-specific primitive lowering;
- the current first-order/THF preprocessing certificate is larger than the
  desired minimal endpoint;
- broad detached replay does not itself close 100 original Megalodon theorems.
- finite unherbrandization for nested/dependent witnesses is not implemented;
  the use inventory therefore changes the contract and E4 evidence, not the
  67/100 source-target or 14-case E1 scores.

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

The direct AVATAR Ivy batch is:

```text
/project/tmp/avatar-sat-direct-frozen100-export.g9ogAf
100 certificates exported with 20 workers
27 AVATAR refutations, each with a direct producer proof block

/project/tmp/avatar-sat-direct-frozen100-replay.aej885
100 strict cached source-emission and Megalodon checks passed
```

Focused mutations reject altered local SAT proof references. The representative
split test includes a 19-node factor/resolution refutation. This closes the
already-started AVATAR consumer-synthesis migration; it does not change the
priority of producer-expanded instantiation and Skolem discharge below.

The direct local Skolem Ivy batch is:

```text
/project/tmp/native_live_skolem_pf_frontier.E25yFj
35 certificates exported and native-proof checked with 10 workers
35/35 SKOLEM_PF_PASS

/project/tmp/skolem-ivy-current35-source.o7iL8g
the same frozen certificates emitted to standalone Megalodon source
35/35 independently checked by Megalodon
```

The batch includes dependent witnesses and formulas under universal,
existential, implication, conjunction, and disjunction contexts, plus positive
and negative equality symmetry. Focused mutations reject a bad Ivy version, an
undeclared parent, a wrong choice theorem, and a corrupted choice definition.
Shared AVATAR split and contradiction tests also pass with these direct Skolem
objects present.

## Immediate Producer Work

1. Extend the producer proof-expansion pass analogous to Prover9's
   `expand_proof_ivy` beyond the now-direct AVATAR, local Skolem, resolution,
   factor, single-site paramodulation, and reflexive equality-resolution
   objects. Equality-resolution constraints, compound trivial-inequality
   cleanup, and equality factoring are the next clausal macros; their parents
   must become explicit `instantiate` nodes before small primitive proofs, with
   no consumer unification or case synthesis.
2. Run Skolem-use collection over those expanded nodes and emit a finite,
   dependency-ordered unherbrandization plan linked to each typed Skolem
   branch and source formula.
3. Make the consumer verify the complete occurrence multiset and eliminate the
   source existentials without introducing a global choice axiom. Reject every
   final term containing a certificate-local symbol.
4. Prove this path first on the known 12-case dependent-Skolem class, then run
   the cached 100 gate. Do not broaden AVATAR beyond its now-direct Ivy replay
   or do `UnionI` work meanwhile.
5. Delete the corresponding old CPS/search route after the producer-expanded
   path passes. Continue migrating other macro families only through the same
   expansion pass.

The cross-repository execution design is
`reports/VAMPIRE-MEGALODON-IVY-SMOLKA-EXECUTION-DESIGN-2026-08-27.md` in the
Megalodon repository.

The goal is a smaller producer-normalized certificate and a smaller consumer,
not maximum metadata volume or benchmark-specific pass counts.
