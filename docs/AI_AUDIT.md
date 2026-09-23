# Brief for an AI reviewer

You audit a Lean 4 formalization of the protocol in Section 7 of the paper. The
proof is kernel-checked, so do not re-check arithmetic. Check that the theorem
says what the documents claim, and that its premises describe the protocol and
not a convenient special case. Read the code cold: do not assume an earlier
review was right. Cite every finding by file and line, and by the declaration.

## Reading order

1. `README.md` — the claims under audit.
2. `DecoupledConsensusModel/Generic/Run.lean`, `Generic/Env.lean` — events,
   runs, the state folds, the network and timing environment.
3. `DecoupledConsensusModel/Execution/Instance.lean`, `DecoupledConsensusModel/Execution/Setup.lean` — the protocol as a
   generic spec, and the structural conditions of a run.
4. `DecoupledConsensusStatements/Generic/` in this order: `Interface.lean` (what
   a protocol exposes), `Constants.lean` (timing values and units),
   `Properties.lean` (what an output can satisfy), `Conditions.lean` (atomic
   premises), `Regimes.lean` (premise bundles), `Claims.lean` (the bundle).
5. `DecoupledConsensusStatements/Instantiation.lean` and `DecoupledConsensusStatements/Instantiation/` — the concrete binding.
6. `DecoupledConsensusProofs/ReviewTheorem.lean` — the theorem and its type; then
   `DecoupledConsensusWitnesses/Index.lean` — the non-vacuity witnesses.
7. `docs/AI_AUDIT.md`, `docs/ARCHITECTURE.md`, `docs/CONVENTIONS.md`,
   `docs/MODEL_MAP.md`, `docs/MODELING_CHOICES.md`, `docs/PROTOCOL.md`, and
   `docs/REVIEW_GUIDE.md` — the repository rules, source map, choices, protocol,
   and review ledger.

## The six dimensions

**1. Generic execution model.** Does a run describe the real world? Check the
four folds in `DecoupledConsensusModel/Generic/Run.lean`: `stateBefore` takes events by index,
`stateBeforeTime` events strictly before `t`, `readAt` events up to and
including `t`, `final` all events. Check that `emits` recomputes the emitted
list from the pre-event state, so a run cannot insert an emission a node would
not make. Check `handles`, `acceptsAt` and `carries`: can a Byzantine node's
object still reach an honest node? Does anything silently exclude an adversary?

**2. Generic statements.** Do the predicates mean what their names say? Check
the quantifier ranges of `SafeFrom`, `AccountablySafeFrom`, `LiveFrom`,
`IncludedFrom`, `PersistsFrom` and `OutputOrder` in `Properties.lean`. Watch the
guards: `LiveFrom` needs `t + D ≤ rho.horizon` and `IncludedFrom` needs
`proposalTime s + D ≤ rho.horizon`; a guard that is too tight empties a claim
near the run's end. Check that `LiveFrom` asks for a block above the read.

**3. Concrete instantiation.** Is the abstract bundle about this protocol? Read
`Instantiation.lean` field by field against the model. `confirmed`, `stable` and
`finalized` must be the protocol's own getters; `proposalTime`, `committee` and
`proposer` must be its schedule; `evidence`, `slashable` and `slashes` must be
its slashing predicates, at the right weight threshold. Every constant must
carry the right unit: `period` is one SG round, `participationWindow` is `η_SG`
rounds, `confirmationDelay` is `6Δ`. A wrong field here leaves the theorem true
and empty, so this is the highest-value dimension.

**4. Protocol against the paper.** Read `Protocol/` against Section 7 with
`docs/MODEL_MAP.md` open. For each `none` and `renamed` row, check the Lean
against the paper text. For each `inlined` and `different shape` row, check the
stated reason holds and behavior really is unchanged. Where the paper's prose and
the Lean disagree on a model detail, the Lean is the reference, unless the Lean
behavior is a protocol error.

**5. Strength of the premises.** This is the adversarial dimension. For each
regime in `Regimes.lean`, ask three questions. Is it satisfiable at all, and does
`DecoupledConsensusWitnesses` prove that with at least one Byzantine validator?
Is it stronger than the paper's assumption, and does the extra strength matter?
Does a premise accidentally imply the conclusion? Look at `RecoveredBy`, which is
inductive and may hide a recovery obligation; at `FinalityRegime.gapBound` and
`longEnough`; and at `WindowMajority`, `FullParticipation` and `FreshMajority`.

**6. Documentation consistency.** Does every claim in `README.md`,
`docs/REVIEW_GUIDE.md`, `docs/ARCHITECTURE.md` and each module docstring match
the code? Check paths, declaration names, field counts and regime names. A
document that names a moved file is MINOR; one that misstates a premise is not.

## Boundary rules

- `DecoupledConsensusModel` and `DecoupledConsensusStatements` hold definitions
  only. A theorem may appear only when a definition needs it to type-check;
  report any other proof term on the review surface.
- One library, one top namespace, one directory tree; report a file that declares
  a namespace belonging to another library.
- The review theorem must depend only on `propext`, `Classical.choice` and
  `Quot.sound`. No `sorry`, no `admit`, no project axiom.
- `StatementReachability.lean` must report `STATEMENT_UNREACHABLE_COUNT 0`, so no
  unlisted second collection of claims can pass as part of the surface.

## Commands

```sh
lake exe cache get
scripts/verify.sh
ruby scripts/check-review-boundary.rb && ruby scripts/check-review-boundary.rb --self-test
lake env lean scripts/StatementReachability.lean
lake env lean scripts/ReviewSurfaceShape.lean
lake env lean scripts/ReviewAxioms.lean
```

Follow the fresh-clone steps in README [How to verify](../README.md#how-to-verify).
Write scratch files under `.audit-scratch/<your-name>/`. You may run `lake env
lean` on a scratch file to print a type or an axiom list. Avoid starting a
second build while one already runs; do not change a tracked file.

## Severity and report format

```text
┌─────────┬──────────────────────────────────────────────────────────────────────────┐
│ BLOCKER │ The review theorem does not say what the documents claim.                │
│ MAJOR   │ A premise or definition is wrong, vacuous, or materially stronger        │
│         │ than the paper.                                                          │
│ MINOR   │ Readability, naming, dead code, or a document that is out of date.       │
└─────────┴──────────────────────────────────────────────────────────────────────────┘
```

Report a coverage table (every file read, line ranges), then a findings table:

```text
┌────┬──────────┬───────────┬───────┬──────────┬───────────────┬──────────┐
│ ID │ Severity │ file:line │ Claim │ Evidence │ Suggested fix │ Boundary │
└────┴──────────┴───────────┴───────┴──────────┴───────────────┴──────────┘
```

`Claim` is what the code or document asserts. `Evidence` is what you read that
shows the problem, quoted. `Boundary` says whether the fix touches a frozen
statement, the model, or documents only. End with the files you checked and found
correct, and the questions you could not settle.
