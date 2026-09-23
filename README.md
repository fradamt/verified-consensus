# verified-consensus

A Lean 4 model of the decoupled consensus protocol (Section 7 of the paper) and
a machine-checked proof of its consensus guarantees.

The model is an executable state machine: a cumulative store, the fork-choice
and grade functions, the validator duties, the finality gadget and the tick
handler. A generic execution model turns it into runs: sorted lists of tick and
delivery events at honest nodes, folded into per-node states. The claims speak
only about what an honest node reads from its own state: the confirmed, stable
and finalized chains. One theorem proves all of them. The proof has no `sorry`
and no project-specific axiom.

The results assume well-formed executions with unforgeable honest signatures
and collision-free roots, bounded delivery after GST, and honest committee
majorities. Liveness also needs participation and proposer recurrence. The
[premise ledger](#premise-ledger) gives the exact premises of each claim.

## The review theorem

`DecoupledConsensusModel.Proofs.concreteConsensus`, in
`DecoupledConsensusProofs/ReviewTheorem.lean`:

```lean
theorem concreteConsensus (S : Setup V) : Statements.Instantiation.Consensus S
```

`Consensus` (`DecoupledConsensusStatements/Instantiation.lean`) is the generic
bundle `Generic.Consensus` (`DecoupledConsensusStatements/Generic/Claims.lean`)
applied to this protocol. It has twelve fields:

- `constants` — the timing and bound parameters satisfy `Constants.Valid`.
- `nested` — at every read, finalized is below stable and stable is below
  confirmed.
- `certificatesAccountable` — two finality certificates finalize compatible
  targets, or they hold slashable evidence against at least a third of the
  weight.
- `finalizedAccountable` — two honest finalized reads are compatible, or the
  two read states hold slashable evidence.
- `honestNeverSlashed` — no honest validator is slashable from any two reads.
- `finalizedMonotone` — each honest node's finalized reads only extend.
- `finalizedSafe` — honest finalized reads agree.
- `available` — confirmed and stable reads are safe, and an honest proposal is
  in every confirmed read within `6Δ` of its proposal and in every stable read
  within `η_SG + 1` rounds plus `8Δ`.
- `confirmedLive` — the confirmed chain keeps growing.
- `stableLive` — the stable chain keeps growing.
- `finalized` — after a startup lag, an honest proposal is finalized everywhere
  by its deadline, and the finalized chain keeps growing.
- `stableAsynchronyResilient` — a block in an honest stable read at `T` stays
  in every honest stable read from `b₀` to the horizon, across the outage.

## Premise ledger

All conditions are in `DecoupledConsensusStatements/Generic/Conditions.lean`,
and all regimes are in `DecoupledConsensusStatements/Generic/Regimes.lean`.
`base` is `ExecutionValid`, `PartialSynchrony`, `t_GST ≤ t₀` and
`HonestCommittees`. `ExecutionValid` is `ScheduleWellFormed` (sorted, finite,
honest-only events on the public time grid), `DeliveryWellFormed` (wire,
dependency and freshness checks), `UnforgeableSignatures` and root collision
freedom. Tier 1 of proposer recurrence counts the windows from `t₀`, and tiers
2 and 3 count those from GST; all count only windows that end inside the run.

```text
┌───────────────────────────┬────────────────────────┬────────────────────────────────────────────────────┐
│ Claim                     │ Regime                 │ Conditions                                         │
├───────────────────────────┼────────────────────────┼────────────────────────────────────────────────────┤
│ constants                 │ none                   │ Constants.Valid                                    │
│ nested                    │ none                   │ —                                                  │
│ certificatesAccountable   │ none                   │ collision-free roots on the two ancestor chains    │
│ finalizedAccountable      │ RunWellFormed          │ horizon ≥ 0; sorted events; collision-free roots   │
│ finalizedMonotone         │ RunWellFormed          │ horizon ≥ 0; sorted events; collision-free roots   │
│ honestNeverSlashed        │ UnforgeableRun         │ UnforgeableSignatures; sorted; honest-only;        │
│                           │                        │ horizon ≥ 0                                        │
│ finalizedSafe             │ AccountableRegime      │ RunWellFormed; SlashableBound                      │
│ available                 │ SleepyRegime           │ base; WindowMajority; RecoveredBy                  │
│ confirmedLive             │ LiveSleepyRegime       │ SleepyRegime; SingleProposerRecurrence (tier 1)    │
│ stableLive                │ LiveSleepyRegime       │ SleepyRegime; SingleProposerRecurrence (tier 1)    │
│ finalized                 │ FinalityRegime         │ base; BelowOneThird; FullParticipation from GST;   │
│                           │                        │ StrongMultiProposerRecurrence; gap + 2 ≤ K;        │
│                           │                        │ run long enough                                    │
│ stableAsynchronyResilient │ OutageRegime           │ base with t_GST ≤ b₁; HealthyPrefixDelivery before │
│                           │                        │ b₀; FreshMajority; SlashableBound; outage bounds   │
└───────────────────────────┴────────────────────────┴────────────────────────────────────────────────────┘
```

`RecoveredBy` is either genesis or a bounded recovery prefix under
`RecoveryRegime`, which uses `MultiProposerRecurrence` (tier 2).

## Where to read

- **What is proved.** `DecoupledConsensusModel/Generic/Run.lean` and
  `Generic/Env.lean`, then the statement files in
  `DecoupledConsensusStatements/Generic/` in this order: `Interface`,
  `Constants`, `Properties`, `Conditions`, `Regimes`, `Claims`. Then
  `Instantiation.lean`, which binds each interface field and constant to a
  protocol definition.
- **The protocol.** `DecoupledConsensusModel/Objects/`, then `Protocol/`
  (store, fork choice, grades, duties, validator client, chain state, handlers,
  tick). [`docs/MODEL_MAP.md`](docs/MODEL_MAP.md) maps each Section 7 item to
  its Lean declaration.

Only two libraries must be trusted, and both hold definitions only:
`DecoupledConsensusModel` (29 files, about 5,700 lines) and
`DecoupledConsensusStatements` (12 files, about 1,150 lines). The kernel checks
the rest: `DecoupledConsensusProofs` (the proof), `DecoupledConsensusInternal`
(proof vocabulary) and `DecoupledConsensusWitnesses` (concrete runs that
satisfy each regime).

## How to verify

Prerequisites: the Lean toolchain (through `elan`) and Ruby 3.x.

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh   # install elan
lake exe cache get                                       # fetch mathlib binaries
scripts/verify.sh                                        # build and check
```

A full build takes about one hour on a recent laptop. `scripts/verify.sh`
builds the five libraries, then checks that:

- no internal module is in the closure of the statements
  (`check-review-boundary.rb`);
- every statement declaration is reachable from the bundle
  (`StatementReachability.lean`);
- the bundle has exactly the twelve fields (`ReviewSurfaceShape.lean`);
- `concreteConsensus` depends only on `propext`, `Classical.choice` and
  `Quot.sound` (`ReviewAxioms.lean`).

The outage witness decides five finite checks with `native_decide`, so it also
depends on `Lean.ofReduceBool`. The review theorem does not.

## Scope and limitations

[`docs/MODELING_CHOICES.md`](docs/MODELING_CHOICES.md) gives each item in full.

- **Generic statements.** The bundle is stated over an abstract interface.
  Only `Instantiation.lean` ties it to this protocol, so read that file with
  care: a wrong binding leaves the theorem true and empty.
- **Stronger participation premises.** The premises hold at every time, not
  only at round samples. Thus finality needs `K ≥ 5`, not the paper's `K ≥ 4`
  (§7).
- **One outage.** The outage claim covers one asynchronous period, with
  bounded delivery before it and after GST. A run with more than one outage is
  not modelled (§5.1).
- **Witnesses show satisfiability.** The witness runs have one honest node and
  one silent Byzantine validator. They do not exercise equivocation or
  adversarial traffic.
- **Outside the bundle.** Leak fairness, validator-client vote safety and
  height progress are proved in `ReviewTheorem.lean`, but they are not fields
  of `Consensus` (§10).

## Documentation

- [Review guide](docs/REVIEW_GUIDE.md) — reading order, full premise ledger,
  mechanical checks.
- [Modeling choices](docs/MODELING_CHOICES.md) — each difference in form from the
  paper and each idealization.
- [Model map](docs/MODEL_MAP.md) — Section 7, item by item.
- [Protocol](docs/PROTOCOL.md) — the reference pseudocode.
- [Architecture](docs/ARCHITECTURE.md) — libraries, directories, naming.
- [Conventions](docs/CONVENTIONS.md) — modeling conventions.
- [AI audit brief](docs/AI_AUDIT.md) — instructions for an AI reviewer.

## Paper and license

Paper: `consensus.tex` at commit `9f5ed717ffac` (not yet public). The reference
pseudocode (Section 7, verbatim) is in [`docs/PROTOCOL.md`](docs/PROTOCOL.md).
License: CC0-1.0. An earlier formalization of the accountable-safety and store
arguments for the height-filtered protocol is at tag `legacy-2026-07`.
