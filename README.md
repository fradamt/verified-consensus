# fradamt/decoupled-consensus-lean — a Lean 4 formalization of the decoupled consensus protocol

This repository holds a machine-checked model of the complete protocol of
Section 7 of the paper, and a machine-checked proof of its consensus guarantees.
The model defines the protocol as an executable state machine: a cumulative
store, the fork-choice and grade functions, the validator duties, the finality
gadget, and the tick handler. A generic execution model turns that machine into
runs, which are lists of tick and delivery events at honest nodes, folded into
per-node states. The claims speak only about what an honest node reads from its
own state: the confirmed, stable and finalized chains. One theorem proves all of
them, from premises that are all written down. The proof has no `sorry` and no
project-specific axiom.

The results assume well-formed executions with unforgeable honest signatures
and collision-free roots, bounded delivery after GST except for objects excluded
by finality, and honest committee majorities. Liveness also needs participation
and proposer recurrence; see the [premise ledger](#premise-ledger).

## The review theorem

`DecoupledConsensusModel.Proofs.concreteConsensus`, in
`DecoupledConsensusProofs/ReviewTheorem.lean`:

```lean
theorem concreteConsensus (S : Setup V) : Statements.Instantiation.Consensus S
```

`Consensus` is a definition, not a proof: in
`DecoupledConsensusStatements/Instantiation.lean` it is `Generic.Consensus
(Execution.spec S) (env S) (interface S) (constants S)`. `Generic.Consensus`
(`DecoupledConsensusStatements/Generic/Claims.lean`) has eleven fields in ten premise groups, in protocol words. `constants` is first:

- `constants` — `Constants.Valid` holds, so timing and bound parameters satisfy
  the stated constraints.
- `nested` — at every read, finalized is below stable and stable is below
  confirmed.
- `certificates` — two finality certificates finalize compatible targets, or
  they hold slashable evidence against at least a third of the weight.
- `finalizedAccountable` — two honest finalized reads are compatible, or the
  two read states hold slashable evidence.
- `honestNeverSlashed` — no honest validator is slashable from any two reads.
- `finalizedSafe` — honest finalized reads agree and only extend.
- `available` — confirmed and stable reads are safe, and an honest proposal is
  in every confirmed read within `6Δ` of its proposal.
- `confirmedLive` — the confirmed chain keeps growing: after every time, a
  later honest proposal rises above every read and reaches every read.
- `stableLive` — an honest proposal reaches every stable read by its deadline,
  and the stable chain keeps growing.
- `finalized` — after the startup lag an honest proposal is finalized
  everywhere by its deadline, and the finalized chain keeps growing.
- `stablePersists` — a block in an honest stable read at `T` stays in every
  honest stable read from `b₀` to the horizon, across the outage.

## Two reading routes

**Paper route** — you know the paper and want the protocol.
`DecoupledConsensusModel/Objects/` → `Protocol/` (`StoreBase.lean`,
`Store.lean`, `ForkChoice/`, `Grades.lean`, `Duties/`, `ValidatorClient.lean`,
`ChainState.lean`, `Handlers.lean`, `Tick.lean`) → `docs/MODEL_MAP.md`, which
maps each paper store component and each Section 7 function to its Lean
declaration and names every divergence.

**Claim route** — you want to know what is proved. `DecoupledConsensusModel/Generic/Run.lean` and
`DecoupledConsensusModel/Generic/Env.lean` → the six generic statement files in order (`Interface`,
`Constants`, `Properties`, `Conditions`, `Regimes`, `Claims`) →
`Instantiation.lean`, which binds every interface field and constant to a
closed protocol definition.

## Trust boundary

An auditor reads two libraries: `DecoupledConsensusModel` (29 files, 5,722
lines) and `DecoupledConsensusStatements` (12 files, 1,155 lines).
Both hold definitions only. Everything else is checked by the Lean kernel:
`DecoupledConsensusProofs` (848 files) holds the proof, and
`DecoupledConsensusWitnesses` holds selected concrete runs. The fixtures show
that each named regime is satisfiable in a selected run. They activate the
stated inclusion and growth guards. They do not exercise every safety or
adversarial case. Four scripts hold the boundary: `check-review-boundary.rb`
(model and statement modules only in the closure), `StatementReachability.lean` (no unlisted
claims), `ReviewSurfaceShape.lean` (exactly these fields), `ReviewAxioms.lean`.

## Premise ledger

Each claim, its regime, and the atomic conditions that regime holds, all in
`DecoupledConsensusStatements/Generic/Conditions.lean` and `DecoupledConsensusStatements/Generic/Regimes.lean`. `base` is
`ExecutionValid`, `PartialSynchrony`, `t_GST ≤ t₀` and `HonestCommittees`;
`ExecutionValid` is `ScheduleWellFormed` (sorted, finite, honest-only events;
ticks on the public time grid), `DeliveryWellFormed` (wire, dependency and
freshness checks), `UnforgeableSignatures` (honest-attributed objects come from honest
emission) and root collision freedom.

```text
┌──────────────────────┬────────────────────────┬────────────────────────────────────────────────────────────┐
│ Claim                │ Regime                 │ Atomic conditions                                          │
├──────────────────────┼────────────────────────┼────────────────────────────────────────────────────────────┤
│ constants            │ none                   │ Constants.Valid                                            │
│ nested               │ none                   │ —                                                          │
│ certificates         │ none                   │ collision-free certificate roots (`collisionFree` =        │
│                      │                        │ `RootInjectiveOnAncestors` on the two ancestor chains);    │
│                      │                        │ no run premise                                             │
│ finalizedAccountable │ RunWellFormed          │ nonnegative horizon; sorted events; collision-free roots   │
│ honestNeverSlashed   │ UnforgeableRun         │ UnforgeableSignatures; sorted; honest-only; horizon ≥ 0    │
│ finalizedSafe        │ AccountableRegime      │ RunWellFormed; SlashableBound                              │
│ available            │ SleepyRegime           │ base; WindowMajority; RecoveredBy                          │
│ confirmedLive        │ LiveSleepyRegime       │ SleepyRegime; SingleProposerRecurrence from `t₀` (tier 1)  │
│ stableLive           │ StrongLiveSleepyRegime │ SleepyRegime; SingleProposerRecurrence from `t₀` (tier 1); │
│                      │                        │ StrongMultiProposerRecurrence (tier 3)                     │
│ finalized            │ FinalityRegime         │ base; BelowOneThird; FullParticipation from GST;           │
│                      │                        │ StrongMultiProposerRecurrence; gap + 2 ≤ K; run long       │
│                      │                        │ enough                                                     │
│ stablePersists       │ OutageRegime           │ base, with t_GST ≤ b₁; HealthyPrefixDelivery before b₀;    │
│                      │                        │ FreshMajority; SlashableBound; outage and expiry bounds    │
└──────────────────────┴────────────────────────┴────────────────────────────────────────────────────────────┘
```

The recovery branch of `RecoveredBy` uses `RecoveryRegime` with
`MultiProposerRecurrence` (tier 2).

## How to verify

Prerequisites: the pinned Lean toolchain and Ruby 3.x (CI uses Ruby 3.3).

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh   # install the toolchain
lake exe cache get                                       # fetch mathlib binaries
scripts/verify.sh                                        # build and run all checks
```

With the module system, a proof-body edit rebuilds one module (12.80 seconds in
the migration measurement); a Statements edit rebuilt about 18 modules (80.81
seconds).

Lean and mathlib are pinned in `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. No `sorry`, `admit`, or project axiom is permitted.
The accepted proof must depend only on `propext`, `Classical.choice`, and
`Quot.sound`. The outage witness (`DecoupledConsensusWitnesses/Outage.lean`)
decides five finite checks with `native_decide`, so those declarations also
depend on `Lean.ofReduceBool`; the review theorem and every other witness depend
only on `propext`, `Classical.choice` and `Quot.sound`.
`scripts/verify.sh` runs `lake build` over the five libraries, then
`check-review-boundary.rb` with its self-test, then `StatementReachability.lean`,
`ReviewSurfaceShape.lean` and `ReviewAxioms.lean`. A full build takes about one
hour on a recent laptop. Green means: every file compiles; no internal module
is in the statement closure;
`STATEMENT_UNREACHABLE_COUNT 0`; all eleven bundle fields present and no legacy
statement record; and `'concreteConsensus' depends on axioms: [propext,
Classical.choice, Quot.sound]`. The toolchain is pinned in `lean-toolchain` and
`lake-manifest.json` (`leanprover/lean4:v4.30.0-rc2`, mathlib `v4.30.0-rc2`).

## Scope and known limitations

- **Generic first, concrete second.** The bundle is stated over an abstract
  `Interface` and `Constants`; only `Instantiation.lean` ties it to this
  protocol, and a wrong field there leaves the theorem true and empty.
- **Continuous-time participation.** The participation premises quantify over
  every time in scope, not only over action-round samples, so they are stronger
  than the paper's round-sampled form. One consequence: the smallest satisfiable
  strong recurrence gap is 3, so the finality claims are non-vacuous only for
  `K ≥ 5`, one more than the paper's `K ≥ 4`.
- **Participation from GST.** Full participation (finality and recovery) is
  required only from GST; the window-majority premise of the sleepy regimes
  starts at `t₀`. Tiers 2 and 3 still start at
  time 0 and range over the whole finite run; finite from-`t₀` forms are planned
  after publication.
- **Witness scope.** The witnesses use one honest node and one silent Byzantine
  validator. They establish satisfiability of each regime, not two-node
  delivery, equivocation, or adversarial traffic. The finality fixture reaches
  the first public finality deadlines. The recovery fixture ends at its
  recovery boundary, so it activates no later guard of the non-genesis branch;
  the genesis fixture activates those guards.
- **Structural conditions are not premises.** `Setup`, `HealConfig` and
  `HeightConfig` require `Δ > 0`, `R ≥ 3`, `η_SG ≥ 1`, `K ≥ 4`, `D ≥ 2`, a
  timeout of a whole number of rounds and at least `2R`, that each node runs its
  own validator index, `committee_nonempty`, and `outage_window` (`4 ≤ R · η_SG`).
  Check them in the model, not in a theorem. A round is `4ΔR`, and the SG
  window is `η_SG` rounds.
- **Delivery premises and finality.** `PartialSynchrony` and
  `HealthyPrefixDelivery` do not require an honest node to handle an object that
  its state at the delivery deadline excludes: a block that conflicts with the
  node's finalized block (`ProtocolSpec.excludes`). Without this exemption, the
  premises admit no run once a lagging honest node accepts a Byzantine block
  whose parent another honest node has already rejected for good; ordinary
  finality lag would then fall outside every liveness claim.
- **Proposal size.** An honest proposal keeps at most two distinct attestation
  rows per validator and round (`NamedProposalRows.proposalRows`); the paper
  copies every eligible row. Lean proves that a proposal has at most twice as
  many rows as distinct (validator, round) keys among its window-filtered
  inputs, so at most `2 · |V| · (η_SG + 1)`; the last step (the window count)
  is argued in the docstring, not proved. An honest validator signs one row per
  round, so in an admissible run every selected honest row that is not already
  on the parent chain survives the cap. Two distinct rows from one validator and
  round are kept, so a double vote stays visible on chain; a Byzantine
  validator with many variants chooses which two, and such a pair need not be
  slashable evidence (E1/E2 compare heights and targets, not rounds). The model bounds rows, not
  bytes; a deployment at Ethereum scale needs aggregate signatures.
- **One outage.** The model has a single GST. `[b₀, b₁)` is the initial
  asynchronous period, the paper's outage is the case `b₁ = t_GST`, and a later
  temporary outage is not modelled.
- **Representation divergences.** `docs/MODEL_MAP.md` marks each Section 7 item
  `none`, `renamed`, `inlined`, `different shape` or `protocol change`. The
  two `protocol change` rows (`propose_block`, `proposal_attestations`) are the
  proposal row cap (see Proposal size). The `different shape` rows
  are representation choices with behavior stated unchanged: typed timestamp
  maps, list-backed pools, the core and named store split, the split
  anti-slashing record, the `StoreBase` layer chain that builds Σ, and the
  three-step tick. MODEL_MAP names the edit that removes each one; the edits
  are not made.
- **Outside the bundle.** Leak fairness, validator-client vote safety and
  height progress are proved, but are not fields of `Consensus`.

## Documentation

- [AI audit brief](docs/AI_AUDIT.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Modeling conventions](docs/CONVENTIONS.md)
- [Model map](docs/MODEL_MAP.md)
- [Modeling choices](docs/MODELING_CHOICES.md)
- [Protocol extraction](docs/PROTOCOL.md)
- [Review guide](docs/REVIEW_GUIDE.md)

## Paper and license

Paper: `consensus.tex` at commit `f0ffa095d6ea` (not yet public). The
reference pseudocode (Section 7, verbatim) is in this repository:
[`docs/PROTOCOL.md`](docs/PROTOCOL.md). License `CC0-1.0`.
