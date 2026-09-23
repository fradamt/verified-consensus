# Modeling choices

The paper gives the protocol in prose and pseudocode. Lean needs typed data,
total functions, and finite collections. This document lists each place where
the two differ, and each place where a stated premise replaces a physical
property.

Each heading carries a marker. **representation** means that the shape of the
data or of a definition differs while the behavior stays the same;
`docs/MODEL_MAP.md` marks the same items `different shape`, `renamed` or
`inlined`, and names the edit that removes each one. Those edits need the proofs
to be redone, and are not made. **idealization** means that a premise replaces a
physical property; each one is a declaration of
`DecoupledConsensusStatements/Generic/Conditions.lean`. **protocol divergence**
means that the selected behavior differs from the paper. Section 8 lists the
structural conditions.

Each entry has four bullets: **Paper** cites `docs/PROTOCOL.md`, **Lean** gives
the file and the declaration, **Why** gives the reason, and **Check** says what
to confirm. A path with no library prefix is under `DecoupledConsensusModel/`.

## 1 The store

### 1.1 The layer chain, then a flat store — representation

- **Paper** — section 1.1 gives the store as one flat record of 17 components.
- **Lean** — the earlier layers form an `extends` chain:
  `Protocol.GoldfishStore` (`Protocol/StoreBase.lean`), `Protocol.SGStore` and
  `Protocol.FGStore` (`Protocol/ForkChoice/Goldfish.lean`),
  `Protocol.HealingStore` (`Protocol/Grades.lean`). `Protocol.Store`
  (`Protocol/Store.lean`) is a separate flat structure of 16 fields, joined to
  the chain by the read-only projection `Protocol.Store.toHealing`.
- **Why** — the chain carries bare SG votes, the flat store carries combined
  attestations, and a Lean `extends` cannot retype a field.
- **Check** — read `toHealing` field by field. It copies every field, changes
  only the SG pool through `Protocol.sgVote`, and leaves every write to `Store`.

### 1.2 Typed timestamp maps, and grades out of the store — representation

- **Paper** — section 1.1 gives one heterogeneous `timestamp[·]`, and three
  saved grades as store components.
- **Lean** — `Protocol.Store` holds `timestamp_block`, `timestamp_vote` and
  `timestamp_sg_vote`, each a `TimestampMap` (`Objects/Time.lean`), the SG one
  keyed by `Protocol.sgVote`. `Protocol.Frame` and `Protocol.Cache`
  (`Protocol/Grades.lean`) hold the grades, in the frames `current` and `next`,
  as a field of `Execution.NamedNodeState` (`Execution/Node.lean`).
- **Why** — Lean has no untyped key, and the pool admits one attestation per
  validator and head in a round, so the projection is injective on it. The next
  round's grade 2 completes before the round rotates, so one frame is not
  enough. The two moves make 17 paper components 16 Lean fields.
- **Check** — each read uses the map of its own kind and the same comparison
  `Protocol.stampedBefore`; readers take the aligned frame through
  `Protocol.cacheAtRound`; `Protocol.clipCache` runs after every tick and
  delivery, and `Protocol.alignRound` rebuilds no missed phase.

### 1.3 List-backed pools, committee filter at the gate — representation

- **Paper** — section 1.1 calls the pools sets, and `PROTOCOL.md#goldfish_score`
  counts committee members.
- **Lean** — `Protocol.Store.gf_votes` and `Protocol.Store.sg_votes` are lists,
  read as sets by `Protocol.Store.pool` and `Protocol.Store.sg_pool`.
  `Protocol.on_goldfish_vote_checked` (`Protocol/Handlers.lean`) rejects a vote
  from outside its slot committee, and `Protocol.raw_goldfish_score`
  (`Protocol/ForkChoice/Goldfish.lean`) applies no further filter.
- **Why** — `PROTOCOL.md#propose_block` copies pooled attestations into a block,
  and `Finset.toList` is noncomputable in Mathlib, so a set pool could not be
  copied. The model tests committee membership once, at the gate.
- **Check** — every set read goes through `pool` or `sg_pool`, and
  `PROTOCOL.md#on_goldfish_vote` and `PROTOCOL.md#on_sg_vote` reject a duplicate
  before they append, which keeps each reachable list duplicate-free.

### 1.4 The core store and the named store — representation

- **Paper** — section 1.1 holds full block and attestation payloads in one
  store.
- **Lean** — `Protocol.Store` holds the erased geometry, `Block` and
  `CombinedAttestation`. `Protocol.NamedStore` (`Protocol/Handlers.lean`) wraps
  it with `bodies` and `sg_rows`, which hold `NamedBlock` and
  `NamedAttestation` (`Objects/NamedBlocks.lean`).
- **Why** — the erased types carry what the fork choice and the grades read. The
  named types carry the signed payload, including the timeout entry target that
  erasure drops. One admission path writes both.
- **Check** — `NamedAttestation.erase` and `NamedBlock.erase` keep every field
  the erased rules read.

### 1.5 The split anti-slashing record — representation

- **Paper** — section 1.2 gives the validator record as four maps: target,
  timeout, lock, and the timeout history.
- **Lean** — `Protocol.Record` holds `target`, `timeout` and `lock`;
  `Protocol.NamedRecord` holds it as `legacy` and adds `timeoutHistory`
  (`Protocol/ValidatorClient.lean`).
- **Why** — the history records the entry target that the erased timeout drops.
  `PROTOCOL.md#create_attestation` writes the map and the history in one step.
- **Check** — `PROTOCOL.md#record_attestation` and the named creator update both
  halves together.

### 1.6 Bounded proposal rows — protocol divergence

- **Paper** — `PROTOCOL.md#proposal_attestations` copies every eligible row.
- **Lean** — `Protocol.NamedProposalRows.proposalRows`
  (`Protocol/Duties/Proposals.lean`) drops rows already on the parent chain,
  then keeps at most two distinct full rows per validator and round. The
  selected round window gives a bound of
  `2 · Fintype.card V · (η_SG + 1)` rows per proposal.
- **Why** — carried side blocks can contain arbitrarily many distinct rows
  with one validator and round. The cap bounds the proposal payload.
- **Check** — `capPerSigner` keeps the first two distinct rows for each key;
  `capPerSigner_length_le_keys` proves the bound of twice the number of distinct
  (validator, round) keys, and `mem_proposalRows_of_unique` keeps every selected
  honest row that is not already on the parent chain, in an admissible run. The count of keys in the round window is not a separate lemma.
- **Limits** — two distinct rows from one validator and round stay visible on
  chain, but a Byzantine validator with many variants chooses which two, and
  such a pair need not be slashable evidence. The cap bounds honest proposals
  only: the model puts no limit on the rows of a received block, counts rows
  and not bytes, and does not bound computation. A deployment at Ethereum scale
  needs aggregate signatures.

## 2 The tick

### 2.1 The tick is three steps — representation

- **Paper** — `PROTOCOL.md#on_tick` is one function.
- **Lean** — `Execution.NamedNode.tick` (`Execution/Node.lean`) completes the
  grade phases with `Protocol.onPhaseTick`, runs the duties with
  `Protocol.NamedTick.tick` (`Protocol/Tick.lean`), then clips the cache with
  `Protocol.clipCache`. The duty driver is `Protocol.TickScheduler.runWith`.
- **Why** — grade completion reads the store from before the tick, the duties
  read the completed frames, and the clip applies the new finalized block. This
  is the order of `PROTOCOL.md#on_tick`.
- **Check** — read `runWith`. Each duty branch reads the state the previous
  branch produced, and the branch order matches `PROTOCOL.md#on_tick`.

### 2.2 The awake flag suppresses one duty — idealization

- **Paper** — section 3 states that an honest validator awake in a round runs
  its attestation, and that one asleep skips it and nothing else.
- **Lean** — `Protocol.Node.awake` (`Protocol/Schedule.lean`) is read at one
  place, the attestation branch of `Protocol.TickScheduler.runWith`
  (`Protocol/Handlers.lean`).
- **Why** — an asleep validator still ticks, still receives, and still processes
  every delivered object, so its store stays current.
- **Check** — search the model for `awake` and confirm the one read. Do not read
  the participation claims as availability in a model where an asleep node
  misses messages.

## 3 Computability and decidability

### 3.1 Executable definitions, decidable propositions — representation

- **Paper** — the pseudocode is executable, and `PROTOCOL.md#supports` and
  `PROTOCOL.md#opposes` are quantified statements.
- **Lean** — no declaration of `DecoupledConsensusModel` is `noncomputable`; the
  review surface holds three, all in the statement layer
  (`Statements.Generic.awakeIn`, `Statements.Instantiation.constants`,
  `Statements.Instantiation.recoveryRound`). `Protocol.Supports` and `Protocol.Opposes`
  (`Protocol/Grades.lean`) stay quantified propositions, with the instances
  `Protocol.supportsDecidable` and `Protocol.opposesDecidable`;
  `Protocol.positive`, `Protocol.opposing` and `Protocol.gradeBool` are the
  executable tests. `Block.pickUnique?` (`Objects/Blocks.lean`) returns `none`
  unless one element matches, and `Block.find?` and `Block.deepest?` use it.
- **Why** — an executable model runs on a fixture, and
  `DecoupledConsensusWitnesses` runs one per regime. The propositions keep the
  shape of the paper rules, and the instances keep them executable. Two raw
  `Block` values may share a root, so selection must answer without choice.
- **Check** — search the model for `noncomputable`, `partial`, `sorry` and
  `axiom`, and expect no hit. The instances add no case, and every caller of
  `find?` and `deepest?` handles `none`.

## 4 The generic execution model

### 4.1 Events happen at honest nodes only — idealization

- **Paper** — the paper gives the protocol as honest node behavior.
- **Lean** — `Generic.Event` (`Generic/Run.lean`) is a tick or a delivery at one
  node, and `Statements.Generic.ScheduleWellFormed.honest_only` requires the
  node of every event to be honest.
- **Why** — a faulty validator has no state here. It acts through the objects
  honest nodes receive, and those objects are arbitrary, except for the
  unforgeability premise below.
- **Check** — no claim quantifies over the state of a faulty node, and the
  slashing evidence reads honest stores, through
  `Statements.Instantiation.interface`.

### 4.2 Folds, emissions and handler calls — representation

- **Paper** — the paper reads a node's state at a time, a duty emits an object,
  and a handler accepts or rejects an object.
- **Lean** — all in `Generic/Run.lean`. `Generic.Run.stateBefore` folds the
  events before an index, `Generic.Run.stateBeforeTime` those with time strictly
  below `t`, `Generic.Run.readAt` those with time at or below `t`, and
  `Generic.Run.final` the whole list. `Generic.Run.emittedAt` recomputes a tick
  output from the state before the event, and `Generic.Run.emits` reads it.
  `Generic.ProtocolSpec.handles` records a handler call, which may reject;
  `Generic.Run.acceptsAt` adds the change of `Generic.ProtocolSpec.processed`
  from `false` to `true`; `Generic.ProtocolSpec.carries` is structural
  containment, with the containing object first. `Execution.spec` and `Execution.handles`
  (`Execution/Instance.lean`) bind them.
- **Why** — a read at a time must include the tick at that time, so `readAt`
  uses `≤`; a precondition must not, so `stateBeforeTime` uses `<`.
  `Generic.Event.key` orders events by time, then by phase, so a tick precedes
  the deliveries at that time. The run holds no emission list, so an emission is
  a fact about the protocol, not data a run may misstate. A guard-rejected call
  consumes nothing, and the node can accept the same object later. A claim
  reads the state after all events at its time; it says nothing about the
  states between deliveries at one time.
- **Check** — each claim uses the fold its statement needs, no premise adds
  emissions to a run, and `Statements.Generic.PartialSynchrony` uses `handlesAt`
  for its conclusion and `acceptsAt` for its relay trigger.

## 5 The environment

### 5.1 One delay bound and one GST — idealization

- **Paper** — section 3.4 gives an outage as an interval `[b₀, b₁)`, and
  synchrony resumes at `b₁`.
- **Lean** — `Generic.Env` (`Generic/Env.lean`) holds one `Δ` and one `t_GST`.
  `Statements.Generic.PartialSynchrony` bounds delivery after `t_GST`, and
  `Statements.Generic.HealthyPrefixDelivery` bounds it before a cut.
  Neither bound applies to an object that the receiver's state at the deadline
  excludes (`ProtocolSpec.excludes`): a block that conflicts with the receiver's
  finalized block. The receiver would reject that block for good, and its
  children could never meet the parent condition of a delivery.
- **Why** — the model has one asynchronous period, `[b₀, b₁)`, at the start of
  the run. The paper's outage is the case `b₁ = t_GST`. A later temporary outage
  is not modelled.
- **Check** — the outage claim states delivery as healthy before `b₀` and again
  from `t_GST`, and `Δ` is strict: the premises conclude
  `t' < max t t_GST + Δ`: an object sent before GST arrives before
  `t_GST + Δ`.

### 5.2 A round-sampled awake profile, read in continuous time — representation

- **Paper** — section 3 makes participation an input for each round.
- **Lean** — `Protocol.Node.awake` takes a round and `Generic.Env.awake` takes a
  time. `Statements.Instantiation.env` binds the second to the first through
  `Statements.Instantiation.actionRound`
  (`DecoupledConsensusStatements/Instantiation.lean`).
- **Why** — the protocol needs the flag once each round, but the premises
  quantify over time. `actionRound` gives round `r` the half-open window
  `[a_r, a_{r+1})`, and clamps every time below `a_0` to round 0.
- **Check** — confirm the clamp. A round-0 sleepy window is not a premise:
  sampled windows start at rounds above 0, whose preceding action is in the run.

### 5.3 Weights and committees stay apart — representation

- **Paper** — Goldfish counts committee members; the SG rule, the finality
  gadget and the grades count weight.
- **Lean** — `Electorate` carries the weights and `Committees` carries
  membership only (`Objects/Weights.lean`). Nothing routes a committee through
  `Electorate.weightOf`.
- **Why** — the two counting regimes must not be conflated. `Committees` states
  no size, no honesty and no overlap law; those are premises.
- **Check** — `Protocol.raw_goldfish_score` counts cardinality, while
  `Protocol.gradeBool` and `Electorate.finalityThreshold` count weight.

## 6 Idealizations that are premises

Each premise named here is a declaration of
`DecoupledConsensusStatements/Generic/Conditions.lean`.

**Unforgeable signatures.** The model has no cryptography.
`Statements.Generic.UnforgeableSignatures` has two clauses: `unforgeable` covers
an object a node processes directly, and `carried` covers an object that a
processed object carries. Each says that an object attributed to an honest
validator comes from an emission by that validator, at an earlier time or the
same time. Check both; the honest-never-slashed claim consumes `carried`.

**Collision-free roots.** Block roots are the model's hash identifiers, and the
`Block` inductive stays a raw datatype. `Execution.RootInjectiveBelow` and
`Execution.RootInjectiveOnAncestors` (`Execution/Setup.lean`) state collision
freedom on a named scope, and `Execution.NamedRootCollisionFree`
(`Execution/Run.lean`) packages it over the blocks one run puts in play.
`Statements.Instantiation.interface` binds it to the interface field
`idealization`, which `ExecutionValid` and `RunWellFormed` require. This premise
makes `Block.find?` act as a hash lookup. Check that the scope covers every
block a claim compares.

**Honest committees.** `Statements.Generic.HonestCommittees` requires a strict
honest majority by count in every slot committee. This is a premise, not a fact
of `Committees`. Check that the claims that need Goldfish counting name it, and
that the safety claims of the finality gadget do not.

**Ticks on the public time grid.** `Statements.Generic.PublicTime` says that a
time is a natural multiple of `Δ`. The four per-slot instants are `t_s + kΔ` for
`k` in `0 … 3`, with `t_s = 4Δs`, so the public times are exactly those
multiples. `ScheduleWellFormed.tick_public` keeps every tick on the grid, and
`ScheduleWellFormed.tick_total` supplies every honest tick on the grid in
`[0, horizon]`. Check both: without `tick_total` a node could miss a duty, and
every liveness claim would fail.

**The accountable bound, as a negation.** Section 3.3 writes the bound as
`W + w(X) < 2q` for the set `X` with evidence.
`Statements.Generic.SlashableBound` says instead that no two certificates of the
run hold evidence, where the interface binds evidence to
`HasSlashableWeightBetween` (`Protocol/Evidence.lean`). The two agree, because
`HasSlashableWeightBetween` asserts a set of weight at least `2q − W`, written
additively as `2q ≤ W + w(S)` to keep natural subtraction out of the definition.
Check the direction of the inequality, and check that `SlashableBetween` permits
the two occurrences to be one attestation.

## 7 Continuous-time participation — idealization

Section 3 states each participation condition for each round whose action time
or grade completion time falls in the run. The Lean premises quantify over every
time in scope: `Statements.Generic.WindowMajority`,
`Statements.Generic.FreshMajority`, `Statements.Generic.SingleProposerRecurrence`,
`Statements.Generic.MultiProposerRecurrence` and
`Statements.Generic.StrongMultiProposerRecurrence` are continuous-time contracts, and
are therefore stronger than the round-sampled form. The recurrence tiers count
only the windows that end inside the run and start at or after `t₀` (tier 1)
or GST (tiers 2 and 3).

One consequence is visible in the constants. In continuous time the window
`[t + 2·period, t + gap·period]` of `StrongMultiProposerRecurrence` is a single point
at `gap = 2`, so the smallest satisfiable strong gap is 3. The finality claims
need `gap + 2 ≤ K`, so they are non-vacuous only for `K ≥ 5`, one more than the
paper's `K ≥ 4`. The finality fixture witnesses `gap = 3` at `K = 5`. Check that
each fixture in `DecoupledConsensusWitnesses` satisfies the continuous form, and
not only the samples; the fixtures use a constant awake profile, which is why
they can.

## 8 Structural conditions, not premises

These conditions live in the parameter structures. A theorem cannot state them,
and a theorem cannot avoid them. Check them in the model. Each file below is
under `DecoupledConsensusModel/`.

```text
┌──────────────────────────────┬──────────────────────────┬──────────────────────────┐
│ Condition                    │ Field                    │ File                     │
├──────────────────────────────┼──────────────────────────┼──────────────────────────┤
│ Δ > 0                        │ Env.Δ_pos                │ Objects/Parameters.lean  │
│ Δ > 0, generic environment   │ Generic.Env.Δ_pos        │ Generic/Env.lean         │
│ R ≥ 3                        │ HealConfig.R_ge_three    │ Protocol/Grades.lean     │
│ η_SG ≥ 1                     │ HealConfig.η_SG_ge_one   │ Protocol/Grades.lean     │
│ K ≥ 4                        │ HeightConfig.K_ge_four   │ Protocol/ChainState.lean │
│ D ≥ 2                        │ HeightConfig.D_ge_two    │ Protocol/ChainState.lean │
│ Timeout: whole rounds, ≥ 2R  │ Setup.timeout_rounds     │ Execution/Setup.lean     │
│ Node runs its own index      │ Setup.node_val_index     │ Execution/Setup.lean     │
│ Committee is nonempty        │ Setup.committee_nonempty │ Execution/Setup.lean     │
│ 4 ≤ R · η_SG                 │ Setup.outage_window      │ Execution/Setup.lean     │
└──────────────────────────────┴──────────────────────────┴──────────────────────────┘
```

A round is `4ΔR`, and the SG expiry window is `η_SG` rounds. `node_val_index`
ties the node record to the validator that runs it: without it a validator could
tick with another identity, and every proposer test and committee test would
read the wrong name. `committee_nonempty` and `outage_window` stop two claims
from becoming vacuous: an empty committee makes every committee premise false,
and at `R = 3` with `η_SG = 1` the outage window is empty.

## 9 Closed-form round times — representation

- **Paper** — appendix A.11 gives the round schedule and the action time `a_r`.
- **Lean** — `Statements.Instantiation.nextRound`
  (`DecoupledConsensusStatements/Instantiation/RoundTimes.lean`) is a closed
  form: `Int.toNat (t − a₀)` divided by `Statements.Instantiation.roundPeriod`, with a
  ceiling. `Statements.Instantiation.roundAt` is its public name.
- **Why** — a closed form reduces in a proof, and it executes. The least-round
  specification does neither.
- **Check** — read `Proofs.nextRound_eq_find`
  (`DecoupledConsensusProofs/Bridge/RoundTimes.lean`), which proves the closed
  form equal to the least round whose action time is at or after `t`. This is
  the only place where the two forms must agree.

## 10 Results proved outside the bundle

Three results are proved and are not fields of `Consensus`.
`Proofs.leakFairness` says that an honest validator's current-production
attestation supplies a height contribution, and that the inactivity-leak ledger
protects it. `Proofs.voteSafetyOfClients` says that an honest validator that
follows the validator-client signing rules is never slashable.
`Proofs.heightProgress` is the height progress of the finality gadget. All three
are in `DecoupledConsensusProofs/ReviewTheorem.lean`, and each speaks about
attestation rows, ledgers or heights, which have no protocol-independent form.
Do not read them as bundle guarantees.

## 11 Scope of this document

This document covers the current model. It records no history of a choice, and
it omits the proof-side vocabulary of `DecoupledConsensusInternal`. Read
`docs/MODEL_MAP.md` for the item-by-item comparison with the paper,
`docs/REVIEW_GUIDE.md` for the reading order and the premise ledger, and
`docs/ARCHITECTURE.md` for the library layout.
