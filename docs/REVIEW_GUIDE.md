# Review guide

## Contents

1. Reading order
2. Domain of the setup
3. Reading notes
4. Generic interface and vocabulary
5. Generic premise ledger
6. Protocol instantiation
7. Generic result bundle
8. Results outside the generic bundle
9. Mechanical checks

## Reading order

Read the review in this order:

1. [Generic protocol and run](../DecoupledConsensusModel/Generic/Run.lean),
   then [the generic environment](../DecoupledConsensusModel/Generic/Env.lean).
   These files define the protocol object, runs, event processing, and the
   hooks used by the statements.
2. [The execution setup](../DecoupledConsensusModel/Execution/Setup.lean),
   the [execution instance](../DecoupledConsensusModel/Execution/Instance.lean),
   and the [model map](MODEL_MAP.md). The setup gives the structural domain;
   the instance gives `Execution.spec` and `Execution.handles`.
3. Read the five run equalities for `stateBefore`, `stateBeforeTime`, `readAt`,
   `final`, and `emittedAt` in
   [the proof-side execution vocabulary](../DecoupledConsensusProofs/ModelVocabulary/Execution/Instance.lean).
4. The generic statement files in this order:
   [Interface.lean](../DecoupledConsensusStatements/Generic/Interface.lean),
   [Constants.lean](../DecoupledConsensusStatements/Generic/Constants.lean),
   [Properties.lean](../DecoupledConsensusStatements/Generic/Properties.lean),
   [Conditions.lean](../DecoupledConsensusStatements/Generic/Conditions.lean),
   [Regimes.lean](../DecoupledConsensusStatements/Generic/Regimes.lean),
   and [Claims.lean](../DecoupledConsensusStatements/Generic/Claims.lean).
5. [Instantiation.lean](../DecoupledConsensusStatements/Instantiation.lean),
   which fills each interface field and constant with a closed definition of
   this protocol.
6. `Proofs.concreteConsensus` in
   [ReviewTheorem.lean](../DecoupledConsensusProofs/ReviewTheorem.lean),
   followed by `StatementReachability.lean`, `ReviewSurfaceShape.lean`,
   `ReviewAxioms.lean`, and `check-review-boundary.rb` in `scripts/`.

The statement library imports the model and the closed definitions needed by
`Instantiation`. It does not import proofs or fixtures. The old protocol-shaped
records and predicates remain in `DecoupledConsensusInternal/Legacy` for proof
compatibility. They are not part of the review surface.

## Domain of the setup

Every public field quantifies over a `Setup`. A `Setup` fixes a finite
validator type with node identity equal to validator identity, a network delay
`Δ > 0`, a nonnegative `t_GST`, positive electorate weights, the SG round
length `R ≥ 3` slots, the SG expiry window `η_SG ≥ 1` rounds, and the FG
parameters `K ≥ 4` and `D ≥ 2`. `Setup` also requires `node_val_index` and a
whole timeout count of at least `2R`, a nonempty committee at every slot, and
the outage-window bound `4 ≤ R · η_SG`. These are structural conditions of the
model. The liveness
constants (recovery endpoint, finality startup and deadline, stable-growth lag)
are closed formulas in these parameters and in the field's own `gap`, with
protocol-specific timing rules kept in the concrete instance.

## Reading notes

First, `FinalizedAt.finalizedIncluded` quantifies over the block that the honest
proposer’s duty exposes through `proposedBlock`. Under full participation the
proposer emits that block, and the conclusion that the block is below a
finalized read makes it an ancestor of a finalized block.

Second, the outage field lives in the model's single-GST world. `[b₀, b₁)`
is the initial asynchronous period, delivery is healthy before `b₀` and again
from `t_GST`, and the paper's outage with synchrony resuming at `b₁` is the
case `b₁ = t_GST`. A later temporary outage is not modelled.

Third, each regime states its own time-indexed premises. The strong regimes
require every honest validator awake from GST and less than one third faulty
weight. The sleepy and
outage regimes use the awake profile in their stated window or lag form. The
recovery constructor ends the source at `C.prefixEnd` and requires a
continuation through `C.recoveryEnd`.

Execution boundaries are part of the contract. `stateBeforeTime` folds events
with time `< t`, while `readAt` folds events with time `≤ t`; valid events are
honest-only, ticks are on the public time grid, and `tick_total` supplies every
honest tick on that grid in `[0, horizon]`. `actionRound` clamps every time
below `a₀`, including negative time, to round `0`. `awakeIn` and the sleepy
window use half-open intervals `[a, b)`. The paper's outage interval is the
half-open `[b₀, b₁)` interval. The round-0 clamp is not a round-0 sleepy
window premise: sampled sleepy windows start at rounds `r > 0` whose preceding
action is in the run. Event keys sort by `(time, phase)`, so a tick at a time
comes before deliveries at that same time; delivery order remains list order.

## Generic interface and vocabulary

`Generic.Interface` exposes the three output getters, the proposal schedule,
committees, certificates, finalization, evidence, run membership, the
idealization, and the slashable-state predicate. `Generic.Constants` also
exposes `stableInclusionDelay` for the stable output.

`UnforgeableSignatures` has two clauses. `unforgeable` covers an honest-
attributed object processed directly. `carried` covers an honest-attributed
object carried by a processed object. `UnforgeableRun` adds sorted,
honest-only events and a nonnegative horizon. The `handlesAt` relation records
a handler call, which may reject; `acceptsAt` adds the false-to-true
`processed` transition.

`Output` is a getter from a protocol state to a block. `readAt` applies an
output getter to the state read at a node and time. `ConsistentFrom` compares
two outputs across honest reads; `AgreeFrom` is its one-output specialization.
`MonotoneFrom` states prefix growth at one honest node, and `SafeFrom` bundles
agreement and monotonicity.

The five output predicates have these meanings:

```text
┌────────────────────────────┬──────────────────────────────────────────────────────────────┐
│ Predicate                  │ Meaning                                                      │
├────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ SafeFrom                   │ Honest reads agree, and each honest node's reads only extend.│
│ AccountablySafeFrom        │ Reads agree, or the two read states hold slashable evidence.│
│ LiveFrom                   │ A later honest proposal is above current reads and is present │
│                            │ in every honest read by the deadline.                       │
│ IncludedFrom               │ Every later honest proposal is in every honest read by its  │
│                            │ inclusion deadline.                                           │
│ PersistsFrom               │ A block in the stable read at `T` remains in every honest    │
│                            │ read from `b₀` through the horizon.                           │
└────────────────────────────┴──────────────────────────────────────────────────────────────┘
```

`Prefix` is the pointwise prefix relation between outputs. `InBy` says that a
block is below every honest read at one time. `HonestProposalAt` and
`honestAfter` provide proposal provenance. `NoFutureRead` records that a
proposal cannot be in an honest read before its proposal time.

The hierarchy theorem is `liveFrom_of_includedFrom`: with `0 ≤ t₀`,
`0 ≤ D`, positive period, a nonempty proposer range, the block-order facts
supplied by the concrete layer, monotonicity, no-future-read, inclusion, and
weak recurrence,
`IncludedFrom` yields `LiveFrom` with delay `gap · period + D`.
This hierarchy fact is proved in the proof library.

## Generic premise ledger

The ledger lists the direct premise for each field. `constants`, `nested`, and
`certificatesAccountable` have no run-regime premise. The conclusion record is shown in
the middle column.

```text
┌────────────────────────┬──────────────────────┬────────────────────────────────────────────────┐
│ Named premise          │ Conclusion record    │ Conclusion fields                              │
├────────────────────────┼──────────────────────┼────────────────────────────────────────────────┤
│ `Constants.Valid`      │ none                 │ timing and bound parameters are valid          │
│ none                   │ `OutputOrder`        │ finalized below stable; stable below confirmed │
│ `collisionFree` for    │ none                 │ compatible certificate targets or evidence     │
│ two certificates       │                      │ (no run regime)                                │
│ RunWellFormed          │ none                 │ finalized accountable safety                   │
│ UnforgeableRun         │ none                 │ honest validators are never slashed            │
│ AccountableRegime      │ none                 │ finalized safety                               │
│ SleepyRegime           │ `AvailableAt`        │ confirmed safety, confirmed inclusion, stable  │
│                        │                      │ safety                                         │
│ LiveSleepyRegime       │ `LiveFrom`           │ confirmed liveness                             │
│ StrongLiveSleepyRegime │ `StableLiveAt`       │ stable inclusion and stable liveness           │
│ FinalityRegime         │ `FinalizedAt`        │ finalized inclusion and finalized liveness     │
│ OutageRegime           │ none                 │ stable persistence                             │
└────────────────────────┴──────────────────────┴────────────────────────────────────────────────┘
```

`AccountableRegime` extends `RunWellFormed` with `SlashableBound`.
`SleepyRegime` requires `ExecutionValid`, `PartialSynchrony`, GST by `t₀`,
`HonestCommittees`, `WindowMajority`, and a sound `RecoveredBy` start.
`LiveSleepyRegime` adds `SingleProposerRecurrence` from `t₀` (tier 1).
`StrongLiveSleepyRegime` inherits those premises and adds
`StrongMultiProposerRecurrence` (tier 3), with the two-opening lookback.
Tier 1 counts the windows from `t₀`, and tiers 2 and 3 count those from GST;
all count only windows that end inside the run.
`FinalityRegime` extends `BFTRegime`: execution validity, partial synchrony,
GST by `t₀`, honest committees, `BelowOneThird`, and `FullParticipation`
(every honest validator awake from GST).
It adds strong recurrence, `gap + 2 ≤ maxGap`, and `longEnough`.
`OutageRegime` requires execution validity, partial synchrony, GST by `b₁`,
honest committees, `HealthyPrefixDelivery`, a public outage boundary,
`FreshMajority`, `SlashableBound`, and its interval and expiry bounds.

`Constants.Valid` requires positive `period`, nonnegative participation
window and lag, positive `proposerSlots`, `maxGap ≥ 2`, nonnegative delays,
`prefixEnd ≤ recoveryEnd`, and `outageStart T < expiry T`. `Setup` supplies
`committee_nonempty` and `outage_window`; every concrete fixture proves both.

The participation premises are continuous-time contracts. They quantify every
time in scope, not only action-round samples. The fixtures witness this where
the profile is constant: `DecoupledConsensusModel.Witnesses.generic_sleepy_regime`,
`DecoupledConsensusModel.Witnesses.generic_recovery_regime`, and `DecoupledConsensusModel.Witnesses.generic_outage_regime`.

The participation predicates are stated on the environment's awake profile:
`WindowMajority` for sleepy recovery, `FullParticipation` from GST for the BFT
profile, and `FreshMajority` for the outage profile. Recurrence uses honest
openings and multi-proposer windows. `maxGap`, `proposerSlots`, and `PublicTime` are explicit
generic fields or premises. Timeout rules stay protocol-specific.
`HonestCommittees`, `BelowOneThird`,
and `SlashableBound` remain separate so each theorem shows the exact condition
it uses.

The premise corrections are deliberate. `ScheduleWellFormed` and
`RunWellFormed` require a nonnegative run horizon. `honestNeverSlashed` uses
`UnforgeableRun`; its proof consumes only the carried clause of
`UnforgeableSignatures`, together with the sorted and honest-only run fields.
`SleepyRegime.windows` also requires
`participationLag ≤ t`, so the reference time `t − participationLag` is in the
run. Weak recurrence is strict after the sampled time. Continuous strong
recurrence remains unchanged; its satisfiable finality domain starts at
`gap = 3` and therefore `K ≥ 5`.

The concrete regime-to-fixture non-vacuity map is:

```text
┌──────────────────────┬──────────────────────────────────────────────────────────────┐
│ Regime or premise    │ Selected witness                                             │
├──────────────────────┼──────────────────────────────────────────────────────────────┤
│ `Constants.Valid`    │ `Proofs.constants_valid` for every selected `Setup`.           │
│ committee_nonempty   │ Each fixture's concrete `Setup.committee_nonempty`.           │
│ outage_window        │ Each fixture's concrete `Setup.outage_window`.                │
│ ScheduleWellFormed   │ `schedule_well_formed` in each fixture.                       │
│ DeliveryWellFormed   │ `delivery_well_formed` in WeakGenesis, FinalityLiveness,      │
│                      │ and StrongRecovery; Outage uses its named equivalent.         │
│ ExecutionValid       │ `admissible_core`/`execution_valid` in the four fixtures.     │
│ UnforgeableRun       │ Construct `UnforgeableRun` from `ExecutionValid`.              │
│ RunWellFormed        │ The schedule and idealization projections in the bridges.      │
│ AccountableRegime    │ DecoupledConsensusModel.Witnesses.generic_outage_regime, projected with its execution    │
│                      │ and slashable bound.                                           │
│ BFTRegime            │ DecoupledConsensusModel.Witnesses.generic_recovery_regime and                    │
│                      │ DecoupledConsensusModel.Witnesses.generic_finality_regime.                     │
│ RecoveryRegime       │ DecoupledConsensusModel.Witnesses.generic_recovery_regime.                       │
│ RecoveredBy          │ StrongRecovery source and continuation facts for the           │
│                      │ non-genesis constructor; WeakGenesis supplies genesis.         │
│ SleepyRegime         │ DecoupledConsensusModel.Witnesses.generic_sleepy_regime at `t₀ = 0`.                  │
│ LiveSleepyRegime     │ `DecoupledConsensusModel.Witnesses.generic_strong_live_sleepy_regime` projects  │
│                      │ its weak parent at `gap = 3`.                                 │
│ StrongLiveSleepyRegime│ `DecoupledConsensusModel.Witnesses.generic_strong_live_sleepy_regime` at      │
│                      │ `gap = 3`, with the same strong recurrence as finality.        │
│ FinalityRegime       │ DecoupledConsensusModel.Witnesses.generic_finality_regime at `gap = 3`, `K = 5`.│
│ OutageRegime         │ DecoupledConsensusModel.Witnesses.generic_outage_regime.                                  │
└──────────────────────┴──────────────────────────────────────────────────────────────┘
```

## Protocol instantiation

`Instantiation.lean` defines `env`, `interface`, and `constants` for the
selected protocol. Its interface fields are the confirmed, stable, and
finalized getters; the proposer and proposal-time functions; the committee and
proposal observers; named finality certificates; root collision freedom;
chain and store evidence; run membership; and the named root idealization.

Evidence between two certificates is a slashable set of weight at least
`2q − W` among the attestations included on chain in the two stores. The pool
may hold more rows. Here `q = ⌈2W/3⌉`; the concrete predicate is
`HasSlashableWeightBetween` in `DecoupledConsensusModel/Protocol/Evidence.lean`.

The same `2q − W ≥ W/3` threshold applies to both certificate evidence and the
state-pair evidence used by `finalizedAccountable` and `finalizedSafe`.
`slashes` is different: it uses the per-validator `SlashableBetween` predicate
over two run reads.

The constants are closed protocol definitions. They include the healing
boundary, the finality startup and deadline formulas, the awake-window and
outage timing values, and the expiry time of the first round action at or
after `T`.

Let `L = S.a 1 − S.a 0 = 4ΔR` and
`e = S.cfg.timeoutDelay / S.hc.R − 2`.

```text
┌─────────────────────────┬──────────────────────────────────────────────────────────────┬────────────┬─────────────────────────────────────────────┐
│ Field                   │ Selected value                                                │ Unit       │ Protocol meaning                             │
├─────────────────────────┼──────────────────────────────────────────────────────────────┼────────────┼─────────────────────────────────────────────┤
│ period                  │ L = S.a 1 − S.a 0 = 4ΔR                                      │ Time       │ One SG round.                                │
│ participationWindow     │ η_SG · L                                                     │ Time       │ Retained SG awake-history window.            │
│ participationLag        │ L                                                            │ Time       │ Reference one action round earlier.          │
│ proposerSlots            │ 3                                                            │ slots      │ Opening slot and the next two proposal slots.│
│ prefixEnd               │ a_(recoveryRound t₀ gap e)                                   │ Time       │ End of the bounded recovery source prefix.  │
│ recoveryEnd             │ healingBoundaryTime(recoveryRound t₀ gap e)                 │ Time       │ Completed recovery boundary.                 │
│ maxGap                  │ K                                                            │ periods    │ Maximum generic recurrence gap.              │
│ confirmationDelay       │ 6Δ                                                           │ Time       │ Proposal-to-confirmation delay.              │
│ growthDelay             │ gap·L + 6Δ = gap·period + confirmationDelay                   │ Time       │ Inclusion-to-liveness corollary delay.        │
│ stableGrowthDelay       │ (gap + η_SG)L + 2Δ                                           │ Time       │ Stable-output growth deadline.                │
│ stableInclusionDelay    │ 6Δ + ((gap + η_SG)L + 2Δ)                                    │ Time       │ Stable-output inclusion deadline.            │
│ finalityStartup         │ healingBoundaryTime(finalityStartup(gap,e) + 1) − a₀          │ Time       │ Finality startup lag.                         │
│ finalityDeadline        │ healingBoundaryTime(finalityDeadline(gap,e) + 1) − a₀ + 3Δ    │ Time       │ Finality inclusion deadline.                 │
│ outageStart(T)          │ nextAction(T) + L + Δ                                         │ Time       │ Earliest permitted outage start.             │
│ expiry(T)               │ G2 early cutoff at round s + η_SG + 1, where a_s ≥ T           │ Time       │ Expiry of the stable-read vote window.       │
└─────────────────────────┴──────────────────────────────────────────────────────────────┴────────────┴─────────────────────────────────────────────┘
```

The setup timeout is `timeoutDelay = (2 + e)R` for
`e = S.cfg.timeoutDelay / S.hc.R − 2`;
`timeout_rounds` requires this to be a whole number of rounds and at least
`2R`. The concrete finality fixture uses `e = 0`, so its timeout is `2R`.

In continuous time the smallest satisfiable strong gap is 3 (the window
`[t + 2·period, t + gap·period]` is a point at gap 2), so finality claims are
non-vacuous only for `gap ≥ 3`, hence `K ≥ 5`. This is one period more than
the paper's round-sampled premise, and the finality fixture witnesses gap 3 at
`K = 5`.

`LiveFrom` asks for `t₀ ≤ t` and `t + D ≤ horizon`; its proposed block is
strictly future, `t < proposalTime`. `IncludedFrom` asks for the strict guard
`t₀ < proposalTime` and `proposalTime + D ≤ horizon`. `PersistsFrom` starts
with a block below one honest read at `T`, then uses `b₀ ≤ t ≤ horizon` for
every later read.

The proof routes are split. `confirmedLive` uses
`liveFrom_of_includedFrom` with `SingleProposerRecurrence`, confirmed inclusion,
confirmed monotonicity, and no-future-read. Stable inclusion and stable liveness are both
under `StrongLiveSleepyRegime`: stable inclusion uses its direct inclusion route,
and stable liveness uses the existing stable-growth route. `finalizedIncluded`
uses direct finality inclusion. `finalizedLive` uses the concrete finalized
instance of the same corollary through `DecoupledConsensusModel.Proofs.finalized_growth`.

Inclusion appears in two places because the confirmed chain is available from
the sleepy regime without recurrence, while stable inclusion needs an
honest-proposer window and therefore belongs with `StableLiveAt` under strong
recurrence.

## Generic result bundle

`Generic.Consensus` has the `constants : Constants.Valid` premise followed by
ten result fields, in premise-first order:

1. `nested` and `certificatesAccountable` have no run-regime premise.
2. `finalizedAccountable` names `RunWellFormed`.
3. `honestNeverSlashed` names `UnforgeableRun`.
4. `finalizedSafe` names `AccountableRegime`.
5. `available` names `SleepyRegime` and returns `AvailableAt`.
6. `confirmedLive` names `LiveSleepyRegime` and returns `LiveFrom`.
7. `stableLive` names `StrongLiveSleepyRegime` and returns `StableLiveAt`.
8. `finalized` names `FinalityRegime` and returns `FinalizedAt`.
9. `stablePersists` names `OutageRegime` and returns `PersistsFrom`.

This makes each claim readable as `run and parameters → named premise → named
conclusion`, except for the two fields with no run-regime premise at the top. Confirmed
inclusion remains in `AvailableAt`; stable inclusion is explicit in
`StableLiveAt` because it needs strong recurrence.

The only review theorem is `Proofs.concreteConsensus : ∀ S,
Statements.Instantiation.Consensus S`. `reviewedInternal`, `legacyConsensus`, and
per-result theorems remain internal proof-layer results. Their statement types
are in the proof and internal libraries, outside the review surface.

## Results outside the generic bundle

`LeakFairnessL1CurrentProduction` is a protocol-shaped result outside the
generic bundle: an honest validator's current-production attestation, read at
its source frontier, supplies a height contribution and is protected by the
inactivity-leak ledger. It speaks about attestation rows, the source frontier,
and the leak ledger's progress snapshot, which have no protocol-independent
form, so it stays a library theorem: `Proofs.leakFairness`.

The row-level half of validator-client vote safety is
`EmissionVoteSafety`. Its theorem is `DecoupledConsensusModel.Proofs.voteSafetyOfClients`. The full
validator-client result also contains the honest-attributed store half and is
assembled by `Proofs.voteSafetyOfClients`.

The execution instance binds `Execution.spec` and `Execution.handles`. The
five equalities identify the generic folds with the selected named folds; they
are proof-side results in
`DecoupledConsensusProofs/ModelVocabulary/Execution/Instance.lean`, so the
review can follow the same state before and after each event.

### Safety-regime inventory

The public safety surface has three independent parts. `FinalitySafety`
exposes accountability from `AdmissibleCore` and whole-run agreement from
`AdmissibleCore` together with `SlashableBound`. `DynamicParticipationSafety`
states the local finalized-prefix property without a run-regime premise, GST-zero
stored-confirmation safety, and safety after a bounded strong phase. The
arbitrary-GST strong-run package provides height progress, shared-witness weak
continuation, uniform healing, canonical suffix execution, the honest-proposal
lifecycle, and conditional finality. Its unrestricted finality clause keeps
the explicit `hnotLost` input.

The GST-zero branch uses core execution, honest committee majorities, and
honest awake-window majorities. It does not require `BelowOneThird`, a
slashable bound, or proposer recurrence. The bounded phase-shift branch fixes
the source endpoint from the progress deadline and recovery lag, selects one
protected seed in the bounded interval, and requires awake-window majorities
only after that endpoint. The continuation may extend beyond the endpoint.

The public continuation records use one bootstrap and one seed. They include
read safety, actual destination votes, the record and reorganization facts,
finality agreement, confirmation renewal and order, protection at actual
votes, and honest-proposal confirmation with later read safety. The
`RefreshedLatestSafety` and `UserConfirmationAfterHealing` interfaces treat
the exposed record boundary and the bounded handoff explicitly; they do not
assume that an arbitrary pre-healing user record has already refreshed.

The shared-witness continuation, the bounded phase-shift clause, and the
strong-run result use different recovery endpoints. No weak-regime finality
progress, raw G2 producer, or active-grade result follows from these
contracts. Those results need their own checked statements and proofs.

## Mechanical checks

```sh
lake build DecoupledConsensusModel DecoupledConsensusStatements \
  DecoupledConsensusInternal DecoupledConsensusProofs \
  DecoupledConsensusWitnesses
ruby scripts/check-review-boundary.rb --self-test
ruby scripts/check-review-boundary.rb
lake env lean scripts/StatementReachability.lean
lake env lean scripts/ReviewSurfaceShape.lean
lake env lean scripts/ReviewAxioms.lean
```

The boundary script checks that the closure of the Statements entry point
contains only model and Statements modules. The reachability script uses the
generic consensus constructor and `Instantiation.Consensus` as its only roots. The
shape script checks the generic fields and the absence of the old statement
root declarations. The axiom script prints the closed review theorem
first, then the internal theorem roster. Accepted proof axioms are only
`propext`, `Classical.choice`, and `Quot.sound`.
