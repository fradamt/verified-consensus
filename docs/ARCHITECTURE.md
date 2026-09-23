# Architecture

## Five libraries

```text
┌──────────────────────────────┬───────┬──────────────────────────────────────────────────────┐
│ Library                      │ Files │ Role                                                 │
├──────────────────────────────┼───────┼──────────────────────────────────────────────────────┤
│ DecoupledConsensusModel      │    29 │ Section 7 protocol + generic execution model.        │
│ DecoupledConsensusStatements │    12 │ Review surface: generic claims + concrete binding.   │
│ DecoupledConsensusInternal   │   139 │ Proof-side vocabulary, internal regimes,             │
│                              │       │ round-sampled records. Not for review.               │
│ DecoupledConsensusProofs     │   848 │ The proofs. Root: ReviewTheorem.lean.                │
│ DecoupledConsensusWitnesses  │     8 │ One satisfying run per regime; Index.lean lists it.  │
└──────────────────────────────┴───────┴──────────────────────────────────────────────────────┘
```

`Model` and `Statements` hold definitions only; `lakefile.toml` names all five.

Every project file starts with `module` and its public imports. Proof bodies are
private by construction under the module system. The shared setup
abbreviations live in the bridge files that use them.

## Directory map

```text
DecoupledConsensusModel.lean      contents page; import order only
  DecoupledConsensusModel/Generic/Run.lean, Env.lean  Event, ProtocolSpec, Run, the state folds; Δ, GST, weights, awake
  Objects/                         identifiers, time, weights, blocks, parameters
  DecoupledConsensusModel/Protocol/Schedule.lean, StoreBase.lean  slot/round/phase arithmetic; the layer-chain base
  DecoupledConsensusModel/Protocol/ForkChoice/  Views, Goldfish (score, ghost, eligibility), Head
  DecoupledConsensusModel/Protocol/Grades.lean  SG support, opposition, grades, saved grades, clip
  DecoupledConsensusModel/Protocol/Store.lean  Σ, the flat cumulative store of §7.1
  DecoupledConsensusModel/Protocol/Handlers.lean, Evidence.lean  on_block, on_goldfish_vote, on_sg_vote,
                                   update_finality; slashing predicates and committee pools
  DecoupledConsensusModel/Protocol/Duties/, Duties.lean  Inputs, Proposals, and the duty functions
  DecoupledConsensusModel/Protocol/ValidatorClient.lean  Λ: finality_pair, height_pair, create/record_attestation
  DecoupledConsensusModel/Protocol/ChainState.lean  σ: state_transition, process_height_events, advance_height
  DecoupledConsensusModel/Protocol/Tick.lean  on_tick: grade completion, the tick, cache clipping
  DecoupledConsensusModel/Execution/  Setup, Node, Objects, Run, Instance (protocol as a spec)

DecoupledConsensusStatements.lean contents page
  DecoupledConsensusStatements/Generic/Interface.lean  what a protocol exposes: outputs, proposals, certificates
  DecoupledConsensusStatements/Generic/Constants.lean  timing and bound parameters, with a unit per field
  DecoupledConsensusStatements/Generic/Properties.lean  SafeFrom, LiveFrom, IncludedFrom, PersistsFrom, OutputOrder
  DecoupledConsensusStatements/Generic/Conditions.lean, Regimes.lean  atomic premises; the named premise bundles
  DecoupledConsensusStatements/Generic/Claims.lean  the bundle: AvailableAt, StableLiveAt, FinalizedAt, Consensus
  Instantiation.lean, Instantiation/*  env, interface, constants, Consensus; RoundTimes,
                                   Deadlines, OutageWindow, Proposals, Certificates

DecoupledConsensusInternal/        Definitions/ (internal predicates), Execution/ (run vocabulary),
                                   Legacy/ (round-sampled records, kept for proof compatibility),
                                   ModelVocabulary/ (proof-only Model reads)

DecoupledConsensusProofs/
  ReviewTheorem.lean               alone at the root: the public theorems, concreteConsensus
  Generic/ 36, Objects/ 37         generic run facts, the liveness corollary; block/weight facts
  Protocol/ 550                    one directory per Model subject (Store, Handlers, ForkChoice,
                                   Grades, Duties, ChainState, …)
  Execution/ 179                   run-level invariants, recovery, the result assemblies
  Bridge/ 8, ModelVocabulary/ 37   generic ↔ concrete; run equalities for the Model

DecoupledConsensusWitnesses/       WeakGenesis, StrongRecovery, FinalityLiveness, Outage, Index
```

## Naming rules

- A Section 7 function keeps the paper's name, in `snake_case`: `on_tick`,
  `on_block`, `goldfish_score`, `get_head`, `advance_height`. `MODEL_MAP.md`
  records every transliteration that is not letter for letter. Types are
  `CamelCase`: `Block`, `Store`, `ChainState`, `Record`.
- The protocol lives in one namespace, `DecoupledConsensusModel.Protocol`. No
  namespace and no directory is named after an earlier paper section; those
  sections survive as the functions Section 7 calls.
- A `Named*` type keeps the prefix only where an erased twin remains:
  `NamedStore` carries signed payloads beside the erased `Store`, `NamedBlock`
  the body beside `Block`.
- Source files carry no plan vocabulary: no rule numbers, internal workstream names, or
  build state. That history lives in git and in the private repository.
- Every file on the reading path opens with a module docstring: what it defines,
  where the paper defines it, what to read before and next, what to check.

## Import policy

The order is `Model ← Statements ← Internal ← Proofs ← Witnesses`. An arrow
points from a library to the ones that may import it; no library imports to its
right. `Model` and `Statements` are definition-only: a proof term
appears there only when a definition needs it to type-check, such as a
decidability or termination obligation. Four scripts hold the policy:

- `check-review-boundary.rb` walks the import closure of
  `DecoupledConsensusStatements` with the pinned Lean parser, not a text search.
  It stops on any module that is not a `Model` or `Statements` module, and fails
  if a statement file is not in the closure. `--self-test` checks the predicate.
- `StatementReachability.lean` starts from the bundle constructor and from
  `Instantiation.Consensus`, and requires `STATEMENT_UNREACHABLE_COUNT 0`.
- `ReviewSurfaceShape.lean` checks that every bundle field exists and that no
  legacy statement record is back on the surface.
- `ReviewAxioms.lean` prints the axiom list of the review theorem and of the
  public theorems beside it.

## The store layering

The paper gives Σ as one flat record of 17 components. Lean builds it in two
steps. The earlier layers form an `extends` chain: `GoldfishStore`
(`Protocol/StoreBase.lean`) ← `SGStore` ← `FGStore`
(`Protocol/ForkChoice/Goldfish.lean`) ← `HealingStore` (`Protocol/Grades.lean`).
`Protocol.Store` (`Protocol/Store.lean`) is then its own flat structure of 16
fields, joined to the chain by the read-only projection `Store.toHealing`, not by
`extends`: the chain carries bare SG votes while Σ carries combined attestations,
and a Lean `extends` cannot retype a field. Σ has 16 fields for 17 paper
components because the one heterogeneous `timestamp[·]` becomes three typed maps.
`NamedStore` wraps `Store` with the signed bodies and attestation rows. Flattening
the chain, and merging `NamedStore` into `Store`, are not made: they would require
the proofs to be redone.

## Where to add a lemma

Put a lemma with the definition it is about: a fact about `Protocol.Grades` goes
under `Proofs/Protocol/Grades/`, a fact about runs under `Proofs/Execution/`, a
protocol-independent fact under `Proofs/Generic/`. A lemma that crosses two
subjects goes with the invariant it establishes, not the theorem that consumes
it. Never add a lemma to `Model` or `Statements`; new vocabulary for a new claim
goes in `DecoupledConsensusInternal`.
