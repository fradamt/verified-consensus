# Decoupled Consensus

A Lean 4 / mathlib formalization of the accountable-safety and store
arguments for a height-filtered shared-finality protocol.

The project contains executable protocol models, proof-free public theorem
statements, and proved theorem facades. It currently builds with no `sorry`s
and uses no project-specific axioms.

## Status

| Item | Status |
| --- | --- |
| Lean toolchain | `v4.30.0-rc2` |
| Main build target | `DecoupledConsensus` |
| Protocol layers modeled | State machine and store |
| Public theorem surfaces | `State.TheoremStatements`, `Store.TheoremStatements` |
| Proof facades | `State.ProvenTheorems`, `Store.ProvenTheorems` |
| `sorry` / `admit` | none |
| Project axioms | none |

## Quick Start

```sh
lake exe cache get
lake build DecoupledConsensus
```

The root module imports the public state and store developments:

```lean
import DecoupledConsensus
```

## Entry Points

- `DecoupledConsensus.lean` imports the full development.
- `DecoupledConsensus/State/Model.lean` imports the executable state-machine
  model.
- `DecoupledConsensus/Store/Model.lean` imports the executable store model.
- `DecoupledConsensus/State/TheoremStatements.lean` contains the public
  Section 2 statement surface.
- `DecoupledConsensus/Store/TheoremStatements.lean` contains the public
  Section 3 statement surface.
- `DecoupledConsensus/State/ProvenTheorems.lean` and
  `DecoupledConsensus/Store/ProvenTheorems.lean` expose the proved theorem
  facades.
- `docs/project-design.md` records modeling decisions and technical rationale.

## What Is Proved

### State Layer

The state layer formalizes the accountable-safety argument over chain-local
state transitions. Its public theorem statements are:

| Public statement | Informal content |
| --- | --- |
| `State.MainSafetyStatement` | A chain past a finalized height contains the finalized block, unless enough validators are slashable. |
| `State.FinalizedBlocksFormChainStatement` | Finalized blocks at ordered heights form a chain, unless enough validators are slashable. |
| `State.AccountableSafetyStatement` | Two finalized blocks are compatible, unless enough validators are slashable. |

### Store Layer

The store layer formalizes the node-local accepted tree, height filter,
confirmed-output set, and replay/order-independence properties. Its public
theorem statements are:

| Public statement | Informal content |
| --- | --- |
| `Store.FinalityIrreversibilityStatement` | Store finality only moves forward. |
| `Store.FAncestorJStatement` | Reachable stores maintain `F <= J`. |
| `Store.GetConfirmedTotalStatement` | `getConfirmed` is nonempty on reachable stores, and every output is valid. |
| `Store.ForkChoiceConsistencyStatement` | Future confirmed outputs descend from earlier finalized roots. |
| `Store.LocalFinalityUpdateStatement` | Accepted finality updates move store finality far enough. |
| `Store.LockInStatement` | Processed finalized checkpoints remain locked into future confirmed outputs. |
| `Store.ParentFirstReplayLiveEquivalentStatement` | Parent-first replays of the same block set agree on the live store view. |
| `Store.ParentFirstReplayGetConfirmedStatement` | Such replays have the same `getConfirmed` membership. |

## Repository Layout

```text
DecoupledConsensus/
  State/
    Model/                 executable Section 2 definitions
    Proof/                 Section 2 proof internals
    TheoremStatements.lean public Section 2 theorem surface
    ProvenTheorems.lean    proved Section 2 facade
  Store/
    Model/                 executable Section 3 definitions
    Proof/                 Section 3 proof internals
    TheoremStatements.lean public Section 3 theorem surface
    ProvenTheorems.lean    proved Section 3 facade
docs/
  project-design.md        modeling decisions and rationale
```

The `TheoremStatements` files are the intended review surface for external
readers. Proof-internal lemmas, decomposition predicates, and engineering
machinery live under `Proof`.

## Reading Order

1. Read this README for scope and entry points.
2. Read `State/TheoremStatements.lean` and `Store/TheoremStatements.lean` for
   the public claim surface.
3. Read `docs/project-design.md` for why the model is structured the way it is.
4. Open `State/Model` or `Store/Model` for executable definitions.
5. Inspect `State/ProvenTheorems.lean` and `Store/ProvenTheorems.lean` to
   connect public statements to proof artifacts.

## Verification

The primary verification command is:

```sh
lake build DecoupledConsensus
```

For a lightweight local audit, useful checks are:

```sh
rg -n '\b(sorry|admit|axiom)\b' DecoupledConsensus --glob '*.lean'
lake build DecoupledConsensus
```

The first command should not find proof placeholders or project axioms in Lean
source files. The second command elaborates the executable model, theorem
statements, and all proof facades.
