# Decoupled Consensus

A Lean 4 / mathlib formalization of the accountable-safety and store
arguments for a height-filtered shared-finality protocol.

The project contains executable protocol models, proof-free public theorem
statements, and proved theorem facades. It currently builds with no `sorry`s
and uses no project-specific axioms.

**Reference paper:** `height_filter_and_timeouts.tex` (the "height filter and
timeouts" shared-finality protocol) — §"Model and definitions" (`sec:model`) and
§"Accountable safety" (`sec:safety`) for the State layer, §"Fork-choice store"
(`sec:store`) for the Store layer. A definition/theorem-level side-by-side
correspondence is in [`docs/model-annotation.md`](docs/model-annotation.md).

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
  accountable-safety statement surface (paper `sec:model` + `sec:safety`).
- `DecoupledConsensus/Store/TheoremStatements.lean` contains the public
  fork-choice-store statement surface (paper `sec:store`).
- `DecoupledConsensus/State/ProvenTheorems.lean` and
  `DecoupledConsensus/Store/ProvenTheorems.lean` expose the proved theorem
  facades.
- `docs/project-design.md` records modeling decisions and technical rationale.
- `docs/model-annotation.md` is the paper↔Lean correspondence (definitions and
  theorems side-by-side).

## What Is Proved

### State Layer

The state layer formalizes the accountable-safety argument over chain-local
state transitions. Its public theorem statements are:

| Public statement | Paper | Informal content |
| --- | --- | --- |
| `State.MainSafetyStatement` | `lem:mainsafety` | A chain past a finalized height contains the finalized block, unless enough validators are slashable. |
| `State.FinalizedBlocksFormChainStatement` | `lem:finchain` | Finalized blocks at ordered heights form a chain, unless enough validators are slashable. |
| `State.AccountableSafetyStatement` | `thm:safety` | Two finalized blocks are compatible, unless enough validators are slashable. |

### Store Layer

The store layer formalizes the node-local accepted tree, height filter,
confirmed-output set, and replay/order-independence properties. Its public
theorem statements are:

| Public statement | Paper | Informal content |
| --- | --- | --- |
| `Store.FinalityIrreversibilityStatement` | `thm:finperm` | Store finality only moves forward. |
| `Store.FAncestorJStatement` | `thm:fleqr` | Reachable stores maintain `F <= J`. |
| `Store.GetConfirmedTotalStatement` | `cor:getConfirmed-total` | `getConfirmed` is nonempty on reachable stores, and every output is valid. |
| `Store.ForkChoiceConsistencyStatement` | `thm:fcconsistency` | Future confirmed outputs descend from earlier finalized roots. |
| `Store.LocalFinalityUpdateStatement` | `thm:finlive` | Accepted finality updates move store finality far enough. |
| `Store.LockInStatement` | `thm:lockin` | If the justification for a finalized block has been processed, future confirmed outputs descend from that block. |
| `Store.ParentFirstReplayLiveEquivalentStatement` | `thm:orderindep` | Parent-first replays of the same block set agree on the live store view. |
| `Store.ParentFirstReplayGetConfirmedStatement` | `thm:orderindep` | Such replays have the same `getConfirmed` membership. |

## Repository Layout

```text
DecoupledConsensus/
  State/                   paper sec:model + sec:safety (accountable safety)
    Model/                 executable state-machine definitions
    Proof/                 proof internals
    TheoremStatements.lean public theorem surface
    ProvenTheorems.lean    proved facade
  Store/                   paper sec:store (fork-choice store)
    Model/                 executable store definitions
    Proof/                 proof internals
    TheoremStatements.lean public theorem surface
    ProvenTheorems.lean    proved facade
docs/
  project-design.md        modeling decisions and rationale
  model-annotation.md      paper <-> Lean correspondence (defs + theorems)
```

The `TheoremStatements` files are the intended review surface for external
readers. Proof-internal lemmas, decomposition predicates, and engineering
machinery live under `Proof`.

## Reading Order

1. Read this README for scope and entry points.
2. Read `State/TheoremStatements.lean` and `Store/TheoremStatements.lean` for
   the public claim surface (each statement cites its paper label).
3. Read `docs/model-annotation.md` to check the definitions and theorems against
   the reference paper side-by-side.
4. Read `docs/project-design.md` for why the model is structured the way it is.
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
statements, and all proof facades, and is **warning-clean**: the mathlib
standard-set linter is on via `lakefile.toml` with only the opt-in
`linter.flexible` disabled, so any new warning indicates a regression.
