# Decoupled Consensus Lean Architecture

This repository formalizes the accountable-safety and store arguments from
`height_filter_and_timeouts.tex`. The development builds with no `sorry`s and
uses only Lean/mathlib standard axioms.

## File Layout

The project is split first by protocol layer, then by model/statements/proofs:

- `DecoupledConsensus/State/Model`: executable Section 2 state-machine model.
- `DecoupledConsensus/State/Statements.lean`: proof-free public Section 2
  theorem statements.
- `DecoupledConsensus/State/Proof`: Section 2 proof internals.
- `DecoupledConsensus/State/Properties.lean`: proved Section 2 facade.
- `DecoupledConsensus/Store/Model`: executable Section 3 store model.
- `DecoupledConsensus/Store/Statements.lean`: proof-free public Section 3
  theorem statements and specification vocabulary.
- `DecoupledConsensus/Store/Proof`: Section 3 proof internals.
- `DecoupledConsensus/Store/Properties.lean`: proved Section 3 facade.

Use `DecoupledConsensus.State.Model` or `DecoupledConsensus.Store.Model` when
only executable definitions are needed. Use `Statements.lean` files to review
the specification surface without proof scripts. The `Properties.lean` facades
import proofs because they expose actual theorem constants.

`DecoupledConsensus/AccountableSafety.lean` is the Section 2 public facade.
`DecoupledConsensus.lean` exports both State and Store facades.

## Blocks, Votes, And Chains

Validators are `Fin n`. Blocks carry explicit ids and embedded vote payloads:

```lean
abbrev BlockId := Nat

structure Vote (n : Nat) where
  validator : Validator n
  height : Nat
  target : Option BlockId
  finalize : Option (Nat × BlockId)

inductive Block (n : Nat) where
  | genesis
  | mk (id : BlockId) (parent : Block n) (slot : Nat) (votes : List (Vote n))
```

Votes refer to block ids rather than recursively containing blocks.
`Block.findById` resolves an id against the current chain head. Collision
freedom is not assumed globally for all raw block syntax; the public safety
statements assume `Block.IdInjectiveOnAncestors B₁ B₂` only for the compared
histories.

`Chain n B` is an indexed validity witness for a chain ending at `B`. Its
`extend` constructor enforces strict slot growth. `stateOf chain` is the
formal `sigma[B]`; it is computed from the chain, not stored in a separate
map.

## State Machine

`State` mirrors the paper tuple:

```lean
(L, s, h, sh, targets, timeouts, J, hj, F, P)
```

There is no finalized-height field in protocol state. Finalization height is
certificate/proof data, not state data.

The per-block transition is executable:

```lean
stateTransition sigma B =
  processHeight (processBlock (iterateProcessSlot sigma (B.slot - sigma.s)) B)
```

`processSlot` closes empty slots when the current slot has no block on the
chain, then increments `s`. `stateTransition` closes the block slot after
`processBlock`, so a block whose votes justify the current height can be a
target for the next height without forcing an extra block delay.

`processVoteCore` updates `targets`/`timeouts` only when the target id resolves
on the current chain, has `T.slot >= sigma.sh`, and is a strict ancestor of the
current block (`T.slot < sigma.L.slot`). The finalize `P` gate is intentionally
separate: a vote with a stale or unresolved target side can still count toward
`P` if `v.finalize = some (sigma'.hj, sigma'.J.id)`.

Justification selection is deterministic and executable: `firstJustifiedTarget`
scans validators in index order and returns the first currently justified
target.

## Section 2 Statement Surface

The public finalization predicate is chain-scoped:

```lean
def State.IsFinalizedOn {B : Block n} (chain : Chain n B)
    (C : Block n) (h_f : Nat) : Prop
```

There is intentionally no tip-only existential `IsFinalized` wrapper. The
public accountable-safety statements keep the two witnessing histories in the
premises because the accountability conclusion is scoped to those histories.

The three public State statements are:

- `State.MainSafetyStatement`
- `State.FinalizedBlocksFormChainStatement`
- `State.AccountableSafetyStatement`

Their accountability conclusion is:

```lean
AtLeastFThirdSlashableBetween chain₁ chain₂ f
```

This means the two offending histories themselves contain the slashable vote
pairs. The older unscoped `AtLeastFThirdSlashable` remains as a legacy/global
predicate for store-side assumptions.

`FinalizedCertificate` is proof/certificate vocabulary. For non-genesis
finality it records a finalize quorum for `(C, h_f)`, a justify quorum for
`C.id` at `h_f`, the height-closed fact
`(stateOf (chain.subchain hC)).h = h_f`, and that the witnessing chain has
advanced past `h_f`.

## Store Model

`Store` is the executable Section 3 tuple:

```lean
(entries, F, J, hj, hmax)
```

`entries` is the accepted tree plus a `Chain` witness for each accepted block.
The derived TeX state map `sigma[B]` is represented by `AcceptedBlockState`
and `Store.findChain?`.

The exposed store mutator is total:

```lean
Store.onBlock : Store n -> Block n -> Store n
```

Rejected blocks are no-ops for the modeled store. The internal helper
`acceptBlock? : Store n -> Block n -> Option (Store n)` records accepted
transitions for proofs and reachability. `Store.replayBlocks` folds total
`onBlock` directly; there is no `tryOnBlock`.

`getConfirmed` is modeled as a finite list of all possible confirmed outputs,
rather than choosing one output with an oracle. The statements prove properties
about every member of that output set.

## Section 3 Statement Surface

The Store statement layer includes:

- unconditional invariants such as `HjMonotoneStatement`,
  `FinalityIrreversibilityStatement`, `FAncestorJStatement`,
  `FViableStatement`, `GetConfirmedTotalStatement`,
  `ForkChoiceConsistencyStatement`, and `NoHighJustificationsStatement`;
- accountable/conditional statements such as `CertChainStatement`,
  `UpgradeStatement`, `FinalizedViableStatement`,
  `FinalityUpdateAcceptanceStatement`, and `LockInStatement`;
- observable order-independence statements.

Raw full-store equality under different replay orders is not the right
statement: a block accepted before finality moves can remain in one store while
another replay rejects it after finality moves. The proved replay surface uses
the live view rooted at finality:

- `LiveEquivalent` equates `F`, `J`, `hj`, `hmax`, and accepted entries in the
  finality subtree.
- `ParentFirstReplayLiveEquivalentStatement` proves this live equivalence for
  parent-first replays of equivalent inputs.
- `ParentFirstReplayGetConfirmedStatement` proves equality of `getConfirmed`
  membership for those replays.

## Current Caveats

- Public quorum/safety statements still use the exact committee convention
  `n = 3 * f + 1`. Generalizing to `n >= 3 * f + 1` requires refactoring the
  quorum/advance arithmetic lemmas.
- Store-side accountable assumptions still use the legacy global
  `AtLeastFThirdSlashable` predicate. State accountable-safety conclusions are
  already scoped to the two compared histories.
- `FinalizedCertificate` packages height facts as certificate/proof evidence.
  This is not protocol state, but it is still part of the external finality
  predicate surface.
