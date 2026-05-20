# Project Design Notes

This file records technical modeling decisions for the Decoupled Consensus
Lean formalization. The README is intentionally short and external-facing;
this document is the place for "why is it modeled this way?" details.

## Statement Layer Discipline

The project separates three kinds of files:

- `Model` files contain executable definitions and protocol data structures.
- `TheoremStatements.lean` files contain public, proof-free theorem statements.
- `Proof` files contain internal lemmas, proof decomposition, and proof scripts.
- `ProvenTheorems.lean` files expose theorem constants proving the public
  statements.

The statement files are reserved for results that are meant to be externally
reviewed. Helper lemmas and proof-engineering predicates should stay under
`Proof`, even when they correspond to useful intermediate facts.

## Blocks, IDs, Votes, And Chains

Validators are `Fin n`.

Blocks are raw parent-pointer trees with explicit ids and embedded votes:

```lean
abbrev BlockId := Nat

structure Vote (n : Nat) where
  validator : Validator n
  height : Nat
  target : Option BlockId
  finalize : Option (Prod Nat BlockId)

inductive Block (n : Nat) where
  | genesis
  | mk (id : BlockId) (parent : Block n) (slot : Nat) (votes : List (Vote n))
```

Votes refer to block ids rather than recursively containing blocks. This avoids
mutual recursion between blocks and votes while still modeling the intended
"vote names a block hash" behavior.

`Block.findById` resolves ids by scanning ancestors of the current chain head.
Raw block syntax can contain id collisions. Safety statements assume scoped
id-injectivity only for the compared histories, via
`Block.IdInjectiveOnAncestors`. This models collision resistance as a local
assumption about the histories under consideration rather than as a global
well-formedness condition on all possible raw blocks.

`Chain n B` is an indexed validity witness for a chain ending at `B`. Its
`extend` constructor enforces strict slot growth. The state at a block is
computed by `stateOf chain`; the model does not store an independent state map
that could disagree with the chain.

## State Transition

`State` mirrors the protocol state tuple:

```lean
(L, s, h, sh, targets, timeouts, J, hj, F, P)
```

There is no finalized-height field in `State`. Heights attached to finality
events are certificate/proof data, not protocol state.

The per-block transition is executable:

```lean
stateTransition sigma B =
  processHeight (processBlock (iterateProcessSlot sigma (B.slot - sigma.s)) B)
```

`processSlot` closes empty slots when the current slot has no block on the
chain, then increments `s`. `stateTransition` closes the block slot after
`processBlock`, so a block whose votes justify the current height can be used
for the next height without forcing an extra block delay.

Within `processHeight`, the height event is processed before the slot counter
is advanced. When a height transition fires, `sh` is set to the current slot.
This keeps the height-freshness condition aligned with the slot of the block
or empty slot that triggered the transition.

## Vote Processing

`processVoteCore` updates `targets` and `timeouts` only when the target side of
the vote is valid for the current chain:

- the target id resolves on the current chain;
- the vote height matches the state height;
- the target slot is at or after `sh`;
- the target is a strict ancestor of the block being processed.

The finality-participation update is intentionally independent of the target
side. A vote can fail to update `targets` while still counting toward `P` if
its finalize commitment matches the current `(hj, J.id)` after the core vote
update. This matches the intended protocol behavior: stale target information
does not necessarily invalidate an otherwise relevant finality commitment.

Justification selection is deterministic and executable. The current model
scans validators in index order and returns the first target that is justified
under the current target map.

## Certificates And Accountability Evidence

Votes included in blocks are the structural evidence for accountability. The
model does not include cryptographic signatures directly; instead, an included
vote is treated as authenticated evidence from its declared validator. A
concrete protocol with working signatures instantiates this structural model
by verifying those signatures before accepting votes.

Public state safety conclusions are scoped to the two offending histories:

```lean
AtLeastFThirdSlashableBetween chain1 chain2 f
```

This ensures the theorem identifies slashable evidence in the histories that
witness the conflicting finality facts.

Some store-side conditional statements use a global no-slashability premise.
That is a statement-level assumption about the execution environment, not a
protocol state field.

## Store Semantics

The executable store is:

```lean
(entries, F, J, hj, hmax)
```

`entries` is the accepted block tree plus a `Chain` witness for each accepted
block. The TeX-style state map `sigma[B]` is derived from those chain
witnesses by lookup plus `stateOf`.

The public store mutator is total:

```lean
Store.onBlock : Store n -> Block n -> Store n
```

Rejected blocks are no-ops for the modeled store. The internal helper
`acceptBlock? : Store n -> Block n -> Option (Store n)` remains useful for
proofs because accepted transitions need explicit witnesses.

`getConfirmed` is modeled as a finite list of all possible confirmed outputs
instead of selecting one output through an oracle. Theorems quantify over every
member of this output set.

## Viable Tree And Height Filter

The store model uses a high-descendant characterization of viable-tree
membership:

```lean
B is viable iff B is accepted and has an accepted descendant D
whose state height is at least hmax - 1.
```

For valid stores this is equivalent to the leaf-witness characterization used
by the protocol text. The high-descendant form is easier to execute and easier
to use in proofs because it avoids a separate maximal-leaf search.

The confirmation root is:

```lean
if hmax = hj + 1 then J else F
```

A confirmed output must be viable, descend from this root, and meet the same
height threshold.

## Replay And Order Independence

Raw full-store equality is not the correct replay-order statement. A block
accepted before finality advances may remain in one store, while another
parent-first replay can reject that block after finality advances.

The externally relevant result is equality of the live view rooted at finality:

- same `F`;
- same `J`;
- same `hj`;
- same `hmax`;
- matching accepted entries in the finality subtree.

This is captured by `LiveEquivalent`. The public order-independence theorem
then proves equality of `getConfirmed` membership for parent-first replays of
the same available block set.

## Current Modeling Boundaries

The public quorum and safety statements currently use the exact committee
convention:

```lean
n = 3 * f + 1
```

Generalizing the public surface to `n >= 3 * f + 1` would require refactoring
the quorum arithmetic lemmas.

`TheoremStatements.lean` should remain focused on public theorem surfaces. If a
new result is only needed to make a proof go through, it should live under
`Proof`.
