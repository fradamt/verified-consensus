# Accountable Safety — Architectural Notes

This Lean development formalizes the accountable-safety argument from
`height_filter_and_timeouts.tex`. It currently builds with zero
`sorry`s and uses only Lean/mathlib standard axioms.

The executable model lives under `AccountableSafety/Model`, while proof facts,
invariants, the advance lemma, and the safety theorem live under
`AccountableSafety/Proof`. `DecoupledConsensus/AccountableSafety.lean` is the
public facade import.

## Core Model

Validators are `Fin n`. The state machine uses the strict quorum predicate
`IsQuorumStrict n Q := 3 * Q.card ≥ 2 * n + 1`; public safety statements use
the BFT form `IsQuorum f Q := Q.card ≥ 2 * f + 1`, converted under
`n = 3 * f + 1`.

Blocks carry their own id and vote payload:

```lean
abbrev BlockId := ℕ

structure Vote (n : ℕ) where
  validator : Validator n
  height : ℕ
  target : Option BlockId
  finalize : Option (ℕ × BlockId)

inductive Block (n : ℕ) where
  | genesis
  | mk (id : BlockId) (parent : Block n) (slot : ℕ) (votes : List (Vote n))
```

Votes refer to block ids rather than block values. `Block.findById` resolves
an id against the current chain head, and the safety theorem assumes
`Block.IdInjective n`, modelling collision-free block hashes.

The finalize commitment is intentionally one optional pair. This avoids
ill-formed votes that specify a finalize height without a target, or a target
without a height.

## Chains And State

`Chain n B` is an indexed inductive witness that `B` is the tip of a valid
chain. The `extend` constructor enforces strict slot growth. Since votes are
embedded in blocks, there is no separate `World : Block -> Votes` mapping.

```lean
inductive Chain (n : ℕ) : Block n → Type where
  | genesis : Chain n Block.genesis
  | extend {parent : Block n}
      (c : Chain n parent)
      (bid : BlockId)
      (newSlot : ℕ)
      (votes : List (Vote n))
      (hSlot : newSlot > parent.slot) :
      Chain n (Block.mk bid parent newSlot votes)
```

`stateOf : Chain n B -> State n` is the formal `σ[B]`. The per-block
transition is:

```lean
stateTransition σ B =
  processHeight (processBlock (iterateProcessSlot σ (B.slot - σ.s)) B)
```

`processBlock` sets `L := B` and folds `processVote` over `B.votes`.
`processHeight` is run before the block state is recorded, so block states are
height-closed.

## Freshness And Id Resolution

`processVoteCore` resolves `v.target : Option BlockId` through `σ.L.findById`.
A target vote is fresh only if the id resolves on the current chain and the
resolved block has `T.slot ≥ σ.sh`. A timeout vote (`target = none`) only
checks the vote height.

Finalize updates to `P` use the id form:

```lean
v.finalize = some (σ'.hj, σ'.J.id)
```

## Finality Predicate

`State` stores `F : Block n` but no finalized height. The external predicate
records the height as certificate data:

```lean
def IsFinalizedAt (f : ℕ) (C : Block n) (h_f : ℕ) : Prop :=
  ∃ B : Block n, ∃ chain : Chain n B, ∃ hC : C ≼ B,
    (stateOf chain).F = C ∧
    FinalizedCertificate chain C h_f hC
```

For non-genesis finality, the certificate contains a finalize quorum for
`(h_f, C.id)`, a justify quorum for `C.id` at `h_f`, the height-closed fact
`(stateOf (chain.subchain hC)).h = h_f`, and that the witnessing chain has
advanced past `h_f`.

## Main Safety Surface

The final theorem has the collision-free id premise explicitly:

```lean
theorem accountable_safety
    (hn : n = 3 * f + 1)
    (hId : Block.IdInjective n)
    (hC : IsFinalizedAt f C h_f)
    (hC' : IsFinalizedAt f C' h_f') :
    AtLeastFThirdSlashable f ∨ C ~ C'
```

This is the right place for id injectivity: the protocol can use opaque ids,
but the proof must be allowed to turn equal ids into equal blocks when deriving
a slashing conflict. Slashability is stated structurally over votes included in
chain histories; a concrete signature layer can authenticate those payloads
without changing the safety theorem.

## Current Status

The Lean development currently proves:

- quorum intersection in both strict and BFT forms;
- all transition field-preservation lemmas used by the invariants;
- chain invariants for targets, slots, `J`, `F`, `hj`, `sh`, and witnesses;
- `advance_witness` without a model-level assumption;
- `main_safety`, `finalized_chain`, and `accountable_safety`.
