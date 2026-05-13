# Accountable Safety — Architectural Notes

This Lean development formalizes the accountable-safety argument from
`height_filter_and_timeouts.tex`. It currently builds with zero
`sorry`s and uses only Lean/mathlib standard axioms.

The state-machine executable model lives under `DecoupledConsensus/State/Model`,
while the proof-free statement surface lives in
`DecoupledConsensus/State/Statements.lean`. State proof facts, invariants, and
named proof constants live under `DecoupledConsensus/State/Proof`.
`DecoupledConsensus/State/Properties.lean` is the proved property facade,
showing which statements have proofs without exposing proof scripts.
`DecoupledConsensus/AccountableSafety.lean` is the section-2 public facade.
Section 3 store definitions live under `DecoupledConsensus/Store`.

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
an id against the current chain head. The safety theorem assumes
`Block.IdInjectiveOnAncestors B₁ B₂`, modelling collision-free block hashes
only over the two chain histories under consideration.

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

Unresolved or non-fresh target sides are ignored by `processVoteCore`, so they
do not enter `targets` or `timeouts`. The finalize gate is intentionally
separate and independent of target freshness: a vote can affect `P` whenever
its finalize commitment matches the current `(hj, J.id)` after the core vote
update.

## Finality Predicate

`State` stores `F : Block n` but no finalized height. The public finality
predicate records the height as certificate data and scopes the evidence to a
witnessing chain tip:

```lean
def IsFinalized (C : Block n) (h_f : ℕ) (B : Block n) : Prop :=
  ∃ chain : Chain n B, ∃ hC : C ≼ B,
    (stateOf chain).F = C ∧
    FinalizedCertificate chain C h_f hC
```

For non-genesis finality, the certificate contains a finalize quorum for
`(h_f, C.id)`, a justify quorum for `C.id` at `h_f`, the height-closed fact
`(stateOf (chain.subchain hC)).h = h_f`, and that the witnessing chain has
advanced past `h_f`.

## Main Safety Surface

The minimal state-machine review surface is the model plus finalization
vocabulary and three statements in `DecoupledConsensus/State/Statements.lean`:

- `State.IsFinalized`
- `State.MainSafetyStatement`
- `State.FinalizedBlocksFormChainStatement`
- `State.AccountableSafetyStatement`

All other state lemmas and theorems are proof internals used to discharge those
statements. `DecoupledConsensus/State/Properties.lean` has the short proved
facade, for example:

```lean
theorem main_safety_property {f : ℕ} :
    MainSafetyStatement n f :=
  proof_main_safety_property
```

The final statement has the collision-free id premise explicitly, while
tip-scoped finalization evidence is bundled by `State.IsFinalized`:

```lean
def AccountableSafetyStatement (n f : ℕ) : Prop :=
  n = 3 * f + 1 →
    ∀ {B₁ B₂ C C' : Block n} {h_f h_f' : ℕ},
      Block.IdInjectiveOnAncestors B₁ B₂ →
        State.IsFinalized C h_f B₁ →
          State.IsFinalized C' h_f' B₂ →
            AtLeastFThirdSlashable f ∨ C ~ C'
```

This scopes id injectivity to ancestors of the two witnessing chain tips. The
protocol can use opaque ids, while the proof can turn equal ids into equal
blocks exactly where the compared histories require it. Slashability is stated
structurally over votes included in chain histories; a concrete signature layer
can authenticate those payloads without changing the safety theorem.

## Current Status

The Lean development currently proves:

- quorum intersection in both strict and BFT forms;
- all transition field-preservation lemmas used by the invariants;
- chain invariants for targets, slots, `J`, `F`, `hj`, `sh`, and witnesses;
- `advance_witness` without a model-level assumption;
- the three public state statements named main safety, finalized blocks form a
  chain, and accountable safety.
