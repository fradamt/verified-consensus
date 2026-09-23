module
public import DecoupledConsensusModel.Generic.Run
public import DecoupledConsensusModel.Execution.Node
public import DecoupledConsensusModel.Execution.Run
public import DecoupledConsensusModel.Execution.Setup

@[expose] public section

/-!
# `DecoupledConsensusModel/Execution/Instance.lean`

Purpose: execution — the protocol spec instance: the Section 7 protocol as a generic protocol.
Paper: generic execution adapter around the Section 7 protocol.

Defines: handles and spec, the concrete ProtocolSpec adapter.

Read after: `DecoupledConsensusModel.Generic.Run`, `DecoupledConsensusModel.Execution.Node`, `DecoupledConsensusModel.Execution.Run`
Read next: `DecoupledConsensusStatements.Instantiation`.

State read: `Setup`, node state, protocol records, and event/run observations.
State written: execution state, receipts, handles, or the protocol-spec value returned by the adapter.

Representation notes: Execution records keep named payloads beside erased protocol state; adapters preserve the protocol definitions.
-/

-- ── from Execution/Instance.lean ──
namespace DecoupledConsensusModel
namespace Execution

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The protocol handler-call relation used by `Generic.ProtocolSpec`. It covers
direct block, Goldfish-vote, and attestation calls, and rows carried by a block
when that block enters the relevant named collection. It records a call, not
whether the handler accepts the object. -/
def handles (S : Setup V) (n : NamedNodeState V) (e : NamedEvent V) :
    NamedObject V → Prop :=
  let blockCall (B : NamedBlock V) (before : Protocol.NamedStore V) : Prop :=
    (∃ t : Time, e = .deliver e.node (.block B) t ∧ before = n.st) ∨
      ∃ t : Time, e = .tick e.node t ∧
        NamedObject.block B ∈ (NamedNode.tick S e.node n t).2 ∧
        before = Protocol.NamedStore.setClock S.E n.st t
  fun
  | .block B =>
      (∃ t : Time, e = .tick e.node t ∧
        NamedObject.block B ∈ (NamedNode.tick S e.node n t).2) ∨
        ∃ t : Time, e = .deliver e.node (.block B) t
  | .gfVote u =>
      ((∃ t : Time, e = .tick e.node t ∧
          NamedObject.gfVote u ∈ (NamedNode.tick S e.node n t).2) ∨
        ∃ t : Time, e = .deliver e.node (.gfVote u) t) ∨
        ∃ (B : NamedBlock V) (j : Nat) (before : Protocol.NamedStore V),
          blockCall B before ∧ B.erase ∉ before.core.T ∧
          B.erase ∈ (NamedReceiptCalls.postCore S before B).core.T ∧
          B.gf_votes[j]? = some u
  | .attest a =>
      ((∃ t : Time, e = .tick e.node t ∧
          NamedObject.attest a ∈ (NamedNode.tick S e.node n t).2) ∨
        ∃ t : Time, e = .deliver e.node (.attest a) t) ∨
        ∃ (B : NamedBlock V) (j : Nat) (before : Protocol.NamedStore V),
          blockCall B before ∧ B ∉ before.bodies ∧
          B ∈ (NamedReceiptCalls.postCore S before B).bodies ∧
          B.attestations[j]? = some a

/-! `spec` binds the generic hooks to the selected named runtime: `tick` and
`process` are the node transitions, `wellFormed`/`depsPresent`/`processed`/
`excludes` are receipt checks, `handles` is the observation relation, and `carries` describes
block-contained vote and attestation rows. -/
def spec (S : Setup V) : Generic.ProtocolSpec V where
  State := NamedNodeState V
  Object := NamedObject V
  init := NamedNode.initial
  tick := NamedNode.tick S
  process := NamedNode.process S
  author := NamedObject.author
  wellFormed := NamedReceipt.wellFormed S
  depsPresent := fun n o => NamedReceipt.depsPresent n.st o
  processed := fun n o => NamedReceipt.processed n.st o
  excludes := fun n o => NamedReceipt.excludes n.st o
  carries := fun o o' =>
    match o with
    | .block B =>
        (∃ u ∈ B.gf_votes, o' = .gfVote u) ∨
          (∃ a ∈ B.attestations, o' = .attest a)
    | _ => False
  handles := handles S

end Execution
end DecoupledConsensusModel

end
