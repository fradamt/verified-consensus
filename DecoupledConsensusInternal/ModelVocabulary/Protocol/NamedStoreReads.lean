module
public import DecoupledConsensusModel

@[expose] public section

/-!
# Named store and node-state read facade

Core store reads on `NamedStore` and `NamedNodeState` are explicit forwards to
the selected named runtime. No field is reconstructed; named `bodies` and
`sg_rows` remain available through their own names.
-/
namespace DecoupledConsensusModel.Protocol.NamedStore
variable {V : Type} [DecidableEq V] [Fintype V]

@[reducible] def t (st : NamedStore V) : Time := st.core.t
@[reducible] def s (st : NamedStore V) : Slot := st.core.s
@[reducible] def T (st : NamedStore V) : Finset (Block V) := st.core.T
@[reducible] def F (st : NamedStore V) : Block V := st.core.F
@[reducible] def J (st : NamedStore V) : Block V := st.core.J
@[reducible] def h_j (st : NamedStore V) : Height := st.core.h_j
@[reducible] def h_max (st : NamedStore V) : Height := st.core.h_max
@[reducible] def σ (st : NamedStore V) : Block V → Protocol.ChainState V := st.core.σ
@[reducible] def live_confirmed (st : NamedStore V) : Block V := st.core.live_confirmed
@[reducible] def latest_confirmed (st : NamedStore V) : Block V := st.core.latest_confirmed
@[reducible] def latest_stable (st : NamedStore V) : Block V := st.core.latest_stable
@[reducible] def sg_pool (st : NamedStore V) (r : Round) : Finset (CombinedAttestation V) :=
  st.core.sg_pool r
@[reducible] def timestamp_block (st : NamedStore V) := st.core.timestamp_block
@[reducible] def timestamp_vote (st : NamedStore V) := st.core.timestamp_vote
@[reducible] def timestamp_sg_vote (st : NamedStore V) := st.core.timestamp_sg_vote
@[reducible] def gf_votes (st : NamedStore V) := st.core.gf_votes
@[reducible] def pool (st : NamedStore V) := st.core.pool
@[reducible] def toHealing (st : NamedStore V) : Protocol.HealingStore V := st.core.toHealing

/-- The full named rows whose SG projection is the core pool bucket. -/
def namedPool (st : NamedStore V) (r : Round) : Finset (NamedAttestation V) :=
  (st.sg_rows r).toFinset

end DecoupledConsensusModel.Protocol.NamedStore

namespace DecoupledConsensusModel.Execution.NamedNodeState
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The observers return the prepared node state used by the named duties; all
core store fields remain readable on that state. -/
@[reducible] def toHealing (n : NamedNodeState V) : Protocol.HealingStore V := n.st.core.toHealing
@[reducible] def s (n : NamedNodeState V) : Slot := n.st.core.s
@[reducible] def T (n : NamedNodeState V) : Finset (Block V) := n.st.core.T
@[reducible] def F (n : NamedNodeState V) : Block V := n.st.core.F
@[reducible] def J (n : NamedNodeState V) : Block V := n.st.core.J
@[reducible] def h_j (n : NamedNodeState V) : Height := n.st.core.h_j
@[reducible] def h_max (n : NamedNodeState V) : Height := n.st.core.h_max
@[reducible] def σ (n : NamedNodeState V) : Block V → Protocol.ChainState V := n.st.core.σ
@[reducible] def live_confirmed (n : NamedNodeState V) : Block V := n.st.core.live_confirmed
@[reducible] def pool (n : NamedNodeState V) := n.st.core.pool
@[reducible] def timestamp_block (n : NamedNodeState V) := n.st.core.timestamp_block

end DecoupledConsensusModel.Execution.NamedNodeState

/- The record projections forward the named record's core fields. -/
namespace DecoupledConsensusModel.Protocol.NamedRecord

@[reducible] def target (Λ : NamedRecord) : Height → Option BlockId := Λ.legacy.target
@[reducible] def timeout (Λ : NamedRecord) : Height → Bool := Λ.legacy.timeout
@[reducible] def lock (Λ : NamedRecord) : Height → Option BlockId := Λ.legacy.lock

end DecoupledConsensusModel.Protocol.NamedRecord

end
