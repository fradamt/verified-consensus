module
public import DecoupledConsensusModel.Execution.Setup
public import DecoupledConsensusModel.Protocol.Grades
public import DecoupledConsensusModel.Protocol.Tick
public import DecoupledConsensusModel.Execution.Objects
public import DecoupledConsensusModel.Protocol.Handlers

@[expose] public section

/-!
# `DecoupledConsensusModel/Execution/Node.lean`

Purpose: execution — the node profile, its receipt for one event, and the node state transition.
Paper: generic execution adapter around the Section 7 protocol.

Defines: NamedNodeState, NamedNode.tick, and NamedNode.process.

Read after: `DecoupledConsensusModel.Execution.Setup`, `DecoupledConsensusModel.Protocol.Grades`, `DecoupledConsensusModel.Protocol.Tick`
Read next: `DecoupledConsensusModel.Execution.Instance`.

State read: `Setup`, node state, protocol records, and event/run observations.
State written: execution state, receipts, handles, or the protocol-spec value returned by the adapter.

Representation notes: Execution records keep named payloads beside erased protocol state; adapters preserve the protocol definitions.
-/

-- ── from Execution/NamedProfile.lean ──
section
/-! Closed named behavior with the supplied Setup unchanged.
The caller supplies the prepared cache. Phase completion and final cache
clipping belong to the later named-node composition. The existing named tick
already fixes carried admission, proposal row selection and named signing. -/
namespace DecoupledConsensusModel.Execution.NamedProfile
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The selected grade behavior is the existing frame contract. -/
def gradeContract (cache : DecoupledConsensusModel.Protocol.Cache V) : Protocol.GradeContract V :=
  DecoupledConsensusModel.Protocol.frameContract cache

/-- Call the existing named tick once with the original environment, healing
config, height config and node identity. Preserve its full returned payloads. -/
def tick (S : Setup V) (cache : DecoupledConsensusModel.Protocol.Cache V) (v : V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time) :
    Protocol.NamedStore V × Protocol.NamedRecord × List (NamedObject V) :=
  Protocol.NamedTick.tick (gradeContract cache) S.E S.hc S.cfg (S.node v) st record t

end DecoupledConsensusModel.Execution.NamedProfile
end

-- ── from Execution/NamedReceipt.lean ──
section
/-! Full named ingress checks and closed local dispatch. The existing wire-shape
test uses only the block projection. Dependencies and processed markers retain
full named identity. The dispatcher calls the existing named/core handlers. -/
namespace DecoupledConsensusModel.Execution.NamedReceipt
variable {V : Type} [DecidableEq V]

/-- Apply the existing three wire-shape checks to the full named object. -/
def wellFormed [Fintype V] (S : Setup V) : NamedObject V → Bool
  | .block B => Protocol.carried_votes_well_formed B.erase &&
      Protocol.carried_support_well_formed B.erase &&
      B.erase.gf_votes.all (fun u => decide (u.val_index ∈ S.E.committee u.slot))
  | .gfVote u => Protocol.vote_well_formed S.E u
  | .attest _ => true

/-- Blocks require their exact named parent. Vote resolution is a later read. -/
def depsPresent (st : Protocol.NamedStore V) : NamedObject V → Bool
  | .block B => decide (B.parent ∈ st.bodies)
  | .gfVote _ => true
  | .attest _ => true

/-- Mark the full admitted object, including the original named row. -/
def processed (st : Protocol.NamedStore V) : NamedObject V → Bool
  | .block B => decide (B ∈ st.bodies)
  | .gfVote u => decide (u ∈ st.core.pool u.slot)
  | .attest a => decide (a ∈ st.sg_rows a.round)

/-- A block that conflicts with the node's finalized block (neither is an
ancestor of the other) is excluded for good, since finality only extends;
votes and attestations are never excluded. -/
def excludes (st : Protocol.NamedStore V) : NamedObject V → Bool
  | .block B => !Block.compatible st.core.F B.erase
  | .gfVote _ => false
  | .attest _ => false

/-- The block branch admits carried rows (`.alsoCarried`) and forwards S.cfg unchanged. -/
def process [Fintype V] (S : Setup V) (st : Protocol.NamedStore V) :
    NamedObject V → Protocol.NamedStore V
  | .block B => Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B
  | .gfVote u => { st with core := Protocol.on_goldfish_vote_checked S.E st.core u }
  | .attest a => Protocol.NamedAdmission.admit_row S.hc st a

end DecoupledConsensusModel.Execution.NamedReceipt
end

-- ── from Execution/NamedNode.lean ──
section
/-! One named node with the existing phase cache. The incoming store supplies
phase reads before clock staging. The existing named tick supplies all duties,
and the returned finalized root supplies the final cache clip. -/
namespace DecoupledConsensusModel.Execution

structure NamedNodeState (V : Type) where
  st : Protocol.NamedStore V
  record : Protocol.NamedRecord
  cache : DecoupledConsensusModel.Protocol.Cache V

namespace NamedNode
variable {V : Type} [DecidableEq V]

def initial : NamedNodeState V :=
  ⟨Protocol.NamedStore.initial, Protocol.NamedRecord.initial, DecoupledConsensusModel.Protocol.initialCache⟩

/-- Complete phases from the incoming store, then call the closed tick once. -/
def tick [Fintype V] (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time) :
    NamedNodeState V × List (NamedObject V) :=
  let c := DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache
  let out := NamedProfile.tick S c v n.st n.record t
  (⟨out.1, out.2.1, DecoupledConsensusModel.Protocol.clipCache out.1.core.F c⟩, out.2.2)

/-- A receipt retains the signing record and clips the existing cache. -/
def process [Fintype V] (S : Setup V) (n : NamedNodeState V) (o : NamedObject V) :
    NamedNodeState V :=
  let st := NamedReceipt.process S n.st o
  ⟨st, n.record, DecoupledConsensusModel.Protocol.clipCache st.core.F n.cache⟩

end NamedNode
end DecoupledConsensusModel.Execution
end

end
