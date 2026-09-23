module
public import DecoupledConsensusModel.Protocol.Handlers
public import DecoupledConsensusModel.Protocol.Duties.Proposals
public import DecoupledConsensusModel.Execution.Objects

@[expose] public section

/-!
# `DecoupledConsensusModel/Protocol/Tick.lean`

Purpose: Section 7, block 1 — on_tick, which drives the duties of block 3 and therefore sits above them.
Paper: `docs/PROTOCOL.md` `sec:public-handlers`; algorithm block: `alg:on-tick`.

Defines: namedOps, tick.

Read after: `DecoupledConsensusModel.Protocol.Handlers`, `DecoupledConsensusModel.Protocol.Duties.Proposals`, `DecoupledConsensusModel.Execution.Objects`
Read next: `DecoupledConsensusModel.Execution.Node`.

State read: the protocol environment, schedule, store layers, and the view inputs named by the definitions.
State written: the returned store, chain state, record, or view value; pure readers write no state.

Representation notes: Typed Lean records, finite collections, and projections preserve the executable protocol representation. This module states no proof theorem.
MODEL_MAP rows: namedOps, tick.
-/

-- ── from Protocol/NamedTick.lean ──
/-! Closed named duties bound to the shared tick scheduler. Clock and slot
use the core store; emitted payloads retain named bodies and rows. -/
namespace DecoupledConsensusModel.Protocol.NamedTick
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

def namedOps (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) :
    TickScheduler.TickOps (NamedStore V) Protocol.NamedRecord
      (NamedBlock V) (GoldfishVote V) (NamedAttestation V) where
  clock := fun st t s => { st with core := { st.core with t := t, s := s } }
  slot := fun st => st.core.s
  proposal := NamedDuties.propose_block_with gc E hc cfg nd
  vote := NamedDuties.goldfish_vote_with gc E hc nd
  confirmation := NamedDuties.update_confirmation_with gc E hc
  attestation := NamedDuties.attest_with gc E hc nd

def tick (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) :
    NamedStore V × Protocol.NamedRecord × List (NamedObject V) :=
  TickScheduler.runWith E hc nd (namedOps gc E hc cfg nd)
    NamedObject.block NamedObject.gfVote NamedObject.attest
    (fun st record emitted => (st, record, emitted)) st record t

end DecoupledConsensusModel.Protocol.NamedTick

end
