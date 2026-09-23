module
public import DecoupledConsensusModel.Protocol.Duties.Inputs
public import DecoupledConsensusModel.Protocol.Duties.Proposals

/-!
# `DecoupledConsensusModel/Protocol/Duties.lean`

Purpose: Section 7, block 3 — the validator duties.
Paper: `docs/PROTOCOL.md` `sec:public-handlers`; algorithm block: `alg:duties`.

Defines: the duty input and proposal modules collected by its imports.

Read after: `DecoupledConsensusModel.Protocol.Duties.Inputs`, `DecoupledConsensusModel.Protocol.Duties.Proposals`
Read next: `DecoupledConsensusModel.Protocol.Handlers`.

State read: the protocol environment, schedule, store layers, and the view inputs named by the definitions.
State written: the returned store, chain state, record, or view value; pure readers write no state.

Representation notes: Typed Lean records, finite collections, and projections preserve the executable protocol representation. This module states no proof theorem.
-/
