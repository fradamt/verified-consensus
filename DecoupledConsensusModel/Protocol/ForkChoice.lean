module
public import DecoupledConsensusModel.Protocol.ForkChoice.Views
public import DecoupledConsensusModel.Protocol.ForkChoice.Goldfish
public import DecoupledConsensusModel.Protocol.ForkChoice.Head

/-!
# `DecoupledConsensusModel/Protocol/ForkChoice.lean`

Purpose: Section 7, block 2a — the fork choice: views, the Goldfish and FG trees, and the head.
Paper: `docs/PROTOCOL.md` `sec:complete-store`; algorithm block: `alg:goldfish` / `alg:fg-store`.

Defines: the fork-choice modules collected by its imports.

Read after: `DecoupledConsensusModel.Protocol.ForkChoice.Views`, `DecoupledConsensusModel.Protocol.ForkChoice.Goldfish`, `DecoupledConsensusModel.Protocol.ForkChoice.Head`
Read next: `DecoupledConsensusModel.Protocol.Grades`.

State read: the protocol environment, schedule, store layers, and the view inputs named by the definitions.
State written: the returned store, chain state, record, or view value; pure readers write no state.

Representation notes: Typed Lean records, finite collections, and projections preserve the executable protocol representation. This module states no proof theorem.
-/
