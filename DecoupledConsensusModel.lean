module
public import DecoupledConsensusModel.Objects.Identifiers
public import DecoupledConsensusModel.Objects.Time
public import DecoupledConsensusModel.Objects.Weights
public import DecoupledConsensusModel.Objects.Blocks
public import DecoupledConsensusModel.Objects.NamedBlocks
public import DecoupledConsensusModel.Objects.Parameters
public import DecoupledConsensusModel.Generic.Run
public import DecoupledConsensusModel.Generic.Env
public import DecoupledConsensusModel.Execution.Objects
public import DecoupledConsensusModel.Protocol.Schedule
public import DecoupledConsensusModel.Protocol.StoreBase
public import DecoupledConsensusModel.Protocol.ChainState
public import DecoupledConsensusModel.Protocol.ForkChoice.Views
public import DecoupledConsensusModel.Protocol.ForkChoice.Goldfish
public import DecoupledConsensusModel.Protocol.ValidatorClient
public import DecoupledConsensusModel.Protocol.Grades
public import DecoupledConsensusModel.Protocol.ForkChoice.Head
public import DecoupledConsensusModel.Protocol.ForkChoice
public import DecoupledConsensusModel.Protocol.Duties.Inputs
public import DecoupledConsensusModel.Protocol.Store
public import DecoupledConsensusModel.Protocol.Evidence
public import DecoupledConsensusModel.Protocol.Handlers
public import DecoupledConsensusModel.Protocol.Duties.Proposals
public import DecoupledConsensusModel.Protocol.Duties
public import DecoupledConsensusModel.Protocol.Tick
public import DecoupledConsensusModel.Execution.Setup
public import DecoupledConsensusModel.Execution.Node
public import DecoupledConsensusModel.Execution.Run
public import DecoupledConsensusModel.Execution.Instance

/-!
# `DecoupledConsensusModel.lean`

Purpose: the Section 7 protocol Model and the generic execution adapter.
Paper: the protocol model; the imported subject files name the paper algorithm blocks.

Defines: the four reading parts: `Generic`, `Objects`, `Protocol`, and `Execution`.

Read after: none; this is the contents page.
Read next: `Generic.Run` → `Generic.Env` → `Objects` → `Protocol` → `Execution`.

Reading order:
* `Generic/` — the execution model used by the claims.
* `Objects/` — identifiers, parameters, weights, and wire objects.
* `Protocol/` — Section 7, in algorithm-block order.
* `Execution/` — the adapter from the protocol to generic runs.

State read: none; this page only orders imports.
State written: none; this page defines no declarations.

Representation notes: this is an import-only contents page.
MODEL_MAP rows: the four reading parts and their imported modules.
-/
