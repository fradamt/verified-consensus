module
public import DecoupledConsensusStatements.Generic.Interface
public import DecoupledConsensusStatements.Generic.Constants
public import DecoupledConsensusStatements.Generic.Properties
public import DecoupledConsensusStatements.Generic.Conditions
public import DecoupledConsensusStatements.Generic.Regimes
public import DecoupledConsensusStatements.Generic.Claims
public import DecoupledConsensusStatements.Instantiation

/-!
# Decoupled consensus statements

Purpose: provide the complete manual review surface in dependency order.
An auditor reads the generic execution model, then `Interface`, `Constants`,
`Properties`, `Conditions`, `Regimes`, `Claims`, and finally the concrete
`Instantiation`.

Defines: no declarations; this is the contents page for the statement
library. The generic files state the reusable contract. The instantiation
fills it for the selected protocol.

Read after: `DecoupledConsensusModel.Generic.Run` and `Env`.
Read next: `DecoupledConsensusStatements.Generic.Interface`.
-/
