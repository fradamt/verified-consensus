module
public import DecoupledConsensusModel.Execution.Run

@[expose] public section

/-!
# Instantiation proposal observers

Purpose: expose the prepared proposal read and proposal-duty output for the
selected protocol.
An auditor checks that the observers use the prepared read and do not add a
proof-side assumption.

Defines: `proposerReadAt` and `proposedBlockAt`.
Read after: the model execution and proposal-duty definitions.
Read next: the instantiation contents page.
-/
namespace DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The prepared read of slot `s`'s proposer at the proposal time: strict read,
clock staged, and cache prepared. -/
def proposerReadAt (S : Setup V) (rho : Run V) (s : Slot) : NamedNodeState V :=
  NamedActionReads.confirmationReadAt S rho (S.E.proposer s) (Protocol.proposal_time S.E s)

/-- The block the named proposal duty computes, with the full pool-and-carried
attestation rows and source label, if the parent body is retained. -/
def proposedBlockAt (S : Setup V) (rho : Run V) (s : Slot) : Option (NamedBlock V) :=
  let n := proposerReadAt S rho s
  Protocol.NamedActions.proposal_with (NamedProfile.gradeContract n.cache) .poolAndCarried
    S.E S.hc (S.node (S.E.proposer s)) n.st

end DecoupledConsensusModel.Statements.Instantiation

end
