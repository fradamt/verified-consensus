module
public import DecoupledConsensusStatements.Instantiation.Proposals
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedAdmissible
public import DecoupledConsensusModel.Protocol.Duties.Proposals
public import DecoupledConsensusModel.Protocol.Duties.Proposals

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The shared proposal input the named duty reads on that prepared read. -/
def proposalInputAt (S : Setup V) (rho : Run V) (s : Slot) : Protocol.ProposalInput V :=
  let n := proposerReadAt S rho s
  Protocol.proposal_input_with (NamedProfile.gradeContract n.cache) S.E S.hc
    (S.node (S.E.proposer s)) n.st.core.toHealing

/-- The parent the honest proposer selects: the input's parent field. -/
def proposedParent (S : Setup V) (rho : Run V) (s : Slot) : Block V :=
  (proposalInputAt S rho s).parent

end DecoupledConsensusModel.Proofs.HealingSurface

end
