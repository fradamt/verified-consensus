module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalPivot
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalWalkTransportCore
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.Handlers.HonestProposalAdmission
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalVoteDuty

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Named prepared vote-head bridge -/

/-- A named vote-store extension identifies the prepared vote-duty head with
the named proposal. The proposal witness is retained in the statement so
callers do not fall back to the retired total proposal reader. -/
theorem voterHeadAt_eq_proposedBlockAt_of_namedVoteStoreExtends
    (S : Setup V) {rho : Run V} {s : Slot} {v : V}
    {tree₀ : Finset (Block V)} {P : NamedBlock V}
    (hP : Statements.Instantiation.proposedBlockAt S rho s = some P)
    (hstore : Proofs.Optimistic.NamedVoteStoreExtends S rho v s tree₀
      (Proofs.HealingSurface.proposedParent S rho s) P) :
    Internal.voterHeadAt S rho v s = P.erase := by
  exact hstore.head

#print axioms voterHeadAt_eq_proposedBlockAt_of_namedVoteStoreExtends

end Protocol
end DecoupledConsensusModel

end
