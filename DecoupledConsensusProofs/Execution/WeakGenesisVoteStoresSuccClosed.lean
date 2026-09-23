module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGenesisVoteStoresSuccPins
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakProposalCandidateNamed
public import DecoupledConsensusProofs.Protocol.Grades.WeakProposalPivotNamed
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.PreparedProtectedProposalPivotFrozenBandNamed
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.PreparedProtectedProposalPivotCaptureNamed
public import DecoupledConsensusProofs.Execution.ProposalScoreEqNamed

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Closed later GST-zero prepared vote-store extension -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

theorem honestVoteStoresExtend_succ_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {d : Slot} (hd : 1 ≤ d)
    (hhor : Protocol.confirmation_time S.E (d + 1) ≤ rho.horizon)
    (hprop : S.E.proposer (d + 1) ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho (d + 1) = some B) :
    ∀ v ∈ rho.honest,
      Proofs.Optimistic.NamedVoteStoreExtends S rho v (d + 1)
        (namedWalkTargetTree S rho (d + 1) v B)
        (proposedParent S rho (d + 1)) B := by
  exact honestVoteStoresExtend_succ_of_gstZero_of_pins
    proposedBlock_voterCandidate_of_gstZero_named
    exists_preparedProtectedProposalPivot_of_gstZero
    PreparedProtectedProposalPivot.frozenBandInputs
    namedProposalPivotSuffixTransfer_of_riseLeOne_core
    PreparedProtectedProposalPivot.preceq_proposalFreeHead_core
    namedProposalScoreEq_afterGST_core
    S h hd hhor hprop hB

#print axioms honestVoteStoresExtend_succ_of_gstZero

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
