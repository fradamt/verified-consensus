module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.WeakGenesisCanonicalProposalDutyPins
public import DecoupledConsensusProofs.Protocol.Grades.WeakGenesisVoteStoresPositiveClosed
public import DecoupledConsensusProofs.Objects.GSTZeroProposalEvaluationCore
public import DecoupledConsensusProofs.Protocol.Grades.WeakConfirmationReadAnchorsNamed
public import DecoupledConsensusProofs.Execution.WeakConfirmationReadBandCandidateClosed
public import DecoupledConsensusProofs.Protocol.Schedule.CanonicalSuffixDutyNamed

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Closed named GST-zero canonical proposal duty -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

theorem canonicalProposalDuty_positive_of_gstZero_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    CanonicalProposalDutyAt S rho s B := by
  exact canonicalProposalDuty_positive_of_gstZero_named_of_pins
    honestVoteStoresExtend_positive_of_gstZero
    Protocol.honestVotesName_of_voteStoresExtend_core
    preparedConfirmationAnchor_preceq_voterHeadAt_of_gstZero
    (fun S _rho h _s hs hhor hprop _B hB _hstores =>
      proposedBlock_confirmationBandAndCandidate_of_gstZero
        S h hs hhor hprop hB)
    Protocol.CanonicalSuffixProposalStoreFacts.duty_core
    S h hs hhor hprop hB

#print axioms canonicalProposalDuty_positive_of_gstZero_named

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
