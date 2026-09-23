module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakConfirmationReadBandCandidateNamed
public import DecoupledConsensusProofs.Generic.WeakProposalAdmissionNamed
public import DecoupledConsensusProofs.Protocol.Grades.WeakGenesisVoteStoresPositiveClosed

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Closed current proposal band and prepared confirmation candidate -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

theorem proposedBlock_confirmationBandAndCandidate_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    ∀ v ∈ rho.honest,
      (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core.h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg B).h ∧
        B.erase ∈ confTree (Proofs.Optimistic.confStore S rho v s) := by
  exact proposedBlock_confirmationBandAndCandidate_of_gstZero_of_pins
    proposedBlock_admittedBefore_vote_of_gstZero_named
    S h hs hhor hprop hB
    (honestVoteStoresExtend_positive_of_gstZero S h hs hhor hprop hB)

#print axioms proposedBlock_confirmationBandAndCandidate_of_gstZero

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
