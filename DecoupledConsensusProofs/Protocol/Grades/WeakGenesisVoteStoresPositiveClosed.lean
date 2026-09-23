module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.WeakGenesisVoteStoresPositivePins
public import DecoupledConsensusProofs.Execution.WeakGenesisVoteStoresSuccClosed
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakGenesisProposalOneNamed

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Closed positive GST-zero prepared vote-store extension -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

theorem honestVoteStoresExtend_positive_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    ∀ v ∈ rho.honest,
      Proofs.Optimistic.NamedVoteStoreExtends S rho v s
        (namedWalkTargetTree S rho s v B)
        (proposedParent S rho s) B := by
  exact honestVoteStoresExtend_positive_of_gstZero_of_pins
    honestVoteStoresExtend_succ_of_gstZero
    honestVoteStoresExtend_one_of_gstZero_named
    S h hs hhor hprop hB

#print axioms honestVoteStoresExtend_positive_of_gstZero

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
