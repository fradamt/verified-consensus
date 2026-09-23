module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.WeakGenesisLatestAtProposalPins
public import DecoupledConsensusProofs.Execution.WeakGenesisCanonicalProposalDutyClosed

@[expose] public section

/-! # Closed GST-zero latest-at-proposal field -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Statements

variable {V : Type} [DecidableEq V] [Fintype V]

theorem latestAtProposalField_of_weakGenesis
    (S : Setup V) : ∀ rho, WeakGenesis S rho →
      LatestAtProposalField S rho 0 := by
  exact latestAtProposalField_of_weakGenesis_of_pins
    canonicalProposalDuty_positive_of_gstZero_named S

#print axioms latestAtProposalField_of_weakGenesis

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
