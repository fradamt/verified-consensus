import DecoupledConsensusProofs.ReviewTheorem
import DecoupledConsensusInternal.Legacy.Definitions.FinalityDeadlinesInternal

/-! This validation script checks the exact type of `concreteConsensus` and
prints the axiom dependencies of the closed review theorem and its proof-side
supporting results. -/
#print axioms DecoupledConsensusModel.Proofs.concreteConsensus
#print axioms DecoupledConsensusModel.Proofs.reviewedInternal
#print axioms DecoupledConsensusModel.Proofs.legacyConsensus
#print axioms DecoupledConsensusModel.Proofs.recoveryProducesHealedState
#print axioms DecoupledConsensusModel.Proofs.finalitySafety
#print axioms DecoupledConsensusModel.Proofs.voteSafetyOfClients
#print axioms DecoupledConsensusModel.Proofs.finalizedPrefix
#print axioms DecoupledConsensusModel.Proofs.nestedOutputs
#print axioms DecoupledConsensusModel.Proofs.gstZeroGuarantees
#print axioms DecoupledConsensusModel.Proofs.boundedSafety
#print axioms DecoupledConsensusModel.Proofs.voteSafety
#print axioms DecoupledConsensusModel.Proofs.leakFairness
#print axioms DecoupledConsensusModel.Proofs.stableSafety
#print axioms DecoupledConsensusModel.Proofs.liveness
#print axioms DecoupledConsensusModel.Proofs.asynchronyResilience
#print axioms DecoupledConsensusModel.Proofs.honestProposalConfirmation
#print axioms DecoupledConsensusModel.Proofs.availableChainGrowth
#print axioms DecoupledConsensusModel.Proofs.stableRecordGrowth
#print axioms DecoupledConsensusModel.Proofs.finalizedChainGrowth
#print axioms DecoupledConsensusModel.Proofs.honestProposalFinalization
#print axioms DecoupledConsensusModel.Statements.finalityStartup_pos
#print axioms DecoupledConsensusModel.Proofs.HealingSurface.finalityDeadline_eq_recurringFinalityDeadline
#print axioms DecoupledConsensusModel.Proofs.HealingSurface.rawRecoveryAndRecurrence_le_recurringFinalityDeadline

-- Internal proof-side results, not bundle fields.
#print axioms DecoupledConsensusModel.Proofs.heightProgress

namespace DecoupledConsensusModel.Proofs

variable {V : Type} [DecidableEq V] [Fintype V]

example (S : Execution.Setup V) : Statements.Instantiation.Consensus S :=
  concreteConsensus S

end DecoupledConsensusModel.Proofs
