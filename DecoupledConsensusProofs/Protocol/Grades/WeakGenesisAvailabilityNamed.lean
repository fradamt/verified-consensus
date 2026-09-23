module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.WeakLiveMonotoneNamed
public import DecoupledConsensusProofs.Protocol.ChainState.GSTZeroSixFieldBypassNamed

@[expose] public section

/-! # Available confirmations from weak genesis -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Weak genesis supplies compatibility, record monotonicity, and genuine
positive-slot confirmation renewal from time zero. -/
theorem availableConfirmationsFrom_of_weakGenesis_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho) :
    AvailableConfirmationsFrom S rho 0 := by
  have hchain := availableChainFrom_of_weakGenesis_named S h
  refine ⟨hchain.1, hchain.2.1, ?_⟩
  intro s hs _ hhor v hv
  exact genuineConfirmationAt_positive_of_weakGenesis S h hs hhor hv

#print axioms availableConfirmationsFrom_of_weakGenesis_named

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
