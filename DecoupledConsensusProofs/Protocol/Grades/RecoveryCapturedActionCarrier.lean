module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionConfirmationCore
public import DecoupledConsensusProofs.Execution.RecoveryActionUpperCarrier
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryProposalConfirmationRead
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusInternal.Execution.Run
public import DecoupledConsensusProofs.Execution.Concentration
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

theorem actionStoreAt_eq_update_confirmation_confStore
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    (actionStoreAt S rho v r).st.core =
      Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache)
        S.E S.hc
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r))
        (S.hc.opening_slot r) := by
  exact actionStoreAt_eq_update_confirmation_openingConfStore S rho v r







/-! The retired carrier ceiling remains outside the named proof surface. -/

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
