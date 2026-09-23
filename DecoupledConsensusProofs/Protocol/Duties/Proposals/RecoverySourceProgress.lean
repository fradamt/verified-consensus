module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.ChainState.NjGap
public import DecoupledConsensusProofs.Protocol.ChainState.ProgressQuorumCore
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusInternal.Healing
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Generic.FrontierCoverage
public import DecoupledConsensusProofs.Protocol.ChainState.Main
public import DecoupledConsensusInternal.Execution.Assumptions
public import DecoupledConsensusProofs.Protocol.Handlers.NamedStore
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordFresh
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordTargetHistory
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.ChainState.NamedNjGap
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecoveryTimeout
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionActivity

@[expose] public section

/-!
# Operational meaning of a strict recovery source

`FrontierHeightRun` proves the exact source-height split. A source is at the
recovery height, or the source action store has `h_max > H`. This file records
what the strict branch buys without another protocol assumption:

* the source is a genuine run block and a strict descendant of the common
  graded block;
* the source validator's local `h_max > H` fact persists at all later reads.

This local fact is not the all-honest `h_j` predicate
`HonestStoresCrossedAt`, and it does not force a later proposal parent to select
the source branch. The last theorem exposes the exact source-selection premise
that upgrades the strict branch to `RecoveryActivationRun`'s parent-height
outcome.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The virtual post-confirmation action store agrees with the named derivation
on every retained named body. -/
theorem derivedStateAgrees_actionStoreAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (v : V) (r : Round) :
    Internal.NamedDerivedStateAgrees S.E S.cfg (actionStoreAt S rho v r).st := by
  intro D hD
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
    S rho (S.a r) v D hDpre
  simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
    NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
    NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hview

/- The action-read activity is supplied separately from the named grade. -/






end HealingSurface
end Proofs
end DecoupledConsensusModel

#print axioms DecoupledConsensusModel.Proofs.HealingSurface.derivedStateAgrees_actionStoreAt

end
