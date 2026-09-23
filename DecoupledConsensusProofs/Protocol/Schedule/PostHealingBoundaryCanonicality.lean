module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingContinuation
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroActionHead
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmission
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusInternal.Legacy.Definitions.NamedHeadReads
public import DecoupledConsensusInternal.Definitions.NamedLifecycle

@[expose] public section

/-!
# Canonicality after the healed boundary

Pure time and store transport is restated to the named runtime. The remaining
head-recursion declarations stay as explicit open items until their named frontier,
prepared-read anchor, and cross-reader Goldfish-vote producers land.
-/



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]



/-- The action read preserves the healing grade view. -/
theorem actionStoreAt_gradeView_eq_storeBeforeTime
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    (Proofs.HealingSurface.actionStoreAt S rho v r).toHealing.gradeView =
      (rho.storeBeforeTime S v (S.a r)).toHealing.gradeView := by
  rfl













/-! ## Named public surfaces -/





















end Protocol
end DecoupledConsensusModel

end

/- Exact earlier-tree goals for the absent declarations below. Each declaration
   remains absent from the active named cone until its named producer lands. -/













































