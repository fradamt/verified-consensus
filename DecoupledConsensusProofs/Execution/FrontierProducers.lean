module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroSelectionSafety
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RoundZero
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.Schedule.ProposalCanonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.Handlers.GoldfishVotePool
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.IntrinsicEntry
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.Grades.FrameCompleted
public import DecoupledConsensusProofs.Protocol.Grades.FrameForward
public import DecoupledConsensusProofs.Protocol.Grades.Interpolation
public import DecoupledConsensusProofs.Protocol.Grades.Q10Frame
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSupporter

@[expose] public section



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol (derive_named)
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
















/-! ## Indexed action-read bridge -/

/-- The event-indexed action read is the strict-time action read at its tick. -/
theorem actionEventRead_eq_actionReadAt_of_tick
    (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho)
    {i : Nat} {v : V} {r : Round}
    (hi : rho.events[i]? = some (Event.tick v (S.a r))) :
    actionEventRead S rho i v r =
      Proofs.HealingSurface.actionReadAt S rho v r := by
  change NamedActionReads.actionReadFrom S (rho.stateBefore S i v) r =
    NamedActionReads.actionReadFrom S
      (NamedRun.stateBeforeTime S rho (S.a r) v) r
  exact congrArg (fun before => NamedActionReads.actionReadFrom S before r)
    (Proofs.NamedActionSources.action_read_index S rho sch i v r hi)













/-! ## Named prefix source projections -/





/-! ## Source history at a time cutoff -/















#print axioms honestAttestationOutputPreceqAtIndex_of_activeSources
#print axioms actionEventRead_eq_actionReadAt_of_tick

end Protocol
end DecoupledConsensusModel

end
