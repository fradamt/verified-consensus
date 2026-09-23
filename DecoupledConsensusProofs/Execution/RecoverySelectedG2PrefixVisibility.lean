module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeDelivery
public import DecoupledConsensusProofs.Protocol.ChainState.RecoveryCrossingCore
public import DecoupledConsensusProofs.Protocol.ChainState.RecoveryPrefix
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusInternal.Execution.Run
public import DecoupledConsensusProofs.Execution.Concentration
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightRegimeFrame

/-!
# Prefix-capped raw visibility of a selected G2

A selected grade-2 block has a timely supporting head. For a finite recovery
prefix, the cap on every locally available finalization, together with the
exact recovery-height ancestor of the selected block, supplies the
receiver-local finalized-ancestor guard for that head's relay. No live-grade
state is used.
-/
