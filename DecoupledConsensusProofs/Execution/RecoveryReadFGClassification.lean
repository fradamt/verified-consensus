module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterRetention
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryCapturedSlotInterval
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingReuse
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterInterference
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HonestMajorityCore
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.Handlers.StoreFinality
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordClean
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Objects.EmittedHeightBound
public import DecoupledConsensusProofs.Execution.ReleasedCertificateHeightProgress
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecoveryTimeout
public import DecoupledConsensusProofs.Execution.RecoveryGradeProcessedRead
public import DecoupledConsensusProofs.Execution.StoreFinalityRun
public import DecoupledConsensusProofs.Execution.CertificateUniqueness
public import DecoupledConsensusProofs.Protocol.ChainState.ProgressQuorumCore
public import DecoupledConsensusProofs.Protocol.Handlers.Staleness
public import DecoupledConsensusModel.Protocol.ChainState
public import DecoupledConsensusProofs.Protocol.Handlers.BlockProcessingDefaults
public import DecoupledConsensusProofs.Protocol.ChainState.TargetedTimeoutBinding
public import DecoupledConsensusProofs.Protocol.ChainState.TimeoutBindingDefaults
public import DecoupledConsensusProofs.Protocol.ChainState.NjGap
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusInternal.Execution.Run
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusProofs.Execution.Concentration
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusInternal.Definitions.NamedDerived
public import DecoupledConsensusProofs.Protocol.ChainState.NamedNjGap
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusInternal.Healing
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationCarrier

/-!
# Recovery FG-root classification at one honest read

The named classifier is provided by
`RecoveryNoFGInterferenceProducerRun.recoveryRead_selectedRootCompatible_or_restart`.
This module keeps the historical import path used by the active cone.

the prior round-facing specialization remains blocked. Its old goal uses an
erased block, `GradeFormsAt`, `derived_state`, and an erased restart carrier.
The named classifier instead needs a `NamedBlock` witness, `NamedGradeFormsAt`,
`derive_named`, and `RunBlock` for that witness. No named next-action producer
with the prior public shape is available in this cone.

Open (design note, class d): the following live-consumer declaration is absent.
The exact old goal is retained here. Its earlier route first proves processed
membership with `gradeFormsAt_processedAtNextAction`, converts the strict
pre-action store with `storeBeforeTime_eq_storeAt_sub_one_recovery`, and then
applies the pointwise classifier.

The first earlier diagnostic was:

    RecoveryReadFGClassificationRun.lean:42:42: error:
    Application type mismatch: The argument
      post₁
    has type
      Protocol.Store V
    but is expected to have type
      Protocol.NamedStore V
    in the application
      RecoveryBoundaryRestartAt S rho post₁
-/


