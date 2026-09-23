module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.NjGap
public import DecoupledConsensusProofs.Protocol.ChainState.ProgressQuorumCore
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusInternal.Healing
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradePersistence
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.RecoverySourceProgress

/-!
# The next operational outcome after recovery-source relay

Open (design note, class d): this module depends on the named-runtime gap facts
removed from NjGapRun: NjGap.store_root_eq_F_or_above_gap and
NjGap.store_h_j_ne_recovery_height. The proposal declarations also depend
on the absent weighted source and named proposal-body producers.

The earlier and selection files are byte-identical. The exact old module, including
all six declarations, is archived at
the compatibility layer
under  because no declaration in this module has a live consumer.
The first errors were:

    DecoupledConsensusProofs/HealingSurface/RecoverySourceNextRun.lean:36:15:
    error(lean.unknownIdentifier): Unknown identifier
    NjGap.store_root_eq_F_or_above_gap

    DecoupledConsensusProofs/HealingSurface/RecoverySourceNextRun.lean:66:6:
    error(lean.unknownIdentifier): Unknown identifier
    NjGap.store_h_j_ne_recovery_height
-/


