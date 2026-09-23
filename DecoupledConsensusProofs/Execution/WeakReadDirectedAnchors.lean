module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapSG
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakSGWindow
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryRelativeMajorityProvenance
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HonestMajorityCore
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Execution.WeakProposalHead

/-!
# Directed SG anchors in the weak continuation

Every retained honest SG emission is below each prior honest duty head.
The same bound therefore holds for the actual SG root. Proposal-parent
capture then places each reader's SG root below the honest proposal parent.
-/
