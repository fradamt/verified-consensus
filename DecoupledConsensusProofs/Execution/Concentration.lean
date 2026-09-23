module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGRepresentation
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroSelectionSafety
public import DecoupledConsensusInternal.Definitions.PhaseGradeQueries
public import DecoupledConsensusProofs.Protocol.Grades.VoteBelowSource
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeDelivery
public import DecoupledConsensusProofs.Protocol.Schedule.Action

/-!
# Run bridge for clean-round concentration

`ActionRun` pins the Section 7 attestation to the store that it actually reads.
At `a_r`, the tick first runs `update_confirmation` and then runs `attest` on
that updated store. This module builds its exact SG projection and follows that
projection through the clean-round concentration path.

The second half follows the actual wire path. After GST, honest-duty broadcast
puts the emitted attestation's SG projection in every honest reader before one
network delay. The protocol condition `R >= 2` puts that deadline no later
than the next round's earliest grade cutoff.

`CleanActionReadFor` isolates the remaining clean-round content: the actual
projected vote and its named block resolve before the next `Gamma[-1]` cutoff
and cover one common active prefix. Honest authenticity makes each honest
batch slice a singleton, so this exact read condition reduces to
`CleanGradeReadFor` and then to a common active G2.
-/


