module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroActionHead
public import DecoupledConsensusProofs.Objects.GSTZeroProposalEvaluation
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroSelectionSafety
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroConfirmationZero
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradePersistence
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore

/-!
# The first common-grade execution seam

The final Section 7 action emits `actionSGBlockAt`, not the internal Goldfish
`actionHead`. This file separates the facts that the run contract proves from
the one order relation that concentration needs.

First, every branch of the SG selector is a processed block in the action
store. Admissibility can therefore relay that block to the next grade read
whenever it extends one common block that remains active. This discharges the
receipt, block-resolution, and cutoff parts of `CleanActionReadFor`; only the
common-carrier order remains.

Second, the GST-zero honest-proposer/view-merge development gives exact
confirmation of the proposal and puts both the proposal and the actual SG
carrier below the same internal Goldfish action head. Thus it proves
compatibility, but not that the proposal precedes the carrier. Section 7's
safety-ranked grade-2 and raw-anchor fallbacks do not provide that missing
orientation.
-/
