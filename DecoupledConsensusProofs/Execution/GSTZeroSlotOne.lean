module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroConfirmationZero
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroSelectionSafety
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalVoteDuty

/-!
# Exact GST-zero confirmation in slot one

Slot one is the boundary case for exact honest-proposal liveness. Its proposal
and vote duties precede the first healing action. The first action coincides
with the slot-zero confirmation duty, and its round-zero grade inputs are empty.
This module records the boundary argument without declarations.
-/


