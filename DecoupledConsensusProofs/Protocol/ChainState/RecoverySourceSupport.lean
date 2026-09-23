module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Execution.RecoverySourceNext
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingReuse
public import DecoupledConsensusProofs.Protocol.Schedule.ProposalCanonicality

/-!
# Post-GST Goldfish support for a relayed strict source

This file closes the fork-choice half of the strict-source selection seam.
For a fully post-GST slot, every honest previous-slot vote reaches the next
honest proposer's raw view by the support cutoff. If the named heads resolve
in the proposal store, the same votes enter its fixed support view. An honest
vote cone above `Q`, an anchor below `Q`, and proposal-time candidate membership
then make the final Section 7 Goldfish walk pass through `Q`.

Block relay alone does not produce the vote cone. The remaining recovery
producer must show that every honest previous-slot head is in the relayed
strict source's cone.
-/
