module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalPivot

/-!
# Recovery-local honest-proposal walk transfer

This module serves to give the recovery-local replacement for the GST-zero
proposal-walk transfer: a `RecoveryProposalPivotTransfer` interface (the
frozen-tree candidate, compatibility, pivot, suffix and common-score facts
read between one proposal and one same-slot vote duty, with no `t_GST = 0`
premise), the theorem obtaining `ProposalWalkTransferred` from it, and the
corollaries identifying the recovery vote-duty head with the honest proposal.

**Named-run proof (branches choke-pivotchain3).**
None of this module's seven declarations —
`RecoveryProposalPivotTransfer`, `proposalWalkTransferred_of_recoveryPivot`,
`recoveryVoteDutyHead`, `voteDutyHead_eq_proposedBlock_of_recoveryPivot`,
`HonestRecoveryProposalPivotTransfers`,
`honestVoteDutyHeads_eq_proposedBlock_of_recoveryPivots` and
`voteStoresExtend_of_recoveryPivots` — is restated.

Every one of them, directly or through `RecoveryProposalPivotTransfer`,
names `Protocol.proposalWalkTargetTree` and
`Protocol.ProposalPivotSuffixTransfer` (: both retired; their frozen
named twins `Proofs.HealingSurface.namedWalkTargetTree` and
`Proofs.HealingSurface.NamedProposalPivotSuffixTransfer`, in
`DecoupledConsensusStatements/Instantiation/NamedProposalPivot.lean`, bind an
explicit named proposal `P: NamedBlock V` and read the proposer's/voter's
own prepared duty cache — `proposalDutyRead` / `voteDutyRead` — rather than
`Protocol.proposerDutyStore` / `Proofs.Optimistic.voteDutyStore`). Rebinding
`RecoveryProposalPivotTransfer` over that frozen shape is not a mechanical
substitution: `NamedProposalPivotSuffixTransfer`'s own `persist`/`reflect`
fields are stated over `namedWalkSourceTree` / `namedWalkSourceScore` /
`namedWalkSourceEligible` (the prepared-read source views), not over this
module's `Protocol.proposalWalkSourceTree` / `proposalWalkSourceScore`
(the `proposerDutyStore`-based views also referenced by the `commonScore` and
`targetPasses` fields below); no lemma equating `proposalDutyRead`'s cached
core with `proposerDutyStore`, or `voteDutyRead`'s with `Proofs.Optimistic.
voteDutyStore`, is in scope of this cone, so mixing the two families into one
coherent structure would be a new statement shape, not a restatement, and is
not guessed at here (class d).

Independently, `proposalWalkTransferred_of_recoveryPivot` (and everything
built from it: `voteDutyHead_eq_proposedBlock_of_recoveryPivot`,
`honestVoteDutyHeads_eq_proposedBlock_of_recoveryPivots`,
`voteStoresExtend_of_recoveryPivots`) calls `Protocol.
proposalWalkTransferred_of_frozenCompatiblePivot`, itself absent in
`Availability/ProposalPivotRun.lean` ('s barred head-equality class,
recorded there): even a correctly rebound `RecoveryProposalPivotTransfer`
could not discharge this producer without naming Q-PR2. The boundary-check
section (`ProposalWalkBoundaryCheck`) opened
`Protocol.ProposalWalkTransferCounterexample`, itself fully retired with
no live or named twin, and carried no live declaration beyond that; it is not
restated.

Per the  companion rule these seven are simply absent, not archived: they
keep the many live cone consumers listed below. Their exact earlier text is
unchanged from the last green copy of this file (see `git log -p` on this
path) and is not repeated here. Not guessed at; not available.

Live consumers, for the next branches on this cone (a class-d on the
frozen-shape rebinding above, and a resolution of 's Q-PR2, are both
prerequisites before any of them can be restated):
`RecoveryProposalPivotTransfer` — `HealingSurface/
RecoveryProposalCapReflectionRun.lean`, `HealingSurface/
OpeningActiveSingletonCounterexample.lean`.
`HonestRecoveryProposalPivotTransfers` — `HealingSurface/
RecoveryStableProposalConfirmationRun.lean`, `HealingSurface/
RecoveryProposalConfirmationDirectRun.lean`, `HealingSurface/
RecoveryProposalPivotAssemblyRun.lean`, `HealingSurface/
RecoveryCapturedRestartRebaseRun.lean`, `HealingSurface/
RecoveryProposalStableCaptureAssemblyRun.lean`, `HealingSurface/
RecoveryStableProposalGenuineRun.lean`, `HealingSurface/
RecoveryBoundaryOpeningProposalAncestryRun.lean`, `HealingSurface/
RecoveryStableProposalCaptureDirectRun.lean`, `HealingSurface/
RecoveryStableProposalCaptureRun.lean`, `HealingSurface/
RecoveryBoundaryConfirmationSeedRun.lean`, `HealingSurface/
RecoveryProposalPreCaptureAssemblyRun.lean`.
`voteStoresExtend_of_recoveryPivots` — `HealingSurface/
RecoveryStableProposalConfirmationRun.lean`, `HealingSurface/
RecoveryProposalConfirmationDirectRun.lean`, `HealingSurface/
RecoveryBoundaryConfirmationSeedRun.lean`.
`proposalWalkTransferred_of_recoveryPivot`,
`voteDutyHead_eq_proposedBlock_of_recoveryPivot`,
`honestVoteDutyHeads_eq_proposedBlock_of_recoveryPivots` and
`recoveryVoteDutyHead` have no consumer outside this file.
-/


