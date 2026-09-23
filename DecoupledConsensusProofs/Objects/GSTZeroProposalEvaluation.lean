module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.GSTZeroSlotOne
public import DecoupledConsensusProofs.Protocol.Grades.ProposalWalkComposition

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Exact GST-zero honest-proposal evaluation

This file starts after the proposal-to-vote walk theorem. It serves to take the
public `VoteStoresExtend` fact as an explicit premise and discharge the vote
emission, evaluation-store, exact `live_confirmed`, and stable-record
consequences.

**Named-run proof (branches choke-pivotchain3, design note).**
Every declaration below the vote-emission fact rests on the bare total reader
`proposedBlock S rho s`, which is retired (: the named
`Statements.Instantiation.proposedBlockAt` is an `Option (NamedBlock V)`, so a bound
witness `B` with `hB: proposedBlockAt S rho s = some B` replaces it), and on
one or more of the following producers, each already confirmed absent from the
live named-runtime tree with no in-tree replacement:

* `voteStoresExtend_gstZero` and `HonestWeightMajority.
  honestSelectionFrontierAtIndex_gstZero` — both recorded absent in this file's
  own import `ProposalWalkCompositionRun.lean`, which lists this file among
  their live consumers for the next branches;
* `proposedBlock_canonicalHistoryBeforeConfirmation_one_gstZero` — one of the
  six declarations `GSTZeroSlotOneRun.lean` withholds outright (its own Open
  note: the slot-one base case needs `HonestWeightMajority.
  evaluationStoreOk_of_history` and the `latest_confirmed` transport, both
  absent);
* `HonestWeightMajority.evaluationStoreOk_of_history`,
  `proposedBlock_visibleAtEvaluation_gstZero_all`,
  `HonestWeightMajority.confirmationAbsorbedAtEvaluation_gstZero`,
  `HonestWeightMajority.confirmationCompatibleFrom_gstZero` and
  `proposedBlock_slot` — none has an in-tree named twin.

Separately, the one theorem that stays independent of `proposedBlock`
(`confirmationSelectionAt_eq_previousSlot_of_in_proposalWindow`) hits 's own
named Open directly: `confirmationSelectionAt_slot` now returns the value at
the confirmation duty's own frame-contract read (`confirmationWrite`, in
`Availability/ConfirmationHistoryRun.lean`), not the bare
`Protocol.update_confirmation` this theorem's conclusion names, and no bridge
between the two forms exists in the tree (: "a site needing the bare write
to equal the frame read open items"). `PreviousSlotConfirmationPreceqProposal` and
its two consumers name the same bare form and inherit the same gap.

Per the  companion rule: the four declarations with no live cone consumer —
`confirmationSelectionAt_eq_previousSlot_of_in_proposalWindow`,
`proposedBlock_canonicalHistoryBeforeConfirmation_of_window_gstZero`,
`evaluationStoreOk_of_voteStoresExtend_window_gstZero` and
`exactProposalConfirmed_of_voteStoresExtend_window_gstZero` — are archived
byte-exact  at `the compatibility layer
GSTZeroProposalEvaluationRunRetired.lean`, together with
`proposedBlock_liveConfirmed_of_voteStoresExtend_window_gstZero` (also
consumer-free). The remaining absent declarations keep live cone consumers
and stay recorded below, not archived:

* `ProposalConfirmationSelectionWindow` (def) —
  `Availability/GSTZeroReorgResilienceRun.lean`;
* `PreviousSlotConfirmationPreceqProposal` (def) —
  `Availability/GSTZeroPreviousConfirmationRun.lean`;
* `proposalConfirmationSelectionWindow_of_previousSlot` —
  `Availability/GSTZeroReorgResilienceRun.lean`,
  `Availability/GSTZeroActionHeadRun.lean`;
* `previousSlotConfirmationPreceqProposal_one_gstZero` —
  `Availability/GSTZeroPreviousConfirmationRun.lean`;
* `proposedBlock_preceq_latestConfirmed_from_of_voteStoresExtend_window_gstZero`
  — `Availability/GSTZeroActionHeadRun.lean`;
* `proposedBlock_canonicalHistoryBeforeConfirmation_of_previousSlot_gstZero`,
  `evaluationStoreOk_of_previousSlot_gstZero`,
  `proposedBlock_liveConfirmed_of_previousSlot_gstZero` and
  `exactProposalConfirmed_of_previousSlot_gstZero` —
  `Availability/GSTZeroPreviousConfirmationRun.lean`.

Their headline goals, in the earlier vocabulary, are unchanged from the last
green copy of this file (`git log -p` on this path). Not guessed at; not
available.

**restated below.** `honestVotesName_of_voteStoresExtend` needed neither
`proposedBlock` nor any absent producer: `VoteStoresExtend` already binds a
`NamedBlock V` witness `B` directly (design note), and its two producers
(`Proofs.Optimistic.voteTickExtends_of_extends`, `Proofs.Optimistic.honestVotesName_of_extends`)
are both live and already stated over that same `B`.

** named shape for the downstream statements.** Every evaluation result
that refers to the proposal binds
`P: NamedBlock V` and
`hP: Statements.Instantiation.proposedBlockAt S rho s = some P`.
The vote-store input is `VoteStoresExtend S rho s P`, and proposal geometry is
stated over `P.erase`; no result takes `ProposalWalkTransferred` or concludes
a bare head equality. The proof obligations remain in the Open ledger above.
-/



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `VoteStoresExtend` makes every honest committee vote name the exact bound
proposal `B`. This theorem is independent of the proposal-walk
implementation. -/
theorem honestVotesName_of_voteStoresExtend
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon)
    {B : NamedBlock V}
    (hstores : VoteStoresExtend S rho s B) :
    Proofs.HealingSurface.NamedHonestVotesName S rho s B.erase :=
  Proofs.Optimistic.honestVotesName_of_extends S rho s B
    (Proofs.Optimistic.voteTickExtends_of_extends S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hs hvoteHor hstores)

end Protocol
end DecoupledConsensusModel

end
