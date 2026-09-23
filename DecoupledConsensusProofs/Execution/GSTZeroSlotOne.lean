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

This file isolates that boundary. It uses only admissibility, GST zero, honest
committees, and a strict honest-weight majority.

**Open (class d),.** All six declarations of this module
are withheld.  audit: `confirmationSelection_eq_genesis_before_one` does
not use the retired proposal reader. Its exact earlier and selection goal is:

  theorem confirmationSelection_eq_genesis_before_one
      (S: Setup V) {rho: Run V} (adm: Admissible S rho)
      (hmajority: Execution.HonestWeightMajority S rho.honest)
      (hfinality: Proofs.HealingSurface.FinalityTargetHeightSource S rho)
      {i: Nat}
      (hi: i < (rho.events.filter (fun e => decide
        (e.time < Protocol.confirmation_time S.E 1))).length)
      {v: V} (hv: v ∈ rho.honest) {C: Block V}
      (hselection: ConfirmationSelectionAt S rho v i C):
      C = Block.genesis

The missing producer is the slot-zero genesis theorem for the prepared
`confirmationWrite` read. earlier's `updateConfirmation_eq_genesis_zero` is over
bare `Protocol.update_confirmation`;  forbids assuming that it equals the
frame-contract write. No compiler error is recorded for this Open.

The other five declarations are withheld:
`proposedBlock_canonicalHistoryBeforeConfirmation_one_gstZero`,
`evaluationStoreOk_one_gstZero`, `proposedBlock_liveConfirmed_one_gstZero`,
`proposedBlock_preceq_latestConfirmed_from_one_gstZero` and
`exactProposalConfirmed_one_gstZero`.

The other five name the retired total proposal reader `proposedBlock S rho
1` (: the named `proposedBlockAt` is an `Option (NamedBlock V)`, and this
file's slot-one witness would be bound rather than constructed), and the chain
above them consumes `HonestWeightMajority.evaluationStoreOk_of_history` and the
`latest_confirmed` transport, both recorded as absent in
`Availability/EvaluationStoreRun.lean` and
`Availability/ConfirmationHistoryRun.lean`, plus the slot-one candidate and
admission results recorded as absent in
`Availability/ProposalVoteDutyRun.lean`.

The headline goal, in the restated vocabulary, is:

  theorem exactProposalConfirmed_one_gstZero
      (S: Setup V) {rho: Run V} (hadm: Admissible S rho)
      (hGST: S.E.t_GST = 0)
      (hcom: HonestCommittees S rho.honest)
      (hmajority: Execution.HonestWeightMajority S rho.honest)
      (hfinality: Proofs.HealingSurface.FinalityTargetHeightSource S rho)
      (hhor: Protocol.confirmation_time S.E 1 ≤ rho.horizon)
      (hprop: S.E.proposer 1 ∈ rho.honest):
      ∃ B: NamedBlock V, B.slot = 1 ∧
        Statements.Instantiation.proposedBlockAt S rho 1 = some B ∧
        NamedRun.emits S rho (S.E.proposer 1) (Object.block B)
          (Protocol.proposal_time S.E 1) ∧
        (∀ v ∈ rho.honest,
          (rho.storeAt S v (Protocol.confirmation_time S.E 1)).core.live_confirmed
            = B.erase) ∧
        (∀ v ∈ rho.honest, ∀ t: Time,
          Protocol.confirmation_time S.E 1 ≤ t → t ≤ rho.horizon →
          Block.Preceq B.erase (rho.storeAt S v t).core.latest_confirmed)

Its emission half is already available: `NamedProposalBridge.
proposedBlockAt_emits_of_honest` gives the bound block and its emission with no
premise beyond a well-formed schedule, an honest proposer and the horizon. What
is missing is only the confirmation half. The byte-exact earlier text is
archived  at
`the compatibility layer`.
Not guessed at; not available.
-/


