module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.WeakGenesisCanonicalProposalDutyClosed
public import DecoupledConsensusProofs.Protocol.Grades.ProposalLifecycleCore
public import DecoupledConsensusProofs.Protocol.Handlers.TickBridges

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# W4 A2: GST-zero exact named live confirmation

Named proof of earlier's `WeakGenesisProposalConfirmationRun.lean:82-93`
(`honestProposal_liveConfirmed_at_confirmation_positive_of_gstZero`) through
`proposedBlockAt`,: the duty binds a named block `P` with
`proposedBlockAt S rho s = some P`, and the conclusion records `P.erase`.

The closed named GST-zero duty (`WeakGenesisCanonicalProposalDutyClosedRun`)
already supplies `CanonicalProposalDutyAt S rho s P`; the store-recording step
is the same two lemmas earlier's blocked `WeakProposalConfirmationCoreRun.
storeAt_liveConfirmed_eq_of_duty` uses (`Proofs.Optimistic.live_confirmed_eq_update`,
`Protocol.updateConfirmation_eq_proposedBlock_of_dutyExecution`), reached
here through a clean import path (`WeakProposalConfirmationCoreRun` itself is
on a red path through `WeakConfirmationReadAnchorsRun` ->
`WeakProposalResolvedSnapshotRun`, so its statement is reproduced directly
instead of imported).
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- At GST zero, every positive honest proposal is the live-confirmed record
at every honest node's confirmation-time store. -/
theorem honestProposal_liveConfirmed_named_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest) {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P) :
    ∀ v ∈ rho.honest,
      (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed =
        P.erase := by
  intro v hv
  have hduty : CanonicalProposalDutyAt S rho s P :=
    canonicalProposalDuty_positive_of_gstZero_named S h hs hhor hprop hP
  rw [Proofs.Optimistic.live_confirmed_eq_update S h.core.toNamedScheduleWellFormed hv s hhor]
  exact Protocol.updateConfirmation_eq_proposedBlock_of_dutyExecution
    S h.committees hduty hv

#print axioms honestProposal_liveConfirmed_named_of_gstZero

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
