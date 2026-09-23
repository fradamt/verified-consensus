module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Objects.Final

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# W4 A1 — named proposal emission bridge

Clean copy of the live private bridge at `LivenessContractsRun.lean:162-173`
(selection tree), used as a shared input by the honest-proposal-confirmation and
available-chain-growth public liveness adapters. See the liveness audit
`the proof record` §5 A1.

This module imports only `NamedProposalBridge` and `Protocol.Final`, both
outside the red import closures listed in the branches records.
-/



namespace DecoupledConsensusModel
namespace Proofs
open Internal Execution Statements
variable {V : Type} [DecidableEq V] [Fintype V]

/-- **The honest slot-`s` proposer's block is retained and emitted, over
`AdmissibleCore`.** Exact copy of the selection's live private bridge
(`LivenessContractsRun.lean:162-173`), made public for the liveness adapters. -/
theorem proposedBlock_emitted_of_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s) (hp : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    ∃ B : NamedBlock V, Statements.Instantiation.proposedBlockAt S rho s = some B ∧
      NamedRun.emits S rho (S.E.proposer s) (.block B)
        (Protocol.proposal_time S.E s) := by
  have hproposal : Protocol.proposal_time S.E s ≤ rho.horizon :=
    (Protocol.proposal_time_le_confirmation_time S.E s).trans hhor
  obtain ⟨B, hB, _, hemit⟩ := DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_emits_of_honest S
    adm.toNamedScheduleWellFormed s hs hp hproposal
  exact ⟨B, hB, hemit⟩

#print axioms proposedBlock_emitted_of_core

end Proofs
end DecoupledConsensusModel

end
