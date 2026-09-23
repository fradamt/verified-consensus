module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.SafetyRegimes
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Handlers.UserConfirmationRecovery

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Named GST-zero latest record at an honest proposal

This leaf isolates the named proposal and confirmation-write provenance step.
It does not import the recovery closure.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Once the prepared confirmation floor and the named proposal duty are
available, proposal totality and the actual named duty write give the exact
`latest_confirmed` field required by `GSTZeroGuarantees`. -/
theorem latestAtProposalField_of_weakGenesis_of_heads_of_duty
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    (hheads : HonestHeadExtendsStableFrom S rho 0)
    (hduty : ∀ {s : Slot}, 0 < s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      S.E.proposer s ∈ rho.honest → ∀ {B : NamedBlock V},
        proposedBlockAt S rho s = some B →
        CanonicalProposalDutyAt S rho s B) :
    LatestAtProposalField S rho 0 := by
  intro s hs hhor hprop
  obtain ⟨B, hB⟩ := proposedBlockAt_isSome S rho s
  refine ⟨B, hB, ?_⟩
  intro v hv
  exact UserConfirmationFreshness.latest_eq_proposedBlock_of_duty
    S h.core hheads h.committees hB (hduty hs hhor hprop hB)
      (Proofs.Optimistic.confirmation_time_nonneg S.E s) hhor hv



#print axioms latestAtProposalField_of_weakGenesis_of_heads_of_duty

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
