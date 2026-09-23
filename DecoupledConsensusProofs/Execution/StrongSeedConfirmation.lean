module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.StrongSeedVoteCone
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationRecordOrigin

@[expose] public section

/-!
# Strong-regime prepared opening seed

The opening voter-head equality is committee-scoped, as is the vote cone.
The confirmation field records the exact prepared live value and the
post-write stable/confirmed nesting supplied by `floor_on_stable`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.NamedRecoveryRead Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]


/-- Each honest prepared opening confirmation writes the bound proposal as
its live value and leaves the stable record below the confirmed record. -/
theorem NamedSGProposalLifecycleInputs.confirmationSeed
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {r : Round} {s : Slot} {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P) :
    ∀ w ∈ rho.honest,
      let contract := NamedProfile.gradeContract
        (confirmationInputRead S rho w (s + 1)).cache
      let updated := Protocol.update_confirmation_with contract S.E S.hc
        (confStore S rho w (s + 1)) (s + 1)
      updated.live_confirmed = P.erase ∧
        Block.Preceq updated.latest_stable updated.latest_confirmed := by
  intro w hw
  dsimp only
  have hgc := h.genuineConfirmation adm hcom hw
  have hhor : Protocol.confirmation_time S.E (s + 1) ≤ rho.horizon := by
    rw [show Protocol.confirmation_time S.E (s + 1) = S.a (r + 1) by
      rw [h.openingSlot]
      exact (Protocol.a_eq_confirmation_time S.hc S.E (r + 1)).symm]
    exact h.actionInHorizon
  have hrecord := Proofs.Optimistic.live_confirmed_eq_update S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw (s + 1) hhor
  constructor
  · simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead] using
      hrecord.symm.trans hgc.2
  · exact ConfirmationOrigin.update_confirmation_stable_le_confirmed
      (NamedProfile.gradeContract
        (confirmationInputRead S rho w (s + 1)).cache)
      S.E S.hc (confirmationInputRead S rho w (s + 1)).st (s + 1)

#print axioms NamedSGProposalLifecycleInputs.confirmationSeed

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
