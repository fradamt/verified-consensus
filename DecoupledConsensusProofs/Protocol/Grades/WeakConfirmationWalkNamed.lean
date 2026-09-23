module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.WeakUserCandidateSelectionNamed
public import DecoupledConsensusProofs.Protocol.ChainState.GSTZeroSixFieldBypassNamed

@[expose] public section

/-! # Directed old-live capture at a prepared confirmation -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A positive prepared confirmation extends every earlier honest live value. -/
theorem liveConfirmed_preceq_at_confirmation_of_weakGenesis_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    {t : Time} (ht : t < Protocol.confirmation_time S.E s) :
    Block.Preceq (rho.storeAt S u t).live_confirmed
      (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed := by
  have hwalk := confirmationWalk_of_readFacts_named S h hs hhor hv
    (fun x hx =>
      (confirmationFields_at_read_preceq_voteDutyHead_of_weakGenesis_named
        S h hhor (Nat.le_succ s) ht hu hx).2)
  rw [live_confirmed_eq_update
    S h.core.toNamedScheduleWellFormed hv s hhor]
  change Block.Preceq (rho.storeAt S u t).live_confirmed
    (Protocol.update_confirmation_with
      (NamedProfile.gradeContract
        (NamedRecoveryRead.confirmationInputRead S rho v s).cache)
      S.E S.hc
      (NamedRecoveryRead.confirmationInputRead S rho v s).st.core s).live_confirmed
  have helig := hwalk.2
  change confEligible S.E
      (NamedRecoveryRead.confirmationInputRead S rho v s).st.core s
      (confWalkWith
        (NamedProfile.gradeContract
          (NamedRecoveryRead.confirmationInputRead S rho v s).cache)
        S.E S.hc
        (NamedRecoveryRead.confirmationInputRead S rho v s).st.core s) = true
    at helig
  rw [update_confirmation_with_live_confirmed, if_pos helig]
  simpa only [namedConfirmationWalk] using hwalk.1

#print axioms liveConfirmed_preceq_at_confirmation_of_weakGenesis_named

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
