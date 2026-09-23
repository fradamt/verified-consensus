module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakConfirmationWalkFactsNamed

@[expose] public section

/-! # Genuine positive-slot prepared confirmations -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every positive in-horizon honest confirmation writes the prepared walk and
clears that walk's gate. -/
theorem genuineConfirmationAt_positive_of_weakGenesis
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    GenuineConfirmationAt S rho v s := by
  let n := NamedRecoveryRead.confirmationInputRead S rho v s
  let contract := NamedProfile.gradeContract n.cache
  have hwalk := confirmationWalk_of_readFacts_named
    S h hs hhor hv
      (fun x _ => Protocol.preceq_genesis (voterHeadAt S rho x s))
  unfold GenuineConfirmationAt
  change (rho.storeAt S v
      (Protocol.confirmation_time S.E s)).live_confirmed =
        namedConfirmationWalk S n s ∧
      confirmationEligible S.E n.st.core s
        (namedConfirmationWalk S n s) = true
  constructor
  · rw [live_confirmed_eq_update S h.core.toNamedScheduleWellFormed hv s hhor]
    change (Protocol.update_confirmation_with contract S.E S.hc n.st.core s).live_confirmed =
      namedConfirmationWalk S n s
    rw [update_confirmation_with_live_confirmed, if_pos (by
      simpa only [n] using hwalk.2)]
    rfl
  · simpa only [n] using hwalk.2

#print axioms genuineConfirmationAt_positive_of_weakGenesis

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
