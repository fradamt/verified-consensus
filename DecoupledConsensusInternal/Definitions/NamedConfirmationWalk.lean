module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.NamedConfirmationWalk

@[expose] public section

/-! Proof-side named confirmation-walk queries. -/
namespace DecoupledConsensusModel.Internal
open Execution NamedRecoveryRead
variable {V : Type} [DecidableEq V] [Fintype V]

def confirmationWalkAt (S : Setup V) (ρ : Run V) (v : V) (s : Slot) : Block V :=
  namedConfirmationWalk S (confirmationInputRead S ρ v s) s

def ConfirmationDutyWritesWalkQuery (S : Setup V) (ρ : Run V) : Prop :=
  ∀ (v : V) (s : Slot), 0 < s →
    let n := confirmationInputRead S ρ v s
    let out := Protocol.NamedDuties.update_confirmation_with
      (NamedProfile.gradeContract n.cache) S.E S.hc n.st s
    (confirmationEligible S.E n.st.core s (namedConfirmationWalk S n s) = true →
      out.core.live_confirmed = namedConfirmationWalk S n s) ∧
    (confirmationEligible S.E n.st.core s (namedConfirmationWalk S n s) = false →
      out.core.live_confirmed = Protocol.get_fg_root n.st.core.toHealing.toFG)

end DecoupledConsensusModel.Internal

end
