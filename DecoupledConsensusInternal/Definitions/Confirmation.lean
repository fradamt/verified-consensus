module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.Confirmation

@[expose] public section

/-! Proof-side confirmation helpers outside `Statements.Consensus`. -/
namespace DecoupledConsensusModel.Internal
open Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The core store read by the slot confirmation duty. -/
def confirmationInputStore (S : Setup V) (ρ : Run V) (v : V) (s : Slot) :
    Protocol.Store V :=
  (NamedActionReads.confirmationReadAt S ρ v (Protocol.confirmation_time S.E s)).st.core

/-- The stable record written from a prepared confirmation read. -/
def confirmationStableWrite (S : Setup V) (n : NamedNodeState V) : Block V :=
  match (NamedProfile.gradeContract n.cache).stableRoot S.E S.hc n.st.core.toHealing
      (S.hc.round_of n.st.core.s) with
  | some G => Protocol.advance_confirmed n.st.core.latest_stable G
  | none => n.st.core.latest_stable

/-- At each covered honest confirmation duty, the walk result extends the
stable record that the duty writes. -/
def HonestHeadExtendsStableFrom (S : Setup V) (rho : Run V) (t0 : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ s : Slot, t0 ≤ Protocol.confirmation_time S.E s →
    Protocol.confirmation_time S.E s ≤ rho.horizon →
    Block.Preceq
      (confirmationStableWrite S (NamedRecoveryRead.confirmationInputRead S rho v s))
      (Protocol.advance_confirmed
        (NamedRecoveryRead.confirmationInputRead S rho v s).st.core.latest_confirmed
        (namedConfirmationWalk S
          (NamedRecoveryRead.confirmationInputRead S rho v s) s))

end DecoupledConsensusModel.Internal

end
