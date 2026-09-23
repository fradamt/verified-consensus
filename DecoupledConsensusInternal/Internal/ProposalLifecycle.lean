module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.ProposalSources
public import DecoupledConsensusInternal.Definitions.Confirmation

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! Time-indexed lifecycle used by the internal recovery assembly.
The reviewed confirmation contract uses the same exact outputs in its
genesis and bounded weak-continuation cases. -/

namespace DecoupledConsensusModel
namespace Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every strictly post-boundary honest proposal is emitted and is the exact
protocol live confirmation and user record at every honest confirmation duty.
Future user-output persistence is a separate safety-regime property. -/
def HonestProposalLifecycleFrom
    (S : Setup V) (rho : Run V) (t0 : Time) : Prop :=
  ∀ s : Slot, 0 < s →
    t0 < Protocol.proposal_time S.E s →
    S.E.proposer s ∈ rho.honest →
    Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∃ B : NamedBlock V, Statements.Instantiation.proposedBlockAt S rho s = some B ∧
      rho.emits S (S.E.proposer s) (NamedObject.block B)
          (Protocol.proposal_time S.E s) ∧
        ∀ v ∈ rho.honest,
          (rho.storeAt S v
              (Protocol.confirmation_time S.E s)).live_confirmed = B.erase ∧
            (rho.storeAt S v
              (Protocol.confirmation_time S.E s)).latest_confirmed = B.erase

end Internal
end DecoupledConsensusModel

end
