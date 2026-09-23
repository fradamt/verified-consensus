module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.Final
public import DecoupledConsensusProofs.Protocol.Handlers.TickBridges

@[expose] public section

/-!
# Exact proposal source store

This module names the exact store and parent used by an honest proposal and
records the proposal's definitional slot and parent fields.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The exact store from which the honest slot proposer computes its block. -/
def proposerDutyStore (S : Setup V) (rho : Run V) (s : Slot) : Protocol.Store V :=
  Proofs.Optimistic.tickStore S
    (rho.storeBeforeTime S (S.E.proposer s) (Protocol.proposal_time S.E s)).core
    (Protocol.proposal_time S.E s)

/-- The ordinary composed head that becomes the honest proposal's parent. -/
noncomputable def proposedParent (S : Setup V) (rho : Run V) (s : Slot) : Block V :=
  let st := proposerDutyStore S rho s
  let votes := Protocol.proposer_view st.toHealing.toFG.toSG.toGoldfishStore st.s
  let supportVotes := Protocol.proposer_support_view st.toHealing.toFG.toSG.toGoldfishStore st.s
  Protocol.get_head S.E S.hc st votes.toFinset supportVotes.toFinset (st.s - 1)



end Protocol
end DecoupledConsensusModel

end
