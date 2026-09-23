module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.SafetySlotInduction
public import DecoupledConsensusInternal.Definitions.NamedLifecycle

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

structure PreparedProtectedProposalPivot
    (S : Setup V) (rho : Run V) (d : Slot) (v : V)
    (A : NamedBlock V) : Prop where
  slotProtected : ProtectedVoteSlot S rho d A.erase
  sourceAnchor : Block.Preceq
    (Internal.PhaseGrades.nodeAnchor S (proposerReadAt S rho (d + 1))
      (S.hc.round_of (proposerReadAt S rho (d + 1)).st.core.s)) A.erase
  targetAnchor : Block.Preceq (voterAnchorAt S rho v (d + 1)) A.erase
  sourceBody : A ∈ (proposerReadAt S rho (d + 1)).st.bodies
  targetBody : A ∈ (Internal.NamedRecoveryRead.voteDutyRead S rho v (d + 1)).st.bodies
  sourceBand : (proposerReadAt S rho (d + 1)).st.core.h_max - 1 ≤
    (Protocol.derive_named S.E S.cfg A).h
  targetBand :
    (Internal.NamedRecoveryRead.voteDutyRead S rho v (d + 1)).st.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg A).h
  parent : Block.Preceq A.erase (proposedParent S rho (d + 1))

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
