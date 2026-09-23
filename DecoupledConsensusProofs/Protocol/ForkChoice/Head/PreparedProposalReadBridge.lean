module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PreparedReadBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Agreement
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Protocol.Handlers.TickBridges
public import DecoupledConsensusProofs.Protocol.Schedule.RecordAtBoundary

@[expose] public section

/-!
# Prepared proposal-read bridge

The proposal duty uses the proposer's prepared read and the frame contract in
that read. These equations are the proposal-side twins of the vote-duty
bridge. They do not identify a prepared read with a bare tick-store read.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## K3: the prepared proposal head and anchor -/

/-- The prepared proposal parent is the frame-contract walk on its own read. -/
theorem proposedParent_eq_get_head_with_anchor
    (S : Setup V) (rho : Run V) (s : Slot) :
    proposedParent S rho s =
      Protocol.get_head_with
        (NamedProfile.gradeContract (proposalDutyRead S rho s).cache)
        S.E S.hc (proposalDutyRead S rho s).st.core.toHealing
        (Protocol.proposer_view
          (proposalDutyRead S rho s).st.core.toHealing.toFG.toSG.toGoldfishStore
          (proposalDutyRead S rho s).st.core.s).toFinset
        (Protocol.proposer_support_view
          (proposalDutyRead S rho s).st.core.toHealing.toFG.toSG.toGoldfishStore
          (proposalDutyRead S rho s).st.core.s).toFinset
        ((proposalDutyRead S rho s).st.core.s - 1) := by
  rfl

/-- The proposal anchor is either the active G1 prefix or the FG root. -/
theorem proposalAnchor_cases
    (S : Setup V) (rho : Run V) (s : Slot) :
    nodeAnchor S (proposalDutyRead S rho s)
        (S.hc.round_of (proposalDutyRead S rho s).st.core.s) =
        Protocol.get_fg_root
          (proposalDutyRead S rho s).st.core.toHealing.toFG ∨
      ∃ root A,
        (DecoupledConsensusModel.Protocol.readFrame (proposalDutyRead S rho s).cache
          (proposalDutyRead S rho s).st.core.toHealing
          (S.hc.round_of (proposalDutyRead S rho s).st.core.s)).g1 =
          some (some root) ∧
        DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree
            (proposalDutyRead S rho s).st.core.toHealing.toFG) root = some A ∧
        nodeAnchor S (proposalDutyRead S rho s)
            (S.hc.round_of (proposalDutyRead S rho s).st.core.s) = A := by
  dsimp only [nodeAnchor, nodeRead]
  simp only [NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract,
    DecoupledConsensusModel.Protocol.frameGradeRead]
  unfold DecoupledConsensusModel.Protocol.anchor
  cases hframe : (DecoupledConsensusModel.Protocol.readFrame (proposalDutyRead S rho s).cache
      (proposalDutyRead S rho s).st.core.toHealing
      (S.hc.round_of (proposalDutyRead S rho s).st.core.s)).g1 with
  | none => exact Or.inl rfl
  | some opt =>
      cases opt with
      | none => exact Or.inl rfl
      | some root =>
          cases hactive : DecoupledConsensusModel.Protocol.activePrefix
              (Protocol.get_filtered_block_tree
                (proposalDutyRead S rho s).st.core.toHealing.toFG) root with
          | none => exact Or.inl (by simp only [hactive, Option.getD_none])
          | some A =>
              exact Or.inr ⟨root, A, rfl, hactive, by
                simp only [hactive, Option.getD_some]⟩

/-! ## K4: floors of the prepared proposal head -/

/-- The prepared proposal SG root is below its selected parent. -/
theorem sgRootWith_preceq_proposedParent
    (S : Setup V) (rho : Run V) (s : Slot) :
    Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract (proposalDutyRead S rho s).cache)
        S.E S.hc (proposalDutyRead S rho s).st.core.toHealing
        (S.hc.round_of (proposalDutyRead S rho s).st.core.s))
      (proposedParent S rho s) := by
  rw [proposedParent_eq_get_head_with_anchor]
  exact Protocol.ghost_preceq _ _ _ _

/-- The prepared proposal anchor is below its selected parent. -/
theorem proposalAnchor_preceq_proposedParent
    (S : Setup V) (rho : Run V) (s : Slot) :
    Block.Preceq
      (nodeAnchor S (proposalDutyRead S rho s)
        (S.hc.round_of (proposalDutyRead S rho s).st.core.s))
      (proposedParent S rho s) := by
  change Block.Preceq
    (Protocol.get_sg_root_with
      (NamedProfile.gradeContract (proposalDutyRead S rho s).cache)
      S.E S.hc (proposalDutyRead S rho s).st.core.toHealing
      (S.hc.round_of (proposalDutyRead S rho s).st.core.s))
    (proposedParent S rho s)
  exact sgRootWith_preceq_proposedParent S rho s

/-- The prepared proposal parent is above the read's FG root. -/
theorem fgRoot_preceq_proposedParent
    (S : Setup V) (rho : Run V) (s : Slot) :
    Block.Preceq
      (Protocol.get_fg_root
        (proposalDutyRead S rho s).st.core.toHealing.toFG)
      (proposedParent S rho s) := by
  exact Block.preceq_trans
    (fg_root_preceq_get_sg_root_with_frame
      (proposalDutyRead S rho s).cache S.E S.hc
      (proposalDutyRead S rho s).st.core.toHealing
      (S.hc.round_of (proposalDutyRead S rho s).st.core.s))
    (sgRootWith_preceq_proposedParent S rho s)

/-! ## K5: the same prepared proposal walk -/




#print axioms proposedParent_eq_get_head_with_anchor
#print axioms proposalAnchor_cases
#print axioms sgRootWith_preceq_proposedParent
#print axioms proposalAnchor_preceq_proposedParent
#print axioms fgRoot_preceq_proposedParent

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
