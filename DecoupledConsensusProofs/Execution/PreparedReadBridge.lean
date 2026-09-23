module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.Grades.FrameCompleted
public import DecoupledConsensusProofs.Protocol.Grades.FrameForward
public import DecoupledConsensusProofs.Protocol.Grades.Interpolation
public import DecoupledConsensusProofs.Protocol.Grades.Q10Frame
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Execution.FrontierProducers
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Wire

@[expose] public section

/-!
# Prepared-read bridge kit

These are small equations and order lemmas for the prepared vote-duty read.
They keep the frame contract, its anchor, and its candidate tree in one
vocabulary. In particular, they do not identify a prepared read with the
default contract on an erased store.
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

/-! ## K1: the prepared cache -/



/-! ## K2: frame-history facades -/





/-! ## K3: the prepared head and anchor -/

/-- The prepared vote head is the contract-parametric walk on its own read. -/
theorem voterHeadAt_eq_get_head_with_anchor
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    voterHeadAt S rho v s =
      Protocol.get_head_in_tree_with_layer
        (NamedProfile.gradeContract (voteDutyRead S rho v s).cache)
        S.E S.hc (voteDutyRead S rho v s).st.core.toHealing
        (voterCandidateTreeAt S rho v s)
        (Protocol.voter_view S.E
          (voteDutyRead S rho v s).st.core.toHealing.toFG.toSG.toGoldfishStore
          (voteDutyRead S rho v s).st.core.s)
        (Protocol.voter_support_view S.E
          (voteDutyRead S rho v s).st.core.toHealing.toFG.toSG.toGoldfishStore
          (voteDutyRead S rho v s).st.core.s)
        ((voteDutyRead S rho v s).st.core.s - 1) := by
  rfl

/-- The prepared anchor is either the active prefix of the saved G1 root or
the store's FG root. -/
theorem voterAnchorAt_cases
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    voterAnchorAt S rho v s =
        Protocol.get_fg_root
          (voteDutyRead S rho v s).st.core.toHealing.toFG ∨
      ∃ root A,
        (DecoupledConsensusModel.Protocol.readFrame (voteDutyRead S rho v s).cache
          (voteDutyRead S rho v s).st.core.toHealing
          (S.hc.round_of (voteDutyRead S rho v s).st.core.s)).g1 =
          some (some root) ∧
        DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree
            (voteDutyRead S rho v s).st.core.toHealing.toFG) root = some A ∧
        voterAnchorAt S rho v s = A := by
  dsimp only [voterAnchorAt, nodeAnchor, nodeRead]
  simp only [NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract,
    DecoupledConsensusModel.Protocol.frameGradeRead]
  unfold DecoupledConsensusModel.Protocol.anchor
  cases hframe : (DecoupledConsensusModel.Protocol.readFrame (voteDutyRead S rho v s).cache
      (voteDutyRead S rho v s).st.core.toHealing
      (S.hc.round_of (voteDutyRead S rho v s).st.core.s)).g1 with
  | none => exact Or.inl rfl
  | some opt =>
      cases opt with
      | none => exact Or.inl rfl
      | some root =>
          cases hactive : DecoupledConsensusModel.Protocol.activePrefix
              (Protocol.get_filtered_block_tree
                (voteDutyRead S rho v s).st.core.toHealing.toFG) root with
          | none => exact Or.inl (by simp only [hactive, Option.getD_none])
          | some A =>
              exact Or.inr ⟨root, A, rfl, hactive, by
                simp only [hactive, Option.getD_some]⟩

/-- The prepared confirmation anchor is either the input read's FG root or
the active prefix of its saved G1 root. -/
theorem confirmationAnchorAt_cases
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    confirmationAnchorAt S rho v s =
        Protocol.get_fg_root
          (confirmationInputRead S rho v s).st.core.toHealing.toFG ∨
      ∃ root A,
        (DecoupledConsensusModel.Protocol.readFrame (confirmationInputRead S rho v s).cache
          (confirmationInputRead S rho v s).st.core.toHealing
          (S.hc.round_of (confirmationInputRead S rho v s).st.core.s)).g1 =
          some (some root) ∧
        DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree
            (confirmationInputRead S rho v s).st.core.toHealing.toFG) root = some A ∧
        confirmationAnchorAt S rho v s = A := by
  dsimp only [confirmationAnchorAt, namedConfirmationAnchor]
  unfold Protocol.get_sg_root_with
  simp only [NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract,
    DecoupledConsensusModel.Protocol.frameGradeRead, DecoupledConsensusModel.Protocol.anchor]
  cases hframe : (DecoupledConsensusModel.Protocol.readFrame (confirmationInputRead S rho v s).cache
      (confirmationInputRead S rho v s).st.core.toHealing
      (S.hc.round_of (confirmationInputRead S rho v s).st.core.s)).g1 with
  | none => exact Or.inl rfl
  | some opt =>
      cases opt with
      | none => exact Or.inl rfl
      | some root =>
          cases hactive : DecoupledConsensusModel.Protocol.activePrefix
              (Protocol.get_filtered_block_tree
                (confirmationInputRead S rho v s).st.core.toHealing.toFG) root with
          | none => exact Or.inl (by simp only [hactive, Option.getD_none])
          | some A =>
              exact Or.inr ⟨root, A, rfl, hactive, by
                simp only [hactive, Option.getD_some]⟩

#print axioms confirmationAnchorAt_cases

/-! ## K4: floors of the prepared head -/

/-- The prepared SG root is below the prepared vote-duty head. -/
theorem sgRootWith_preceq_voterHeadAt
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract (voteDutyRead S rho v s).cache)
        S.E S.hc (voteDutyRead S rho v s).st.core.toHealing
        (S.hc.round_of (voteDutyRead S rho v s).st.core.s))
      (voterHeadAt S rho v s) := by
  rw [voterHeadAt_eq_get_head_with_anchor]
  exact Protocol.ghost_preceq _ _ _ _

/-- The prepared anchor is below the prepared vote-duty head. -/
theorem voterAnchorAt_preceq_voterHeadAt
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    Block.Preceq (voterAnchorAt S rho v s)
      (voterHeadAt S rho v s) := by
  change Block.Preceq
    (Protocol.get_sg_root_with
      (NamedProfile.gradeContract (voteDutyRead S rho v s).cache)
      S.E S.hc (voteDutyRead S rho v s).st.core.toHealing
      (S.hc.round_of (voteDutyRead S rho v s).st.core.s))
    (voterHeadAt S rho v s)
  exact sgRootWith_preceq_voterHeadAt S rho v s

/-- The prepared vote head is above the prepared read's FG root. -/
theorem fgRoot_preceq_voterHeadAt
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho v s).st.core.toHealing.toFG)
      (voterHeadAt S rho v s) := by
  exact Block.preceq_trans
    (fg_root_preceq_get_sg_root_with_frame
      (voteDutyRead S rho v s).cache S.E S.hc
      (voteDutyRead S rho v s).st.core.toHealing
      (S.hc.round_of (voteDutyRead S rho v s).st.core.s))
    (sgRootWith_preceq_voterHeadAt S rho v s)

/-! ## K5: the same prepared walk -/

/-- The explicit prepared walk from the same anchor is exactly `voterHeadAt`.
The equality is a structural equation; it does not assert agreement with the
default contract on an erased store. -/
theorem get_head_in_tree_eq_voterHeadAt_of_anchor
    (S : Setup V) (rho : NamedRun V) (v : V) (s : Slot) :
    Protocol.get_head_in_tree_with_layer
        (NamedProfile.gradeContract (voteDutyRead S rho v s).cache)
        S.E S.hc (voteDutyRead S rho v s).st.core.toHealing
        (voterCandidateTreeAt S rho v s)
        (Protocol.voter_view S.E
          (voteDutyRead S rho v s).st.core.toHealing.toFG.toSG.toGoldfishStore
          (voteDutyRead S rho v s).st.core.s)
        (Protocol.voter_support_view S.E
          (voteDutyRead S rho v s).st.core.toHealing.toFG.toSG.toGoldfishStore
          (voteDutyRead S rho v s).st.core.s)
        ((voteDutyRead S rho v s).st.core.s - 1) =
      voterHeadAt S rho v s := by
  exact (voterHeadAt_eq_get_head_with_anchor S rho v s).symm


/-- Prepared twin of the explicit-tree SG-root floor. -/
theorem get_sg_root_with_preceq_get_head_in_tree_with
    (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V))
    (k : Slot) :
    Block.Preceq
      (Protocol.get_sg_root_with contract E hc st (hc.round_of st.s))
      (Protocol.get_head_in_tree_with_layer contract E hc st tree votes support k) := by
  exact Protocol.ghost_preceq _ _ _ _

/-- Prepared twin of the FG-root floor for the frame contract. -/
theorem get_head_in_tree_with_of_preceq_fgRoot
    (cache : DecoupledConsensusModel.Protocol.Cache V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (tree : Finset (Block V)) (F : Block V)
    (votes support : Finset (GoldfishVote V)) (k : Slot)
    (hroot : Block.Preceq F (Protocol.get_fg_root st.toFG)) :
    Block.Preceq F
      (Protocol.get_head_in_tree_with_layer (DecoupledConsensusModel.Protocol.frameContract cache)
        E hc st tree votes support k) := by
  exact Block.preceq_trans hroot
    (Block.preceq_trans
      (fg_root_preceq_get_sg_root_with_frame cache E hc st
        (hc.round_of st.s))
      (get_sg_root_with_preceq_get_head_in_tree_with
        (DecoupledConsensusModel.Protocol.frameContract cache) E hc st tree votes support k))

/-! ## K7: named and erased ancestry -/

/-- On run blocks, erasure reflects ancestry because run-wide roots are
collision-free. -/
theorem namedPreceq_iff_erase_preceq
    (S : Setup V) (rho : NamedRun V)
    (roots : NamedRootCollisionFree S rho)
    {D E : NamedBlock V}
    (hD : NamedRun.blockInRun S rho D)
    (hE : NamedRun.blockInRun S rho E) :
    NamedBlock.Preceq D E ↔ Block.Preceq D.erase E.erase := by
  constructor
  · exact Proofs.NamedWire.erase_preceq
  · intro hDE
    obtain ⟨A, hAE, hAerase⟩ := Proofs.NamedAncestry.erased_ancestor_lift E hDE
    have hroot : A.root = D.root := by
      rw [← Proofs.NamedWire.erase_root A, hAerase, Proofs.NamedWire.erase_root]
    have hEq := roots.root_injective E D hE hD A D
      (Or.inl hAE) (Or.inr (Proofs.NamedAncestry.named_self D)) hroot
    exact hEq ▸ hAE

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
