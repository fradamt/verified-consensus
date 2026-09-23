module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FrontierRise
public import DecoupledConsensusProofs.Protocol.Handlers.HonestProposalAdmission
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Active selected-opening carrier

This module closes the callback-free active arm at one selected honest opening.
The exact-height source itself remains the proposal-time progress carrier. The
actual proposal parent is a separately named marker. Its derived height is
recorded exactly, but no false lower bound by the source height is claimed: the
proposal walk may select a viable lower sibling. In that case the exact
proposal FG root is a strict common ancestor of the source and marker.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The exact proposal parent belongs to the proposal duty's filtered tree. -/
theorem selectedOpeningProposedParent_mem_filtered
    (S : Setup V) {rho : Run V} (s : Slot) :
    proposedParent S rho s ∈
      Protocol.get_filtered_block_tree
        (proposerReadAt S rho s).st.core.toHealing.toFG := by
  let n := proposerReadAt S rho s
  let st := n.st.core.toHealing
  let gc := NamedProfile.gradeContract n.cache
  let votes := Protocol.proposer_view st.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.proposer_support_view st.toFG.toSG.toGoldfishStore st.s
  have hroot : Protocol.get_fg_root st.toFG ∈
      Protocol.get_filtered_block_tree st.toFG := by
    simpa only [n, st, proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      (named_fgRoot_mem_filtered_stateBeforeTime S rho
        (Protocol.proposal_time S.E s) (S.E.proposer s))
  have hanchor : Protocol.get_sg_root_with gc S.E S.hc st
      (S.hc.round_of st.s) ∈ Protocol.get_filtered_block_tree st.toFG := by
    change DecoupledConsensusModel.Protocol.anchor S.E S.hc st (S.hc.round_of st.s)
      (DecoupledConsensusModel.Protocol.readFrame n.cache st (S.hc.round_of st.s)).g1 ∈
      Protocol.get_filtered_block_tree st.toFG
    unfold DecoupledConsensusModel.Protocol.anchor
    match hg : (DecoupledConsensusModel.Protocol.readFrame n.cache st
      (S.hc.round_of st.s)).g1 with
    | none => simpa only [hg] using hroot
    | some none => simpa only [hg] using hroot
    | some (some root) =>
      cases ha : DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree st.toFG) root with
      | none => simpa only [hg, ha, Option.getD_none] using hroot
      | some A =>
        simpa only [hg, ha, Option.getD_some] using
          NamedProposalParent.activePrefix_mem _ root A ha
  have hhead : Protocol.get_head_with gc S.E S.hc st
      votes.toFinset support.toFinset (st.s - 1) ∈
      Protocol.get_filtered_block_tree st.toFG := by
    change Protocol.get_head_in_tree_with_layer gc S.E S.hc st
        (Protocol.get_filtered_block_tree st.toFG)
        votes.toFinset support.toFinset (st.s - 1) ∈
      Protocol.get_filtered_block_tree st.toFG
    rw [Proofs.Optimistic.get_head_in_tree_split_with]
    exact Proofs.Records.ghost_mem_of _ _ hanchor (Finset.Subset.refl _)
  simpa only [proposedParent, proposalInputAt, Protocol.proposal_input_with,
    Protocol.with_proposal_input, DutyInputDefaults.proposal_input_parent,
    n, st, gc, votes, support] using hhead






#print axioms selectedOpeningProposedParent_mem_filtered

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
