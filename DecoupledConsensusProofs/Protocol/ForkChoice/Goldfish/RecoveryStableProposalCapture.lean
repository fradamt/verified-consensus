module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryCapturedActionCarrier
public import DecoupledConsensusProofs.Generic.RecoveryConcentration
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryFreshGradeProvenance
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.RecoveryVoteCone
public import DecoupledConsensusProofs.Protocol.Store.HonestPoolActionBridge
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingBoundaryCanonicality
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGProposalLifecycle
public import DecoupledConsensusProofs.Protocol.Grades.ProposalLifecycleCore
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryProposalConfirmation
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalPivot
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Stable recovery-proposal capture

This module packages the checked capture half of the stable recovery branch.
The exact honest opening proposal is selected and genuinely confirmed at every
honest action store. Its edge above the protected grade then constructs the
stable-capture window used by the next-round absorption proof.

The package open items before Goldfish lock-in. In particular, it does not assume
that later confirmations already descend from the captured proposal.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem fixedHeight_voterCandidateTree_subset_filtered
    (E : Env V) (st : Protocol.Store V) :
    Protocol.voter_filtered_block_tree E st st.s ⊆
      Protocol.get_filtered_block_tree st.toHealing.toFG := by
  intro B hB
  have hB' : B ∈ Proofs.Optimistic.voter_candidate_tree E st.toHealing := by
    simpa only [Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree]
      using hB
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable,
    Finset.mem_filter, decide_eq_true_eq] at hB' ⊢
  obtain ⟨⟨⟨hBprocessed, hFB⟩, W, hWprocessed, hBW, hheight⟩,
    hroot⟩ := hB'
  have hBT : B ∈ st.T := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      at hBprocessed
    exact hBprocessed.1
  have hWT : W ∈ st.T := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      at hWprocessed
    exact hWprocessed.1
  exact ⟨⟨⟨hBT, hFB⟩, W, hWT, hBW, hheight⟩, hroot⟩

/-- Fixed-root cone, parent, frozen-vote, and score facts transfer every
opening committee member's prepared proposal walk. -/
theorem fixedHeightJustificationRoot_namedOpeningVoteStoresExtend
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hconfHor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {A : Block V} {P : NamedBlock V}
    (hP : proposedBlockAt S rho (s + 1) = some P)
    (hprop : S.E.proposer (s + 1) ∈ rho.honest)
    (hcone : NamedHonestVotesCone S rho s (fun X => Block.Preceq A X))
    (hsourceAnchor : Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract (proposerReadAt S rho (s + 1)).cache)
        S.E S.hc (proposerReadAt S rho (s + 1)).st.core.toHealing
        (S.hc.round_of (proposerReadAt S rho (s + 1)).st.core.s)) A)
    (hpivotParent : Block.Preceq A (proposedParent S rho (s + 1)))
    (hfrozen : ∀ v ∈ rho.honest, v ∈ S.E.committee (s + 1) →
      NamedSGOpeningFrozenVoteAt S rho s A v P)
    (hscore : ∀ v ∈ rho.honest, ∀ C,
      C ∈ namedWalkSourceTree S rho (s + 1) →
      C ∈ namedWalkTargetTree S rho (s + 1) v P →
      namedWalkTargetScore S rho (s + 1) v C =
        namedWalkSourceScore S rho (s + 1) C) :
    Protocol.VoteStoresExtend S rho (s + 1) P := by
  intro v hv hcommittee
  have frozen := hfrozen v hv hcommittee
  let read := voteDutyRead S rho v (s + 1)
  let st := read.st.core
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  have hcandidate : A ∈ voterCandidateTreeAt S rho v (s + 1) :=
    Finset.mem_of_mem_erase frozen.pivotCandidate
  have hfiltered : A ∈ Protocol.get_filtered_block_tree st.toHealing.toFG := by
    apply fixedHeight_voterCandidateTree_subset_filtered S.E st
    simpa only [st, read, voterCandidateTreeAt] using hcandidate
  have hroot : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) A :=
    Proofs.Records.preceq_get_fg_root_of_mem_filtered hfiltered
  have hinputs : GoldfishConeVoteInputs S rho s A v :=
    { candidate := hcandidate
      root := by simpa only [st, read] using hroot
      anchor := frozen.pivotAnchorCompatible
      path := by
        intro D hAD hDne hDA _
        exact Finset.mem_of_mem_erase
          (frozen.pivotPath (Block.preceq_trans hAD hDA) D hAD hDne hDA) }
  have hwalk := goldfishCone_pathEligible S adm hcom hs hpost hconfHor
    hcone hv hinputs
  have hhead := Protocol.goldfish_fork_choice_captures_supporter_majority
    S.E st.σ st.h_max st.T
      (namedWalkTargetTree S rho (s + 1) v P) st.s votes support
      (st.s - 1) (Proofs.Optimistic.ConeSupport.sub hwalk.1) hwalk.2.1
      frozen.pivotAnchorCompatible frozen.pivotPath
  have htargetPasses : Block.Preceq A
      (Protocol.ghost (voterAnchorAt S rho v (s + 1))
        (namedWalkTargetTree S rho (s + 1) v P)
        (namedWalkTargetScore S rho (s + 1) v)
        (namedWalkTargetEligible S rho (s + 1) v)) := by
    simpa only [Protocol.goldfish_fork_choice,
      namedWalkTargetScore, namedWalkTargetEligible, st, read, votes, support]
      using hhead
  exact ⟨namedWalkTargetTree S rho (s + 1) v P,
    proposedParent S rho (s + 1),
    Protocol.namedProposalWalkTransferred_of_frozenCompatiblePivot
      S adm hP hprop hv frozen.proposalCandidate
        frozen.proposalAnchorCompatible hsourceAnchor hpivotParent
        htargetPasses frozen.suffix (hscore v hv)⟩

#print axioms fixedHeightJustificationRoot_namedOpeningVoteStoresExtend












end HealingSurface
end Proofs
end DecoupledConsensusModel

end
