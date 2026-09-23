module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGOpeningFrozenSuffix

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Common prepared proposal-candidate score equality

The candidate-local proposal snapshot bridge identifies the proposer and
voter Goldfish scores on every candidate shared by the two prepared walks.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every candidate common to the prepared proposal and voter walks has the
same Goldfish score after GST. -/
theorem namedProposalScoreEq_afterGST_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    (hcandidate : B.erase ∈ voterCandidateTreeAt S rho v s) :
    ∀ C,
      C ∈ namedWalkSourceTree S rho s →
      C ∈ namedWalkTargetTree S rho s v B →
      namedWalkTargetScore S rho s v C = namedWalkSourceScore S rho s C := by
  intro C hCsource hCtarget
  have hproposalFull : B.erase ∈ Protocol.get_filtered_block_tree
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG :=
    frozenVoterCandidateTree_subset_filtered S.E _ hcandidate
  have hCtargetFrozen : C ∈ voterCandidateTreeAt S rho v s :=
    Finset.mem_of_mem_erase hCtarget
  have hCtargetFull : C ∈ Protocol.get_filtered_block_tree
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG :=
    frozenVoterCandidateTree_subset_filtered S.E _ hCtargetFrozen
  have hbridge := namedProposalCandidateScoreBridge_afterGST_core
    S adm hs hpost hprop hv hvoteHor hB hproposalFull
  have hscore := (hbridge C hCsource hCtargetFull).goldfish_score_eq
    S.E (s - 1)
  have hraw : B.erase.gf_votes.toFinset =
      (Protocol.proposer_view
        (Protocol.proposerDutyStore S rho s).toHealing.toFG.toSG.toGoldfishStore
        (Protocol.proposerDutyStore S rho s).s).toFinset := by
    rw [Proofs.NamedWire.erase_goldfish_votes,
      Protocol.proposedBlock_gf_votes S rho s hB]
    rfl
  have hsupport : B.erase.gf_support_votes.toFinset =
      (Protocol.proposer_support_view
        (Protocol.proposerDutyStore S rho s).toHealing.toFG.toSG.toGoldfishStore
        (Protocol.proposerDutyStore S rho s).s).toFinset := by
    rw [Proofs.NamedWire.erase_goldfish_support,
      Protocol.proposedBlock_gf_support_votes S rho s hB]
    rfl
  rw [hraw, hsupport] at hscore
  have hsourceEq :
      (Internal.NamedRecoveryRead.proposalDutyRead S rho s).st.core =
        Protocol.proposerDutyStore S rho s := rfl
  have htargetEq :
      (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core =
        Proofs.Optimistic.voteDutyStore S rho v s := rfl
  have hsourceSlot : (Protocol.proposerDutyStore S rho s).s = s := by
    simp only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      Proofs.Optimistic.slotOf_proposal_time]
  have htargetSlot : (Proofs.Optimistic.voteDutyStore S rho v s).s = s :=
    Proofs.Optimistic.voteDutyStore_slot S rho v s
  symm
  simpa only [namedWalkSourceScore, namedWalkTargetScore,
    hsourceEq, htargetEq, hsourceSlot, htargetSlot] using hscore

#print axioms namedProposalScoreEq_afterGST_core

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
