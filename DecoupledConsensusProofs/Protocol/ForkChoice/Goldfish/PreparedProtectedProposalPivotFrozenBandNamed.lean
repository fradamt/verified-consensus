module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PreparedProtectedProposalPivot
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGOpeningFrozenSuffix

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Prepared protected pivot to frozen proposal bands

The proof-only prepared pivot already contains the two reader-local named
height bounds. This leaf packages them with the candidate geometry required
by the moving-frontier suffix interface.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A prepared protected proposal pivot supplies the moving-frontier frozen
suffix inputs. -/
theorem PreparedProtectedProposalPivot.frozenBandInputs
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {d : Slot} {v : V} {A B : NamedBlock V}
    (hB : proposedBlockAt S rho (d + 1) = some B)
    (hcandidate : B.erase ∈ voterCandidateTreeAt S rho v (d + 1))
    (hpivot : PreparedProtectedProposalPivot S rho d v A) :
    NamedFrozenProposalSuffixBandInputs
      S rho (d + 1) A.erase v B := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho v (d + 1)
  let st := read.st.core
  have hproposalFiltered : B.erase ∈
      Protocol.get_filtered_block_tree st.toHealing.toFG := by
    apply frozenVoterCandidateTree_subset_filtered S.E st.toHealing
    simpa only [st, read, voterCandidateTreeAt] using hcandidate
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg read.st := by
    simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Run.storeBeforeTime] using
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
        (Protocol.vote_time S.E (d + 1)) v).1.1.1
  have hpivotT : A.erase ∈ st.T := by
    change A.erase ∈ read.st.core.T
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hpivot.targetBody
  have hparentProposal : Block.Preceq
      (proposedParent S rho (d + 1)) B.erase := by
    rw [← proposedBlockErased_parent S rho (d + 1) hB]
    exact preceq_parent B.erase
  have hpivotProposal : Block.Preceq A.erase B.erase :=
    Block.preceq_trans hpivot.parent hparentProposal
  have hrootPivot : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) A.erase := by
    exact Block.preceq_trans
      (NamedOutageClosure.fg_root_preceq_anchor S.E S.hc st.toHealing
        (S.hc.round_of st.s)
        (DecoupledConsensusModel.Protocol.readFrame read.cache st.toHealing
          (S.hc.round_of st.s)).g1)
      (by simpa only [st, read, voterAnchorAt] using hpivot.targetAnchor)
  have hFJ : Block.Preceq st.F st.J := by
    simpa only [st, read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using
      (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho (Protocol.vote_time S.E (d + 1)) v)
  have hpivotFiltered : A.erase ∈
      Protocol.get_filtered_block_tree st.toHealing.toFG :=
    Proofs.Records.mem_filtered_of_preceq (st := st.toHealing.toFG) hFJ
      hproposalFiltered hpivotT hpivotProposal hrootPivot
  have hsourceView :
      ((proposerReadAt S rho (d + 1)).st.core.σ A.erase).h =
        (Protocol.derive_named S.E S.cfg A).h := by
    have hbody : A ∈ (rho.stateBeforeTime S
        (Protocol.proposal_time S.E (d + 1)) (S.E.proposer (d + 1))).st.bodies := by
      simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hpivot.sourceBody
    simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using congrArg (fun x => x.h)
        (Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
          (Protocol.proposal_time S.E (d + 1))
          (S.E.proposer (d + 1)) A hbody)
  have htargetView :
      (st.σ A.erase).h = (Protocol.derive_named S.E S.cfg A).h := by
    have hbody : A ∈ (rho.stateBeforeTime S
        (Protocol.vote_time S.E (d + 1)) v).st.bodies := by
      simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hpivot.targetBody
    simpa only [st, read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using congrArg (fun x => x.h)
        (Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
          (Protocol.vote_time S.E (d + 1)) v A hbody)
  exact
    { sourceAnchor := hpivot.sourceAnchor
      pivotTarget := by simpa only [st, read] using hpivotFiltered
      proposalCandidate := hcandidate
      pivotAnchorCompatible :=
        Block.compatible_of_preceq_common hpivot.targetAnchor
          (Block.preceq_self A.erase)
      proposalAnchorCompatible :=
        Block.compatible_of_preceq_common
          (Block.preceq_trans hpivot.targetAnchor hpivotProposal)
          (Block.preceq_self B.erase)
      sourceBand := by rw [hsourceView]; exact hpivot.sourceBand
      targetBand := by rw [htargetView]; exact hpivot.targetBand }

#print axioms PreparedProtectedProposalPivot.frozenBandInputs

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
