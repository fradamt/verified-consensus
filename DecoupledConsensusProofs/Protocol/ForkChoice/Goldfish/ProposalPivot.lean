module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalWalkTransportCore
public import DecoupledConsensusProofs.Execution.StoreFinalityCore
public import DecoupledConsensusProofs.Protocol.Handlers.Blocks
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.FrontierProducers
public import DecoupledConsensusProofs.Execution.ProposerCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryFinalityFilterRetainedVoteConeSeed
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusInternal.Definitions.NamedProposalPivot

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

































/-! ## Frozen candidate membership supplies the stored path -/

/-- Restricting the processed-block domain can only remove candidates: every
restricted member and viability witness is also present in the full tree. -/
private theorem voter_candidate_tree_subset_filtered
    (E : Env V) (st : Protocol.HealingStore V) :
    Proofs.Optimistic.voter_candidate_tree E st ⊆
      Protocol.get_filtered_block_tree st.toFG := by
  intro B hB
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hB ⊢
  obtain ⟨⟨⟨hBprocessed, hFB⟩, W, hWprocessed, hBW, hheight⟩,
    hroot⟩ := hB
  have hBT : B ∈ st.T := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      at hBprocessed
    exact hBprocessed.1
  have hWT : W ∈ st.T := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      at hWprocessed
    exact hWprocessed.1
  exact ⟨⟨⟨hBT, hFB⟩, W, hWT, hBW, hheight⟩, hroot⟩


/-! ## Proposer-side and voter-side walk readings -/







#print axioms voter_candidate_tree_subset_filtered




/-! ## Named prepared-read proposal walk -/

private theorem named_voter_candidate_tree_subset_filtered
    (E : Env V) (st : Protocol.Store V) :
    Protocol.voter_filtered_block_tree E st st.s ⊆
      Protocol.get_filtered_block_tree st.toHealing.toFG := by
  intro B hB
  have hB' : B ∈ Proofs.Optimistic.voter_candidate_tree E st.toHealing := by
    simpa only [Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree] using hB
  exact voter_candidate_tree_subset_filtered E st.toHealing hB'

private theorem named_rootInjectiveBelow_source_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {s : Slot} (hprop : S.E.proposer s ∈ rho.honest) :
    RootInjectiveBelow (Proofs.HealingSurface.namedWalkSourceTree S rho s) := by
  let t := Protocol.proposal_time S.E s
  let n := NamedRun.stateBeforeTime S rho t (S.E.proposer s)
  obtain ⟨i, hi, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed t
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg n.st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t
      (S.E.proposer s)).1.1.1
  have hrun : ∀ C ∈ n.st.bodies, RunBlock S rho C := by
    intro C hC
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hprop (i := i)
    rw [← congrArg (fun w => (w (S.E.proposer s)).st.bodies) hi]
    exact hC
  have hinj := Proofs.Bridges.rootInjectiveBelow_of_runBlocks S
    adm.toNamedRootCollisionFree hrun
  rw [← hcoh.1] at hinj
  intro A C hA hC hroot
  refine hinj A C ?_ ?_ hroot
  · obtain ⟨B, hB, hAB⟩ := hA
    have hBT : B ∈ n.st.core.T := by
      simpa only [n, t, Proofs.HealingSurface.namedWalkSourceTree,
        Internal.NamedRecoveryRead.proposalDutyRead, Statements.Instantiation.proposerReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
        (Proofs.Records.get_filtered_block_tree_subset _ hB)
    exact ⟨B, hBT, hAB⟩
  · obtain ⟨B, hB, hCB⟩ := hC
    have hBT : B ∈ n.st.core.T := by
      simpa only [n, t, Proofs.HealingSurface.namedWalkSourceTree,
        Internal.NamedRecoveryRead.proposalDutyRead, Statements.Instantiation.proposerReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
        (Proofs.Records.get_filtered_block_tree_subset _ hB)
    exact ⟨B, hBT, hCB⟩


set_option maxHeartbeats 800000 in
private theorem named_rootInjectiveBelow_target_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {s : Slot} {v : V} (hv : v ∈ rho.honest)
    {P : NamedBlock V} :
    RootInjectiveBelow (Proofs.HealingSurface.namedWalkTargetTree S rho s v P) := by
  let t := Protocol.vote_time S.E s
  let n := NamedRun.stateBeforeTime S rho t v
  obtain ⟨i, hi, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed t
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg n.st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).1.1.1
  have hrun : ∀ C ∈ n.st.bodies, RunBlock S rho C := by
    intro C hC
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := i)
    rw [← congrArg (fun w => (w v).st.bodies) hi]
    exact hC
  have hinj := Proofs.Bridges.rootInjectiveBelow_of_runBlocks S
    adm.toNamedRootCollisionFree hrun
  rw [← hcoh.1] at hinj
  intro A C hA hC hroot
  refine hinj A C ?_ ?_ hroot
  · obtain ⟨B, hB, hAB⟩ := hA
    have hBtree : B ∈ Proofs.HealingSurface.voterCandidateTreeAt S rho v s :=
      Finset.mem_of_mem_erase hB
    have hBfull : B ∈ Protocol.voter_filtered_block_tree S.E
        (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core
        (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.s := by
      exact hBtree
    have hBT : B ∈ n.st.core.T := by
      have hBfiltered : B ∈ Protocol.get_filtered_block_tree
          (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.toHealing.toFG :=
        named_voter_candidate_tree_subset_filtered
          S.E (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core hBfull
      have hBTread : B ∈
          (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.T :=
        Proofs.Records.get_filtered_block_tree_subset
          (st := (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.toHealing.toFG)
          hBfiltered
      change B ∈ n.st.core.T at hBTread
      exact hBTread
    exact ⟨B, hBT, hAB⟩
  · obtain ⟨B, hB, hCB⟩ := hC
    have hBtree : B ∈ Proofs.HealingSurface.voterCandidateTreeAt S rho v s :=
      Finset.mem_of_mem_erase hB
    have hBfull : B ∈ Protocol.voter_filtered_block_tree S.E
        (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core
        (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.s := by
      exact hBtree
    have hBT : B ∈ n.st.core.T := by
      have hBfiltered : B ∈ Protocol.get_filtered_block_tree
          (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.toHealing.toFG :=
        named_voter_candidate_tree_subset_filtered
          S.E (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core hBfull
      have hBTread : B ∈
          (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.T :=
        Proofs.Records.get_filtered_block_tree_subset
          (st := (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.toHealing.toFG)
          hBfiltered
      change B ∈ n.st.core.T at hBTread
      exact hBTread
    exact ⟨B, hBT, hCB⟩


private theorem named_voter_path_of_candidate_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {s : Slot} {v : V} {P : NamedBlock V}
    (hP : P.erase ∈ Proofs.HealingSurface.voterCandidateTreeAt S rho v s)
    (hslot : P.slot = s) :
    ∀ C : Block V,
      Block.Preceq (Proofs.HealingSurface.voterAnchorAt S rho v s) C →
      C ≠ Proofs.HealingSurface.voterAnchorAt S rho v s →
      Block.Preceq C P.erase →
      C ∈ Proofs.HealingSurface.voterCandidateTreeAt S rho v s := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho v s
  let st := read.st.core
  let tree := Proofs.HealingSurface.voterCandidateTreeAt S rho v s
  have hPfull : P.erase ∈ Protocol.get_filtered_block_tree st.toHealing.toFG := by
    have hPtree : P.erase ∈ Protocol.voter_filtered_block_tree S.E st st.s := by
      exact hP
    exact named_voter_candidate_tree_subset_filtered S.E st hPtree
  have hFJ : Block.Preceq st.F st.J := by
    simpa only [st, read] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (Protocol.vote_time S.E s) v
  have hPmem : P.erase ∈ st.T :=
    Proofs.Records.get_filtered_block_tree_subset st.toHealing.toFG hPfull
  intro C hAC hCne hCP
  have hCT : C ∈ st.T := by
    have hpc0 := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (Protocol.vote_time S.E s) v
    have hpc : ParentClosed st := by
      change ParentClosed st at hpc0
      exact hpc0
    exact Proofs.Records.mem_of_preceq ((Proofs.parentClosed_iff st).mp hpc).2 C P.erase
      hPmem hCP
  have hroot : Block.Preceq (Protocol.get_fg_root st.toHealing.toFG) C :=
    Block.preceq_trans
      (Proofs.HealingSurface.fg_root_preceq_get_sg_root_with_frame
        read.cache S.E S.hc st.toHealing (S.hc.round_of st.s)) hAC
  have hCfull := Proofs.Records.mem_filtered_of_preceq
    (st := st.toHealing.toFG) (show Block.preceq st.F st.J = true from hFJ)
    hPfull hCT hCP hroot
  have hPold : P.erase ∈ Proofs.Optimistic.voter_candidate_tree S.E st.toHealing := by
    simpa only [Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree] using hP
  have hPdata := hPold
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.voter_processed_block_tree,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hPdata
  have hCdata := hCfull
  simp only [Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable,
    Finset.mem_filter, decide_eq_true_eq] at hCdata
  obtain ⟨W, hWprocessed, hPW, hheight⟩ := hPdata.1.2
  have hCprocessed : C ∈ Protocol.voter_processed_block_tree S.E
      st.toHealing.toFG.toSG.toGoldfishStore st.s := by
    have hPslot : P.erase.slot = st.s := by
      calc
        P.erase.slot = s := by rw [Proofs.NamedWire.erase_slot]; exact hslot
        _ = st.s := by
          simpa only [st, read] using
            (Proofs.Optimistic.voteDutyRead_slot S rho v s).symm
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    exact ⟨hCT, Or.inr ⟨P.erase, ⟨hPmem, hPslot⟩, hCP⟩⟩
  change C ∈ Proofs.Optimistic.voter_candidate_tree S.E st.toHealing
  have hWprocessed' : W ∈ Protocol.voter_processed_block_tree S.E
      st.toHealing.toFG.toSG.toGoldfishStore st.s := by
    simpa only [Protocol.voter_processed_block_tree, Finset.mem_filter] using
      hWprocessed
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
  exact ⟨⟨⟨hCprocessed, hCdata.1.1.2⟩, W, hWprocessed',
    Block.preceq_trans hCP hPW, hheight⟩, hCdata.2⟩


theorem namedProposalWalkTransferred_of_frozenCompatiblePivot_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {s : Slot} {P : NamedBlock V}
    (hP : Statements.Instantiation.proposedBlockAt S rho s = some P)
    (hprop : S.E.proposer s ∈ rho.honest)
    {pivot : Block V} {v : V} (hv : v ∈ rho.honest)
    (hcandidate : P.erase ∈ Proofs.HealingSurface.voterCandidateTreeAt S rho v s)
    (hcompat : Block.compatible
      (Proofs.HealingSurface.voterAnchorAt S rho v s) P.erase = true)
    (hsourcePivot : Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract
          (Statements.Instantiation.proposerReadAt S rho s).cache)
        S.E S.hc
        (Statements.Instantiation.proposerReadAt S rho s).st.core.toHealing
        (S.hc.round_of
          (Statements.Instantiation.proposerReadAt S rho s).st.core.s)) pivot)
    (hpivotParent : Block.Preceq pivot
      (Proofs.HealingSurface.proposedParent S rho s))
    (htargetPasses : Block.Preceq pivot
      (Protocol.ghost
        (Proofs.HealingSurface.voterAnchorAt S rho v s)
        (Proofs.HealingSurface.namedWalkTargetTree S rho s v P)
        (Proofs.HealingSurface.namedWalkTargetScore S rho s v)
        (Proofs.HealingSurface.namedWalkTargetEligible S rho s v)))
    (hsuffix : Proofs.HealingSurface.NamedProposalPivotSuffixTransfer
      S rho s pivot v P)
    (hscore : ∀ C,
      C ∈ Proofs.HealingSurface.namedWalkSourceTree S rho s →
      C ∈ Proofs.HealingSurface.namedWalkTargetTree S rho s v P →
      Proofs.HealingSurface.namedWalkTargetScore S rho s v C =
        Proofs.HealingSurface.namedWalkSourceScore S rho s C) :
    Proofs.Optimistic.NamedVoteStoreExtends S rho v s
      (Proofs.HealingSurface.namedWalkTargetTree S rho s v P)
      (Proofs.HealingSurface.proposedParent S rho s) P := by
  let source := Statements.Instantiation.proposerReadAt S rho s
  let target := Internal.NamedRecoveryRead.voteDutyRead S rho v s
  let sourceAnchor := Protocol.get_sg_root_with
    (NamedProfile.gradeContract source.cache) S.E S.hc source.st.core.toHealing
    (S.hc.round_of source.st.core.s)
  let targetAnchor := Proofs.HealingSurface.voterAnchorAt S rho v s
  let H := Proofs.HealingSurface.proposedParent S rho s
  have hslot : P.slot = s := DecoupledConsensusModel.Proofs.Optimistic.proposedBlockAt_slot S rho s hP
  have hslotErase : P.erase.slot = s := by
    rw [Proofs.NamedWire.erase_slot]
    exact hslot
  have hparent : P.erase.parent? = some H := by
    obtain ⟨Q, hQ, hQerase⟩ := DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_parent S rho s hP
    have hQerase' : Q.erase = H := by simpa only [H] using hQerase
    simpa only [Proofs.NamedWire.erase_parent_optional, hQ, Option.map_some, hQerase']
  have hcandidate' : P.erase ∈ Proofs.Optimistic.voter_candidate_tree S.E
      target.st.core.toHealing := by
    simpa only [target, Proofs.HealingSurface.voterCandidateTreeAt] using hcandidate
  have hsourceRoot := named_rootInjectiveBelow_source_core S adm hprop
  have htargetRoot := named_rootInjectiveBelow_target_core S adm (s := s) hv (P := P)
  have hsource : Protocol.ghost sourceAnchor
      (Proofs.HealingSurface.namedWalkSourceTree S rho s)
      (Proofs.HealingSurface.namedWalkSourceScore S rho s)
      (Proofs.HealingSurface.namedWalkSourceEligible S rho s) = H := by
    rfl
  have hfullPath := named_voter_path_of_candidate_core S adm hcandidate hslot
  have hpath : ∀ C : Block V,
      Block.Preceq targetAnchor C → C ≠ targetAnchor →
      Block.Preceq C H →
      C ∈ Proofs.HealingSurface.namedWalkTargetTree S rho s v P := by
    intro C hAC hCne hCH
    have hPH : Block.Preceq H P.erase := preceq_of_parent? hparent
    have hCP : Block.Preceq C P.erase := Block.preceq_trans hCH hPH
    have hCfull := hfullPath C hAC hCne hCP
    change C ∈ (Proofs.HealingSurface.voterCandidateTreeAt S rho v s).erase P.erase
    rw [Finset.mem_erase]
    refine ⟨?_, hCfull⟩
    intro hEq
    subst C
    have hdepth := Block.preceq_depth_le hCH
    have hstrict : H.depth < P.erase.depth := by
      have hparentDepth : P.erase.depth = H.depth + 1 :=
        depth_of_parent? hparent
      omega
    exact (Nat.not_lt_of_ge hdepth) hstrict
  have hforward : Block.Preceq targetAnchor P.erase →
      Block.Preceq P.erase
        (Protocol.ghost targetAnchor
          (Proofs.HealingSurface.voterCandidateTreeAt S rho v s)
          (Proofs.HealingSurface.namedWalkTargetScore S rho s v)
          (Proofs.HealingSurface.namedWalkTargetEligible S rho s v)) := by
    intro hAP
    by_cases hEq : targetAnchor = P.erase
    · rw [hEq]
      exact ghost_preceq _ _ _ _
    · have hAH : Block.Preceq targetAnchor H :=
        Proofs.Optimistic.preceq_parent_of_ne hparent hAP hEq
      obtain ⟨hstopped, hwalk⟩ :=
        ghost_transport_via_bridge_of_target_passes
          hsourceRoot htargetRoot hsource hsourcePivot hpivotParent hAH
          hpath htargetPasses hsuffix.persist hsuffix.reflect hscore
      have htree : Proofs.HealingSurface.voterCandidateTreeAt S rho v s =
          insert P.erase
            (Proofs.HealingSurface.namedWalkTargetTree S rho s v P) := by
        change Proofs.HealingSurface.voterCandidateTreeAt S rho v s =
          insert P.erase
            ((Proofs.HealingSurface.voterCandidateTreeAt S rho v s).erase P.erase)
        exact (Finset.insert_erase hcandidate).symm
      have hnotin : P.erase ∉
          Proofs.HealingSurface.namedWalkTargetTree S rho s v P :=
        (Proofs.HealingSurface.voterCandidateTreeAt S rho v s).notMem_erase P.erase
      have helig : Proofs.HealingSurface.namedWalkTargetEligible S rho s v P.erase = true := by
        have hcur : P.erase.slot = target.st.core.s := by
          calc
            P.erase.slot = s := hslotErase
            _ = target.st.core.s :=
              (show target.st.core.s = s from
                Proofs.Optimistic.voteDutyRead_slot S rho v s).symm
        simpa only [Proofs.HealingSurface.namedWalkTargetEligible, target,
          Protocol.Store.toHealing] using
          Proofs.Optimistic.goldfish_eligible_current S.E target.st.core.toHealing.σ
            target.st.core.toHealing.h_max target.st.core.T target.st.core.s
            (Protocol.voter_view S.E target.st.core.toHealing.toFG.toSG.toGoldfishStore target.st.core.s)
            (Protocol.voter_support_view S.E
              target.st.core.toHealing.toFG.toSG.toGoldfishStore target.st.core.s)
            (target.st.core.s - 1) hcur
      have hfresh : ∀ C ∈ Proofs.HealingSurface.namedWalkTargetTree S rho s v P,
          C.parent? ≠ some P.erase := by
        intro C hC
        exact candidate_leaf_at_vote_core S adm hslotErase C
          (Finset.mem_of_mem_erase hC)
      rw [htree]
      have hinsert := Proofs.Optimistic.ghost_insert_eq hparent helig hnotin
        (fun C hC hCP => hstopped C hC hCP) hfresh hwalk
      rw [hinsert]
      exact Block.preceq_self _
  have hanchorTerminal : Block.Preceq P.erase targetAnchor →
      targetAnchor = P.erase := by
    intro hPA
    have hmem : targetAnchor ∈ target.st.core.T := by
      exact Proofs.NamedConfirmationMembership.runtime_anchor_mem target.cache
        S.E S.hc target.st.core.toHealing (S.hc.round_of target.st.core.s)
        (Proofs.NamedStoreRoots.fg_root_mem target.st
          (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
            (Protocol.vote_time S.E s) v).1.1.2)
    exact by
      apply voteDutyStore_terminal_of_preceq_core S adm hslotErase hmem
      exact hPA
  have htreeTerminal : ∀ X ∈
      Proofs.HealingSurface.voterCandidateTreeAt S rho v s,
      Block.Preceq P.erase X → X = P.erase := by
    intro X hX hPX
    exact voter_candidate_tree_terminal_of_preceq_core S adm hslotErase hX hPX
  have hhead : Protocol.ghost targetAnchor
      (Proofs.HealingSurface.voterCandidateTreeAt S rho v s)
      (Proofs.HealingSurface.namedWalkTargetScore S rho s v)
      (Proofs.HealingSurface.namedWalkTargetEligible S rho s v) = P.erase :=
    Proofs.Optimistic.ghost_eq_of_compatible_anchor_and_terminal
      hcompat hforward hanchorTerminal htreeTerminal
  refine { cur := ?_, parent := hparent, tree := ?_, fresh := ?_, leaf := ?_, head := ?_ }
  · calc
      P.slot = s := hslot
      _ = target.st.core.s :=
        (show target.st.core.s = s from
          Proofs.Optimistic.voteDutyRead_slot S rho v s).symm
  · change Proofs.HealingSurface.voterCandidateTreeAt S rho v s =
      insert P.erase
        ((Proofs.HealingSurface.voterCandidateTreeAt S rho v s).erase P.erase)
    exact (Finset.insert_erase hcandidate).symm
  · exact (Proofs.HealingSurface.voterCandidateTreeAt S rho v s).notMem_erase P.erase
  · exact fun C hC => candidate_leaf_at_vote_core S adm hslotErase C
      (Finset.mem_of_mem_erase hC)
  · change Internal.voterHeadAt S rho v s = P.erase
    dsimp only [Internal.voterHeadAt, target]
    simpa only [Proofs.Optimistic.get_head_in_tree_split_with,
      Proofs.HealingSurface.namedWalkTargetScore,
      Proofs.HealingSurface.namedWalkTargetEligible, Protocol.Store.toHealing] using hhead

theorem namedProposalWalkTransferred_of_frozenCompatiblePivot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {P : NamedBlock V}
    (hP : Statements.Instantiation.proposedBlockAt S rho s = some P)
    (hprop : S.E.proposer s ∈ rho.honest)
    {pivot : Block V} {v : V} (hv : v ∈ rho.honest)
    (hcandidate : P.erase ∈ Proofs.HealingSurface.voterCandidateTreeAt S rho v s)
    (hcompat : Block.compatible
      (Proofs.HealingSurface.voterAnchorAt S rho v s) P.erase = true)
    (hsourcePivot : Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract
          (Statements.Instantiation.proposerReadAt S rho s).cache)
        S.E S.hc
        (Statements.Instantiation.proposerReadAt S rho s).st.core.toHealing
        (S.hc.round_of
          (Statements.Instantiation.proposerReadAt S rho s).st.core.s)) pivot)
    (hpivotParent : Block.Preceq pivot
      (Proofs.HealingSurface.proposedParent S rho s))
    (htargetPasses : Block.Preceq pivot
      (Protocol.ghost
        (Proofs.HealingSurface.voterAnchorAt S rho v s)
        (Proofs.HealingSurface.namedWalkTargetTree S rho s v P)
        (Proofs.HealingSurface.namedWalkTargetScore S rho s v)
        (Proofs.HealingSurface.namedWalkTargetEligible S rho s v)))
    (hsuffix : Proofs.HealingSurface.NamedProposalPivotSuffixTransfer
      S rho s pivot v P)
    (hscore : ∀ C,
      C ∈ Proofs.HealingSurface.namedWalkSourceTree S rho s →
      C ∈ Proofs.HealingSurface.namedWalkTargetTree S rho s v P →
      Proofs.HealingSurface.namedWalkTargetScore S rho s v C =
        Proofs.HealingSurface.namedWalkSourceScore S rho s C) :
    Proofs.Optimistic.NamedVoteStoreExtends S rho v s
      (Proofs.HealingSurface.namedWalkTargetTree S rho s v P)
      (Proofs.HealingSurface.proposedParent S rho s) P :=
  namedProposalWalkTransferred_of_frozenCompatiblePivot_core S
    (rho := rho) adm.toNamedAdmissibleCore (s := s) (P := P) hP hprop
      (pivot := pivot) (v := v) hv hcandidate hcompat hsourcePivot
      hpivotParent htargetPasses hsuffix hscore

#print axioms namedProposalWalkTransferred_of_frozenCompatiblePivot_core
#print axioms namedProposalWalkTransferred_of_frozenCompatiblePivot

end Protocol
end DecoupledConsensusModel

end
