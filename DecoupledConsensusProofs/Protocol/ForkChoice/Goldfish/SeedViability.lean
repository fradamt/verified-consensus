module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FrontierParent
public import DecoupledConsensusProofs.Protocol.Grades.GoldfishConePersistence
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGTargetCanonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalPivot
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.Handlers.HonestProposalAdmission
public import DecoupledConsensusProofs.Protocol.Schedule.WeakProcessedTree
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Protocol
open Internal.NamedRecoveryRead
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Pure two-view majority extraction -/




/-! ## Named vote-duty store invariants -/

/-- The prepared vote-duty read exposes the local named store invariants and
root injectivity needed by the frozen-candidate arguments. -/
theorem voteDuty_parentClosed_agrees_rootInjective
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) (d : Slot) :
    let read := voteDutyRead S rho w d
    NamedStore.NamedParentClosed read.st ∧
      Internal.NamedDerivedStateAgrees S.E S.cfg read.st ∧
      RootInjectiveBelow read.st.core.T := by
  let read := voteDutyRead S rho w d
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg read.st := by
    simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime] using
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
        (Protocol.vote_time S.E d) w).1.1.1
  have hinj : RootInjectiveBelow (read.st.bodies.image NamedBlock.erase) := by
    apply Proofs.Bridges.rootInjectiveBelow_of_runBlocks S
      adm.toNamedAdmissibleCore.toNamedRootCollisionFree
    intro C hC
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.vote_time S.E d)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i := n)
    have hCpre : C ∈
        (rho.stateBeforeTime S (Protocol.vote_time S.E d) w).st.bodies := by
      simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Run.storeBeforeTime] using hC
    rw [hn] at hCpre
    exact hCpre
  refine ⟨hcoh.2.2.1, hcoh.2.2.2.2, ?_⟩
  have htree : (voteDutyRead S rho w d).st.core.T =
      (voteDutyRead S rho w d).st.bodies.image NamedBlock.erase := by
    simpa only [read] using hcoh.1
  rw [htree]
  exact hinj

/-- A child towards a frozen viability witness remains in the prepared
candidate tree. -/
theorem namedFrozenCandidate_child_towards_witness
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {H W D : Block V}
    (hHcandidate : H ∈ voterCandidateTreeAt S rho w (s + 1))
    (hWprocessed : W ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (voteDutyStore S rho w (s + 1)).toHealing.s)
    (hDparent : D.parent? = some H)
    (hDW : Block.Preceq D W)
    (hWheight : (voteDutyStore S rho w (s + 1)).h_max - 1 ≤
      ((voteDutyStore S rho w (s + 1)).σ W).h) :
    D ∈ voterCandidateTreeAt S rho w (s + 1) := by
  let duty := voteDutyStore S rho w (s + 1)
  have hfacts := voteDuty_parentClosed_agrees_rootInjective S adm hw (s + 1)
  have hpc : ParentClosed duty := by
    simpa only [duty, voteDutyStore, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime] using
      Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w
  have hHfull : H ∈ Protocol.get_filtered_block_tree duty.toHealing.toFG := by
    have hdata := hHcandidate
    simp only [voterCandidateTreeAt, Protocol.voter_filtered_block_tree,
      Protocol.get_filtered_block_tree,
      Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Protocol.voter_processed_block_tree, Finset.mem_filter,
      decide_eq_true_eq] at hdata ⊢
    obtain ⟨⟨⟨hHprocessed, hFH⟩, Z, hZprocessed, hHZ, hZheight⟩,
      hrootH⟩ := hdata
    exact ⟨⟨⟨hHprocessed.1, hFH⟩, Z,
      hZprocessed.1, hHZ, hZheight⟩, hrootH⟩
  have hHdata := hHfull
  simp only [Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable,
    Finset.mem_filter, decide_eq_true_eq] at hHdata
  have hWT : W ∈ duty.T := by
    have hdata := hWprocessed
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    exact hdata.1
  have hDT : D ∈ duty.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff duty).mp hpc).2 D W hWT hDW
  have hHD : Block.Preceq H D := preceq_of_parent? hDparent
  have hFD : Block.Preceq duty.F D := Block.preceq_trans hHdata.1.1.2 hHD
  have hrootD : Block.Preceq
      (Protocol.get_fg_root duty.toHealing.toFG) D :=
    Block.preceq_trans hHdata.2 hHD
  have hDprocessed : D ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s := by
    simpa only [duty] using
      WeakGoldfish.ancestorProcessed_of_voterProcessed
        S adm.toNamedAdmissibleCore hw hWprocessed D hDW
  simp only [voterCandidateTreeAt, Protocol.voter_filtered_block_tree,
    Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable,
    Finset.mem_filter, decide_eq_true_eq]
  exact ⟨⟨⟨hDprocessed, hFD⟩, W, hWprocessed, hDW, hWheight⟩, hrootD⟩

/-- A named processed descendant at the frontier makes every filtered
ancestor a prepared voter candidate. -/
theorem namedAncestorCandidate_of_processedDescendant_and_hMax_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot}
    {C : Block V} {H : NamedBlock V}
    (hHprocessed : H.erase ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (voteDutyStore S rho w (s + 1)).toHealing.s)
    (hHrun : RunBlock S rho H) (hCH : Block.Preceq C H.erase)
    (hCfiltered : C ∈ Protocol.get_filtered_block_tree
      (voteDutyStore S rho w (s + 1)).toHealing.toFG)
    (hmax : (voteDutyStore S rho w (s + 1)).h_max ≤
      (derive_named S.E S.cfg H).h + 1) :
    C ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (voteDutyStore S rho w (s + 1)).toHealing := by
  let time := Protocol.vote_time S.E (s + 1)
  have hHT : H.erase ∈ (rho.stateBeforeTime S time w).st.core.T := by
    have hdata := hHprocessed
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    simpa only [time, voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hdata.1
  obtain ⟨Hn, hHnbody, hHnerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho time w hHT
  have hHnrun : RunBlock S rho Hn := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedScheduleWellFormed time
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i := n)
    rw [← hn]
    exact hHnbody
  have hHnEq : Hn = H := by
    apply adm.toNamedRootCollisionFree.root_injective
      Hn H hHnrun hHrun Hn H (Or.inl (Proofs.NamedAncestry.named_self Hn))
      (Or.inr (Proofs.NamedAncestry.named_self H))
    rw [← Proofs.NamedWire.erase_root Hn, hHnerase, Proofs.NamedWire.erase_root]
  have hHbody : H ∈ (rho.stateBeforeTime S time w).st.bodies := by
    rw [← hHnEq]
    exact hHnbody
  have hsigma : (rho.stateBeforeTime S time w).st.core.σ H.erase =
      derive_named S.E S.cfg H :=
    Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho time w H hHbody
  have hheight : (voteDutyStore S rho w (s + 1)).h_max - 1 ≤
      ((voteDutyStore S rho w (s + 1)).σ H.erase).h := by
    have hbound : (voteDutyStore S rho w (s + 1)).h_max - 1 ≤
        (derive_named S.E S.cfg H).h := Nat.sub_le_iff_le_add.mpr hmax
    have hsigma' : (voteDutyStore S rho w (s + 1)).σ H.erase =
        derive_named S.E S.cfg H := by
      simpa only [time, voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hsigma
    rw [hsigma']
    exact hbound
  have hCprocessed : C ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (voteDutyStore S rho w (s + 1)).toHealing.s :=
    WeakGoldfish.ancestorProcessed_of_voterProcessed S
      adm hw hHprocessed C hCH
  have hdata := hCfiltered
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable,
    Finset.mem_filter, decide_eq_true_eq] at hdata ⊢
  obtain ⟨⟨⟨hCT, hFC⟩, _, _, _, _⟩, hrootC⟩ := hdata
  exact ⟨⟨⟨hCprocessed, hFC⟩, H.erase, hHprocessed, hCH, hheight⟩, hrootC⟩

/-- A named processed descendant at the frontier makes every filtered
ancestor a prepared voter candidate. -/
theorem namedAncestorCandidate_of_processedDescendant_and_hMax
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot}
    {C : Block V} {H : NamedBlock V}
    (hHprocessed : H.erase ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (voteDutyStore S rho w (s + 1)).toHealing.s)
    (hHrun : RunBlock S rho H) (hCH : Block.Preceq C H.erase)
    (hCfiltered : C ∈ Protocol.get_filtered_block_tree
      (voteDutyStore S rho w (s + 1)).toHealing.toFG)
    (hmax : (voteDutyStore S rho w (s + 1)).h_max ≤
      (derive_named S.E S.cfg H).h + 1) :
    C ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (voteDutyStore S rho w (s + 1)).toHealing :=
  namedAncestorCandidate_of_processedDescendant_and_hMax_core
    S adm.toNamedAdmissibleCore hw hHprocessed hHrun hCH hCfiltered hmax

/-- The prepared vote head has a retained named witness at the local
`h_max - 1` viability boundary. -/
theorem voteDutyHead_height_ge_frontier_sub_one_of_candidate
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {C : Block V}
    (hinputs : GoldfishConeVoteInputs S rho s C w)
    (hanchor : Block.Preceq (voterAnchorAt S rho w (s + 1)) C) :
    ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho w (s + 1) ∧ RunBlock S rho Hn ∧
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max - 1 ≤
          (derive_named S.E S.cfg Hn).h := by
  let read := voteDutyRead S rho w (s + 1)
  let duty := read.st.core
  let tree := voterCandidateTreeAt S rho w (s + 1)
  let A := voterAnchorAt S rho w (s + 1)
  let score := Protocol.goldfish_score S.E duty.T
    (Protocol.voter_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s)
    (Protocol.voter_support_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s)
    (duty.s - 1)
  let eligible := Protocol.goldfish_eligible S.E duty.σ duty.h_max duty.T
    duty.s (Protocol.voter_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s)
    (Protocol.voter_support_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s)
    (duty.s - 1)
  let H := voterHeadAt S rho w (s + 1)
  have hHghost : H = Protocol.ghost A tree score eligible := by
    rfl
  have hfacts := voteDuty_parentClosed_agrees_rootInjective S adm hw (s + 1)
  have htreeT : tree ⊆ duty.T := by
    intro B hB
    have hprocessed := Proofs.Records.get_filtered_block_tree_from_subset
      duty.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E
        duty.toHealing.toFG.toSG.toGoldfishStore duty.s) hB
    exact (Finset.mem_filter.mp hprocessed).1
  have hrootTree : RootInjectiveBelow tree :=
    Protocol.RootInjectiveBelow.mono hfacts.2.2 htreeT
  have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.vote_time S.E (s + 1)) w).1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st := by
    simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt] using
      Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ _ hinvPre
  have hroot : Protocol.get_fg_root duty.toHealing.toFG ∈ duty.T :=
    Proofs.NamedStoreRoots.fg_root_mem read.st hinv.1.2
  have hAT : A ∈ duty.T := by
    exact Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc duty.toHealing (S.hc.round_of duty.s) hroot
  have hHT : H ∈ duty.T := by
    rw [hHghost]
    exact Proofs.Records.ghost_mem_of _ _ hAT htreeT
  have hHpre : H ∈
      (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w).st.core.T := by
    simpa only [read, duty, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hHT
  obtain ⟨Hn, hHnBody, hHnErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.vote_time S.E (s + 1)) w hHpre
  have hHnRun : RunBlock S rho Hn := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.vote_time S.E (s + 1))
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i := n)
    simpa only [Run.storeBeforeTime, hn] using hHnBody
  have hHnRead : Hn ∈ read.st.bodies := by
    simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hHnBody
  have hSigma : duty.σ H = derive_named S.E S.cfg Hn := by
    rw [← hHnErase]
    exact hfacts.2.1 Hn hHnRead
  refine ⟨Hn, hHnErase, hHnRun, ?_⟩
  by_contra hnot
  have hHlow : (duty.σ H).h < duty.h_max - 1 := by
    rw [hSigma]
    exact Nat.lt_of_not_ge hnot
  have stopContradiction : ∀ (Z W : Block V),
      Z = H → Z ∈ tree →
      W ∈ Protocol.voter_processed_block_tree S.E
        duty.toHealing.toFG.toSG.toGoldfishStore duty.s →
      Block.Preceq Z W → duty.h_max - 1 ≤ (duty.σ W).h → False := by
    intro Z W hZH hZtree hWprocessed hZW hWheight
    subst Z
    have hHneW : H ≠ W := by
      intro hEq
      subst W
      exact (Nat.not_lt_of_ge hWheight) hHlow
    obtain ⟨D, hDparent, hDW⟩ := exists_child_towards W hZW hHneW
    have hDtree : D ∈ tree := by
      simpa only [tree, duty, read, voteDutyStore] using
        namedFrozenCandidate_child_towards_witness S adm hw hZtree
          hWprocessed hDparent hDW hWheight
    have hDeligible : eligible D = true := by
      rw [Proofs.Optimistic.goldfish_eligible_iff, parent_eq_of_parent? hDparent]
      exact Or.inl hHlow
    have hDfalse : eligible D = false := by
      have hparent := hDparent
      rw [hHghost] at hparent
      exact eligible_child_false_at_ghost_result hrootTree hDtree hparent
    rw [hDfalse] at hDeligible
    contradiction
  rcases Proofs.Records.ghost_mem A tree score eligible with hHA | hHtree
  · have hHA' : H = A := by simpa only [hHghost] using hHA
    have hAC : Block.Preceq A C := by simpa only [A] using hanchor
    by_cases hACeq : A = C
    · have hHC : H = C := hHA'.trans hACeq
      have hCdata := hinputs.candidate
      simp only [voterCandidateTreeAt, Protocol.voter_filtered_block_tree,
        Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
        Protocol.finalized_descendants, Protocol.viable,
        Finset.mem_filter, decide_eq_true_eq] at hCdata
      obtain ⟨⟨⟨-, -⟩, W, hWprocessed, hCW, hWheight⟩, -⟩ := hCdata
      exact stopContradiction C W hHC.symm
        (by simpa only [tree] using hinputs.candidate)
        (by simpa only [duty, read, voteDutyStore] using hWprocessed)
        hCW (by simpa only [duty, read, voteDutyStore] using hWheight)
    · obtain ⟨D, hDparent, hDC⟩ := exists_child_towards C hAC hACeq
      have hAD : Block.Preceq A D := preceq_of_parent? hDparent
      have hDneA : D ≠ A := by
        intro hEq
        subst D
        have hdepth := depth_of_parent? hDparent
        omega
      have hDtree : D ∈ tree := by
        by_cases hDCeq : D = C
        · subst D
          simpa only [tree] using hinputs.candidate
        · simpa only [tree] using hinputs.path D
            (by simpa only [A] using hAD)
            (by simpa only [A] using hDneA) hDC hDCeq
      have hDeligible : eligible D = true := by
        rw [Proofs.Optimistic.goldfish_eligible_iff, parent_eq_of_parent? hDparent]
        have hAlow : (duty.σ A).h < duty.h_max - 1 := by
          simpa only [hHA'] using hHlow
        exact Or.inl hAlow
      have hDfalse : eligible D = false := by
        have hparent := hDparent
        rw [← hHA', hHghost] at hparent
        exact eligible_child_false_at_ghost_result hrootTree hDtree hparent
      rw [hDfalse] at hDeligible
      contradiction
  · have hHtree' : H ∈ tree := by simpa only [hHghost] using hHtree
    have hHdata := hHtree'
    simp only [tree, voterCandidateTreeAt, Protocol.voter_filtered_block_tree,
      Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq] at hHdata
    obtain ⟨⟨⟨-, -⟩, W, hWprocessed, hHW, hWheight⟩, -⟩ := hHdata
    exact stopContradiction H W rfl hHtree'
      (by simpa only [duty, read, voteDutyStore] using hWprocessed)
      hHW (by simpa only [duty, read, voteDutyStore] using hWheight)



#print axioms voteDuty_parentClosed_agrees_rootInjective
#print axioms namedAncestorCandidate_of_processedDescendant_and_hMax_core
#print axioms namedAncestorCandidate_of_processedDescendant_and_hMax
#print axioms voteDutyHead_height_ge_frontier_sub_one_of_candidate

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
