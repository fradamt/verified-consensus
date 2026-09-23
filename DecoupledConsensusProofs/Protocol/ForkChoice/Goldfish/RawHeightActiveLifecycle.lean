module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawExactHeightSeed
public import DecoupledConsensusProofs.Protocol.ChainState.RawHeightCoverage
public import DecoupledConsensusProofs.Execution.RecoveryGradeProcessedRead
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusInternal.Definitions.NamedLifecycle

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Active exact-height opening classification

The root-robust carrier is restored over named blocks and named derivation.
The caller now supplies the source as a run block, so root collision freedom
recovers the exact retained named witness. The complete earlier source is
retained below.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The named root-robust result of transporting an exact-height active carrier
to one honest opening proposal read. -/
structure ActiveExactHeightProposalRootCarrierAt
    (S : Setup V) (rho : Run V) (H : Height) (q : Round) (endpoint : Time)
    (source root : NamedBlock V) : Prop where
  proposerCarrier : ProposerCarrierAt S rho q
  proposerHonest : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest
  proposalRead_le_action :
    Protocol.proposal_time S.E (S.hc.opening_slot q) ≤ S.a q
  action_le_endpoint : S.a q ≤ endpoint
  endpointInHorizon : endpoint ≤ rho.horizon
  endpointCap : honestHMaxAt S rho endpoint ≤ H
  gradeFormsPrev : NamedGradeFormsAt S rho (q - 1) source.erase
  sourceActiveAtAction : ∀ w ∈ rho.honest,
    source.erase ∈ Protocol.get_filtered_block_tree
      (healStoreAt S rho w q).toFG
  sourceProcessed : source ∈
    (rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot q))
      (Protocol.proposal_time S.E (S.hc.opening_slot q))).bodies
  sourceRunBlock : RunBlock S rho source
  sourceExactHeight : (Protocol.derive_named S.E S.cfg source).h = H
  sourceNotActive : source.erase ∉ filteredTree
    (proposerReadAt S rho (S.hc.opening_slot q))
  root_eq : root.erase = Protocol.get_fg_root
    (proposerReadAt S rho (S.hc.opening_slot q)).st.core.toHealing.toFG
  sourceStrictRoot : Block.Prec source.erase root.erase
  rootActive : root.erase ∈ filteredTree
    (proposerReadAt S rho (S.hc.opening_slot q))
  rootProcessed : root ∈
    (rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot q))
      (Protocol.proposal_time S.E (S.hc.opening_slot q))).bodies
  rootRunBlock : RunBlock S rho root
  rootExactHeight : (Protocol.derive_named S.E S.cfg root).h = H
  rootExactTarget :
    (Protocol.derive_named S.E S.cfg root).T_h.root =
      (Protocol.derive_named S.E S.cfg source).T_h.root
  rootPreceqProposedParent :
    Block.Preceq root.erase (proposedParent S rho (S.hc.opening_slot q))

private theorem lifecycle_runBlock_of_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {w : V} (hw : w ∈ rho.honest) {t : Time} {D : NamedBlock V}
    (hD : D ∈ (rho.storeBeforeTime S w t).bodies) : RunBlock S rho D := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S sch t
  have hD' : D ∈ (rho.stateBefore S n w).st.bodies := by
    simpa only [Run.storeBeforeTime, hn] using hD
  exact Proofs.Bridges.runBlock_of_stateBefore_mem S hw hD'

private theorem lifecycle_runBlock_unique_of_erase_eq
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {A D : NamedBlock V} (hA : RunBlock S rho A) (hD : RunBlock S rho D)
    (herase : A.erase = D.erase) : A = D :=
  adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
    A D hA hD A D (Or.inl (Proofs.NamedAncestry.named_self A))
      (Or.inr (Proofs.NamedAncestry.named_self D))
      (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])

/-- A named grade source that is a run block is the exact body retained at a
later honest strict read. -/
private theorem namedGradeSource_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {source : NamedBlock V}
    (hforms : NamedGradeFormsAt S rho q source.erase)
    (hsourceRun : RunBlock S rho source)
    {reader : V} (hreader : reader ∈ rho.honest) {read : Time}
    (hle : S.a q ≤ read) :
    source ∈ (rho.storeBeforeTime S reader read).bodies := by
  have hsourceMem : source.erase ∈
      (rho.storeBeforeTime S reader read).core.T :=
    gradeFormsAt_processedAtRead_of_action_le
      S adm hforms hreader hle
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
      S rho read reader hsourceMem
  have hDrun : RunBlock S rho D :=
    lifecycle_runBlock_of_mem_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hreader hDbody
  have hDsource : D = source :=
    lifecycle_runBlock_unique_of_erase_eq
      adm hDrun hsourceRun hDerase
  simpa only [hDsource] using hDbody

private theorem actionStore_hMax_le_honestHMaxAt_lifecycle
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {v : V} (hv : v ∈ rho.honest) {endpoint : Time}
    (hle : S.a r ≤ endpoint) :
    (actionStoreAt S rho v r).st.core.h_max ≤
      honestHMaxAt S rho endpoint := by
  have hpre : (actionStoreAt S rho v r).st.core.h_max =
      (rho.storeBeforeTime S v (S.a r)).core.h_max := rfl
  rw [hpre]
  exact (storeBeforeTime_hMax_le_storeAt S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v (S.a r)).trans
    ((stateAt_h_max_mono S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v hle).trans
      (localHMax_le_honestHMaxAt S rho endpoint hv))

omit [Fintype V] in
private theorem lifecycle_parent_preceq (B : NamedBlock V) :
    NamedBlock.Preceq B.parent B := by
  cases B with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
        (Proofs.NamedAncestry.named_self parent)

/-- Normalize the active orientation at one selected named opening. -/
theorem activeExactHeightOpeningLifecycle_or_hMaxRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {q : Round} {source : NamedBlock V} {endpoint : Time}
    (hq : 0 < q)
    (hcarrier : ProposerCarrierAt S rho q)
    (hformsPrev : NamedGradeFormsAt S rho (q - 1) source.erase)
    (hwindowPrev : ∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w (S.a (q - 1)) source.erase)
    (hdomainWindow : ∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) source.erase)
    (hsourceRun : RunBlock S rho source)
    (hsourceHeight :
      (Protocol.derive_named S.E S.cfg source).h = H)
    (hpostPrev : S.E.t_GST ≤ S.a (q - 1))
    (hmature : ProposalTimeoutMatureAt
      S rho (S.hc.opening_slot q))
    (hactiveAtAction : ∀ w ∈ rho.honest,
      source.erase ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w q).toFG)
    (hactionEnd : S.a q ≤ endpoint)
    (hendHor : endpoint ≤ rho.horizon) :
    H < honestHMaxAt S rho endpoint ∨
      (FixedHeightRootInterferenceAtRead S rho H
          (S.E.proposer (S.hc.opening_slot q))
          (Protocol.proposal_time S.E (S.hc.opening_slot q))
          source.erase ∧
        Protocol.proposal_time S.E (S.hc.opening_slot q) ≤ S.a q ∧
        S.a q ≤ endpoint ∧ endpoint ≤ rho.horizon) ∨
      ∃ root : NamedBlock V,
        ActiveExactHeightProposalRootCarrierAt
          S rho H q endpoint source root := by
  let s := S.hc.opening_slot q
  let p := S.E.proposer s
  let read := Protocol.proposal_time S.E s
  let pre := rho.storeBeforeTime S p read
  let duty := Protocol.proposerDutyStore S rho s
  let root := Protocol.get_fg_root duty.toHealing.toFG
  have hprop : S.E.proposer s ∈ rho.honest := by
    simpa only [s] using hcarrier.1
  have hproposalAction : read ≤ S.a q := by
    dsimp only [read, s]
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact Protocol.proposal_time_le_confirmation_time S.E _
  have hreadEnd : read ≤ endpoint := hproposalAction.trans hactionEnd
  have hreadHor : read ≤ rho.horizon := hreadEnd.trans hendHor
  have hround : S.hc.round_of s = q := by
    simpa only [s] using round_of_opening_slot_eq S.hc q
  have hdelay : S.a (q - 1) + S.E.Δ ≤ read := by
    simpa only [read, hround] using
      (Protocol.previous_action_add_delta_le_proposal S
        (s := s) (by simpa only [hround] using hq))
  have hprevActionRead : S.a (q - 1) ≤ read :=
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hdelay
  have hsourceMem : source ∈ pre.bodies := by
    simpa only [pre, p] using namedGradeSource_mem_storeBeforeTime
      S adm hformsPrev hsourceRun hprop hprevActionRead
  have hsourceCore : source.erase ∈ pre.core.T := by
    have htree :=
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read p).1.1.1.1
    have htree' : pre.core.T = pre.bodies.image NamedBlock.erase := by
      simpa only [pre] using htree
    rw [htree']
    exact Finset.mem_image_of_mem NamedBlock.erase hsourceMem
  by_cases hriseEnd : H < honestHMaxAt S rho endpoint
  · exact Or.inl hriseEnd
  have hcapEnd : honestHMaxAt S rho endpoint ≤ H :=
    Nat.le_of_not_gt hriseEnd
  have hcapRead : honestHMaxAt S rho read ≤ H :=
    (honestHMaxAt_mono S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hreadEnd).trans
        hcapEnd
  have hfrontier : pre.core.h_max = H := by
    apply Nat.le_antisymm
    · exact ((storeBeforeTime_hMax_le_storeAt S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed p read).trans
        (localHMax_le_honestHMaxAt S rho read hprop)).trans hcapRead
    · rw [← hsourceHeight]
      exact Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime
        S rho read p source hsourceMem
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird
      (S := S) hfb
  by_cases hactive : source.erase ∈
      Protocol.get_filtered_block_tree duty.toHealing.toFG
  · have hcut : S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon := by
      calc
        S.hc.Γ_neg1 S.E.Δ q ≤ S.hc.Γ_0 S.E.Δ q :=
          le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos q)
        _ = read := by
          simpa only [read, s] using
            Protocol.Γ_0_eq_proposal_time S.hc S.E q
        _ ≤ rho.horizon := hreadHor
    obtain ⟨B, hB⟩ := proposedBlockAt_isSome S rho s
    have hspos : 0 < s := by
      dsimp only [s]
      exact Nat.mul_pos hq
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
    have hBRun : RunBlock S rho B :=
      proposedBlockAt_blockInRun_of_admissible S
        adm.toNamedAdmissibleCore s hspos hprop hreadHor hB
    have hparentRun : RunBlock S rho B.parent :=
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBRun
        (lifecycle_parent_preceq B)
    have hparentErase : B.parent.erase = proposedParent S rho s := by
      obtain ⟨parent, hparent, hparentErase⟩ :=
        proposedBlockAt_parent S rho s hB
      cases B with
      | genesis => cases hparent
      | node parent' slot root' votes support rows proposer =>
          have heq : parent' = parent := Option.some.inj hparent
          simpa only [NamedBlock.parent, heq] using hparentErase
    have hparentMem : B.parent ∈ pre.bodies := by
      have hpay := Proofs.NamedActions.proposal_payload
        (NamedProfile.gradeContract (proposerReadAt S rho s).cache)
        .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
        (proposerReadAt S rho s).st B hB
      simpa only [pre, p, read, proposerReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hpay.1
    have hprevPositive : 0 < q - 1 := by
      by_contra hnonpos
      have hzero : q - 1 = 0 := Nat.eq_zero_of_not_pos hnonpos
      have hnonempty : rho.honest.Nonempty := by
        by_contra hnone
        have hzeroWeight : S.E.electorate.weightOf rho.honest = 0 := by
          rw [Finset.not_nonempty_iff_eq_empty.mp hnone]
          simp [Electorate.weightOf]
        have hsum := S.E.electorate.weightOf_add_weightOf_sdiff rho.honest
        unfold HonestWeightMajority at hmajority
        omega
      obtain ⟨w, hw⟩ := hnonempty
      have hgrade := (hformsPrev w hw).2
      rw [hzero] at hgrade
      simp [storeGrade, phaseGrade, Protocol.latest_window_zero,
        DecoupledConsensusModel.Protocol.gradeBool,
        DecoupledConsensusModel.Protocol.positive,
        DecoupledConsensusModel.Protocol.opposing,
        DecoupledConsensusModel.Protocol.readyView,
        DecoupledConsensusModel.Protocol.rawView,
        DecoupledConsensusModel.Protocol.interpretedInputs,
        DecoupledConsensusModel.Protocol.rawInputs, DecoupledConsensusModel.Protocol.Supports,
        DecoupledConsensusModel.Protocol.Opposes, DecoupledConsensusModel.Protocol.CleanFrom,
        Electorate.weightOf] at hgrade
    have hpred : q - 1 + 1 = q := Nat.sub_add_cancel hq
    have hclean : CleanActionReadFor S rho (q - 1) source.erase := by
      apply cleanActionReadFor_of_namedGradeFormsAt_and_retained_active
        S adm hprevPositive hformsPrev hpostPrev
      · simpa only [hpred] using hcut
      · exact hwindowPrev
      · intro w hw
        simpa only [hpred] using hactiveAtAction w hw
      · intro w hw
        simpa only [hpred] using hdomainWindow w hw
    have hsourceParent : Block.Preceq source.erase B.parent.erase := by
      have hfloor :=
        protected_preceq_nextOpeningProposedParent_of_cleanActionRead
          S adm hmajority hclean
            (by simpa only [hpred, s] using hprop)
            (by simpa only [hpred, duty, s] using hactive)
            (by simpa only [hpred, s] using hB)
      simpa only [hpred, s, Proofs.NamedWire.erase_parent] using hfloor
    have hsourceParentNamed : NamedBlock.Preceq source B.parent :=
      Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hsourceRun hparentRun hsourceParent
    have hparentHeight :
        (Protocol.derive_named S.E S.cfg B.parent).h = H := by
      apply Nat.le_antisymm
      · exact (Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime
          S rho read p B.parent hparentMem).trans_eq hfrontier
      · rw [← hsourceHeight]
        exact Proofs.NamedEntryHeight.derive_height_mono
          S.E S.cfg hsourceParentNamed
    have hprevHor : S.a (q - 1) ≤ rho.horizon :=
      hprevActionRead.trans hreadHor
    have hinWindow : Protocol.ProposalRows.inWindow S.hc
        (proposerReadAt S rho s).st.core (q - 1) = true := by
      unfold Protocol.ProposalRows.inWindow
      simp only [decide_eq_true_eq]
      have hreadRound : S.hc.round_of
          (proposerReadAt S rho s).st.core.s = q := by
        simpa only [proposerReadAt,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock, Proofs.Optimistic.slotOf_proposal_time,
          hround]
      rw [hreadRound]
      have heta := S.hc.η_SG_ge_one
      exact ⟨Nat.sub_le_sub_left heta q, Nat.sub_le q 1⟩
    let target :=
      (Protocol.derive_named S.E S.cfg source).T_h.root
    have hsourceTarget :
        (Protocol.derive_named S.E S.cfg source).T_h.root = target :=
      rfl
    have hcoverage : NamedTargetedHonestActionProposalCoverageAt
        S rho (q - 1) B H target := by
      intro v hv
      rcases actionAttestationAt_pair_or_hMaxRise
          S adm hprevPositive hprevHor hformsPrev hsourceRun
            hsourceHeight hsourceTarget hv (hwindowPrev v hv) with
        hpair | hlocal
      · refine ⟨?_, hpair⟩
        exact actionAttestationAt_coveredAtProposal
          S adm hformsPrev hsourceRun hsourceHeight hsourceTarget hB
            hsourceParentNamed hparentHeight hprop hreadHor hpostPrev
            hdelay hv (hwindowPrev v hv) hinWindow hpair
      · have hpublic := hlocal.trans_le
          (actionStore_hMax_le_honestHMaxAt_lifecycle
            S adm hv (hprevActionRead.trans hreadEnd))
        exact False.elim (hriseEnd hpublic)
    have hparentTarget :
        (Protocol.derive_named S.E S.cfg B.parent).T_h.root =
          target := by
      rw [← hsourceTarget]
      exact congrArg (fun X => X.root)
        (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg
          hsourceParentNamed
          (by rw [hsourceHeight, hparentHeight])) |>.symm
    have hproposalHeight :
        (Protocol.derive_named S.E S.cfg B).h = H + 1 :=
      named_proposedBlock_height_eq_succ_of_actionCoverage
        S hfb hB hmature hcoverage hparentHeight hparentTarget
    have hproposalPublic := honestProposedBlock_height_le_honestHMaxAt
      S adm hspos hprop hreadHor hB
    have hsuccLe : H + 1 ≤ honestHMaxAt S rho read := by
      rw [← hproposalHeight]
      exact hproposalPublic
    have hreadRise : H < honestHMaxAt S rho read :=
      Nat.lt_of_succ_le (by
        simpa only [Nat.succ_eq_add_one] using hsuccLe)
    exact False.elim (hriseEnd
      (hreadRise.trans_le
        (honestHMaxAt_mono S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hreadEnd)))
  · have hrootActive : root ∈
        Protocol.get_filtered_block_tree duty.toHealing.toFG := by
      have hrootPre := named_fgRoot_mem_filtered_stateBeforeTime
        S rho read p
      simpa only [root, duty, Protocol.proposerDutyStore,
        Proofs.Optimistic.tickStore, pre, p, read] using hrootPre
    have hrootMem : root ∈ pre.core.T :=
      Proofs.Records.get_filtered_block_tree_subset _ (by
        simpa only [root, duty, Protocol.proposerDutyStore,
          Proofs.Optimistic.tickStore, pre, p, read] using hrootActive)
    obtain ⟨rootNamed, hrootBody, hrootErase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
        S rho read p hrootMem
    have hrootRun : RunBlock S rho rootNamed :=
      lifecycle_runBlock_of_mem_storeBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
        hprop hrootBody
    have hrootParent : Block.Preceq root (proposedParent S rho s) := by
      have hanchor := fg_root_preceq_get_sg_root_with_frame
        (proposerReadAt S rho s).cache S.E S.hc
        (proposerReadAt S rho s).st.core.toHealing
        (S.hc.round_of (proposerReadAt S rho s).st.core.toHealing.s)
      have hhead := get_sg_root_with_preceq_get_head_with
        (NamedProfile.gradeContract (proposerReadAt S rho s).cache)
        S.E S.hc (proposerReadAt S rho s).st.core.toHealing
        (Protocol.proposer_view
          (proposerReadAt S rho s).st.core.toHealing.toFG.toSG.toGoldfishStore
          (proposerReadAt S rho s).st.core.s).toFinset
        (Protocol.proposer_support_view
          (proposerReadAt S rho s).st.core.toHealing.toFG.toSG.toGoldfishStore
          (proposerReadAt S rho s).st.core.s).toFinset
        ((proposerReadAt S rho s).st.core.s - 1)
      simpa only [root, duty, Protocol.proposerDutyStore,
        Proofs.Optimistic.tickStore, pre, p, read, proposedParent] using
          Block.preceq_trans hanchor hhead
    by_cases hsourceRoot : Block.Preceq source.erase root
    · have hsourceRootErase : Block.Preceq
          source.erase rootNamed.erase := by
        rw [hrootErase]
        exact hsourceRoot
      have hsourceRootNamed : NamedBlock.Preceq source rootNamed :=
        Protocol.namedPreceq_of_runBlock_erase_preceq
          adm hsourceRun hrootRun hsourceRootErase
      have hne : source.erase ≠ rootNamed.erase := by
        intro heq
        apply hactive
        rw [heq, hrootErase]
        exact hrootActive
      have hsourceStrict : Block.Prec source.erase rootNamed.erase := by
        simpa only [Block.Prec, Block.prec, hne, decide_false,
          Bool.not_false, Bool.true_and] using hsourceRootErase
      have hrootHeight :
          (Protocol.derive_named S.E S.cfg rootNamed).h = H := by
        apply Nat.le_antisymm
        · exact (Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime
            S rho read p rootNamed hrootBody).trans_eq hfrontier
        · rw [← hsourceHeight]
          exact Proofs.NamedEntryHeight.derive_height_mono
            S.E S.cfg hsourceRootNamed
      have hrootTarget :
          (Protocol.derive_named S.E S.cfg rootNamed).T_h.root =
            (Protocol.derive_named S.E S.cfg source).T_h.root :=
        congrArg (fun X => X.root)
          (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg
            hsourceRootNamed (by rw [hsourceHeight, hrootHeight])) |>.symm
      exact Or.inr (Or.inr ⟨rootNamed,
        { proposerCarrier := hcarrier
          proposerHonest := by simpa only [s] using hprop
          proposalRead_le_action := by
            simpa only [read, s] using hproposalAction
          action_le_endpoint := hactionEnd
          endpointInHorizon := hendHor
          endpointCap := hcapEnd
          gradeFormsPrev := hformsPrev
          sourceActiveAtAction := hactiveAtAction
          sourceProcessed := by
            simpa only [pre, p, read, s] using hsourceMem
          sourceRunBlock := hsourceRun
          sourceExactHeight := hsourceHeight
          sourceNotActive := by
            simpa only [duty, s] using hactive
          root_eq := by simpa only [root] using hrootErase
          sourceStrictRoot := hsourceStrict
          rootActive := by
            simpa only [root, duty, s, hrootErase] using hrootActive
          rootProcessed := by
            simpa only [pre, p, read, s] using hrootBody
          rootRunBlock := hrootRun
          rootExactHeight := hrootHeight
          rootExactTarget := hrootTarget
          rootPreceqProposedParent := by
            rw [hrootErase]
            simpa only [root, s] using hrootParent }⟩)
    · have hnotQuiet : ¬ FinalityFilterNoninterferenceAtRead
          S rho p read source.erase := by
        intro hquiet
        rcases hquiet with hroot | hfiltered
        · exact hsourceRoot (by
            simpa only [root, duty, Protocol.proposerDutyStore,
              Proofs.Optimistic.tickStore, pre, p, read] using hroot)
        · exact hactive (by
            simpa only [duty, Protocol.proposerDutyStore,
              Proofs.Optimistic.tickStore, pre, p, read] using hfiltered)
      rcases (not_finalityFilterNoninterferenceAtRead_iff
          S rho p read source.erase).mp hnotQuiet with
        hinterference | hheight
      · have hfixed := fixedHeightRootInterferenceAtRead_of_interference
          S adm hfb hsb hprop hreadHor
            (by simpa only [pre, p, read] using hsourceCore)
            rfl hsourceRun (by rw [hsourceHeight])
            (by simpa only [pre] using hfrontier) hinterference
        exact Or.inr (Or.inl ⟨by
          simpa only [p, read, s] using hfixed,
          by simpa only [read, s] using hproposalAction,
          hactionEnd, hendHor⟩)
      · have hreadRise := heightFilterInterference_lt_honestHMaxAt
          S adm hprop (by simpa only [pre, p, read] using hsourceMem)
            (by rw [hsourceHeight]) hheight
        exact Or.inl (hreadRise.trans_le
          (honestHMaxAt_mono S
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hreadEnd))



/-
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawExactHeightSeed
public import DecoupledConsensusProofs.Protocol.ChainState.RawHeightCoverage
public import DecoupledConsensusProofs.Execution.RecoveryGradeProcessedRead

/-!
# Active exact-height opening classification

An exact common grade that remains active at the next action is transported to
one selected honest opening proposal read. If it is also active in the
proposer duty, the actual proposal covers the preceding action rows and raises
the public raw frontier. Otherwise the proposal read exposes either the fixed
root interference consumed by Claim 4 or an explicit strict same-height FG-root
carrier.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V: Type} [DecidableEq V] [Fintype V]

/-- The root-robust result of transporting an exact-height active carrier to an
honest opening proposal read. Every field names an actual store, selected root,
or schedule inequality. -/
structure ActiveExactHeightProposalRootCarrierAt
    (S: Setup V) (rho: Run V) (H: Height) (q: Round) (endpoint: Time)
    (source root: Block V): Prop where
  proposerCarrier: ProposerCarrierAt S rho q
  proposerHonest: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest
  proposalRead_le_action:
    Protocol.proposal_time S.E (S.hc.opening_slot q) ≤ S.a q
  action_le_endpoint: S.a q ≤ endpoint
  endpointInHorizon: endpoint ≤ rho.horizon
  endpointCap: honestHMaxAt S rho endpoint ≤ H
  gradeFormsPrev: GradeFormsAt S rho (q - 1) source
  sourceActiveAtAction: ∀ w ∈ rho.honest,
    source ∈ Protocol.get_filtered_block_tree
      (healStoreAt S rho w q).toFG
  sourceProcessed: source ∈
    (rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot q))
      (Protocol.proposal_time S.E (S.hc.opening_slot q))).T
  sourceRunBlock: RunBlock S rho source
  sourceExactHeight: (derived_state S.E S.cfg source).h = H
  sourceNotActive: source ∉ Protocol.get_filtered_block_tree
    (Protocol.proposerDutyStore S rho
      (S.hc.opening_slot q)).toHealing.toFG
  root_eq: root = Protocol.get_fg_root
    (Protocol.proposerDutyStore S rho
      (S.hc.opening_slot q)).toHealing.toFG
  sourceStrictRoot: Block.Prec source root
  rootActive: root ∈ Protocol.get_filtered_block_tree
    (Protocol.proposerDutyStore S rho
      (S.hc.opening_slot q)).toHealing.toFG
  rootProcessed: root ∈
    (rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot q))
      (Protocol.proposal_time S.E (S.hc.opening_slot q))).T
  rootRunBlock: RunBlock S rho root
  rootExactHeight: (derived_state S.E S.cfg root).h = H
  rootExactTarget:
    (derived_state S.E S.cfg root).T_h.root =
      (derived_state S.E S.cfg source).T_h.root
  rootPreceqProposedParent: Block.Preceq root
    (Protocol.proposedParent S rho (S.hc.opening_slot q))

private theorem proposalRead_runBlock_of_mem
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} (hprop: S.E.proposer s ∈ rho.honest) {B: Block V}
    (hB: B ∈ (rho.storeBeforeTime S (S.E.proposer s)
      (Protocol.proposal_time S.E s)).T):
    RunBlock S rho B:= by
  obtain ⟨n, hn, _⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toScheduleWellFormed (Protocol.proposal_time S.E s)
  apply Proofs.Bridges.runBlock_of_stateBefore_mem S hprop (i:= n)
  simpa only [Run.storeBeforeTime, hn] using hB

private theorem actionStore_hMax_le_honestHMaxAt_endpoint
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} {v: V} (hv: v ∈ rho.honest) {endpoint: Time}
    (hle: S.a r ≤ endpoint):
    (actionStoreAt S rho v r).h_max ≤ honestHMaxAt S rho endpoint:= by
  have hpre: (actionStoreAt S rho v r).h_max =
      (rho.storeBeforeTime S v (S.a r)).h_max:=
    (attestStore_finality S
      (rho.stateBeforeTime S (S.a r) v).st (S.a r)).2.2.1
  rw [hpre]
  exact (storeBeforeTime_hMax_le_storeAt
      S adm.toScheduleWellFormed v (S.a r)).trans
    ((stateAt_h_max_mono S adm.toScheduleWellFormed v hle).trans
      (localHMax_le_honestHMaxAt S rho endpoint hv))

/-- Normalize the active orientation at one selected opening.

The fixed-interference arm retains the exact proposal-read-to-endpoint timing
needed by the outer Claim-4 schedule. The final arm names the actual strict
same-height proposal FG root. -/
theorem activeExactHeightOpeningLifecycle_or_hMaxRise
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {H: Height} {q: Round} {source: Block V} {endpoint: Time}
    (hq: 0 < q)
    (hcarrier: ProposerCarrierAt S rho q)
    (hformsPrev: GradeFormsAt S rho (q - 1) source)
    (hsourceHeight: (derived_state S.E S.cfg source).h = H)
    (hpostPrev: S.E.t_GST ≤ S.a (q - 1))
    (hmature: ProposalTimeoutMatureAt
      S rho (S.hc.opening_slot q))
    (hactiveAtAction: ∀ w ∈ rho.honest,
      source ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w q).toFG)
    (hactionEnd: S.a q ≤ endpoint)
    (hendHor: endpoint ≤ rho.horizon):
    H < honestHMaxAt S rho endpoint ∨
      (FixedHeightRootInterferenceAtRead S rho H
          (S.E.proposer (S.hc.opening_slot q))
          (Protocol.proposal_time S.E (S.hc.opening_slot q)) source ∧
        Protocol.proposal_time S.E (S.hc.opening_slot q) ≤ S.a q ∧
        S.a q ≤ endpoint ∧ endpoint ≤ rho.horizon) ∨
      ∃ root: Block V,
        ActiveExactHeightProposalRootCarrierAt
          S rho H q endpoint source root:= by
  let s:= S.hc.opening_slot q
  let p:= S.E.proposer s
  let read:= Protocol.proposal_time S.E s
  let pre:= rho.storeBeforeTime S p read
  let duty:= Protocol.proposerDutyStore S rho s
  let root:= Protocol.get_fg_root duty.toHealing.toFG
  have hprop: S.E.proposer s ∈ rho.honest:= by
    simpa only [s] using hcarrier.1
  have hproposalAction: read ≤ S.a q:= by
    dsimp only [read, s]
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact Protocol.proposal_time_le_confirmation_time S.E _
  have hreadEnd: read ≤ endpoint:= hproposalAction.trans hactionEnd
  have hreadHor: read ≤ rho.horizon:= hreadEnd.trans hendHor
  have hround: S.hc.round_of s = q:= by
    simpa only [s] using round_of_opening_slot_eq S.hc q
  have hdelay: S.a (q - 1) + S.E.Δ ≤ read:= by
    simpa only [read, hround] using
      (Protocol.previous_action_add_delta_le_proposal S
        (s:= s) (by simpa only [hround] using hq))
  have hprevActionRead: S.a (q - 1) ≤ read:=
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hdelay
  have hsourceMem: source ∈ pre.T:= by
    simpa only [pre, p] using
      (gradeFormsAt_processedAtRead_of_action_le
        S adm hformsPrev hprop hprevActionRead)
  have hsourceRun: RunBlock S rho source:= by
    apply proposalRead_runBlock_of_mem S adm hprop
    simpa only [p, read] using hsourceMem
  by_cases hriseEnd: H < honestHMaxAt S rho endpoint
  · exact Or.inl hriseEnd
  have hcapEnd: honestHMaxAt S rho endpoint ≤ H:= Nat.le_of_not_gt hriseEnd
  have hcapRead: honestHMaxAt S rho read ≤ H:=
    (honestHMaxAt_mono S adm.toScheduleWellFormed hreadEnd).trans hcapEnd
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node p) pre:= by
    simpa only [pre, p, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed read p)
  have hagree: DerivedStateAgrees S.E S.cfg pre:=
    derivedStateAgrees_depReachable S.E S.hc S.cfg (S.node p) pre hdep
  have htree: TreeHeightsLeHMax pre:=
    treeHeightsLeHMax_depReachable S.E S.hc S.cfg (S.node p) hdep
  have hfrontier: pre.h_max = H:= by
    apply Nat.le_antisymm
    · exact ((storeBeforeTime_hMax_le_storeAt
          S adm.toScheduleWellFormed p read).trans
        (localHMax_le_honestHMaxAt S rho read hprop)).trans hcapRead
    · rw [← hsourceHeight, ← hagree source hsourceMem]
      exact htree source hsourceMem
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hmajority: HonestWeightMajority S rho.honest:=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird
      (S:= S) hfb
  by_cases hactive: source ∈
      Protocol.get_filtered_block_tree duty.toHealing.toFG
  · have hcut: S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon:= by
      calc
        S.hc.Γ_neg1 S.E.Δ q ≤ S.hc.Γ_0 S.E.Δ q:=
          le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos q)
        _ = read:= by
          simpa only [read, s] using
            Protocol.Γ_0_eq_proposal_time S.hc S.E q
        _ ≤ rho.horizon:= hreadHor
    have hG1:= proposerG1_of_gradeFormsAt_prev_and_active
      S adm hmajority hq hformsPrev hpostPrev hcut hactiveAtAction
        (by simpa only [s] using hprop) (by simpa only [duty, s] using hactive)
    have hsourceParent: Block.Preceq source
        (Protocol.proposedParent S rho s):= by
      simpa only [s] using proposedParent_preceq_of_proposerG1
        S (by simpa only [duty, s] using hactive) hG1
    let parent:= Protocol.proposedParent S rho s
    have hparentDuty: parent ∈ duty.T:= by
      simpa only [parent, duty] using Protocol.proposedParent_mem S adm s
    have hparentMem: parent ∈ pre.T:= by
      simpa only [duty, Protocol.proposerDutyStore,
        Proofs.Optimistic.tickStore, pre, p, read] using hparentDuty
    have hparentHeight: (derived_state S.E S.cfg parent).h = H:= by
      apply Nat.le_antisymm
      · calc
          (derived_state S.E S.cfg parent).h = (pre.σ parent).h:=
            (congrArg (fun st => st.h) (hagree parent hparentMem)).symm
          _ ≤ pre.h_max:= htree parent hparentMem
          _ = H:= hfrontier
      · rw [← hsourceHeight]
        exact Protocol.derived_h_mono S.E S.cfg
          (by simpa only [parent] using hsourceParent)
    let target:= (derived_state S.E S.cfg source).T_h.root
    have hsourceTarget:
        (derived_state S.E S.cfg source).T_h.root = target:= rfl
    have hcoverage: HonestActionProposalCoverageAt
        S rho (q - 1) s H target:= by
      intro v hv
      rcases actionAttestationAt_pair_or_hMaxRise
          S adm hformsPrev hsourceHeight hsourceTarget hv with hpair | hlocal
      · refine ⟨?_, hpair⟩
        exact actionAttestationAt_coveredAtProposal
          S adm hformsPrev hsourceHeight hsourceTarget
            (P:= parent) (by rfl)
            (by simpa only [parent] using hsourceParent) hparentHeight
            hprop hreadHor hpostPrev hdelay
            (by simpa only [duty] using hactive) hv hpair
      · have hprevEnd: S.a (q - 1) ≤ endpoint:=
          hprevActionRead.trans hreadEnd
        have hpublic:= hlocal.trans_le
          (actionStore_hMax_le_honestHMaxAt_endpoint
            S adm hv hprevEnd)
        exact False.elim (hriseEnd hpublic)
    have hproposalParentHeight: (derived_state S.E S.cfg
        (Internal.proposedBlock S rho s).parent).h = H:= by
      rw [parent_eq_of_parent?
        (Protocol.proposedBlock_parent S rho s)]
      exact hparentHeight
    have hparentTarget:
        (derived_state S.E S.cfg parent).T_h.root = target:= by
      rw [← hsourceTarget]
      exact congrArg Block.root
        (derivedTarget_eq_of_preceq_same_height
          S.E S.cfg (by simpa only [parent] using hsourceParent)
            (by rw [hparentHeight, hsourceHeight]))
    have hproposalParentTarget: (derived_state S.E S.cfg
        (Internal.proposedBlock S rho s).parent).T_h.root = target:= by
      rw [parent_eq_of_parent?
        (Protocol.proposedBlock_parent S rho s)]
      exact hparentTarget
    have hproposalHeight: (derived_state S.E S.cfg
        (Internal.proposedBlock S rho s)).h = H + 1:=
      proposedBlock_height_eq_succ_of_actionCoverage
        S hfb hmature hcoverage hproposalParentHeight hproposalParentTarget
    have hspos: 0 < s:= by
      dsimp only [s]
      exact Nat.mul_pos hq
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
    have hproposalPublic:= honestProposedBlock_height_le_honestHMaxAt
      S adm hspos hprop hreadHor
    have hsuccLe: H + 1 ≤ honestHMaxAt S rho read:= by
      rw [← hproposalHeight]
      exact hproposalPublic
    have hreadRise: H < honestHMaxAt S rho read:=
      Nat.lt_of_succ_le (by
        simpa only [Nat.succ_eq_add_one] using hsuccLe)
    exact False.elim (hriseEnd
      (hreadRise.trans_le
        (honestHMaxAt_mono S adm.toScheduleWellFormed hreadEnd)))
  · have hrootActive: root ∈
        Protocol.get_filtered_block_tree duty.toHealing.toFG:= by
      have hrootPre:= fgRoot_mem_filtered_depReachable
        S.E S.hc S.cfg (S.node p) hdep
      simpa only [root, duty, Protocol.proposerDutyStore,
        Proofs.Optimistic.tickStore, pre, p, read] using hrootPre
    have hrootDuty: root ∈ duty.T:=
      Proofs.Records.get_filtered_block_tree_subset duty.toHealing.toFG hrootActive
    have hrootMem: root ∈ pre.T:= by
      simpa only [duty, Protocol.proposerDutyStore,
        Proofs.Optimistic.tickStore, pre, p, read] using hrootDuty
    have hrootRun: RunBlock S rho root:= by
      apply proposalRead_runBlock_of_mem S adm hprop
      simpa only [p, read] using hrootMem
    have hrootParent: Block.Preceq root
        (Protocol.proposedParent S rho s):= by
      let votes:= Protocol.proposer_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s
      let support:= Protocol.proposer_support_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s
      have hout:= StoreFinality.get_head_of_preceq_fgRoot
        S.E S.hc duty root votes.toFinset support.toFinset (duty.s - 1)
          (by simpa only [root] using Block.preceq_self root)
      simpa only [Protocol.proposedParent, duty, votes, support] using hout
    by_cases hsourceRoot: Block.Preceq source root
    · have hne: source ≠ root:= by
        intro heq
        apply hactive
        simpa only [heq] using hrootActive
      have hsourceStrict: Block.Prec source root:= by
        simpa only [Block.Prec, Block.prec, hne, decide_false,
          Bool.not_false, Bool.true_and] using hsourceRoot
      have hrootHeight: (derived_state S.E S.cfg root).h = H:= by
        apply Nat.le_antisymm
        · calc
            (derived_state S.E S.cfg root).h = (pre.σ root).h:=
              (congrArg (fun st => st.h) (hagree root hrootMem)).symm
            _ ≤ pre.h_max:= htree root hrootMem
            _ = H:= hfrontier
        · rw [← hsourceHeight]
          exact Protocol.derived_h_mono S.E S.cfg hsourceRoot
      have hrootTarget:
          (derived_state S.E S.cfg root).T_h.root =
            (derived_state S.E S.cfg source).T_h.root:=
        congrArg Block.root
          (derivedTarget_eq_of_preceq_same_height
            S.E S.cfg hsourceRoot (by rw [hrootHeight, hsourceHeight]))
      exact Or.inr (Or.inr ⟨root,
        { proposerCarrier:= hcarrier
          proposerHonest:= by simpa only [s] using hprop
          proposalRead_le_action:= by
            simpa only [read, s] using hproposalAction
          action_le_endpoint:= hactionEnd
          endpointInHorizon:= hendHor
          endpointCap:= hcapEnd
          gradeFormsPrev:= hformsPrev
          sourceActiveAtAction:= hactiveAtAction
          sourceProcessed:= by simpa only [pre, p, read, s] using hsourceMem
          sourceRunBlock:= hsourceRun
          sourceExactHeight:= hsourceHeight
          sourceNotActive:= by simpa only [duty, s] using hactive
          root_eq:= by rfl
          sourceStrictRoot:= hsourceStrict
          rootActive:= by simpa only [root, duty, s] using hrootActive
          rootProcessed:= by simpa only [root, pre, p, read, s] using hrootMem
          rootRunBlock:= by simpa only [root] using hrootRun
          rootExactHeight:= by simpa only [root] using hrootHeight
          rootExactTarget:= by simpa only [root] using hrootTarget
          rootPreceqProposedParent:= by
            simpa only [root, s] using hrootParent }⟩)
    · have hnotQuiet: ¬ FinalityFilterNoninterferenceAtRead
          S rho p read source:= by
        intro hquiet
        rcases hquiet with hroot | hfiltered
        · exact hsourceRoot (by
            simpa only [root, duty, Protocol.proposerDutyStore,
              Proofs.Optimistic.tickStore, pre, p, read] using hroot)
        · exact hactive (by
            simpa only [duty, Protocol.proposerDutyStore,
              Proofs.Optimistic.tickStore, pre, p, read] using hfiltered)
      rcases (not_finalityFilterNoninterferenceAtRead_iff
          S rho p read source).mp hnotQuiet with hinterference | hheight
      · have hfixed:= fixedHeightRootInterferenceAtRead_of_interference
          S adm hfb hsb hprop hreadHor hsourceMem hsourceRun
            (by rw [hsourceHeight]) hfrontier hinterference
        exact Or.inr (Or.inl ⟨by
          simpa only [p, read, s] using hfixed,
          by simpa only [read, s] using hproposalAction,
          hactionEnd, hendHor⟩)
      · have hreadRise:= heightFilterInterference_lt_honestHMaxAt
          S adm hprop hsourceMem (by rw [hsourceHeight]) hheight
        exact Or.inl (hreadRise.trans_le
          (honestHMaxAt_mono S adm.toScheduleWellFormed hreadEnd))


end HealingSurface
end Proofs
end DecoupledConsensusModel
-/

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms ActiveExactHeightProposalRootCarrierAt
#print axioms activeExactHeightOpeningLifecycle_or_hMaxRise
end DecoupledConsensusModel.Proofs.HealingSurface

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
