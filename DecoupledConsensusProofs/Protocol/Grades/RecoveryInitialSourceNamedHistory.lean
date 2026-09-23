module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.HeightRegimeNamed
public import DecoupledConsensusProofs.Protocol.Grades.SameRoundQ2Retained

@[expose] public section

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedRecoveryRead Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem relative_gradeBool_zero_named_history
    (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta : Round) (early late : Time) (B : Block V) :
    DecoupledConsensusModel.Protocol.gradeBool E gv F eta 0 early late B = false := by
  simp [DecoupledConsensusModel.Protocol.gradeBool,
    DecoupledConsensusModel.Protocol.positive, DecoupledConsensusModel.Protocol.opposing,
    DecoupledConsensusModel.Protocol.readyView, DecoupledConsensusModel.Protocol.rawView,
    DecoupledConsensusModel.Protocol.interpretedInputs, DecoupledConsensusModel.Protocol.rawInputs,
    Protocol.latest_window_zero, DecoupledConsensusModel.Protocol.Supports,
    DecoupledConsensusModel.Protocol.Opposes, DecoupledConsensusModel.Protocol.CleanFrom]

private theorem selectedQ2_round_pos_named_history
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {r : Round} {Q : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q) :
    0 < r := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hgrade := selectedQ2_storeGrade_at_g2Domain S adm hQ
  rw [hzero] at hgrade
  simp only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade] at hgrade
  rw [relative_gradeBool_zero_named_history] at hgrade
  cases hgrade

private theorem actionBody_runBlock_named_history
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨j, hj, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a r)
  have hDj : D ∈ (rho.stateBefore S j v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho j v).st.bodies
    rw [← hj]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv j hDj)

private theorem actionStoreDerived_named_history
    (S : Setup V) {rho : Run V} {v : V} {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    (actionStoreAt S rho v r).st.core.σ D.erase =
      Protocol.derive_named S.E S.cfg D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
    S rho (S.a r) v D hDpre
  simpa only [actionStoreAt, actionReadAt,
    NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
    NamedActionReads.confirmationReadFrom,
    NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hview

private theorem selectedQ2_filtered_at_read_of_namedFrame_history
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {Q : NamedBlock V}
    (hselected : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r =
      some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : NamedBlock V} {c0 : Round}
    (hframe : NamedHeightRegimeFrame S rho blocked stop Tprev c0)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : NamedBlock.Preceq Tprev Q)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    {w : V} (hw : w ∈ rho.honest) {read : Time}
    (hdelivery : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2 + S.E.Δ ≤ read)
    (hreadPrefix : strictEventIndex rho read ≤ stop)
    (hreadHor : read ≤ rho.horizon) :
    Q.erase ∈ PhaseGrades.filteredTree
      (PhaseGrades.readAt S rho read w) := by
  let core := adm.toNamedAdmissibleCore
  have hQrun : RunBlock S rho Q :=
    actionBody_runBlock_named_history S adm hp hQmem
  have htargetFQ : Block.Preceq
      (NamedRun.stateBeforeTime S rho read w).st.core.F Q.erase := by
    rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S core.toNamedScheduleWellFormed read) w]
    exact hframe.floor w hw _ hreadPrefix Q hQrun
      (by rw [hQheight]; exact Nat.le_succ blocked) hTQ
  have hQsource : Q ∈
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.bodies :=
    selectedQ2_body_at_capture S adm hp hselected hQmem
  have hgstDomain : S.E.t_GST ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2 :=
    ready.1.trans (NamedOutageClosure.early_le_domain S r)
  have hdeadline : max (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)
      S.E.t_GST + S.E.Δ ≤ read := by
    rw [max_eq_left hgstDomain]
    exact hdelivery
  obtain ⟨hQtarget, -, -⟩ :=
    NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
      S rho core p hp w hw Q
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) read read hQsource
      hdeadline (le_refl _) hreadHor htargetFQ
  have hreadEq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S core.toNamedScheduleWellFormed read) w
  have hQtargetIndex : Q ∈
      (NamedRun.stateBefore S rho (strictEventIndex rho read) w).st.bodies := by
    have h := hQtarget
    rw [hreadEq] at h
    exact h
  have hfiltered := hframe.fgRoot_preceq_and_filteredMem
    adm hfrontier hw hreadPrefix hQtargetIndex hQheight hTQ
  change Q.erase ∈ Protocol.get_filtered_block_tree
    (NamedRun.stateBeforeTime S rho read w).st.core.toHealing.toFG
  rw [hreadEq]
  exact hfiltered.2

private theorem selectedQ2_g1Domain_data_of_namedFrame_history
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {Q : NamedBlock V}
    (hselected : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r =
      some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : NamedBlock V} {c0 : Round}
    (hframe : NamedHeightRegimeFrame S rho blocked stop Tprev c0)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : NamedBlock.Preceq Tprev Q)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    {w : V} (hw : w ∈ rho.honest) :
    Q.erase ∈ PhaseGrades.filteredTree
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w) ∧
      PhaseGrades.storeGrade S.E S.hc
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st
        r .g1 Q.erase = true := by
  let core := adm.toNamedAdmissibleCore
  have hdomainAction : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ S.a r := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (Protocol.proposal_time_lt_vote_time S.E _).le.trans
      ((Protocol.vote_time_le_confirmation_time S.E _).trans (by
        rw [opening_confirmation_time_eq_action]))
  have hdomainPrefix : strictEventIndex rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) ≤ stop :=
    (strictEventIndex_mono rho hdomainAction).trans hactionPrefix
  have hQrun : RunBlock S rho Q :=
    actionBody_runBlock_named_history S adm hp hQmem
  have htargetFQ : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F Q.erase := by
    rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S core.toNamedScheduleWellFormed
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)) w]
    exact hframe.floor w hw _ hdomainPrefix Q hQrun
      (by rw [hQheight]; exact Nat.le_succ blocked) hTQ
  have hfiltered := selectedQ2_filtered_at_read_of_namedFrame_history
    S adm ready hp hselected hQmem hframe hQheight hTQ
      hfrontier hw
      (by
        simp only [DecoupledConsensusModel.Protocol.domain,
          DecoupledConsensusModel.Protocol.Phase.domainOffset]
        ring_nf
        exact le_rfl)
      hdomainPrefix
      (by
        have hle : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤
            DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 := by
          simp only [DecoupledConsensusModel.Protocol.domain,
            DecoupledConsensusModel.Protocol.Phase.domainOffset]
          linarith [S.E.Δ_pos]
        exact hle.trans ready.2)
  have hforward : ∀ sender u root H,
      u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.toHealing.gradeView
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.F
        S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g2) sender →
      DecoupledConsensusModel.Protocol.localCovers
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.toHealing.gradeView
        u.confirmed Q.erase = true →
      u.confirmed = some root →
      Block.find? (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.T root = some H →
      Block.Preceq (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F H := by
    intro sender u root H _ hcover hconf hfind
    exact Block.preceq_trans htargetFQ (by
      unfold DecoupledConsensusModel.Protocol.localCovers at hcover
      unfold Protocol.head_covers at hcover
      simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing, hconf]
        at hcover
      rw [hfind] at hcover
      exact hcover)
  have hbelowReaders := crossReaderFinalizedBelow_of_finalitySafety_and_relay
    S adm hsb ready.1 ready.2 hp hw hforward
  have hguard := crossReaderBodyReadyGuard_of_finalizedBelow
    S core hr ready.1 ready.2 hp hw hbelowReaders
  have hG2 := selectedQ2_storeGrade_at_g2Domain S adm hselected
  have hdelivery := twoCutoffDelivery_of_core S core ready.1
  refine ⟨hfiltered, ?_⟩
  exact storeGrade_g1_of_storeGrade_g2_cross_reader
    S rho core r hdelivery ready.2 p w hp hw Q.erase hG2 hguard

private theorem PrefixFGSelectorConeAt.selectedSource_firstInterior_of_frame_named_history
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    (hselected : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase) :
    (∀ w ∈ rho.honest, Block.Preceq T
      (voterHeadAt S rho w (S.hc.opening_slot a.round + 1))) ∧
      NamedHonestVotesCone S rho (S.hc.opening_slot a.round + 1)
        (fun X => Block.Preceq T X) := by
  have hr : 0 < a.round :=
    selectedQ2_round_pos_named_history S adm hselected
  have hactionBefore : strictEventIndex rho (S.a a.round) < first :=
    hseed.actionPrefix_lt adm.toNamedScheduleWellFormed
  have hprefix : strictEventIndex rho (S.a a.round) ≤ first - 1 :=
    Nat.le_sub_one_of_lt hactionBefore
  have hfrontier : honestHMaxBeforeIndex S rho (first - 1) < blocked + 2 := by
    have hstopLt : first - 1 < first :=
      Nat.sub_lt (Nat.zero_lt_of_lt hactionBefore) Nat.zero_lt_one
    exact (hfirst.before _ hstopLt).trans_lt
      (Nat.lt_succ_self (blocked + 1))
  have hhor : S.a a.round ≤ rho.horizon := hseed.actionHorizon adm
  have hTprevCfg : NamedBlock.Preceq Tprev Cfg :=
    hframe.sourceAbove a.val_index hseed.signerHonest a.round hprefix hhor
      Cfg hseed.sourceMem hseed.exactFGSource hseed.sourceDerivedHeight
  have hTCfg : Block.Preceq T Cfg.erase := by
    rw [hseed.checkpointDerived]
    exact Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg Cfg
  let s := S.hc.opening_slot a.round + 1
  have hs : 0 < s := Nat.succ_pos _
  have hround : S.hc.round_of s = a.round := by
    simpa only [s] using Proofs.HealingLemmas.round_of_opening_succ S.hc a.round
  have hread : DecoupledConsensusModel.Protocol.domain S.E S.hc a.round .g1 <
      Protocol.vote_time S.E s := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (Protocol.proposal_time_lt_vote_time S.E
      (S.hc.opening_slot a.round)).trans_le
        (vote_time_mono_slots S.E (Nat.le_succ _))
  have hta : Protocol.vote_time S.E s ≤ S.a a.round := by
    simpa only [s] using (next_vote_time_lt_action S a.round).le
  have hvotePrefix : strictEventIndex rho (Protocol.vote_time S.E s) ≤
      first - 1 := Nat.le_sub_one_of_lt
    ((strictEventIndex_mono rho hta).trans_lt hactionBefore)
  have hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon := hta.trans hhor
  have hg1Hor : DecoupledConsensusModel.Protocol.domain S.E S.hc a.round .g1 ≤
      rho.horizon := by
    have hle : DecoupledConsensusModel.Protocol.domain S.E S.hc a.round .g1 ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc a.round .g0 := by
      simp only [DecoupledConsensusModel.Protocol.domain,
        DecoupledConsensusModel.Protocol.Phase.domainOffset]
      linarith [S.E.Δ_pos]
    exact hle.trans ready.2
  have hdelivery : DecoupledConsensusModel.Protocol.domain S.E S.hc a.round .g2 + S.E.Δ ≤
      Protocol.vote_time S.E s := by
    have hdomain : DecoupledConsensusModel.Protocol.domain S.E S.hc a.round .g2 + S.E.Δ =
        DecoupledConsensusModel.Protocol.domain S.E S.hc a.round .g1 := by
      simp only [DecoupledConsensusModel.Protocol.domain,
        DecoupledConsensusModel.Protocol.Phase.domainOffset]
      ring
    rw [hdomain]
    exact hread.le
  have hsource : Protocol.grade2_block_with
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.actionDutyRead S rho a.val_index a.round).cache)
      S.E S.hc
      (Internal.NamedRecoveryRead.actionDutyRead S rho
        a.val_index a.round).st.core.toHealing a.round = some Cfg.erase := by
    simpa only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
      Internal.NamedRecoveryRead.actionDutyRead] using hselected
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hbelow
  have hdata : ∀ w ∈ rho.honest,
      Cfg.erase ∈ PhaseGrades.filteredTree
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc a.round .g1) w) ∧
        PhaseGrades.storeGrade S.E S.hc
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc a.round .g1) w).st
          a.round .g1 Cfg.erase = true := by
    intro w hw
    exact selectedQ2_g1Domain_data_of_namedFrame_history
      S adm hsb hr ready hseed.signerHonest hselected hseed.sourceMem
        hframe hseed.sourceDerivedHeight hTprevCfg hprefix hfrontier hw
  have hvote : ∀ w ∈ rho.honest,
      Cfg.erase ∈ PhaseGrades.filteredTree
        (PhaseGrades.readAt S rho (Protocol.vote_time S.E s) w) := by
    intro w hw
    exact selectedQ2_filtered_at_read_of_namedFrame_history
      S adm ready hseed.signerHonest hselected hseed.sourceMem hframe
        hseed.sourceDerivedHeight hTprevCfg hfrontier hw
        hdelivery hvotePrefix hvoteHor
  have hheads : ∀ w ∈ rho.honest,
      Block.Preceq T (voterHeadAt S rho w s) := by
    intro w hw
    have hactive : Cfg.erase ∈ Protocol.get_filtered_block_tree
        (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.toHealing.toFG := by
      simpa only [PhaseGrades.filteredTree, PhaseGrades.readAt,
        Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using
        hvote w hw
    have hpre := selectedActionG2_preceq_sameRoundVoteDutyHead_of_activeAtVote
      S adm.toNamedAdmissibleCore hr hseed.signerHonest hsource hround hw
        hread hta hg1Hor (hdata w hw).1 (hdata w hw).2 (hvote w hw) hactive
    exact Block.preceq_trans hTCfg hpre
  refine ⟨hheads, ?_⟩
  have hconeCfg := honestVotesCone_of_selectedActionG2_of_readDisposition
    S adm hr ready hseed.signerHonest hsource hs hround hread hta hvoteHor
      (by
        intro w hw _
        exact ⟨(hdata w hw).1, (hdata w hw).2, hvote w hw⟩)
      (by
        intro w hw _
        exact Or.inr (by
          simpa only [PhaseGrades.filteredTree, PhaseGrades.readAt,
            Internal.NamedRecoveryRead.voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using
            hvote w hw))
  intro w hw hcommittee
  obtain ⟨X, hCfgX, hXrun, hXemit⟩ := hconeCfg w hw hcommittee
  exact ⟨X, Block.preceq_trans hTCfg hCfgX, hXrun, hXemit⟩

private theorem activeActionAnchor_storeGrade_g1_named_history
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {w : V} (hw : w ∈ rho.honest) {root L : Block V}
    (hframe :
      (DecoupledConsensusModel.Protocol.readFrame
        (actionReadAt S rho w r).cache
        (actionReadAt S rho w r).st.core.toHealing r).g1 =
        some (some root))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (filteredTree (actionReadAt S rho w r)) root = some L) :
    storeGrade S.E S.hc
      (readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st
        r .g1 L = true := by
  let t := S.a r
  let before := NamedRun.stateBeforeTime S rho t w
  let read := actionReadAt S rho w r
  have hround : S.hc.round_of (S.E.slotOf t) = r := by
    have hs := actionStoreAt_round S rho w r
    simpa only [t, actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using hs
  have hdomainAction : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 < t := by
    dsimp only [t]
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (Protocol.proposal_time_lt_vote_time S.E _).trans
      (opening_vote_time_lt_action S r)
  have hg1Horizon : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤
      rho.horizon := by
    have hle : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 := by
      simp only [DecoupledConsensusModel.Protocol.domain,
        DecoupledConsensusModel.Protocol.Phase.domainOffset]
      linarith [S.E.Δ_pos]
    exact hle.trans ready.2
  have hbase := FrameCompleted.frame_phase_completed
    S rho adm.toNamedAdmissibleCore w hw r hr .g1 t hdomainAction
      (le_refl t) hg1Horizon
  have hbase' :
      (DecoupledConsensusModel.Protocol.readFrame before.cache
        before.st.core.toHealing r).g1 =
        some ((storeRoot S.E S.hc
          (readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1).map
            (fun X => DecoupledConsensusModel.Protocol.clipGrade X
              before.st.core.F)) := by
    simpa only [before, storeRoot, phaseRoot, PhaseGrades.readAt] using hbase
  have hprepared := NamedOutageClosure.frame_phase_prepared_eq
    S rho w r .g1 t hround _ hbase'
  have hreadFrame :
      (DecoupledConsensusModel.Protocol.readFrame read.cache
        read.st.core.toHealing r).g1 =
        some ((storeRoot S.E S.hc
          (readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1).map
            (fun X => DecoupledConsensusModel.Protocol.clipGrade X
              read.st.core.F)) := by
    simpa only [read, before, t, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom] using hprepared
  cases hstore : storeRoot S.E S.hc
      (readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1 with
  | none =>
      simp only [hstore, Option.map_none] at hreadFrame
      rw [hframe] at hreadFrame
      cases hreadFrame
  | some raw =>
      have hrootEq : root =
          DecoupledConsensusModel.Protocol.clipGrade raw read.st.core.F := by
        have hopt : some (some root) = some
            (some (DecoupledConsensusModel.Protocol.clipGrade raw read.st.core.F)) :=
          hframe.symm.trans (by
            simpa only [hstore, Option.map_some] using hreadFrame)
        exact Option.some.inj (Option.some.inj hopt)
      have hLroot : Block.Preceq L root := by
        unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
      have hLraw : Block.Preceq L raw := by
        rw [hrootEq] at hLroot
        exact Block.preceq_trans hLroot
          (NamedOutageClosure.q10_clip_preceq raw read.st.core.F)
      have hrawGrade : phaseGrade S.E S.hc
          (readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
          (readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
          r .g1 raw = true := by
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hstore)).2
      exact confirmation_phaseGrade_mono S.E S.hc _ _ r .g1
        hLraw hrawGrade

private theorem activeActionAnchor_namedBody_at_g1Domain_history
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {w : V} (hw : w ∈ rho.honest) {root L : Block V}
    (hframe :
      (DecoupledConsensusModel.Protocol.readFrame
        (actionReadAt S rho w r).cache
        (actionReadAt S rho w r).st.core.toHealing r).g1 =
        some (some root))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (filteredTree (actionReadAt S rho w r)) root = some L) :
    ∃ Ln : NamedBlock V, Ln.erase = L ∧
      Ln ∈ (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.bodies ∧
      RunBlock S rho Ln := by
  let t := S.a r
  let before := NamedRun.stateBeforeTime S rho t w
  let read := actionReadAt S rho w r
  let domainRead := readAt S rho
    (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w
  have hround : S.hc.round_of (S.E.slotOf t) = r := by
    have hs := actionStoreAt_round S rho w r
    simpa only [t, actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using hs
  have hdomainAction : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 < t := by
    dsimp only [t]
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (Protocol.proposal_time_lt_vote_time S.E _).trans
      (opening_vote_time_lt_action S r)
  have hg1Horizon : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤
      rho.horizon := by
    have hle : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 := by
      simp only [DecoupledConsensusModel.Protocol.domain,
        DecoupledConsensusModel.Protocol.Phase.domainOffset]
      linarith [S.E.Δ_pos]
    exact hle.trans ready.2
  have hbase := FrameCompleted.frame_phase_completed
    S rho adm.toNamedAdmissibleCore w hw r hr .g1 t hdomainAction
      (le_refl t) hg1Horizon
  have hbase' :
      (DecoupledConsensusModel.Protocol.readFrame before.cache
        before.st.core.toHealing r).g1 =
        some ((storeRoot S.E S.hc domainRead.st r .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X
            before.st.core.F)) := by
    simpa only [before, domainRead, storeRoot, phaseRoot, PhaseGrades.readAt] using hbase
  have hprepared := NamedOutageClosure.frame_phase_prepared_eq
    S rho w r .g1 t hround _ hbase'
  have hreadFrame :
      (DecoupledConsensusModel.Protocol.readFrame read.cache
        read.st.core.toHealing r).g1 =
        some ((storeRoot S.E S.hc domainRead.st r .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X
            read.st.core.F)) := by
    simpa only [read, before, t, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom] using hprepared
  cases hstore : storeRoot S.E S.hc domainRead.st r .g1 with
  | none =>
      simp only [hstore, Option.map_none] at hreadFrame
      rw [hframe] at hreadFrame
      cases hreadFrame
  | some raw =>
      have hrootEq : root =
          DecoupledConsensusModel.Protocol.clipGrade raw read.st.core.F := by
        have hopt : some (some root) = some
            (some (DecoupledConsensusModel.Protocol.clipGrade raw read.st.core.F)) :=
          hframe.symm.trans (by
            simpa only [hstore, Option.map_some] using hreadFrame)
        exact Option.some.inj (Option.some.inj hopt)
      have hLroot : Block.Preceq L root := by
        unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
      have hLraw : Block.Preceq L raw := by
        rw [hrootEq] at hLroot
        exact Block.preceq_trans hLroot
          (NamedOutageClosure.q10_clip_preceq raw read.st.core.F)
      have hrawTree : raw ∈ domainRead.st.core.T :=
        (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hstore)).1
      have hLtree : L ∈ domainRead.st.core.T := by
        have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w
        exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
          L raw hrawTree hLraw
      obtain ⟨Ln, hLn, hLnErase⟩ :=
        Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
          S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w (by
            simpa only [domainRead, PhaseGrades.readAt] using hLtree)
      have hLnRun : RunBlock S rho Ln := by
        obtain ⟨j, hj, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
          S rho adm.toNamedScheduleWellFormed.sorted
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)
        apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
        change Ln ∈ (NamedRun.stateBefore S rho j w).st.bodies
        rw [← hj]
        exact hLn
      exact ⟨Ln, hLnErase, hLn, hLnRun⟩

private theorem activeActionAnchor_namedBody_at_sourceG0_history
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    (hactionHor : S.a r ≤ rho.horizon)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {root L : Block V}
    (hframe :
      (DecoupledConsensusModel.Protocol.readFrame
        (actionReadAt S rho w r).cache
        (actionReadAt S rho w r).st.core.toHealing r).g1 =
        some (some root))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (filteredTree (actionReadAt S rho w r)) root = some L) :
    ∃ Ln : NamedBlock V, Ln.erase = L ∧
      Ln ∈ (readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.bodies ∧
      Ln ∈ (actionDutyRead S rho p r).st.bodies ∧
      Block.Preceq
        (readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.core.F L ∧
      RunBlock S rho Ln := by
  obtain ⟨Ln, hLnErase, hLnG1, hLnRun⟩ :=
    activeActionAnchor_namedBody_at_g1Domain_history
      S adm hr ready hw hframe hactive
  have hLaction : L ∈ filteredTree (actionReadAt S rho w r) := by
    unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
    exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1
  let source := DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0
  let out := source + S.E.Δ
  have hpost : S.E.t_GST ≤ source := by
    apply ready.1.trans
    dsimp only [source]
    simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
      DecoupledConsensusModel.Protocol.Phase.earlyOffset,
      DecoupledConsensusModel.Protocol.Phase.domainOffset]
    linarith [S.E.Δ_pos]
  have houtAction : out ≤ S.a r := by
    dsimp only [out, source, DecoupledConsensusModel.Protocol.domain,
      DecoupledConsensusModel.Protocol.Phase.domainOffset, Setup.a, Protocol.HealConfig.a,
      DecoupledConsensusModel.Protocol.opening, Protocol.proposal_time, Env.t, slotStart]
    linarith [S.E.Δ_pos]
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hbelow
  have hrelay : Block.Preceq
      (NamedRun.stateBeforeTime S rho source p).st.core.F
      (NamedRun.stateBeforeTime S rho out w).st.core.F :=
    finalized_preceq_of_evidence_delivered
      S adm hsb hp hw hpost rfl (houtAction.trans hactionHor)
  have hmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho out w).st.core.F
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.F := by
    rw [NamedOutageClosure.strict_read_eq_index S rho
        adm.toNamedScheduleWellFormed.sorted out,
      NamedOutageClosure.strict_read_eq_index S rho
        adm.toNamedScheduleWellFormed.sorted (S.a r)]
    exact Proofs.NamedRuntime.stateBefore_F_mono S rho w
      (NamedOutageClosure.strict_lengths_mono rho houtAction)
  have hactionL : Block.Preceq
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.F L := by
    apply GradeDeliveryRun.finalized_preceq_of_mem_filtered_at_read S rho
    simpa only [filteredTree, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hLaction
  have htargetF : Block.Preceq
      (readAt S rho source p).st.core.F Ln.erase := by
    rw [hLnErase]
    exact Block.preceq_trans hrelay (Block.preceq_trans hmono hactionL)
  have hpostG1 : S.E.t_GST ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 := by
    apply ready.1.trans
    simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
      DecoupledConsensusModel.Protocol.Phase.earlyOffset,
      DecoupledConsensusModel.Protocol.Phase.domainOffset]
    linarith [S.E.Δ_pos]
  have hdeadline : max (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)
      S.E.t_GST + S.E.Δ ≤ source := by
    rw [max_eq_left hpostG1]
    dsimp only [source]
    apply le_of_eq
    simp only [DecoupledConsensusModel.Protocol.domain,
      DecoupledConsensusModel.Protocol.Phase.domainOffset]
    ring
  obtain ⟨hLnG0, -, -⟩ :=
    NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
      S rho adm.toNamedAdmissibleCore w hw p hp Ln
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) source source
        hLnG1 hdeadline (le_refl _) ready.2 htargetF
  have hdomainAction : source ≤ S.a r :=
    FrameForward.domain_le_a S r .g0
  have heqG0 := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed source) p
  have heqAction := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed (S.a r)) p
  have hLnG0Index := hLnG0
  rw [heqG0] at hLnG0Index
  have hLnAction : Ln ∈
      (NamedRun.stateBeforeTime S rho (S.a r) p).st.bodies := by
    rw [heqAction]
    exact NamedBodyRetention.stateBefore_bodies_mono S rho p
      (strictEventIndex_mono rho hdomainAction) hLnG0Index
  refine ⟨Ln, hLnErase, ?_, ?_, ?_, hLnRun⟩
  · simpa only [PhaseGrades.readAt, source] using hLnG0
  · simpa only [actionDutyRead, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hLnAction
  · rw [← hLnErase]
    simpa only [source] using htargetF


private theorem PrefixFGSelectorConeAt.selectedSource_preceq_openingHead_of_namedFrame_history
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    (hselected : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase)
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq Cfg.erase
      (voterHeadAt S rho w (S.hc.opening_slot a.round)) := by
  have hr : 0 < a.round :=
    selectedQ2_round_pos_named_history S adm hselected
  have hactionBefore : strictEventIndex rho (S.a a.round) < first :=
    hseed.actionPrefix_lt adm.toNamedScheduleWellFormed
  have hprefix : strictEventIndex rho (S.a a.round) ≤ first - 1 :=
    Nat.le_sub_one_of_lt hactionBefore
  have hfrontier : honestHMaxBeforeIndex S rho (first - 1) < blocked + 2 := by
    have hstopLt : first - 1 < first :=
      Nat.sub_lt (Nat.zero_lt_of_lt hactionBefore) Nat.zero_lt_one
    exact (hfirst.before _ hstopLt).trans_lt
      (Nat.lt_succ_self (blocked + 1))
  have hhor : S.a a.round ≤ rho.horizon := hseed.actionHorizon adm
  have hTprevCfg : NamedBlock.Preceq Tprev Cfg :=
    hframe.sourceAbove a.val_index hseed.signerHonest a.round hprefix hhor
      Cfg hseed.sourceMem hseed.exactFGSource hseed.sourceDerivedHeight
  let s := S.hc.opening_slot a.round
  have hround : S.hc.round_of s = a.round := by
    simpa only [s] using round_of_opening_slot_eq_schedule S.hc a.round
  have hread : DecoupledConsensusModel.Protocol.domain S.E S.hc a.round .g1 <
      Protocol.vote_time S.E s := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact Protocol.proposal_time_lt_vote_time S.E _
  have hta : Protocol.vote_time S.E s ≤ S.a a.round := by
    dsimp only [s]
    exact (Protocol.vote_time_le_confirmation_time S.E _).trans (by
      rw [opening_confirmation_time_eq_action])
  have hvotePrefix : strictEventIndex rho (Protocol.vote_time S.E s) ≤
      first - 1 := Nat.le_sub_one_of_lt
    ((strictEventIndex_mono rho hta).trans_lt hactionBefore)
  have hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon := hta.trans hhor
  have hdelivery : DecoupledConsensusModel.Protocol.domain S.E S.hc a.round .g2 + S.E.Δ ≤
      Protocol.vote_time S.E s := by
    have hdomain : DecoupledConsensusModel.Protocol.domain S.E S.hc a.round .g2 + S.E.Δ =
        DecoupledConsensusModel.Protocol.domain S.E S.hc a.round .g1 := by
      simp only [DecoupledConsensusModel.Protocol.domain,
        DecoupledConsensusModel.Protocol.Phase.domainOffset]
      ring
    rw [hdomain]
    exact hread.le
  have hg1Hor : DecoupledConsensusModel.Protocol.domain S.E S.hc a.round .g1 ≤
      rho.horizon := by
    have hle : DecoupledConsensusModel.Protocol.domain S.E S.hc a.round .g1 ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc a.round .g0 := by
      simp only [DecoupledConsensusModel.Protocol.domain,
        DecoupledConsensusModel.Protocol.Phase.domainOffset]
      linarith [S.E.Δ_pos]
    exact hle.trans ready.2
  have hdata := selectedQ2_g1Domain_data_of_namedFrame_history
    S adm (slashableBound_of_admissible_belowOneThird S adm hbelow)
      hr ready hseed.signerHonest hselected hseed.sourceMem hframe
        hseed.sourceDerivedHeight hTprevCfg hprefix hfrontier hw
  have hvote := selectedQ2_filtered_at_read_of_namedFrame_history
    S adm ready hseed.signerHonest hselected hseed.sourceMem hframe
      hseed.sourceDerivedHeight hTprevCfg hfrontier hw hdelivery
        hvotePrefix hvoteHor
  have hsource : Protocol.grade2_block_with
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.actionDutyRead S rho a.val_index a.round).cache)
      S.E S.hc
      (Internal.NamedRecoveryRead.actionDutyRead S rho
        a.val_index a.round).st.core.toHealing a.round = some Cfg.erase := by
    simpa only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
      Internal.NamedRecoveryRead.actionDutyRead] using hselected
  have hactive : Cfg.erase ∈ Protocol.get_filtered_block_tree
      (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.toHealing.toFG := by
    simpa only [PhaseGrades.filteredTree, PhaseGrades.readAt,
      Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using hvote
  exact selectedActionG2_preceq_sameRoundVoteDutyHead_of_activeAtVote
    S adm.toNamedAdmissibleCore hr hseed.signerHonest hsource hround hw
      hread hta hg1Hor hdata.1 hdata.2 hvote hactive

private theorem PrefixFGSelectorConeAt.selectedSource_compatible_genuineOpening_of_namedFrame_history
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    (hselected : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase)
    {w : V} (hw : w ∈ rho.honest) {C : Block V}
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho w
          (S.hc.opening_slot a.round)).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho w
        (S.hc.opening_slot a.round)) (S.hc.opening_slot a.round) C) :
    Block.compatible Cfg.erase C = true := by
  have hr : 0 < a.round :=
    selectedQ2_round_pos_named_history S adm hselected
  have hopenPos : 0 < S.hc.opening_slot a.round :=
    Nat.mul_pos hr (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hpost : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot a.round) := by
    rw [← Protocol.Γ_1_eq_vote_time]
    exact ready.1.trans
      ((NamedOutageClosure.early_le_opening S a.round).trans
        (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos a.round).le)
  have hconfHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot a.round) ≤ rho.horizon := by
    rw [opening_confirmation_time_eq_action]
    exact hseed.actionHorizon adm
  apply WeakGoldfish.genuineConfirmation_compatible_of_priorProtectedHeads
    S adm.toNamedAdmissibleCore hcom hw hopenPos hpost hconfHor hgenuine
  intro z hz _
  exact hseed.selectedSource_preceq_openingHead_of_namedFrame_history
    adm hbelow hfirst hframe ready hselected hz

omit [Fintype V] in
private theorem compatible_ancestor_left_named_history {A B T : Block V}
    (hAB : Block.Preceq A B) (hBT : Block.compatible B T = true) :
    Block.compatible A T = true := by
  simp only [Block.compatible, Bool.or_eq_true] at hBT ⊢
  rcases hBT with hBT | hTB
  · exact Or.inl (Block.preceq_trans hAB hBT)
  · exact (Block.preceq_linear hAB hTB).elim Or.inl Or.inr

omit [Fintype V] in
private theorem compatible_with_checkpoint_below_named_history
    {A C T : Block V} (hAC : Block.compatible A C = true)
    (hTC : Block.Preceq T C) : Block.compatible A T = true := by
  simp only [Block.compatible, Bool.or_eq_true] at hAC ⊢
  rcases hAC with hAC | hCA
  · exact (Block.preceq_linear hAC hTC).elim Or.inl Or.inr
  · exact Or.inr (Block.preceq_trans hTC hCA)

private theorem actionAnchor_cases_named_history
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    PhaseGrades.nodeAnchor S (actionReadAt S rho v r) r =
        Protocol.get_fg_root
          (actionReadAt S rho v r).st.core.toHealing.toFG ∨
      ∃ root A,
        (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v r).cache
          (actionReadAt S rho v r).st.core.toHealing r).g1 =
          some (some root) ∧
        DecoupledConsensusModel.Protocol.activePrefix
          (filteredTree (actionReadAt S rho v r)) root = some A ∧
        PhaseGrades.nodeAnchor S (actionReadAt S rho v r) r = A := by
  dsimp only [PhaseGrades.nodeAnchor, PhaseGrades.nodeRead]
  simp only [NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract,
    DecoupledConsensusModel.Protocol.frameGradeRead]
  unfold DecoupledConsensusModel.Protocol.anchor
  cases hframe : (DecoupledConsensusModel.Protocol.readFrame
      (actionReadAt S rho v r).cache
      (actionReadAt S rho v r).st.core.toHealing r).g1 with
  | none => exact Or.inl rfl
  | some opt =>
      cases opt with
      | none => exact Or.inl rfl
      | some root =>
          cases hactive : DecoupledConsensusModel.Protocol.activePrefix
              (filteredTree (actionReadAt S rho v r)) root with
          | none => exact Or.inl (by simp only [hactive, Option.getD_none])
          | some A => exact Or.inr ⟨root, A, rfl, hactive, by
              simp only [hactive, Option.getD_some]⟩


private theorem nodeFGSource_of_actionFGSource_history
    (S : Setup V) (rho : Run V) (v : V) (r : Round) {B : Block V}
    (hsource : actionFGSource S (actionStoreAt S rho v r) = some B) :
    PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r = some B := by
  unfold actionFGSource at hsource
  dsimp only at hsource
  have hround : S.hc.round_of
      (actionStoreAt S rho v r).st.core.toHealing.s = r := by
    simpa only [Protocol.Store.toHealing] using
      actionStoreAt_round S rho v r
  rw [hround] at hsource
  simpa only [PhaseGrades.nodeFGSource, PhaseGrades.nodeRead,
    actionStoreAt] using hsource

theorem relativeG0_compatible_clearSource_of_finalizedPreceq_history
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) (hactionHor : S.a r ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) {L B : Block V}
    (hLtree : L ∈ (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) w).st.core.T)
    (hLgrade : PhaseGrades.storeGrade S.E S.hc
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) w).st r .g0 L = true)
    (hFL : Block.Preceq (actionReadAt S rho w r).st.core.F L)
    (hBclear : PhaseGrades.nodeClear S (actionReadAt S rho w r) r B = true) :
    Block.compatible L B = true := by
  obtain ⟨raw, hraw, hLraw⟩ := NamedOutageClosure.q10_freeze_of_graded
    S.E
    (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) w).st.core.toHealing.gradeView
    (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) w).st.core.F
    S.hc.η_SG r (e := DecoupledConsensusModel.Protocol.early S.E S.hc r .g0)
    (l := DecoupledConsensusModel.Protocol.late S.E S.hc r .g0)
    (by
      simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.late,
        DecoupledConsensusModel.Protocol.Phase.earlyOffset,
        DecoupledConsensusModel.Protocol.Phase.lateOffset]
      exact le_rfl)
    hLtree (by simpa only [PhaseGrades.storeGrade] using hLgrade)
  have hactionFrame := actionFrame_g0 S adm.toNamedAdmissibleCore
    hw hr hactionHor
  have hframe :
      (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho w r).cache
        (actionReadAt S rho w r).st.core.toHealing r).g0 =
        some (some (DecoupledConsensusModel.Protocol.clipGrade raw
          (actionReadAt S rho w r).st.core.F)) := by
    simpa only [PhaseGrades.storeRoot, PhaseGrades.phaseRoot, hraw,
      Option.map_some] using hactionFrame
  have hLclip : Block.Preceq L
      (DecoupledConsensusModel.Protocol.clipGrade raw
        (actionReadAt S rho w r).st.core.F) := by
    apply (NamedOutageClosure.q10_retained_prefix raw
      (actionReadAt S rho w r).st.core.F L ?_).mpr hLraw
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFL
  have hBclip : Block.compatible B
      (DecoupledConsensusModel.Protocol.clipGrade raw
        (actionReadAt S rho w r).st.core.F) = true := by
    simpa only [PhaseGrades.nodeClear, PhaseGrades.nodeRead,
      NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract,
      DecoupledConsensusModel.Protocol.frameGradeRead,
      DecoupledConsensusModel.Protocol.clear, hframe] using hBclear
  simp only [Block.compatible, Bool.or_eq_true] at hBclip ⊢
  rcases hBclip with hBclip | hclipB
  · exact (Block.preceq_linear hLclip hBclip).elim Or.inl Or.inr
  · exact Or.inl (Block.preceq_trans hLclip hclipB)

theorem actionQ2_crossReaderBodyReadyGuard_history
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) :
    ∀ w, w ∈ rho.honest → ∀ Q,
      PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r = some Q →
      CrossReaderBodyReadyGuard S rho r p w Q := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hbelow
  intro w hw Q hQ
  have hdomainAction :
      DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 ≤ S.a r :=
    FrameForward.domain_le_a S r .g0
  have hmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.core.F
      (NamedRun.stateBeforeTime S rho (S.a r) p).st.core.F := by
    rw [NamedOutageClosure.strict_read_eq_index S rho
        adm.toNamedScheduleWellFormed.sorted
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0),
      NamedOutageClosure.strict_read_eq_index S rho
        adm.toNamedScheduleWellFormed.sorted (S.a r)]
    exact Proofs.NamedRuntime.stateBefore_F_mono S rho p
      (NamedOutageClosure.strict_lengths_mono rho hdomainAction)
  have hFQAction : Block.Preceq
      (NamedRun.stateBeforeTime S rho (S.a r) p).st.core.F Q := by
    have hactive := actionQ2_mem_filteredTree S rho p r hQ
    have hFQ := NamedOutageClosure.q10_filtered_F hactive
    simpa only [actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hFQ
  have hsourceFQ : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.core.F Q :=
    Block.preceq_trans hmono hFQAction
  have hforward : ∀ sender u root Head,
      u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.toHealing.gradeView
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.F
        S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g2) sender →
      DecoupledConsensusModel.Protocol.localCovers
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.toHealing.gradeView
        u.confirmed Q = true →
      u.confirmed = some root →
      Block.find? (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.T root = some Head →
      Block.Preceq
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F Head := by
    intro sender u root Head _ hcover hconf hfind
    have hpost : S.E.t_GST ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 :=
      ready.1.trans (by
        simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
          DecoupledConsensusModel.Protocol.Phase.earlyOffset,
          DecoupledConsensusModel.Protocol.Phase.domainOffset]
        linarith [S.E.Δ_pos])
    have hhop : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 + S.E.Δ =
        DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 := by
      simp only [DecoupledConsensusModel.Protocol.domain,
        DecoupledConsensusModel.Protocol.Phase.domainOffset]
      ring
    have hrelay : Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.core.F :=
      finalized_preceq_of_evidence_delivered
        S adm hsb hw hp hpost hhop ready.2
    have hQHead : Block.Preceq Q Head := by
      unfold DecoupledConsensusModel.Protocol.localCovers at hcover
      unfold Protocol.head_covers at hcover
      simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing, hconf]
        at hcover
      change Block.find? (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.T root = some Head
        at hfind
      rw [hfind] at hcover
      exact hcover
    exact Block.preceq_trans hrelay
      (Block.preceq_trans hsourceFQ hQHead)
  have hfinalized :=
    crossReaderFinalizedBelow_of_finalitySafety_and_relay
      S adm hsb ready.1 ready.2 hp hw hforward
  exact crossReaderBodyReadyGuard_of_finalizedBelow
    S adm.toNamedAdmissibleCore hr ready.1 ready.2 hp hw hfinalized

/-- The named phase-ladder twin of
`freshAnchor_compatible_fgSource_after_cutoff`. The selected Q2 root is G1
at the anchor reader. If the anchor is above that root, G1-to-G0 delivery
and the cached clear selector give the source compatibility. -/
theorem freshAnchor_compatible_actionFGSource_after_cutoff_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    (hactionHor : S.a r ≤ rho.horizon)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {Q B root L : Block V}
    (hselected : PhaseGrades.nodeQ2
      S (actionReadAt S rho p r) r = some Q)
    (hsource : actionFGSource S (actionStoreAt S rho p r) = some B)
    (hframe :
      (DecoupledConsensusModel.Protocol.readFrame
        (voteDutyRead S rho w (S.hc.opening_slot r + 1)).cache
        (voteDutyRead S rho w
          (S.hc.opening_slot r + 1)).st.core.toHealing r).g1 =
        some (some root))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (filteredTree (voteDutyRead S rho w (S.hc.opening_slot r + 1)))
      root = some L) :
    Block.compatible L B = true := by
  have hLgrade1 := activeVoterAnchor_storeGrade_g1
    S adm hr ready hw hframe hactive
  have hguard := actionQ2_crossReaderBodyReadyGuard_history
    S adm hbelow hr ready hp w hw Q hselected
  have hQgrade1 := selectedG2_G1_at_read_after_cutoff
    S adm hbelow ready hactionHor hp hw hselected hguard
  change DecoupledConsensusModel.Protocol.gradeBool S.E
    (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
    (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
    S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1)
      (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1) L = true at hLgrade1
  change DecoupledConsensusModel.Protocol.gradeBool S.E
    (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
    (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
    S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1)
      (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1) Q = true at hQgrade1
  have hLQ : Block.compatible L Q = true :=
    graded_oneChain_at_reader (V := V) S.E
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
      S.hc.η_SG r
      (early := DecoupledConsensusModel.Protocol.early S.E S.hc r .g1)
      (late := DecoupledConsensusModel.Protocol.late S.E S.hc r .g1)
      (by
        simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.late,
          DecoupledConsensusModel.Protocol.Phase.earlyOffset,
          DecoupledConsensusModel.Protocol.Phase.lateOffset]
        linarith [S.E.Δ_pos])
      hLgrade1 hQgrade1
  have hsourceNode := nodeFGSource_of_actionFGSource_history S rho p r hsource
  have hQB : Block.Preceq Q B :=
    preceq_actionFGSource_of_actionQ2 S rho p r hselected
      (Block.preceq_self Q) hsourceNode
  simp only [Block.compatible, Bool.or_eq_true] at hLQ
  rcases hLQ with hLQ | hQL
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl (Block.preceq_trans hLQ hQB)
  · rcases actionFGSource_genuineClear_or_selectedG2_named
        S rho p r hselected hsource with hclear | hlocal
    · obtain ⟨_, _, _, hwalk, _, _⟩ := hclear
      have hLvote : L ∈ filteredTree
          (voteDutyRead S rho w (S.hc.opening_slot r + 1)) := by
        unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1
      obtain ⟨Ln, hLnErase, hLnG0, _, _⟩ :=
        activeVoterAnchor_namedBody_at_sourceG0_and_action
          S adm hbelow hr ready hactionHor hp hw hframe hactive
      have hLtree : L ∈ (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.core.T := by
        have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).1.1.1
        change L ∈ (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.core.T
        rw [hcoh.1, ← hLnErase]
        exact Finset.mem_image_of_mem NamedBlock.erase hLnG0
      have hFg0L : Block.Preceq
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.core.F L :=
        sourceG0Finalized_preceq_firstInteriorActive
          S adm hbelow ready hactionHor hp hw hLvote
      have hgstG1 : S.E.t_GST ≤ DecoupledConsensusModel.Protocol.early S.E S.hc r .g1 :=
        ready.1.trans (by
          simp only [DecoupledConsensusModel.Protocol.early,
            DecoupledConsensusModel.Protocol.Phase.earlyOffset]
          linarith [S.E.Δ_pos])
      have hforward : ∀ sender u key Head,
          u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
            (PhaseGrades.readAt S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
            (PhaseGrades.readAt S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
            S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1) sender →
          DecoupledConsensusModel.Protocol.localCovers
            (PhaseGrades.readAt S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
            u.confirmed L = true →
          u.confirmed = some key →
          Block.find? (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.T key = some Head →
          Block.Preceq (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.core.F Head := by
        intro sender u key Head _ hcover hconf hfind
        apply Block.preceq_trans hFg0L
        unfold DecoupledConsensusModel.Protocol.localCovers at hcover
        unfold Protocol.head_covers at hcover
        simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing,
          hconf] at hcover
        rw [hfind] at hcover
        exact hcover
      have hbelowReaders :=
        g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relay
          S adm (slashableBound_of_admissible_belowOneThird S adm hbelow)
            hgstG1 ready.2 hw hp hforward
      have hguard := g1G0CrossReaderBodyReadyGuard_of_finalizedBelow
        S adm.toNamedAdmissibleCore hr hgstG1 ready.2 hw hp hbelowReaders
      have hLgrade0 := storeGrade_g0_of_storeGrade_g1_cross_reader
        S rho adm.toNamedAdmissibleCore r
          (g1G0TwoCutoffDelivery_of_core
            S adm.toNamedAdmissibleCore hgstG1)
          ready.2 w p hw hp L hLgrade1 hguard
      have hQaction := actionQ2_mem_filteredTree S rho p r hselected
      have hFQ : Block.Preceq (actionReadAt S rho p r).st.core.F Q :=
        NamedOutageClosure.q10_filtered_F hQaction
      have hFL : Block.Preceq (actionReadAt S rho p r).st.core.F L :=
        Block.preceq_trans hFQ hQL
      have hBclear : PhaseGrades.nodeClear S
          (actionReadAt S rho p r) r B = true := by
        unfold Protocol.deepest_clear at hwalk
        have htest := (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hwalk)).2.2
        simpa only [PhaseGrades.nodeClear, PhaseGrades.nodeRead,
          actionStoreAt] using htest
      exact relativeG0_compatible_clearSource_of_finalizedPreceq_history
        S adm hr hactionHor hp hLtree hLgrade0 hFL hBclear
    · subst B
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hQL

#print axioms freshAnchor_compatible_actionFGSource_after_cutoff_named

/-- The action read's active relative-G1 anchor is compatible with the exact
prepared FG source. This is the action-read twin of the first-interior
anchor lemma and uses the same G2→G1→G0 phase ladder. -/
theorem activeActionAnchor_compatible_actionFGSource_after_cutoff_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    (hactionHor : S.a r ≤ rho.horizon)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {Q B root L : Block V}
    (hselected : PhaseGrades.nodeQ2
      S (actionReadAt S rho p r) r = some Q)
    (hsource : actionFGSource S (actionStoreAt S rho p r) = some B)
    (hframe :
      (DecoupledConsensusModel.Protocol.readFrame
        (actionReadAt S rho w r).cache
        (actionReadAt S rho w r).st.core.toHealing r).g1 =
        some (some root))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (filteredTree (actionReadAt S rho w r)) root = some L) :
    Block.compatible L B = true := by
  have hLgrade1 := activeActionAnchor_storeGrade_g1_named_history
    S adm hr ready hw hframe hactive
  have hguard := actionQ2_crossReaderBodyReadyGuard_history
    S adm hbelow hr ready hp w hw Q hselected
  have hQgrade1 := selectedG2_G1_at_read_after_cutoff
    S adm hbelow ready hactionHor hp hw hselected hguard
  change DecoupledConsensusModel.Protocol.gradeBool S.E
    (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
    (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
    S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1)
      (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1) L = true at hLgrade1
  change DecoupledConsensusModel.Protocol.gradeBool S.E
    (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
    (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
    S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1)
      (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1) Q = true at hQgrade1
  have hLQ : Block.compatible L Q = true :=
    graded_oneChain_at_reader (V := V) S.E
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
      S.hc.η_SG r
      (early := DecoupledConsensusModel.Protocol.early S.E S.hc r .g1)
      (late := DecoupledConsensusModel.Protocol.late S.E S.hc r .g1)
      (by
        simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.late,
          DecoupledConsensusModel.Protocol.Phase.earlyOffset,
          DecoupledConsensusModel.Protocol.Phase.lateOffset]
        linarith [S.E.Δ_pos])
      hLgrade1 hQgrade1
  have hsourceNode := nodeFGSource_of_actionFGSource_history
    S rho p r hsource
  have hQB : Block.Preceq Q B :=
    preceq_actionFGSource_of_actionQ2 S rho p r hselected
      (Block.preceq_self Q) hsourceNode
  simp only [Block.compatible, Bool.or_eq_true] at hLQ
  rcases hLQ with hLQ | hQL
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl (Block.preceq_trans hLQ hQB)
  · rcases actionFGSource_genuineClear_or_selectedG2_named
        S rho p r hselected hsource with hclear | hlocal
    · obtain ⟨_, _, _, hwalk, _, _⟩ := hclear
      obtain ⟨Ln, hLnErase, hLnG0, _, hFg0L, _⟩ :=
        activeActionAnchor_namedBody_at_sourceG0_history
          S adm hbelow hr ready hactionHor hp hw hframe hactive
      have hLtree : L ∈ (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.core.T := by
        have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).1.1.1
        change L ∈ (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.core.T
        rw [hcoh.1, ← hLnErase]
        exact Finset.mem_image_of_mem NamedBlock.erase hLnG0
      have hgstG1 : S.E.t_GST ≤
          DecoupledConsensusModel.Protocol.early S.E S.hc r .g1 :=
        ready.1.trans (by
          simp only [DecoupledConsensusModel.Protocol.early,
            DecoupledConsensusModel.Protocol.Phase.earlyOffset]
          linarith [S.E.Δ_pos])
      have hforward : ∀ sender u key Head,
          u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
            (PhaseGrades.readAt S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
            (PhaseGrades.readAt S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
            S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1) sender →
          DecoupledConsensusModel.Protocol.localCovers
            (PhaseGrades.readAt S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
            u.confirmed L = true →
          u.confirmed = some key →
          Block.find? (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.T key =
              some Head →
          Block.Preceq (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.core.F Head := by
        intro sender u key Head _ hcover hconf hfind
        apply Block.preceq_trans hFg0L
        unfold DecoupledConsensusModel.Protocol.localCovers at hcover
        unfold Protocol.head_covers at hcover
        simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing,
          hconf] at hcover
        rw [hfind] at hcover
        exact hcover
      have hbelowReaders :=
        g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relay
          S adm (slashableBound_of_admissible_belowOneThird S adm hbelow)
            hgstG1 ready.2 hw hp hforward
      have hguard := g1G0CrossReaderBodyReadyGuard_of_finalizedBelow
        S adm.toNamedAdmissibleCore hr hgstG1 ready.2 hw hp hbelowReaders
      have hLgrade0 := storeGrade_g0_of_storeGrade_g1_cross_reader
        S rho adm.toNamedAdmissibleCore r
          (g1G0TwoCutoffDelivery_of_core
            S adm.toNamedAdmissibleCore hgstG1)
          ready.2 w p hw hp L hLgrade1 hguard
      have hQaction := actionQ2_mem_filteredTree S rho p r hselected
      have hFQ : Block.Preceq (actionReadAt S rho p r).st.core.F Q :=
        NamedOutageClosure.q10_filtered_F hQaction
      have hFL : Block.Preceq (actionReadAt S rho p r).st.core.F L :=
        Block.preceq_trans hFQ hQL
      have hBclear : PhaseGrades.nodeClear S
          (actionReadAt S rho p r) r B = true := by
        unfold Protocol.deepest_clear at hwalk
        have htest := (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hwalk)).2.2
        simpa only [PhaseGrades.nodeClear, PhaseGrades.nodeRead,
          actionStoreAt] using htest
      exact relativeG0_compatible_clearSource_of_finalizedPreceq_history
        S adm hr hactionHor hp hLtree hLgrade0 hFL hBclear
    · subst B
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hQL

#print axioms activeActionAnchor_compatible_actionFGSource_after_cutoff_named


/-- Exact same-round checkpoints agree from the fully named regime frame. -/
theorem PrefixFGSelectorConeAt.confirmationWitness_of_sameRound_honestHeightRow_of_frame_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a b : NamedAttestation V} {ta tb : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    {Tprev : NamedBlock V} {c0 : Round}
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    (hb : b.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + 1))
    (hround : a.round = b.round) :
    fgConfirmationWitness S
      (actionStoreAt S rho b.val_index b.round) = some T := by
  obtain ⟨Cfg', T', _, _, hsource', hCfgMem', _, hheight', hT', _⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness S adm hb hemit hrow
  have hselected' : fgConfirmationWitness S
      (actionStoreAt S rho b.val_index b.round) = some T' := by
    have hderived' := actionStoreDerived_named_history S hCfgMem'
    simp only [fgConfirmationWitness, hsource', Option.map_some]
    rw [hderived']
    exact congrArg some hT'.symm
  have hcut : strictEventIndex rho (S.a a.round) < first :=
    hseed.actionPrefix_lt adm.toNamedScheduleWellFormed
  have hprefix : strictEventIndex rho (S.a a.round) ≤ first - 1 :=
    Nat.le_sub_one_of_lt hcut
  have hfrontier : honestHMaxBeforeIndex S rho (first - 1) < blocked + 2 := by
    have hstopLt : first - 1 < first := by
      exact Nat.sub_lt (Nat.zero_lt_of_lt hcut) Nat.zero_lt_one
    exact (hfirst.before _ hstopLt).trans_lt
      (Nat.lt_succ_self (blocked + 1))
  have hhor : S.a a.round ≤ rho.horizon := hseed.actionHorizon adm
  have hsourceAtRound : actionFGSource S
      (actionStoreAt S rho b.val_index a.round) = some Cfg'.erase := by
    simpa only [hround] using hsource'
  have hsourceMemAtRound : Cfg' ∈
      (actionStoreAt S rho b.val_index a.round).st.bodies := by
    simpa only [hround] using hCfgMem'
  have hPrevCfg : NamedBlock.Preceq Tprev Cfg :=
    hframe.sourceAbove a.val_index hseed.signerHonest a.round hprefix
      hhor Cfg hseed.sourceMem hseed.exactFGSource
        hseed.sourceDerivedHeight
  have hPrevCfg' : NamedBlock.Preceq Tprev Cfg' :=
    hframe.sourceAbove b.val_index hb a.round hprefix hhor Cfg'
      hsourceMemAtRound hsourceAtRound hheight'
  have hsourceNode := nodeFGSource_of_actionFGSource_history
    S rho a.val_index a.round hseed.exactFGSource
  have hsourceNode' := nodeFGSource_of_actionFGSource_history
    S rho b.val_index a.round hsourceAtRound
  have hcompat : Block.compatible Cfg.erase Cfg'.erase = true := by
    exact actionFGSources_compatible_of_namedFrame
      S adm hcom hbelow ready hseed.signerHonest hb hsourceNode hsourceNode'
        hseed.sourceMem hsourceMemAtRound hframe hseed.sourceDerivedHeight
          hheight' hPrevCfg hPrevCfg' hprefix hfrontier hhor
  have hCfgRun := actionBody_runBlock_named_history
    S adm hseed.signerHonest hseed.sourceMem
  have hCfg'Run := actionBody_runBlock_named_history S adm hb hCfgMem'
  have hnamedCompat : NamedBlock.compatible Cfg Cfg' = true := by
    simp only [Block.compatible, Bool.or_eq_true] at hcompat
    simp only [NamedBlock.compatible, Bool.or_eq_true]
    rcases hcompat with hpre | hpre
    · exact Or.inl (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hCfgRun hCfg'Run hpre)
    · exact Or.inr (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hCfg'Run hCfgRun hpre)
  have heq : T = T' := by
    apply fgConfirmationWitness_eq_of_compatible_of_height_eq S
      hnamedCompat (hseed.sourceDerivedHeight.trans hheight'.symm)
      hseed.checkpointDerived hT'
  exact heq ▸ hselected'

#print axioms PrefixFGSelectorConeAt.confirmationWitness_of_sameRound_honestHeightRow_of_frame_named

/-- earlier's next-vote retention step over the fully named predecessor frame. -/
theorem ancestorGenuineConfirmation_filtered_at_nextVote_of_namedFrame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {B : NamedBlock V} {C : Block V}
    {contract : Protocol.GradeContract V}
    (hgenuine : GenuineConfirmationWith contract S.E S.hc
      (Proofs.Optimistic.confStore S rho p (S.hc.opening_slot r))
      (S.hc.opening_slot r) C)
    (hBC : Block.Preceq B.erase C)
    (hBmem : B ∈ (actionStoreAt S rho p r).st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : NamedBlock V} {c0 : Round}
    (hframe : NamedHeightRegimeFrame S rho blocked stop Tprev c0)
    (hBheight :
      (Protocol.derive_named S.E S.cfg B).h = blocked + 1)
    (hTB : NamedBlock.Preceq Tprev B)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    (hactionHor : S.a r ≤ rho.horizon)
    {reader : V} (hreader : reader ∈ rho.honest) :
    B.erase ∈ filteredTree
      (voteDutyRead S rho reader (S.hc.opening_slot r + 1)) := by
  let vote := Protocol.vote_time S.E (S.hc.opening_slot r + 1)
  have hfloor : FinalityFloorAt S rho blocked stop Tprev.erase := by
    intro v hv n hn X hXrun hXheight hTX
    have hTXnamed : NamedBlock.Preceq Tprev X :=
      Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hframe.prevRun hXrun hTX
    exact hframe.floor v hv n hn X hXrun hXheight hTXnamed
  have hbody := ancestorGenuineConfirmation_body_at_nextVote_of_floor
    S adm ready hp hgenuine hBC hBmem hfloor hBheight
      (Proofs.NamedWire.erase_preceq hTB) hactionPrefix hactionHor hreader
  have hbodyPre : B ∈
      (NamedRun.stateBeforeTime S rho vote reader).st.bodies := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
      vote] using hbody
  have hvoteAction : vote ≤ S.a r := (next_vote_time_lt_action S r).le
  have hvotePrefix : strictEventIndex rho vote ≤ stop :=
    (strictEventIndex_mono rho hvoteAction).trans hactionPrefix
  have heq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed vote) reader
  have hbodyIndex := hbodyPre
  rw [heq] at hbodyIndex
  have hfiltered := hframe.fgRoot_preceq_and_filteredMem
    adm hfrontier hreader hvotePrefix hbodyIndex hBheight hTB
  rw [← heq] at hfiltered
  simpa only [filteredTree, voteDutyRead,
    NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
    vote] using hfiltered.2

#print axioms ancestorGenuineConfirmation_filtered_at_nextVote_of_namedFrame

/-- The fully named frame producer for earlier's clear-source contract. -/
theorem voterAnchorSourceClearInputsMain_of_namedFrame_source
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    (_hpostPrev : S.E.t_GST ≤ S.a (r - 1))
    {stop : Nat} {H : Height} {Prev : NamedBlock V} {c0 : Round}
    (hframe : NamedHeightRegimeFrame S rho H stop Prev c0)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < H + 2)
    (hactionHor : S.a r ≤ rho.horizon) :
    ∀ {p : V} (A : Block V) (B : NamedBlock V),
      p ∈ rho.honest →
      PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r = some A →
      actionFGSource S (actionStoreAt S rho p r) = some B.erase →
      B ∈ (actionStoreAt S rho p r).st.bodies →
      (Protocol.derive_named S.E S.cfg B).h = H + 1 →
      PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r ≠ some B.erase →
      VoterAnchorSourceClearInputsMain S rho r p B.erase := by
  intro p A B hp hselected hsource hBmem hBheight hnot
  have hTB : NamedBlock.Preceq Prev B :=
    hframe.sourceAbove p hp r hactionPrefix hactionHor B hBmem
      hsource hBheight
  rcases actionFGSource_genuineClear_or_selectedG2_named
      S rho p r hselected hsource with hclear | hlocal
  · obtain ⟨C, hgenuine, -, -, -, hBC⟩ := hclear
    have hnext : ∀ w ∈ rho.honest, B.erase ∈ filteredTree
        (voteDutyRead S rho w (S.hc.opening_slot r + 1)) := by
      intro w hw
      exact ancestorGenuineConfirmation_filtered_at_nextVote_of_namedFrame
        S adm ready hp hgenuine hBC hBmem hframe hBheight hTB
          hactionPrefix hfrontier hactionHor hw
    refine ⟨hnext, ?_⟩
    intro w hw L hanchor
    rcases voterAnchorAt_cases S rho w
        (S.hc.opening_slot r + 1) with hroot | hactive
    · simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inl (by
        rw [← hanchor, hroot]
        exact Proofs.Records.preceq_get_fg_root_of_mem_filtered (hnext w hw))
    · obtain ⟨root, Anchor, hframeL, hactiveL, hanchorL⟩ := hactive
      have hroundDuty : S.hc.round_of
          (voteDutyRead S rho w
            (S.hc.opening_slot r + 1)).st.core.s = r := by
        simpa only [Proofs.Optimistic.voteDutyRead_slot] using
          Proofs.HealingLemmas.round_of_opening_succ S.hc r
      rw [hroundDuty] at hframeL
      have hAnchorEq : Anchor = L := hanchorL.symm.trans hanchor
      have hactiveL' : DecoupledConsensusModel.Protocol.activePrefix
          (filteredTree (voteDutyRead S rho w
            (S.hc.opening_slot r + 1))) root = some L := by
        simpa only [hAnchorEq] using hactiveL
      exact freshAnchor_compatible_actionFGSource_after_cutoff_named
        S adm hbelow hr ready hactionHor hp hw hselected hsource
          (by simpa using hframeL) (by simpa using hactiveL')
  · exact False.elim (hnot (hlocal ▸ hselected))

#print axioms voterAnchorSourceClearInputsMain_of_namedFrame_source
/-- earlier's source-round SG compatibility over the fully named frame. -/
theorem PrefixFGSelectorConeAt.sgEmissionsCompatible_of_source_of_frame_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (_hc0 : c0 ≤ a.round)
    (ready : GradeRoundReady S rho a.round)
    (hpostPrev : S.E.t_GST ≤ S.a (a.round - 1)) :
    HonestSGEmissionsCompatibleAtRound S rho a.round T := by
  have hactionBefore : strictEventIndex rho (S.a a.round) < first :=
    hseed.actionPrefix_lt adm.toNamedScheduleWellFormed
  have hprefix : strictEventIndex rho (S.a a.round) ≤ first - 1 :=
    Nat.le_sub_one_of_lt hactionBefore
  have hfrontier : honestHMaxBeforeIndex S rho (first - 1) < blocked + 2 := by
    have hstopLt : first - 1 < first :=
      Nat.sub_lt (Nat.zero_lt_of_lt hactionBefore) Nat.zero_lt_one
    exact (hfirst.before _ hstopLt).trans_lt
      (Nat.lt_succ_self (blocked + 1))
  have hhor : S.a a.round ≤ rho.horizon := hseed.actionHorizon adm
  have hTCfg : Block.Preceq T Cfg.erase := by
    rw [hseed.checkpointDerived]
    exact Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg Cfg
  have hTprevCfg : NamedBlock.Preceq Tprev Cfg :=
    hframe.sourceAbove a.val_index hseed.signerHonest a.round hprefix hhor
      Cfg hseed.sourceMem hseed.exactFGSource hseed.sourceDerivedHeight
  obtain ⟨A, hA⟩ : ∃ A : Block V, PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some A := by
    cases hq : PhaseGrades.nodeQ2
        S (actionReadAt S rho a.val_index a.round) a.round with
    | none =>
        have hsource := nodeFGSource_of_actionFGSource_history
          S rho a.val_index a.round hseed.exactFGSource
        simp only [PhaseGrades.nodeFGSource, PhaseGrades.nodeQ2,
          PhaseGrades.nodeRead] at hsource hq
        unfold Protocol.fg_source_with Protocol.grade2_block_with at hsource
        rw [hq] at hsource
        cases hsource
    | some A => exact ⟨A, rfl⟩
  have hr : 0 < a.round := selectedQ2_round_pos_named_history S adm hA
  have close
      (hfiltered : ∀ w, w ∈ rho.honest →
        Cfg.erase ∈ filteredTree (actionReadAt S rho w a.round))
      (hgenuineCompat : ∀ w, w ∈ rho.honest → ∀ C,
        GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w
              (S.hc.opening_slot a.round)).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho w
            (S.hc.opening_slot a.round))
            (S.hc.opening_slot a.round) C →
        Block.compatible Cfg.erase C = true) :
      HonestSGEmissionsCompatibleAtRound S rho a.round T := by
    intro w hw _
    have hrootCfg : Block.Preceq
        (Protocol.get_fg_root
          (actionReadAt S rho w a.round).st.core.toHealing.toFG) Cfg.erase :=
      Proofs.Records.preceq_get_fg_root_of_mem_filtered (hfiltered w hw)
    have hrootT : Block.compatible
        (Protocol.get_fg_root
          (actionReadAt S rho w a.round).st.core.toHealing.toFG) T = true :=
      compatible_with_checkpoint_below_named_history
        (by simpa only [Block.compatible, Bool.or_eq_true] using Or.inl hrootCfg)
        hTCfg
    have hanchorCfg : Block.compatible
        (PhaseGrades.nodeAnchor S (actionReadAt S rho w a.round) a.round)
        Cfg.erase = true := by
      rcases actionAnchor_cases_named_history S rho w a.round with
        hroot | ⟨root, L, hframeL, hactiveL, hanchorL⟩
      · rw [hroot]
        simpa only [Block.compatible, Bool.or_eq_true] using Or.inl hrootCfg
      · rw [hanchorL]
        exact activeActionAnchor_compatible_actionFGSource_after_cutoff_named
          S adm hbelow hr ready hhor hseed.signerHonest hw hA
            hseed.exactFGSource hframeL hactiveL
    have hanchorT : Block.compatible
        (PhaseGrades.nodeAnchor S (actionReadAt S rho w a.round) a.round)
        T = true :=
      compatible_with_checkpoint_below_named_history hanchorCfg hTCfg
    have hliveT : Block.compatible
        (actionStoreAt S rho w a.round).live_confirmed T = true := by
      rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot
          S rho w a.round with ⟨C, hgenuine, hC⟩ | ⟨R, hRroot, hRlive⟩
      · rw [← hC]
        have hCCfg : Block.compatible C Cfg.erase = true := by
          simpa only [Block.compatible, Bool.or_comm] using
            hgenuineCompat w hw C hgenuine
        exact compatible_with_checkpoint_below_named_history
          hCCfg hTCfg
      · have hrootEq : Protocol.get_fg_root
            (actionStoreAt S rho w a.round).st.core.toHealing.toFG =
          Protocol.get_fg_root
            (Proofs.Optimistic.confStore S rho w
              (S.hc.opening_slot a.round)).toHealing.toFG := by
          rw [actionStoreAt_eq_update_confirmation_confStore]
          rfl
        rw [← hRlive, hRroot, ← hrootEq]
        exact hrootT
    rcases actionSGBlockAt_tiers S rho w a.round with
      hwalk | ⟨Q, hQ, hsg⟩ | ⟨_, _, hsg⟩ | ⟨_, _, hsg⟩
    · exact compatible_ancestor_left_named_history hwalk.2.1 hliveT
    · rw [hsg]
      exact compatible_ancestor_left_named_history
        (actionQ2_preceq_actionAnchor S adm.toNamedAdmissibleCore hw
          hr hhor hQ) hanchorT
    · rw [hsg]
      exact hrootT
    · rw [hsg]
      exact hanchorT
  by_cases hlocal : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase
  · have hretained := sameRoundSourceQ2Retained_of_namedFrame
      S adm ready hseed.signerHonest hlocal hseed.exactFGSource
        hseed.sourceMem hframe hseed.sourceDerivedHeight hprefix hfrontier hhor
    apply close (fun w hw => (hretained w hw).2.2)
    intro w hw C hgenuine
    exact hseed.selectedSource_compatible_genuineOpening_of_namedFrame_history
      adm hcom hbelow hfirst hframe ready hlocal hw hgenuine
  · rcases actionFGSource_genuineClear_or_selectedG2_named
        S rho a.val_index a.round hA hseed.exactFGSource with
      hclear | hsourceQ2
    · obtain ⟨C0, hgenuine0, -, -, -, hCfgC0⟩ := hclear
      have hmain := voterAnchorSourceClearInputsMain_of_namedFrame_source
        S adm hbelow hr ready hpostPrev hframe hprefix hfrontier hhor
          A Cfg hseed.signerHonest hA hseed.exactFGSource hseed.sourceMem
            hseed.sourceDerivedHeight hlocal
      have hfiltered : ∀ w, w ∈ rho.honest →
          Cfg.erase ∈ filteredTree (actionReadAt S rho w a.round) := by
        intro w hw
        have hbody := actionBody_at_action_of_nextVoteFiltered
          S adm hseed.signerHonest hseed.sourceMem hw (hmain.nextTarget w hw)
        have heq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
          S adm.toNamedScheduleWellFormed (S.a a.round)) w
        have hbodyIndex := hbody
        change Cfg ∈ (NamedRun.stateBeforeTime S rho
          (S.a a.round) w).st.bodies at hbodyIndex
        rw [heq] at hbodyIndex
        have hout := hframe.fgRoot_preceq_and_filteredMem
          adm hfrontier hw hprefix hbodyIndex hseed.sourceDerivedHeight
            hTprevCfg
        have hpre : Cfg.erase ∈ Protocol.get_filtered_block_tree
            (NamedRun.stateBeforeTime S rho
              (S.a a.round) w).st.core.toHealing.toFG := by
          rw [heq]
          exact hout.2
        simpa only [filteredTree, actionReadAt,
          NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
          NamedActionReads.confirmationReadFrom,
          NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hpre
      apply close hfiltered
      intro w hw C hgenuine
      have hpost : S.E.t_GST ≤ Protocol.proposal_time S.E
          (S.hc.opening_slot a.round) :=
        ready.1.trans (NamedOutageClosure.early_le_opening S a.round)
      have hconfHor : Protocol.confirmation_time S.E
          (S.hc.opening_slot a.round) ≤ rho.horizon := by
        rw [opening_confirmation_time_eq_action]
        exact hhor
      have hcompat := Protocol.sameSlot_genuine_compatible_after_gst
        S adm hseed.signerHonest hw hpost hconfHor hgenuine0 hgenuine
      exact compatible_ancestor_left_named_history hCfgC0 hcompat
    · exact False.elim (hlocal (hsourceQ2 ▸ hA))

#print axioms PrefixFGSelectorConeAt.sgEmissionsCompatible_of_source_of_frame_named



/-- earlier's first-interior source protection over the fully named frame. The
genuine-clear arm uses the earlier-shaped clear-source contract; the selected-Q2
arm uses the named phase-ladder transport above. -/
theorem PrefixFGSelectorConeAt.checkpointProtection_firstInterior_of_frame_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (_hc0 : c0 ≤ a.round)
    (ready : GradeRoundReady S rho a.round)
    (hpostPrev : S.E.t_GST ≤ S.a (a.round - 1))
    (_hG1 : ∀ w ∈ rho.honest, ∃ Q : Block V,
      namedG1At S rho w a.round Q) :
    (∀ w ∈ rho.honest, Block.Preceq T
      (voterHeadAt S rho w (S.hc.opening_slot a.round + 1))) ∧
      NamedHonestVotesCone S rho (S.hc.opening_slot a.round + 1)
        (fun X => Block.Preceq T X) := by
  have hactionBefore : strictEventIndex rho (S.a a.round) < first :=
    hseed.actionPrefix_lt adm.toNamedScheduleWellFormed
  have hprefix : strictEventIndex rho (S.a a.round) ≤ first - 1 :=
    Nat.le_sub_one_of_lt hactionBefore
  have hfrontier : honestHMaxBeforeIndex S rho (first - 1) < blocked + 2 := by
    have hstopLt : first - 1 < first :=
      Nat.sub_lt (Nat.zero_lt_of_lt hactionBefore) Nat.zero_lt_one
    exact (hfirst.before _ hstopLt).trans_lt
      (Nat.lt_succ_self (blocked + 1))
  have hhor : S.a a.round ≤ rho.horizon := hseed.actionHorizon adm
  have hTCfg : Block.Preceq T Cfg.erase := by
    rw [hseed.checkpointDerived]
    exact Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg Cfg
  obtain ⟨A, hA⟩ : ∃ A : Block V, PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some A := by
    cases hq : PhaseGrades.nodeQ2
        S (actionReadAt S rho a.val_index a.round) a.round with
    | none =>
        have hsource := nodeFGSource_of_actionFGSource_history
          S rho a.val_index a.round hseed.exactFGSource
        simp only [PhaseGrades.nodeFGSource, PhaseGrades.nodeQ2,
          PhaseGrades.nodeRead] at hsource hq
        unfold Protocol.fg_source_with Protocol.grade2_block_with at hsource
        rw [hq] at hsource
        cases hsource
    | some A => exact ⟨A, rfl⟩
  by_cases hlocal : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase
  · exact hseed.selectedSource_firstInterior_of_frame_named_history
      adm hbelow hfirst hframe ready hlocal
  · rcases actionFGSource_genuineClear_or_selectedG2_named
        S rho a.val_index a.round hA hseed.exactFGSource with hclear | hsourceQ2
    · obtain ⟨C, hgenuine, -, -, -, hCfgC⟩ := hclear
      have hr : 0 < a.round :=
        selectedQ2_round_pos_named_history S adm hA
      have hmain := voterAnchorSourceClearInputsMain_of_namedFrame_source
        S adm hbelow hr ready hpostPrev hframe hprefix hfrontier hhor
          A Cfg hseed.signerHonest hA hseed.exactFGSource hseed.sourceMem
            hseed.sourceDerivedHeight hlocal
      rcases genuineClear_nextVoteCone_or_heightProgressThrough_of_mainInputs
          S adm ready hseed.signerHonest hgenuine hCfgC hseed.sourceMem
            hseed.sourceDerivedHeight hhor hmain
              (through := Protocol.vote_time S.E
                (S.hc.opening_slot a.round + 1))
              (le_refl _) with
        hprogress | hprotected
      · obtain ⟨w, hw, u, hu, hmax⟩ := hprogress
        have huAction : u < S.a a.round :=
          hu.trans_lt (next_vote_time_lt_action S a.round)
        have hcursor : inclusiveEventIndex rho u ≤
            strictEventIndex rho (S.a a.round) := by
          rw [strictEventIndex_eq_inclusiveEventIndex_pred]
          exact inclusiveEventIndex_mono rho
            (Int.le_sub_one_iff.mpr huAction)
        have hlocalMax : (rho.storeAt S w u).h_max ≤
            honestHMaxBeforeIndex S rho
              (strictEventIndex rho (S.a a.round)) := by
          rw [storeAt_eq_stateBefore_inclusiveEventIndex
            S adm.toNamedScheduleWellFormed w u]
          exact (localHMax_le_honestHMaxBeforeIndex S rho
            (inclusiveEventIndex rho u) hw).trans
              (honestHMaxBeforeIndex_mono S rho hcursor)
        have hbad := hmax.trans hlocalMax
        exact False.elim ((not_lt_of_ge hbad)
          (((honestHMaxBeforeIndex_mono S rho hprefix).trans_lt hfrontier).trans_le
            (Nat.le_succ (blocked + 2))))
      · refine ⟨fun w hw => Block.preceq_trans hTCfg
          (hprotected.1 w hw), ?_⟩
        intro w hw hcommittee
        obtain ⟨X, hCfgX, hXrun, hXemit⟩ :=
          hprotected.2 w hw hcommittee
        exact ⟨X, Block.preceq_trans hTCfg hCfgX, hXrun, hXemit⟩
    · exact False.elim (hlocal (hsourceQ2 ▸ hA))

#print axioms PrefixFGSelectorConeAt.checkpointProtection_firstInterior_of_frame_named





/-- earlier's one-round SG successor over the fully named predecessor frame.
The relative G2 and G1 branches use the preceding honest action carrier;
the named checkpoint supplies the common upper needed to interpret it. -/
theorem PrefixFGSelectorConeAt.sgEmissionsCompatible_laterRound_of_frame_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    {r : Round} (hr : a.round ≤ r)
    (hsg : HonestSGEmissionsCompatibleAtRound S rho r T)
    (hgf : NamedHonestVotesCone S rho (S.hc.opening_slot (r + 1))
      (fun X => Block.Preceq T X))
    (hhor : S.a (r + 1) ≤ rho.horizon)
    (hbefore : strictEventIndex rho (S.a (r + 1)) < first) :
    HonestSGEmissionsCompatibleAtRound S rho (r + 1) T := by
  let core := adm.toNamedAdmissibleCore
  have hpostSource : S.E.t_GST ≤ S.a a.round :=
    ready.1.trans ((NamedOutageClosure.early_le_domain S a.round).trans
      (FrameForward.domain_le_a S a.round .g2))
  have hpost : S.E.t_GST ≤ S.a r :=
    hpostSource.trans (Assembly.a_mono S hr)
  have hactionPrefix : strictEventIndex rho (S.a (r + 1)) ≤ first - 1 :=
    Nat.le_sub_one_of_lt hbefore
  have hfrontier : honestHMaxBeforeIndex S rho (first - 1) < blocked + 2 := by
    have hstopLt : first - 1 < first :=
      Nat.sub_lt (Nat.zero_lt_of_lt hbefore) Nat.zero_lt_one
    exact (hfirst.before _ hstopLt).trans_lt
      (Nat.lt_succ_self (blocked + 1))
  obtain ⟨K, hKsource, hKT0, hKheight0, hKCfg, hKrun⟩ :=
    action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
  have hKT : K.erase = T := hKT0.trans hseed.checkpointDerived.symm
  have hKheight : (Protocol.derive_named S.E S.cfg K).h = blocked + 1 :=
    hKheight0.trans hseed.sourceDerivedHeight
  have hTprevCfg : Block.Preceq Tprev.erase Cfg.erase :=
    Proofs.NamedWire.erase_preceq (hframe.sourceAbove a.val_index hseed.signerHonest
      a.round (Nat.le_sub_one_of_lt
        (hseed.actionPrefix_lt adm.toNamedScheduleWellFormed))
      (hseed.actionHorizon adm) Cfg hseed.sourceMem hseed.exactFGSource
      hseed.sourceDerivedHeight)
  have hTprevK : NamedBlock.Preceq Tprev K := by
    rcases Block.preceq_linear hTprevCfg
        (Proofs.NamedWire.erase_preceq hKCfg) with hprevK | hKprev
    · obtain ⟨P, hPK, hPerase⟩ :=
        Proofs.NamedAncestry.erased_ancestor_lift K hprevK
      have hPrun : RunBlock S rho P :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hKrun hPK
      have hPTprev : P = Tprev := by
        apply adm.toNamedRootCollisionFree.root_injective
          P Tprev hPrun hframe.prevRun P Tprev
          (Or.inl (Proofs.NamedAncestry.named_self P))
          (Or.inr (Proofs.NamedAncestry.named_self Tprev))
        rw [← Proofs.NamedWire.erase_root P, hPerase, Proofs.NamedWire.erase_root]
      rw [← hPTprev]
      exact hPK
    · obtain ⟨P, hPTprev, hPerase⟩ :=
        Proofs.NamedAncestry.erased_ancestor_lift Tprev hKprev
      have hPrun : RunBlock S rho P :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hframe.prevRun hPTprev
      have hPK : P = K := by
        apply adm.toNamedRootCollisionFree.root_injective
          P K hPrun hKrun P K
          (Or.inl (Proofs.NamedAncestry.named_self P))
          (Or.inr (Proofs.NamedAncestry.named_self K))
        rw [← Proofs.NamedWire.erase_root P, hPerase, Proofs.NamedWire.erase_root]
      have hKTprev : NamedBlock.Preceq K Tprev := by
        rw [← hPK]
        exact hPTprev
      have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hKTprev
      rw [hKheight] at hmono
      exact False.elim
        (Nat.not_succ_le_self blocked (hmono.trans hframe.prevHeight))
  have hcheckpointFloor : ∀ (p : DecoupledConsensusModel.Protocol.Phase) w,
      w ∈ rho.honest →
      Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) p) w).st.core.F T := by
    intro p w hw
    have hdomainAction := FrameForward.domain_le_a
      S (r + 1) p
    have hdomainPrefix : strictEventIndex rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) p) ≤ first - 1 :=
      (strictEventIndex_mono rho hdomainAction).trans hactionPrefix
    rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) p)) w, ← hKT]
    exact hframe.floor w hw _ hdomainPrefix K hKrun
      (by rw [hKheight]; exact Nat.le_succ blocked) hTprevK
  have hwindow : ∀ p : DecoupledConsensusModel.Protocol.Phase,
      RelativeCarrierWindowAt S rho r p := by
    intro p w hw u hu
    have huHon : u ∈ rho.honest :=
      ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu).1
    obtain ⟨b, hbround, hbval, hemit⟩ :=
      NamedOutageClosure.honestRoundVoter_emits S rho hu
    obtain ⟨j, hj, _, Hb, hHb, hconfirmed⟩ :=
      Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
    have hcarrierMem : actionSGBlockAt S rho u r ∈
        (NamedRun.stateBeforeTime S rho (S.a r) u).st.core.T :=
      actionSGBlockAt_mem_storeBeforeTime S rho u r
    obtain ⟨D, hDbody, hDerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
        S rho (S.a r) u hcarrierMem
    obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      core.toNamedScheduleWellFormed.sorted (S.a r)
    have hDprefix : D ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
      rw [← hn]
      exact hDbody
    have hHbSource : Hb ∈
        (NamedRun.stateBeforeTime S rho (S.a r) u).st.bodies := by
      have hstate := NamedActionSources.action_read_index S rho
        core.toNamedScheduleWellFormed j u b.round (by simpa only [hbround] using hj)
      change Hb ∈ (NamedRun.stateBefore S rho j u).st.bodies at hHb
      rw [← hbround, ← hstate]
      exact hHb
    have hHbPrefix : Hb ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
      rw [← hn]
      exact hHbSource
    have hDrun : RunBlock S rho D :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S huHon hDprefix
    have hHbrun : RunBlock S rho Hb :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S huHon hHbPrefix
    have hroot : D.root = Hb.root := by
      rw [← Proofs.NamedWire.erase_root D, hDerase]
      have hbconfirmed := NamedOutageClosure.honest_emitted_round_confirmed
        S rho core u huHon r (Assembly.a_mono S (Nat.le_succ r) |>.trans hhor)
          hbround hemit
      exact Option.some.inj (hbconfirmed.symm.trans hconfirmed)
    have hDH : D = Hb :=
      core.toNamedRootCollisionFree.root_injective D Hb hDrun hHbrun D Hb
        (Or.inl (Proofs.NamedAncestry.named_self D))
        (Or.inr (Proofs.NamedAncestry.named_self Hb)) hroot
    have hHbErase : Hb.erase = actionSGBlockAt S rho u r := by
      rw [← hDH, hDerase]
    have hHbRoot : Hb.root = (actionSGBlockAt S rho u r).root := by
      rw [← Proofs.NamedWire.erase_root Hb, hHbErase]
    have hawake : (S.node u).awake r = true := by
      simpa only [hbround] using Proofs.Optimistic.emits_attest_awake S hemit
    have hemitAction := honest_emits_exact_actionAttestationAt_of_awake
      S core.toNamedScheduleWellFormed huHon r hawake
        ((Assembly.a_mono S (Nat.le_succ r)).trans hhor)
    have hcarrierT : Block.compatible Hb.erase T = true := by
      rw [hHbErase]
      exact hsg u huHon hemitAction
    have hFT := hcheckpointFloor p w hw
    have hk : r ∈ Protocol.latest_window S.hc.η_SG (r + 1) := by
      apply NamedOutageClosure.mem_latest_window
      · simpa only [Nat.add_sub_cancel] using
          Nat.sub_le_sub_left S.hc.η_SG_ge_one (r + 1)
      · exact Nat.lt_succ_self r
    have hdeadline : max (S.a b.round) S.E.t_GST + S.E.Δ ≤
        DecoupledConsensusModel.Protocol.early S.E S.hc (r + 1) p := by
      rw [hbround, max_eq_left hpost]
      apply (NamedOutageClosure.action_delta_le_early
        S S.hc.R_ge_three (Nat.lt_succ_self r)).trans
      cases p <;> simp only [DecoupledConsensusModel.Protocol.early,
        DecoupledConsensusModel.Protocol.Phase.earlyOffset] <;> linarith [S.E.Δ_pos]
    have horder : DecoupledConsensusModel.Protocol.early S.E S.hc (r + 1) p ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) p := by
      cases p <;> simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
        DecoupledConsensusModel.Protocol.Phase.earlyOffset,
        DecoupledConsensusModel.Protocol.Phase.domainOffset] <;> linarith [S.E.Δ_pos]
    have hcut : DecoupledConsensusModel.Protocol.early S.E S.hc (r + 1) p ≤ rho.horizon :=
      horder.trans ((FrameForward.domain_le_a
        S (r + 1) p).trans hhor)
    have hhead : ∃ j : Nat,
        rho.events[j]? = some (.tick u (S.a r)) ∧
        Hb ∈ (NamedActionReads.actionReadFrom S
          (NamedRun.stateBefore S rho j u) b.round).st.bodies ∧
        b.confirmed = some Hb.root := by
      exact ⟨j, by simpa only [hbround] using hj, hHb, hconfirmed⟩
    change ∃ y ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) p) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) p) w).st.core.F
        S.hc.η_SG (r + 1) (DecoupledConsensusModel.Protocol.early S.E S.hc (r + 1) p) u,
      y.round = r ∧ y.confirmed = some (actionSGBlockAt S rho u r).root ∧
        Block.find? (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) p) w).st.core.T
          (actionSGBlockAt S rho u r).root = some (actionSGBlockAt S rho u r)
    rcases (show Block.Preceq Hb.erase T ∨ Block.Preceq T Hb.erase by
      simpa only [Block.compatible, Bool.or_eq_true] using hcarrierT) with
      hHbT | hTHb
    · simpa only [hbround, hHbErase, hHbRoot] using
        (interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
          S core p hk huHon hw ⟨hbval, hbround, hemit⟩ hhead
            hHbT hFT (by simpa only [hbround] using hpost) hdeadline
              horder hcut)
    · simpa only [hbround, hHbErase, hHbRoot] using
        (interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
          S core p hk huHon hw ⟨hbval, hbround, hemit⟩ hhead
            (Block.preceq_self Hb.erase) (Block.preceq_trans hFT hTHb)
              (by simpa only [hbround] using hpost) hdeadline horder hcut)
  have hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho (r + 1) :=
    gradeFormingMajority_of_admissible_belowOneThird S adm hbelow
      (Nat.succ_pos r)
      ((FrameForward.domain_le_a S (r + 1) .g2).trans hhor)
  have hKsourcePre : K ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hKsource
  have hsourceDeadline : max (S.a a.round) S.E.t_GST + S.E.Δ ≤
      S.a (r + 1) := by
    rw [max_eq_left hpostSource]
    exact (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
      (lt_of_le_of_lt hr (Nat.lt_succ_self r))).trans
        ((NamedOutageClosure.early_le_domain S (r + 1)).trans
          (FrameForward.domain_le_a S (r + 1) .g2))
  have hcheckpointAtAction : ∀ w ∈ rho.honest,
      Block.Preceq (Protocol.get_fg_root
        (actionStoreAt S rho w (r + 1)).st.core.toHealing.toFG) T := by
    intro w hw
    have hreadEq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed (S.a (r + 1))) w
    have hFAction : Block.Preceq
        (NamedRun.stateBeforeTime S rho (S.a (r + 1)) w).st.core.F T := by
      rw [hreadEq, ← hKT]
      exact hframe.floor w hw _ hactionPrefix K hKrun
        (by rw [hKheight]; exact Nat.le_succ blocked) hTprevK
    have hFActionK : Block.Preceq
        (NamedRun.stateBeforeTime S rho (S.a (r + 1)) w).st.core.F K.erase := by
      rw [hKT]
      exact hFAction
    obtain ⟨hKtarget, -, -⟩ :=
      NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
        S rho core a.val_index hseed.signerHonest w hw K
          (S.a a.round) (S.a (r + 1)) (S.a (r + 1)) hKsourcePre
            hsourceDeadline (le_refl _) hhor hFActionK
    have hKtargetIndex : K ∈
        (NamedRun.stateBefore S rho
          (strictEventIndex rho (S.a (r + 1))) w).st.bodies := by
      have h := hKtarget
      rw [hreadEq] at h
      exact h
    have hrootIndex := hframe.rootBelow w hw _ hactionPrefix K
      hKtargetIndex hKheight hTprevK
    rw [actionStoreAt_fgRoot_eq_storeBeforeTime]
    change Block.Preceq (Protocol.get_fg_root
      (NamedRun.stateBeforeTime S rho (S.a (r + 1)) w).st.core.toHealing.toFG) T
    rw [hreadEq, ← hKT]
    exact hrootIndex
  have readyNext : GradeRoundReady S rho (r + 1) := by
    constructor
    · exact hpost.trans
        ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
          (NamedOutageClosure.action_delta_le_early
            S S.hc.R_ge_three (Nat.lt_succ_self r)))
    · exact (FrameForward.domain_le_a
        S (r + 1) .g0).trans hhor
  have hopenPost : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot (r + 1)) := by
    rw [← Protocol.Γ_1_eq_vote_time]
    exact hpost.trans ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
      ((action_add_delta_le_next_Γ_neg1 S r).trans
        ((Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1)).le.trans
          (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos (r + 1)).le)))
  have hconfHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (r + 1)) ≤ rho.horizon := by
    rwa [opening_confirmation_time_eq_action]
  have hopen : 0 < S.hc.opening_slot (r + 1) :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hheads : ∀ x ∈ rho.honest,
      x ∈ S.E.committee (S.hc.opening_slot (r + 1)) →
      Block.Preceq T (voterHeadAt S rho x (S.hc.opening_slot (r + 1))) := by
    intro x hx hxc
    obtain ⟨X, hTX, hXrun, hXemit⟩ := hgf x hx hxc
    obtain ⟨H, hHerase, hHrun, hHemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits S core hx hopen hxc
        ((vote_time_le_confirmation_time S.E _).trans hconfHor)
    have heq := Proofs.Optimistic.emits_gfVote_unique S
      core.toNamedScheduleWellFormed hXemit hHemit rfl
    have hroot : X.root = H.root := by
      simpa only [Proofs.NamedWire.erase_root] using congrArg GoldfishVote.head heq
    have hXH : X = H := core.toNamedRootCollisionFree.root_injective
      X H hXrun hHrun X H (Or.inl (Proofs.NamedAncestry.named_self X))
        (Or.inr (Proofs.NamedAncestry.named_self H)) hroot
    rw [← hHerase, ← hXH]
    exact hTX
  intro w hw _
  have hrootT : Block.compatible
      (Protocol.get_fg_root
        (actionStoreAt S rho w (r + 1)).st.core.toHealing.toFG) T = true := by
    simpa only [Block.compatible, Bool.or_eq_true] using
      Or.inl (hcheckpointAtAction w hw)
  have hliveT : Block.compatible
      (actionStoreAt S rho w (r + 1)).live_confirmed T = true := by
    rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot
        S rho w (r + 1) with ⟨C, hC, hClive⟩ | ⟨R, hRroot, hRlive⟩
    · rw [← hClive]
      simpa only [Block.compatible, Bool.or_comm] using
        (WeakGoldfish.genuineConfirmation_compatible_of_priorProtectedHeads
          S core hcom hw hopen hopenPost hconfHor hC hheads)
    · rw [← hRlive, hRroot]
      exact hrootT
  have hanchorT : Block.compatible
      (PhaseGrades.nodeAnchor S (actionReadAt S rho w (r + 1)) (r + 1)) T = true := by
    rcases actionAnchor_cases_named_history S rho w (r + 1) with
      hroot | ⟨root, L, hframeL, hactiveL, hanchorL⟩
    · rw [hroot]
      exact hrootT
    · rw [hanchorL]
      have hLgrade := activeActionAnchor_storeGrade_g1_named_history
        S adm (Nat.succ_pos r) readyNext hw hframeL hactiveL
      obtain ⟨u, hu, hLu⟩ := relativeGrade_has_roundCarrier
        S core (hwindow .g1) hmajority hw
          (by simpa only [PhaseGrades.storeGrade,
            PhaseGrades.phaseGrade] using hLgrade)
      obtain ⟨huHon, b, _, hbround, hemit⟩ :=
        (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu
      have hawake : (S.node u).awake r = true := by
        simpa only [hbround] using Proofs.Optimistic.emits_attest_awake S hemit
      have hemitAction := honest_emits_exact_actionAttestationAt_of_awake
        S core.toNamedScheduleWellFormed huHon r hawake
          ((Assembly.a_mono S (Nat.le_succ r)).trans hhor)
      exact compatible_ancestor_left_named_history hLu
        (hsg u huHon hemitAction)
  rcases actionSGBlockAt_tiers S rho w (r + 1) with
    hwalk | ⟨Q, hQ, hout⟩ | ⟨_, _, hout⟩ | ⟨_, _, hout⟩
  · exact compatible_ancestor_left_named_history hwalk.2.1 hliveT
  · rw [hout]
    exact compatible_ancestor_left_named_history
      (actionQ2_preceq_actionAnchor S core hw
        (Nat.succ_pos r) hhor hQ) hanchorT
  · rw [hout]
    exact hrootT
  · rw [hout]
    exact hanchorT

#print axioms PrefixFGSelectorConeAt.sgEmissionsCompatible_laterRound_of_frame_named

/-- The named checkpoint is retained and filtered at a later read of the
height-regime prefix. The explicit relay deadline is the only timing input. -/
theorem PrefixFGSelectorConeAt.checkpointFiltered_at_laterRead_of_frame_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    {read : Time}
    (hdelay : max (S.a a.round) S.E.t_GST + S.E.Δ ≤ read)
    (hhor : read ≤ rho.horizon)
    (hbefore : strictEventIndex rho read < first)
    {w : V} (hw : w ∈ rho.honest) :
    (NamedRun.stateBeforeTime S rho read w).st.core.h_max = blocked + 1 ∧
      Block.Preceq (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho read w).st.core.toHealing.toFG) T ∧
      T ∈ Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho read w).st.core.toHealing.toFG := by
  let core := adm.toNamedAdmissibleCore
  obtain ⟨K, hKsource, hKT0, hKheight0, hKCfg, hKrun⟩ :=
    action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
  have hKT : K.erase = T := hKT0.trans hseed.checkpointDerived.symm
  have hKheight : (Protocol.derive_named S.E S.cfg K).h = blocked + 1 :=
    hKheight0.trans hseed.sourceDerivedHeight
  have hTprevCfg : Block.Preceq Tprev.erase Cfg.erase :=
    Proofs.NamedWire.erase_preceq (hframe.sourceAbove a.val_index hseed.signerHonest
      a.round (Nat.le_sub_one_of_lt
        (hseed.actionPrefix_lt adm.toNamedScheduleWellFormed))
      (hseed.actionHorizon adm) Cfg hseed.sourceMem hseed.exactFGSource
      hseed.sourceDerivedHeight)
  have hTprevK : NamedBlock.Preceq Tprev K := by
    rcases Block.preceq_linear hTprevCfg
        (Proofs.NamedWire.erase_preceq hKCfg) with hprevK | hKprev
    · obtain ⟨P, hPK, hPerase⟩ :=
        Proofs.NamedAncestry.erased_ancestor_lift K hprevK
      have hPrun : RunBlock S rho P :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hKrun hPK
      have hPTprev : P = Tprev := by
        apply adm.toNamedRootCollisionFree.root_injective
          P Tprev hPrun hframe.prevRun P Tprev
          (Or.inl (Proofs.NamedAncestry.named_self P))
          (Or.inr (Proofs.NamedAncestry.named_self Tprev))
        rw [← Proofs.NamedWire.erase_root P, hPerase, Proofs.NamedWire.erase_root]
      rw [← hPTprev]
      exact hPK
    · obtain ⟨P, hPTprev, hPerase⟩ :=
        Proofs.NamedAncestry.erased_ancestor_lift Tprev hKprev
      have hPrun : RunBlock S rho P :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hframe.prevRun hPTprev
      have hPK : P = K := by
        apply adm.toNamedRootCollisionFree.root_injective
          P K hPrun hKrun P K
          (Or.inl (Proofs.NamedAncestry.named_self P))
          (Or.inr (Proofs.NamedAncestry.named_self K))
        rw [← Proofs.NamedWire.erase_root P, hPerase, Proofs.NamedWire.erase_root]
      have hKTprev : NamedBlock.Preceq K Tprev := by
        rw [← hPK]
        exact hPTprev
      have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hKTprev
      rw [hKheight] at hmono
      exact False.elim
        (Nat.not_succ_le_self blocked (hmono.trans hframe.prevHeight))
  have hprefix : strictEventIndex rho read ≤ first - 1 :=
    Nat.le_sub_one_of_lt hbefore
  have hfrontier : honestHMaxBeforeIndex S rho (first - 1) < blocked + 2 := by
    have hstopLt : first - 1 < first :=
      Nat.sub_lt (Nat.zero_lt_of_lt hbefore) Nat.zero_lt_one
    exact (hfirst.before _ hstopLt).trans_lt
      (Nat.lt_succ_self (blocked + 1))
  have hreadEq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed read) w
  have hFread : Block.Preceq
      (NamedRun.stateBeforeTime S rho read w).st.core.F K.erase := by
    rw [hreadEq]
    exact hframe.floor w hw _ hprefix K hKrun
      (by rw [hKheight]; exact Nat.le_succ blocked) hTprevK
  have hKsourcePre : K ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hKsource
  obtain ⟨hKtarget, -, -⟩ :=
    NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
      S rho core a.val_index hseed.signerHonest w hw K
        (S.a a.round) read read hKsourcePre hdelay (le_refl _) hhor hFread
  have hKtargetIndex : K ∈
      (NamedRun.stateBefore S rho (strictEventIndex rho read) w).st.bodies := by
    have h := hKtarget
    rw [hreadEq] at h
    exact h
  have hout := hframe.fgRoot_preceq_and_filteredMem
    adm hfrontier hw hprefix hKtargetIndex hKheight hTprevK
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho
    (strictEventIndex rho read) w).1.1.1
  have hKraw : K.erase ∈
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hKtargetIndex
  have hKstored :
      ((rho.stateBefore S (strictEventIndex rho read) w).st.core.σ
        K.erase).h = blocked + 1 := by
    rw [Proofs.NamedStoreBridge.derivedView_stateBefore S rho
      (strictEventIndex rho read) w K hKtargetIndex, hKheight]
  have hmax := localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontier
    S adm hfrontier hw hprefix hKraw hKstored
  rw [hreadEq]
  exact ⟨hmax, by simpa only [hKT] using hout.1,
    by simpa only [hKT] using hout.2⟩

#print axioms PrefixFGSelectorConeAt.checkpointFiltered_at_laterRead_of_frame_named

/-- earlier's one-round SG fact makes every preceding honest action carrier
interpretable in the next round's relative phase reads. -/
theorem PrefixFGSelectorConeAt.relativeCarrierWindow_of_previousSG_of_frame_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    {r : Round} (hr : a.round ≤ r)
    (hsg : HonestSGEmissionsCompatibleAtRound S rho r T)
    (hhor : S.a (r + 1) ≤ rho.horizon)
    (hbefore : strictEventIndex rho (S.a (r + 1)) < first)
    (p : DecoupledConsensusModel.Protocol.Phase) :
    RelativeCarrierWindowAt S rho r p := by
  let core := adm.toNamedAdmissibleCore
  have hpostSource : S.E.t_GST ≤ S.a a.round :=
    ready.1.trans ((NamedOutageClosure.early_le_domain S a.round).trans
      (FrameForward.domain_le_a S a.round .g2))
  have hpost : S.E.t_GST ≤ S.a r :=
    hpostSource.trans (Assembly.a_mono S hr)
  have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) p ≤ rho.horizon :=
    (FrameForward.domain_le_a S (r + 1) p).trans hhor
  have hdomainBefore : strictEventIndex rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) p) < first :=
    (strictEventIndex_mono rho
      (FrameForward.domain_le_a S (r + 1) p)).trans_lt hbefore
  have hsourceDelay : max (S.a a.round) S.E.t_GST + S.E.Δ ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) p := by
    rw [max_eq_left hpostSource]
    apply (add_le_add (Assembly.a_mono S hr) (le_refl S.E.Δ)).trans
    apply (NamedOutageClosure.action_delta_le_early
      S S.hc.R_ge_three (Nat.lt_succ_self r)).trans
    cases p <;> simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
      DecoupledConsensusModel.Protocol.Phase.earlyOffset,
      DecoupledConsensusModel.Protocol.Phase.domainOffset] <;> linarith [S.E.Δ_pos]
  intro w hw u hu
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu).1
  obtain ⟨b, hbround, hbval, hemit⟩ :=
    NamedOutageClosure.honestRoundVoter_emits S rho hu
  obtain ⟨j, hj, _, Hb, hHb, hconfirmed⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
  have hcarrierMem : actionSGBlockAt S rho u r ∈
      (NamedRun.stateBeforeTime S rho (S.a r) u).st.core.T :=
    actionSGBlockAt_mem_storeBeforeTime S rho u r
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
      S rho (S.a r) u hcarrierMem
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    core.toNamedScheduleWellFormed.sorted (S.a r)
  have hDprefix : D ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hDbody
  have hHbSource : Hb ∈
      (NamedRun.stateBeforeTime S rho (S.a r) u).st.bodies := by
    have hstate := NamedActionSources.action_read_index S rho
      core.toNamedScheduleWellFormed j u b.round
        (by simpa only [hbround] using hj)
    change Hb ∈ (NamedRun.stateBefore S rho j u).st.bodies at hHb
    rw [← hbround, ← hstate]
    exact hHb
  have hHbPrefix : Hb ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hHbSource
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon hDprefix
  have hHbrun : RunBlock S rho Hb :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon hHbPrefix
  have hbconfirmed := NamedOutageClosure.honest_emitted_round_confirmed
    S rho core u huHon r ((Assembly.a_mono S (Nat.le_succ r)).trans hhor)
      hbround hemit
  have hroot : D.root = Hb.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase]
    exact Option.some.inj (hbconfirmed.symm.trans hconfirmed)
  have hDH : D = Hb :=
    core.toNamedRootCollisionFree.root_injective D Hb hDrun hHbrun D Hb
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self Hb)) hroot
  have hHbErase : Hb.erase = actionSGBlockAt S rho u r := by
    rw [← hDH, hDerase]
  have hHbRoot : Hb.root = (actionSGBlockAt S rho u r).root := by
    rw [← Proofs.NamedWire.erase_root Hb, hHbErase]
  have hawake : (S.node u).awake r = true := by
    simpa only [hbround] using Proofs.Optimistic.emits_attest_awake S hemit
  have hemitAction := honest_emits_exact_actionAttestationAt_of_awake
    S core.toNamedScheduleWellFormed huHon r hawake
      ((Assembly.a_mono S (Nat.le_succ r)).trans hhor)
  have hcarrierT : Block.compatible Hb.erase T = true := by
    rw [hHbErase]
    exact hsg u huHon hemitAction
  have hread := hseed.checkpointFiltered_at_laterRead_of_frame_named
    adm hfirst hframe hsourceDelay hdomainHor hdomainBefore hw
  have hFT : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) p) w).st.core.F T :=
    NamedOutageClosure.q10_filtered_F hread.2.2
  have hk : r ∈ Protocol.latest_window S.hc.η_SG (r + 1) := by
    apply NamedOutageClosure.mem_latest_window
    · simpa only [Nat.add_sub_cancel] using
        Nat.sub_le_sub_left S.hc.η_SG_ge_one (r + 1)
    · exact Nat.lt_succ_self r
  have hdeadline : max (S.a b.round) S.E.t_GST + S.E.Δ ≤
      DecoupledConsensusModel.Protocol.early S.E S.hc (r + 1) p := by
    rw [hbround, max_eq_left hpost]
    apply (NamedOutageClosure.action_delta_le_early
      S S.hc.R_ge_three (Nat.lt_succ_self r)).trans
    cases p <;> simp only [DecoupledConsensusModel.Protocol.early,
      DecoupledConsensusModel.Protocol.Phase.earlyOffset] <;> linarith [S.E.Δ_pos]
  have horder : DecoupledConsensusModel.Protocol.early S.E S.hc (r + 1) p ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) p := by
    cases p <;> simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
      DecoupledConsensusModel.Protocol.Phase.earlyOffset,
      DecoupledConsensusModel.Protocol.Phase.domainOffset] <;> linarith [S.E.Δ_pos]
  have hcut : DecoupledConsensusModel.Protocol.early S.E S.hc (r + 1) p ≤ rho.horizon :=
    horder.trans hdomainHor
  have hhead : ∃ j : Nat,
      rho.events[j]? = some (.tick u (S.a r)) ∧
      Hb ∈ (NamedActionReads.actionReadFrom S
        (NamedRun.stateBefore S rho j u) b.round).st.bodies ∧
      b.confirmed = some Hb.root := by
    exact ⟨j, by simpa only [hbround] using hj, hHb, hconfirmed⟩
  change ∃ y ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) p) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) p) w).st.core.F
      S.hc.η_SG (r + 1) (DecoupledConsensusModel.Protocol.early S.E S.hc (r + 1) p) u,
    y.round = r ∧ y.confirmed = some (actionSGBlockAt S rho u r).root ∧
      Block.find? (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) p) w).st.core.T
        (actionSGBlockAt S rho u r).root = some (actionSGBlockAt S rho u r)
  rcases (show Block.Preceq Hb.erase T ∨ Block.Preceq T Hb.erase by
    simpa only [Block.compatible, Bool.or_eq_true] using hcarrierT) with
    hHbT | hTHb
  · simpa only [hbround, hHbErase, hHbRoot] using
      (interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
        S core p hk huHon hw ⟨hbval, hbround, hemit⟩ hhead
          hHbT hFT (by simpa only [hbround] using hpost) hdeadline
            horder hcut)
  · simpa only [hbround, hHbErase, hHbRoot] using
      (interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
        S core p hk huHon hw ⟨hbval, hbround, hemit⟩ hhead
          (Block.preceq_self Hb.erase) (Block.preceq_trans hFT hTHb)
            (by simpa only [hbround] using hpost) hdeadline horder hcut)

#print axioms PrefixFGSelectorConeAt.relativeCarrierWindow_of_previousSG_of_frame_named

/-- earlier's later-round Goldfish vote step over the fully named frame. -/
theorem PrefixFGSelectorConeAt.checkpointVoteStep_of_previousSGHistory_of_frame_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hread : S.a a.round ≤ Protocol.vote_time S.E (s + 1))
    (hbefore : strictEventIndex rho (Protocol.vote_time S.E (s + 1)) < first)
    (hc : a.round + 1 ≤ S.hc.round_of (s + 1))
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq T X))
    (hsg : HonestSGEmissionsCompatibleAtRound S rho
      (S.hc.round_of (s + 1) - 1) T) :
    (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w (s + 1))) ∧
      NamedHonestVotesCone S rho (s + 1) (fun X => Block.Preceq T X) := by
  let c := S.hc.round_of (s + 1)
  let q := c - 1
  have hcPos : 1 ≤ c := (Nat.succ_le_succ (Nat.zero_le a.round)).trans hc
  have hqSucc : q + 1 = c := Nat.sub_add_cancel hcPos
  have haQ : a.round ≤ q := Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hc)
  have hpostSource : S.E.t_GST ≤ S.a a.round :=
    ready.1.trans ((NamedOutageClosure.early_le_domain S a.round).trans
      (FrameForward.domain_le_a S a.round .g2))
  have hpostQ : S.E.t_GST ≤ S.a q :=
    hpostSource.trans (Assembly.a_mono S haQ)
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  have hslo : S.hc.opening_slot c ≤ s + 1 := by
    rw [← show S.hc.round_of (s + 1) = c from rfl]
    exact Nat.div_mul_le_self (s + 1) S.hc.R
  have hdomainVote : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 ≤
      Protocol.vote_time S.E (s + 1) := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (Protocol.proposal_time_mono S.E hslo).trans
      (Protocol.proposal_time_lt_vote_time S.E (s + 1)).le
  have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 ≤ rho.horizon :=
    hdomainVote.trans hvoteHor
  have hdomainBefore : strictEventIndex rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) < first :=
    (strictEventIndex_mono rho hdomainVote).trans_lt hbefore
  have hsourceDelay : max (S.a a.round) S.E.t_GST + S.E.Δ ≤
      Protocol.vote_time S.E (s + 1) := by
    rw [max_eq_left hpostSource]
    have hearlyDomain : DecoupledConsensusModel.Protocol.early S.E S.hc c .g2 ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 := by
      simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
        DecoupledConsensusModel.Protocol.Phase.earlyOffset,
        DecoupledConsensusModel.Protocol.Phase.domainOffset]
      linarith [S.E.Δ_pos]
    exact (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
      (Nat.lt_of_succ_le hc)).trans (hearlyDomain.trans hdomainVote)
  have hreads : ∀ w ∈ rho.honest,
      (NamedRun.stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w).st.core.h_max = blocked + 1 ∧
      Block.Preceq (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho
          (Protocol.vote_time S.E (s + 1)) w).st.core.toHealing.toFG) T ∧
      T ∈ Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho
          (Protocol.vote_time S.E (s + 1)) w).st.core.toHealing.toFG := by
    intro w hw
    exact hseed.checkpointFiltered_at_laterRead_of_frame_named
      adm hfirst hframe hsourceDelay hvoteHor hbefore hw
  have hwindow : RelativeCarrierWindowAt S rho q .g1 := by
    have hphaseDelay : max (S.a a.round) S.E.t_GST + S.E.Δ ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 := by
      rw [max_eq_left hpostSource]
      exact (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
        (Nat.lt_of_succ_le hc)).trans (by
          change DecoupledConsensusModel.Protocol.early S.E S.hc c .g2 ≤
            DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1
          simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
            DecoupledConsensusModel.Protocol.Phase.earlyOffset,
            DecoupledConsensusModel.Protocol.Phase.domainOffset]
          linarith [S.E.Δ_pos])
    intro w hw u hu
    have huHon : u ∈ rho.honest :=
      ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u q).mp hu).1
    obtain ⟨b, hbround, hbval, hemit⟩ :=
      NamedOutageClosure.honestRoundVoter_emits S rho hu
    obtain ⟨j, hj, _, Hb, hHb, hconfirmed⟩ :=
      Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
    have hcarrierMem : actionSGBlockAt S rho u q ∈
        (NamedRun.stateBeforeTime S rho (S.a q) u).st.core.T :=
      actionSGBlockAt_mem_storeBeforeTime S rho u q
    obtain ⟨D, hDbody, hDerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
        S rho (S.a q) u hcarrierMem
    obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      adm.toNamedScheduleWellFormed.sorted (S.a q)
    have hDprefix : D ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
      rw [← hn]
      exact hDbody
    have hHbSource : Hb ∈
        (NamedRun.stateBeforeTime S rho (S.a q) u).st.bodies := by
      have hstate := NamedActionSources.action_read_index S rho
        adm.toNamedScheduleWellFormed j u b.round
          (by simpa only [hbround] using hj)
      change Hb ∈ (NamedRun.stateBefore S rho j u).st.bodies at hHb
      rw [← hbround, ← hstate]
      exact hHb
    have hHbPrefix : Hb ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
      rw [← hn]
      exact hHbSource
    have hDrun : RunBlock S rho D :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S huHon hDprefix
    have hHbrun : RunBlock S rho Hb :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S huHon hHbPrefix
    have hdomainG2G1 : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g2 ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 := by
      simp only [DecoupledConsensusModel.Protocol.domain,
        DecoupledConsensusModel.Protocol.Phase.domainOffset]
      linarith [S.E.Δ_pos]
    have hqHor : S.a q ≤ rho.horizon :=
      (NamedOutageClosure.action_le_domain (q := q) (r := c)
        S S.hc.R_ge_three
        (by rw [← hqSucc]; exact Nat.lt_succ_self q)).trans
          (hdomainG2G1.trans hdomainHor)
    have hbconfirmed := NamedOutageClosure.honest_emitted_round_confirmed
      S rho adm.toNamedAdmissibleCore u huHon q hqHor hbround hemit
    have hroot : D.root = Hb.root := by
      rw [← Proofs.NamedWire.erase_root D, hDerase]
      exact Option.some.inj (hbconfirmed.symm.trans hconfirmed)
    have hDH : D = Hb :=
      adm.toNamedRootCollisionFree.root_injective D Hb hDrun hHbrun D Hb
        (Or.inl (Proofs.NamedAncestry.named_self D))
        (Or.inr (Proofs.NamedAncestry.named_self Hb)) hroot
    have hHbErase : Hb.erase = actionSGBlockAt S rho u q := by
      rw [← hDH, hDerase]
    have hHbRoot : Hb.root = (actionSGBlockAt S rho u q).root := by
      rw [← Proofs.NamedWire.erase_root Hb, hHbErase]
    have hawake : (S.node u).awake q = true := by
      simpa only [hbround] using Proofs.Optimistic.emits_attest_awake S hemit
    have hemitAction := honest_emits_exact_actionAttestationAt_of_awake
      S adm.toNamedScheduleWellFormed huHon q hawake hqHor
    have hcarrierT : Block.compatible Hb.erase T = true := by
      rw [hHbErase]
      exact hsg u huHon (by simpa only [hqSucc] using hemitAction)
    have hphaseRead := hseed.checkpointFiltered_at_laterRead_of_frame_named
      adm hfirst hframe hphaseDelay hdomainHor hdomainBefore hw
    have hFT : Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1) w).st.core.F T := by
      rw [hqSucc]
      exact NamedOutageClosure.q10_filtered_F hphaseRead.2.2
    have hk : q ∈ Protocol.latest_window S.hc.η_SG (q + 1) := by
      apply NamedOutageClosure.mem_latest_window
      · simpa only [Nat.add_sub_cancel] using
          Nat.sub_le_sub_left S.hc.η_SG_ge_one (q + 1)
      · exact Nat.lt_succ_self q
    have hdeadline : max (S.a b.round) S.E.t_GST + S.E.Δ ≤
        DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 := by
      rw [hbround, max_eq_left hpostQ]
      apply (NamedOutageClosure.action_delta_le_early
        S S.hc.R_ge_three (Nat.lt_succ_self q)).trans
      simp only [DecoupledConsensusModel.Protocol.early,
        DecoupledConsensusModel.Protocol.Phase.earlyOffset]
      linarith [S.E.Δ_pos]
    have horder : DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 := by
      simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
        DecoupledConsensusModel.Protocol.Phase.earlyOffset,
        DecoupledConsensusModel.Protocol.Phase.domainOffset]
      linarith [S.E.Δ_pos]
    have hhead : ∃ j : Nat,
        rho.events[j]? = some (.tick u (S.a q)) ∧
        Hb ∈ (NamedActionReads.actionReadFrom S
          (NamedRun.stateBefore S rho j u) b.round).st.bodies ∧
        b.confirmed = some Hb.root := by
      exact ⟨j, by simpa only [hbround] using hj, hHb, hconfirmed⟩
    change ∃ y ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1) w).st.core.F
        S.hc.η_SG (q + 1) (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1) u,
      y.round = q ∧ y.confirmed = some (actionSGBlockAt S rho u q).root ∧
        Block.find? (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1) w).st.core.T
          (actionSGBlockAt S rho u q).root = some (actionSGBlockAt S rho u q)
    rcases (show Block.Preceq Hb.erase T ∨ Block.Preceq T Hb.erase by
      simpa only [Block.compatible, Bool.or_eq_true] using hcarrierT) with
      hHbT | hTHb
    · simpa only [hbround, hHbErase, hHbRoot] using
        (interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
          S adm.toNamedAdmissibleCore .g1 hk huHon hw
            ⟨hbval, hbround, hemit⟩ hhead hHbT hFT
              (by simpa only [hbround] using hpostQ) hdeadline horder
                (horder.trans (by simpa only [hqSucc] using hdomainHor)))
    · simpa only [hbround, hHbErase, hHbRoot] using
        (interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
          S adm.toNamedAdmissibleCore .g1 hk huHon hw
            ⟨hbval, hbround, hemit⟩ hhead (Block.preceq_self Hb.erase)
              (Block.preceq_trans hFT hTHb)
                (by simpa only [hbround] using hpostQ) hdeadline horder
                  (horder.trans (by simpa only [hqSucc] using hdomainHor)))
  have hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho c := by
    apply gradeFormingMajority_of_admissible_belowOneThird S adm hbelow hcPos
    have hdomainG2G1 : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g2 ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 := by
      simp only [DecoupledConsensusModel.Protocol.domain,
        DecoupledConsensusModel.Protocol.Phase.domainOffset]
      linarith [S.E.Δ_pos]
    exact hdomainG2G1.trans hdomainHor
  obtain ⟨K, _, hKT0, hKheight0, _, hKrun⟩ :=
    action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
  have hKT : K.erase = T := hKT0.trans hseed.checkpointDerived.symm
  have hKheight : (Protocol.derive_named S.E S.cfg K).h = blocked + 1 :=
    hKheight0.trans hseed.sourceDerivedHeight
  have hanchors : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) T = true := by
    intro w hw
    have hroot : Block.Preceq (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) T := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using (hreads w hw).2.1
    exact voterAnchorAt_compatible_of_previousRelativeCarrier
      S adm (by simpa only [hqSucc] using (show S.hc.round_of (s + 1) = c from rfl))
        hvoteHor hwindow (by simpa only [hqSucc] using hmajority)
          (by simpa only [hqSucc] using hsg) hw hroot
  have hheads : ∀ w ∈ rho.honest,
      Block.Preceq T (voterHeadAt S rho w (s + 1)) := by
    intro w hw
    have hmax : (voteDutyRead S rho w (s + 1)).st.core.h_max = blocked + 1 := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using (hreads w hw).1
    have hroot : Block.Preceq (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) T := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using (hreads w hw).2.1
    have hpositive : 0 < ((S.E.committee s) ∩ rho.honest).card := by
      have hcommittee := hcom s
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hpositive
    have huCommittee : u ∈ S.E.committee s := (Finset.mem_inter.mp hu).1
    have huHonest : u ∈ rho.honest := (Finset.mem_inter.mp hu).2
    obtain ⟨X, hTX, hXrun, hXemit⟩ := hvotes u huHonest huCommittee
    have hXhead : Proofs.Optimistic.HonestHead S rho s X.erase :=
      ⟨u, huHonest, huCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    have hrootDuty : Block.Preceq (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) T := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hroot
    have hprocessed := honestHead_voterProcessed_at_nextDuty_of_postHealingCone
      S adm hpost hhor hvotes hXhead hw hrootDuty
    obtain ⟨K', hK'X, hK'erase⟩ :=
      Proofs.NamedAncestry.erased_ancestor_lift X hTX
    have hK'run : RunBlock S rho K' :=
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hK'X
    have hK'eq : K' = K := by
      apply adm.toNamedRootCollisionFree.root_injective
        K' K hK'run hKrun K' K
        (Or.inl (Proofs.NamedAncestry.named_self K'))
        (Or.inr (Proofs.NamedAncestry.named_self K))
      rw [← Proofs.NamedWire.erase_root K', hK'erase, ← hKT,
        Proofs.NamedWire.erase_root]
    have hKXheight : (Protocol.derive_named S.E S.cfg K).h ≤
        (Protocol.derive_named S.E S.cfg X).h := by
      rw [← hK'eq]
      exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hK'X
    have hXmem : X.erase ∈
        (voteDutyRead S rho w (s + 1)).st.core.T := by
      have hmem := (Finset.mem_filter.mp hprocessed).1
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hmem
    have hstored := WeakJoint.storedHeight_of_runBlock_mem_voteDutyRead
      S adm hw hXrun hXmem
    have hband : (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
        ((voteDutyRead S rho w (s + 1)).st.core.σ X.erase).h := by
      rw [hKheight] at hKXheight
      rw [hstored, hmax]
      exact (Nat.sub_le (blocked + 1) 1).trans hKXheight
    have hpath := WeakJoint.namedCandidatePath_of_processedBandDescendant
      S adm hw hTX hprocessed hband hroot
    apply goldfishCone_step' S adm hcom hs hpost hhor hvotes hw
    exact { rootSide := Or.inl ⟨hroot, hpath⟩, anchor := hanchors w hw }
  refine ⟨hheads, ?_⟩
  intro w hw hcommittee
  obtain ⟨X, hXe, hXrun, hXemit⟩ :=
    named_voter_head_emits S adm hw (Nat.succ_pos s) hcommittee hvoteHor
  exact ⟨X, hXe ▸ hheads w hw, hXrun, hXemit⟩

#print axioms PrefixFGSelectorConeAt.checkpointVoteStep_of_previousSGHistory_of_frame_named

/-- The source-round active voter anchor is compatible with the exact named
FG source at any settled interior duty. -/
theorem activeVoterAnchor_compatible_actionFGSource_at_interior_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    (hactionHor : S.a r ≤ rho.horizon)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {d : Slot} (hslo : S.hc.opening_slot r ≤ d)
    (hround : S.hc.round_of d = r)
    (hnext : Protocol.vote_time S.E d ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1))
    (hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon)
    (hsettled : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 + S.E.Δ ≤
      Protocol.vote_time S.E d)
    (hactionSettled : S.a r + S.E.Δ ≤ Protocol.vote_time S.E d)
    {Q B root L : Block V}
    (hselected : PhaseGrades.nodeQ2
      S (actionReadAt S rho p r) r = some Q)
    (hsource : actionFGSource S (actionStoreAt S rho p r) = some B)
    (hframe : (DecoupledConsensusModel.Protocol.readFrame
      (voteDutyRead S rho w d).cache
      (voteDutyRead S rho w d).st.core.toHealing r).g1 = some (some root))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (filteredTree (voteDutyRead S rho w d)) root = some L) :
    Block.compatible L B = true := by
  obtain ⟨hLtreeG1, hLgrade1⟩ := fixedRoot_activeVoterAnchor_g1_data
    S adm hr hslo hround hnext hvoteHor hw hframe hactive
  have hguard := actionQ2_crossReaderBodyReadyGuard_history
    S adm hbelow hr ready hp w hw Q hselected
  have hQgrade1 := selectedG2_G1_at_read_after_cutoff
    S adm hbelow ready hactionHor hp hw hselected hguard
  change DecoupledConsensusModel.Protocol.gradeBool S.E
    (readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
    (readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
    S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1)
      (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1) L = true at hLgrade1
  change DecoupledConsensusModel.Protocol.gradeBool S.E
    (readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
    (readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
    S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1)
      (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1) Q = true at hQgrade1
  have hLQ : Block.compatible L Q = true :=
    graded_oneChain_at_reader (V := V) S.E
      (readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
      (readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
      S.hc.η_SG r
      (early := DecoupledConsensusModel.Protocol.early S.E S.hc r .g1)
      (late := DecoupledConsensusModel.Protocol.late S.E S.hc r .g1)
      (by
        simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.late,
          DecoupledConsensusModel.Protocol.Phase.earlyOffset,
          DecoupledConsensusModel.Protocol.Phase.lateOffset]
        linarith [S.E.Δ_pos]) hLgrade1 hQgrade1
  have hsourceNode := nodeFGSource_of_actionFGSource_history S rho p r hsource
  have hQB : Block.Preceq Q B :=
    preceq_actionFGSource_of_actionQ2 S rho p r hselected
      (Block.preceq_self Q) hsourceNode
  simp only [Block.compatible, Bool.or_eq_true] at hLQ
  rcases hLQ with hLQ | hQL
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl (Block.preceq_trans hLQ hQB)
  · rcases actionFGSource_genuineClear_or_selectedG2_named
        S rho p r hselected hsource with hclear | hlocal
    · obtain ⟨_, _, _, hwalk, _, _⟩ := hclear
      have hLvote : L ∈ filteredTree (voteDutyRead S rho w d) := by
        unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1
      have hpostG0 : S.E.t_GST ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 :=
        ready.1.trans (by
          simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
            DecoupledConsensusModel.Protocol.Phase.earlyOffset,
            DecoupledConsensusModel.Protocol.Phase.domainOffset]
          linarith [S.E.Δ_pos])
      have hrelay : Block.Preceq
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.core.F
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 + S.E.Δ) w).st.core.F :=
        finalized_preceq_of_evidence_delivered S adm
          (slashableBound_of_admissible_belowOneThird S adm hbelow)
          hp hw hpostG0 rfl (hsettled.trans hvoteHor)
      have hmono : Block.Preceq
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 + S.E.Δ) w).st.core.F
          (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E d) w).st.core.F := by
        rw [NamedOutageClosure.strict_read_eq_index S rho
            adm.toNamedScheduleWellFormed.sorted
              (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 + S.E.Δ),
          NamedOutageClosure.strict_read_eq_index S rho
            adm.toNamedScheduleWellFormed.sorted (Protocol.vote_time S.E d)]
        exact Proofs.NamedRuntime.stateBefore_F_mono S rho w
          (NamedOutageClosure.strict_lengths_mono rho hsettled)
      have hvoteFL : Block.Preceq
          (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E d) w).st.core.F L := by
        apply GradeDeliveryRun.finalized_preceq_of_mem_filtered_at_read S rho
        simpa only [filteredTree, voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using hLvote
      have hFActionL : Block.Preceq
          (NamedRun.stateBeforeTime S rho (S.a r) p).st.core.F L := by
        have hactionRelay : Block.Preceq
            (NamedRun.stateBeforeTime S rho (S.a r) p).st.core.F
            (NamedRun.stateBeforeTime S rho
              (S.a r + S.E.Δ) w).st.core.F :=
          finalized_preceq_of_evidence_delivered S adm
            (slashableBound_of_admissible_belowOneThird S adm hbelow)
            hp hw (ready.1.trans
              ((NamedOutageClosure.early_le_domain S r).trans
                (FrameForward.domain_le_a S r .g2))) rfl
              (hactionSettled.trans hvoteHor)
        have hactionMono : Block.Preceq
            (NamedRun.stateBeforeTime S rho
              (S.a r + S.E.Δ) w).st.core.F
            (NamedRun.stateBeforeTime S rho
              (Protocol.vote_time S.E d) w).st.core.F := by
          rw [NamedOutageClosure.strict_read_eq_index S rho
              adm.toNamedScheduleWellFormed.sorted (S.a r + S.E.Δ),
            NamedOutageClosure.strict_read_eq_index S rho
              adm.toNamedScheduleWellFormed.sorted (Protocol.vote_time S.E d)]
          exact Proofs.NamedRuntime.stateBefore_F_mono S rho w
            (NamedOutageClosure.strict_lengths_mono rho hactionSettled)
        exact Block.preceq_trans hactionRelay
          (Block.preceq_trans hactionMono hvoteFL)
      have hFg0L : Block.Preceq
          (readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.core.F L := by
        simpa only [PhaseGrades.readAt] using Block.preceq_trans hrelay
          (Block.preceq_trans hmono hvoteFL)
      obtain ⟨Ln, hLnG1, hLnErase⟩ :=
        Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w hLtreeG1
      have hLnRun : RunBlock S rho Ln := by
        obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
          adm.toNamedScheduleWellFormed.sorted
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)
        apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
        change Ln ∈ (NamedRun.stateBefore S rho n w).st.bodies
        rw [← hn]
        exact hLnG1
      have hgstG1 : S.E.t_GST ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 :=
        ready.1.trans (by
          simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
            DecoupledConsensusModel.Protocol.Phase.earlyOffset,
            DecoupledConsensusModel.Protocol.Phase.domainOffset]
          linarith [S.E.Δ_pos])
      have hdeadline : max (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)
          S.E.t_GST + S.E.Δ ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 := by
        rw [max_eq_left hgstG1]
        simp [DecoupledConsensusModel.Protocol.domain,
          DecoupledConsensusModel.Protocol.Phase.domainOffset]
      obtain ⟨hLnG0, -, -⟩ :=
        NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
          S rho adm.toNamedAdmissibleCore w hw p hp Ln
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0)
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) hLnG1
              hdeadline (le_refl _) ready.2
                (by simpa only [hLnErase] using hFg0L)
      have hdomainAction := FrameForward.domain_le_a S r .g0
      obtain ⟨hLnAction, -, -⟩ :=
        NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
          S rho adm.toNamedAdmissibleCore w hw p hp Ln
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) (S.a r) hLnG1
              hdeadline hdomainAction ready.2
                (by simpa only [hLnErase] using hFActionL)
      have hgstEarlyG1 : S.E.t_GST ≤ DecoupledConsensusModel.Protocol.early S.E S.hc r .g1 :=
        ready.1.trans (by
          simp only [DecoupledConsensusModel.Protocol.early,
            DecoupledConsensusModel.Protocol.Phase.earlyOffset]
          linarith [S.E.Δ_pos])
      have hforward : ∀ sender u key Head,
          u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
            (readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
            (readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
            S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1) sender →
          DecoupledConsensusModel.Protocol.localCovers
            (readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
            u.confirmed L = true → u.confirmed = some key →
          Block.find? (readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.T key = some Head →
          Block.Preceq (readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.core.F Head := by
        intro sender u key Head _ hcover hconf hfind
        apply Block.preceq_trans hFg0L
        unfold DecoupledConsensusModel.Protocol.localCovers at hcover
        unfold Protocol.head_covers at hcover
        simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing,
          hconf] at hcover
        rw [hfind] at hcover
        exact hcover
      have hbelowReaders :=
        g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relay
          S adm (slashableBound_of_admissible_belowOneThird S adm hbelow)
            hgstEarlyG1 ready.2 hw hp hforward
      have hbodyGuard := g1G0CrossReaderBodyReadyGuard_of_finalizedBelow
        S adm.toNamedAdmissibleCore hr hgstEarlyG1 ready.2 hw hp hbelowReaders
      have hLgrade0 := storeGrade_g0_of_storeGrade_g1_cross_reader
        S rho adm.toNamedAdmissibleCore r
          (g1G0TwoCutoffDelivery_of_core
            S adm.toNamedAdmissibleCore hgstEarlyG1)
          ready.2 w p hw hp L hLgrade1 hbodyGuard
      have hFL : Block.Preceq (actionReadAt S rho p r).st.core.F L := by
        simpa only [actionReadAt, NamedActionReads.actionReadAt,
          NamedActionReads.actionReadFrom,
          NamedActionReads.confirmationReadFrom,
          NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hFActionL
      have hLtree : L ∈ (readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.core.T := by
        have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).1.1.1
        change L ∈ (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) p).st.core.T
        rw [hcoh.1, ← hLnErase]
        exact Finset.mem_image_of_mem NamedBlock.erase hLnG0
      have hBclear : PhaseGrades.nodeClear S
          (actionReadAt S rho p r) r B = true := by
        unfold Protocol.deepest_clear at hwalk
        have htest := (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hwalk)).2.2
        simpa only [PhaseGrades.nodeClear, PhaseGrades.nodeRead,
          actionStoreAt] using htest
      exact relativeG0_compatible_clearSource_of_finalizedPreceq_history
        S adm hr hactionHor hp hLtree hLgrade0 hFL hBclear
    · subst B
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hQL

#print axioms activeVoterAnchor_compatible_actionFGSource_at_interior_named

/-- Named-frame Goldfish step once the prepared anchors are compatible with
the checkpoint. -/
theorem PrefixFGSelectorConeAt.checkpointVoteStep_of_anchors_of_frame_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hdelay : max (S.a a.round) S.E.t_GST + S.E.Δ ≤
      Protocol.vote_time S.E (s + 1))
    (hbefore : strictEventIndex rho (Protocol.vote_time S.E (s + 1)) < first)
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq T X))
    (hanchors : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) T = true) :
    (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w (s + 1))) ∧
      NamedHonestVotesCone S rho (s + 1) (fun X => Block.Preceq T X) := by
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  have hreads := fun w hw =>
    hseed.checkpointFiltered_at_laterRead_of_frame_named
      adm hfirst hframe hdelay hvoteHor hbefore (w := w) hw
  obtain ⟨K, _, hKT0, hKheight0, _, hKrun⟩ :=
    action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
  have hKT : K.erase = T := hKT0.trans hseed.checkpointDerived.symm
  have hKheight : (Protocol.derive_named S.E S.cfg K).h = blocked + 1 :=
    hKheight0.trans hseed.sourceDerivedHeight
  have hheads : ∀ w ∈ rho.honest,
      Block.Preceq T (voterHeadAt S rho w (s + 1)) := by
    intro w hw
    have hmax : (voteDutyRead S rho w (s + 1)).st.core.h_max = blocked + 1 := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using (hreads w hw).1
    have hroot : Block.Preceq (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) T := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using (hreads w hw).2.1
    have hpositive : 0 < ((S.E.committee s) ∩ rho.honest).card := by
      have hcommittee := hcom s
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hpositive
    have huCommittee : u ∈ S.E.committee s := (Finset.mem_inter.mp hu).1
    have huHonest : u ∈ rho.honest := (Finset.mem_inter.mp hu).2
    obtain ⟨X, hTX, hXrun, hXemit⟩ := hvotes u huHonest huCommittee
    have hXhead : Proofs.Optimistic.HonestHead S rho s X.erase :=
      ⟨u, huHonest, huCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    have hrootDuty : Block.Preceq (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) T := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hroot
    have hprocessed := honestHead_voterProcessed_at_nextDuty_of_postHealingCone
      S adm hpost hhor hvotes hXhead hw hrootDuty
    obtain ⟨K', hK'X, hK'erase⟩ :=
      Proofs.NamedAncestry.erased_ancestor_lift X hTX
    have hK'run : RunBlock S rho K' :=
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hK'X
    have hK'eq : K' = K := by
      apply adm.toNamedRootCollisionFree.root_injective
        K' K hK'run hKrun K' K
        (Or.inl (Proofs.NamedAncestry.named_self K'))
        (Or.inr (Proofs.NamedAncestry.named_self K))
      rw [← Proofs.NamedWire.erase_root K', hK'erase, ← hKT,
        Proofs.NamedWire.erase_root]
    have hKXheight : (Protocol.derive_named S.E S.cfg K).h ≤
        (Protocol.derive_named S.E S.cfg X).h := by
      rw [← hK'eq]
      exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hK'X
    have hXmem : X.erase ∈
        (voteDutyRead S rho w (s + 1)).st.core.T := by
      have hmem := (Finset.mem_filter.mp hprocessed).1
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hmem
    have hstored := WeakJoint.storedHeight_of_runBlock_mem_voteDutyRead
      S adm hw hXrun hXmem
    have hband : (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
        ((voteDutyRead S rho w (s + 1)).st.core.σ X.erase).h := by
      rw [hKheight] at hKXheight
      rw [hstored, hmax]
      exact (Nat.sub_le (blocked + 1) 1).trans hKXheight
    have hpath := WeakJoint.namedCandidatePath_of_processedBandDescendant
      S adm hw hTX hprocessed hband hroot
    apply goldfishCone_step' S adm hcom hs hpost hhor hvotes hw
    exact { rootSide := Or.inl ⟨hroot, hpath⟩, anchor := hanchors w hw }
  refine ⟨hheads, ?_⟩
  intro w hw hcommittee
  obtain ⟨X, hXe, hXrun, hXemit⟩ :=
    named_voter_head_emits S adm hw (Nat.succ_pos s) hcommittee hvoteHor
  exact ⟨X, hXe ▸ hheads w hw, hXrun, hXemit⟩

#print axioms PrefixFGSelectorConeAt.checkpointVoteStep_of_anchors_of_frame_named

/-- The source-round Goldfish step from the exact named source. -/
theorem PrefixFGSelectorConeAt.checkpointVoteStep_of_source_of_frame_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (_hc0 : c0 ≤ a.round)
    (ready : GradeRoundReady S rho a.round)
    (_hpostPrev : S.E.t_GST ≤ S.a (a.round - 1))
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hbefore : strictEventIndex rho (Protocol.vote_time S.E (s + 1)) < first)
    (hsround : S.hc.round_of (s + 1) = a.round)
    (hactionSettled : S.a a.round + S.E.Δ ≤
      Protocol.vote_time S.E (s + 1))
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq T X)) :
    (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w (s + 1))) ∧
      NamedHonestVotesCone S rho (s + 1) (fun X => Block.Preceq T X) := by
  have hactionHor : S.a a.round ≤ rho.horizon := hseed.actionHorizon adm
  have hpostAction : S.E.t_GST ≤ S.a a.round :=
    ready.1.trans ((NamedOutageClosure.early_le_domain S a.round).trans
      (FrameForward.domain_le_a S a.round .g2))
  have hdelay : max (S.a a.round) S.E.t_GST + S.E.Δ ≤
      Protocol.vote_time S.E (s + 1) := by
    rw [max_eq_left hpostAction]
    exact hactionSettled
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  have hreads := fun w hw =>
    hseed.checkpointFiltered_at_laterRead_of_frame_named
      adm hfirst hframe hdelay hvoteHor hbefore (w := w) hw
  obtain ⟨A, hA⟩ : ∃ A : Block V, PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some A := by
    cases hq : PhaseGrades.nodeQ2
        S (actionReadAt S rho a.val_index a.round) a.round with
    | none =>
        have hsource := nodeFGSource_of_actionFGSource_history
          S rho a.val_index a.round hseed.exactFGSource
        simp only [PhaseGrades.nodeFGSource, PhaseGrades.nodeQ2,
          PhaseGrades.nodeRead] at hsource hq
        unfold Protocol.fg_source_with Protocol.grade2_block_with at hsource
        rw [hq] at hsource
        cases hsource
    | some A => exact ⟨A, rfl⟩
  have hr : 0 < a.round := selectedQ2_round_pos_named_history S adm hA
  have hTCfg : Block.Preceq T Cfg.erase := by
    rw [hseed.checkpointDerived]
    exact Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg Cfg
  have hanchors : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) T = true := by
    intro w hw
    rcases voterAnchorAt_cases S rho w (s + 1) with
      hroot | ⟨root, L, hframeL, hactiveL, hanchorL⟩
    · rw [hroot]
      have hrootT : Block.Preceq (Protocol.get_fg_root
          (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) T := by
        simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
          Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore] using (hreads w hw).2.1
      simpa only [Block.compatible, Bool.or_eq_true] using Or.inl hrootT
    · rw [hanchorL]
      have hslo : S.hc.opening_slot a.round ≤ s + 1 := by
        rw [← hsround]
        exact Nat.div_mul_le_self (s + 1) S.hc.R
      have hshi : s + 1 < S.hc.opening_slot (a.round + 1) := by
        rw [← hsround]
        apply (Nat.div_lt_iff_lt_mul
          (Nat.zero_lt_of_lt S.hc.R_ge_two)).mp
        exact Nat.lt_succ_self ((s + 1) / S.hc.R)
      have hnext : Protocol.vote_time S.E (s + 1) ≤
          DecoupledConsensusModel.Protocol.opening S.E S.hc (a.round + 1) := by
        have hvoteNext : Protocol.vote_time S.E (s + 1) <
            Protocol.proposal_time S.E (s + 2) := by
          apply lt_trans ?_ (support_cutoff_lt_proposal_time_succ S.E (s + 1))
          rw [← Proofs.Optimistic.vote_time_add_delta]
          exact Int.lt_add_of_pos_right _ S.E.Δ_pos
        exact hvoteNext.le.trans (by
          simpa only [DecoupledConsensusModel.Protocol.opening] using
            proposal_time_mono S.E (Nat.succ_le_iff.mpr hshi))
      have hframeL' : (DecoupledConsensusModel.Protocol.readFrame
          (voteDutyRead S rho w (s + 1)).cache
          (voteDutyRead S rho w (s + 1)).st.core.toHealing a.round).g1 =
          some (some root) := by
        have hslot : (voteDutyRead S rho w (s + 1)).st.core.s = s + 1 :=
          Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
        simpa only [hslot, hsround] using hframeL
      have hsourceCompat := activeVoterAnchor_compatible_actionFGSource_at_interior_named
        S adm hbelow hr ready hactionHor hseed.signerHonest hw hslo hsround
          hnext hvoteHor
          ((add_le_add (FrameForward.domain_le_a S a.round .g0)
            (le_refl S.E.Δ)).trans hactionSettled)
          hactionSettled hA hseed.exactFGSource hframeL' hactiveL
      exact compatible_with_checkpoint_below_named_history
        hsourceCompat hTCfg
  exact hseed.checkpointVoteStep_of_anchors_of_frame_named
    adm hcom hfirst hframe hs hpost hhor hdelay hbefore hvotes hanchors

#print axioms PrefixFGSelectorConeAt.checkpointVoteStep_of_source_of_frame_named

/-- earlier's joint slot/round induction from the named source and frame. -/
theorem PrefixFGSelectorConeAt.checkpointProtection_and_SGHistory_of_source_of_frame_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : GradeRoundReady S rho a.round)
    (hpostPrev : S.E.t_GST ≤ S.a (a.round - 1))
    (hG1 : ∀ w ∈ rho.honest, ∃ Q : Block V,
      namedG1At S rho w a.round Q)
    {c : Round} (hc : a.round ≤ c) :
    (∀ d, S.hc.opening_slot c ≤ d → d < S.hc.opening_slot (c + 1) →
      (c = a.round → S.hc.opening_slot a.round + 1 ≤ d) →
      Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon →
      strictEventIndex rho (Protocol.vote_time S.E d) < first →
      (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w d)) ∧
        NamedHonestVotesCone S rho d (fun X => Block.Preceq T X)) ∧
    (S.a c ≤ rho.horizon → strictEventIndex rho (S.a c) < first →
      HonestSGEmissionsCompatibleAtRound S rho c T) := by
  have hR := S.hc.R_ge_two
  have hopenPost : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot a.round) := by
    rw [← Protocol.Γ_1_eq_vote_time]
    exact ready.1.trans ((early_g2_lt_Γ_0 S a.round).le.trans
        (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos a.round).le)
  have hsourceInterior : ∀ d,
      S.hc.opening_slot a.round + 1 ≤ d →
      d < S.hc.opening_slot (a.round + 1) →
      Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon →
      strictEventIndex rho (Protocol.vote_time S.E d) < first →
      (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w d)) ∧
        NamedHonestVotesCone S rho d (fun X => Block.Preceq T X) := by
    intro d hdlo hdhi hhor hbefore
    have hbase := hseed.checkpointProtection_firstInterior_of_frame_named
      adm hbelow hfirst hframe hc0 ready hpostPrev hG1
    have hfold : ∀ n, S.hc.opening_slot a.round + 1 ≤ n → n ≤ d →
        (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w n)) ∧
          NamedHonestVotesCone S rho n (fun X => Block.Preceq T X) := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => intro _; exact hbase
      | succ n hn ih =>
          intro hntop
          have hprev := ih (Nat.le_of_succ_le hntop)
          have htime := vote_time_mono_slots S.E hntop
          have hnHor : Protocol.confirmation_time S.E n ≤ rho.horizon := by
            rw [← vote_time_succ_add_delta_eq_confirmation_time S.E n]
            exact (add_le_add htime (le_refl S.E.Δ)).trans hhor
          have hnPost : S.E.t_GST ≤ Protocol.vote_time S.E n :=
            hopenPost.trans (vote_time_mono_slots S.E
              ((Nat.le_succ _).trans hn))
          have hnRound : S.hc.round_of (n + 1) = a.round := by
            have hlo : S.hc.opening_slot a.round ≤ n + 1 :=
              (Nat.le_succ _).trans (hn.trans (Nat.le_succ n))
            have hhi : n + 1 < S.hc.opening_slot (a.round + 1) :=
              hntop.trans_lt hdhi
            rcases eq_or_lt_of_le hlo with heq | hlt
            · rw [← heq]
              exact round_of_opening_slot_eq_schedule S.hc a.round
            · exact round_of_eq_of_opening_succ_le_of_lt_next_opening
                S.hc hlt hhi
          have hsettled : S.a a.round + S.E.Δ ≤
              Protocol.vote_time S.E (n + 1) := by
            apply action_add_delta_le_vote_of_lt S
            exact (action_lt_vote_time_two_after S a.round).trans_le
              (vote_time_mono_slots S.E (Nat.succ_le_succ hn))
          exact hseed.checkpointVoteStep_of_source_of_frame_named
            adm hcom hbelow hfirst hframe hc0 ready hpostPrev
              ((Nat.succ_pos _).trans_le hn) hnPost hnHor
                ((strictEventIndex_mono rho htime).trans_lt hbefore)
                  hnRound hsettled hprev.2
    exact hfold d hdlo (le_refl _)
  have hbaseSG := hseed.sgEmissionsCompatible_of_source_of_frame_named
    adm hcom hbelow hfirst hframe hc0 ready hpostPrev
  induction c, hc using Nat.le_induction with
  | base =>
      constructor
      · intro d _ hdhi hstart hhor hbefore
        exact hsourceInterior d (hstart rfl) hdhi hhor hbefore
      · intro _ _
        exact hbaseSG
  | succ c hc ih =>
      have hlastBounds : S.hc.opening_slot c ≤
          S.hc.opening_slot (c + 1) - 1 ∧
          S.hc.opening_slot (c + 1) - 1 < S.hc.opening_slot (c + 1) := by
        rw [opening_slot_succ_eq S.hc c]
        constructor
        · exact Nat.le_sub_one_of_lt
            (Nat.lt_add_of_pos_right (Nat.zero_lt_of_lt hR))
        · exact Nat.sub_lt
            (Nat.add_pos_right _ (Nat.zero_lt_of_lt hR)) Nat.zero_lt_one
      have hlastPos : 0 < S.hc.opening_slot (c + 1) - 1 := by
        rw [opening_slot_succ_eq S.hc c]
        apply Nat.sub_pos_iff_lt.mpr
        exact (show 1 < 2 by decide).trans_le
          (hR.trans (Nat.le_add_left S.hc.R (S.hc.opening_slot c)))
      have hsourceOpen : S.hc.opening_slot a.round ≤ S.hc.opening_slot c :=
        Nat.mul_le_mul_right S.hc.R hc
      have hnextVotes : ∀ d, S.hc.opening_slot (c + 1) ≤ d →
          d < S.hc.opening_slot (c + 1 + 1) →
          Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon →
          strictEventIndex rho (Protocol.vote_time S.E d) < first →
          (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w d)) ∧
            NamedHonestVotesCone S rho d (fun X => Block.Preceq T X) := by
        intro d hdlo hdhi hdhor hdbefore
        have hnextOpening : S.a c ≤
            Protocol.vote_time S.E (S.hc.opening_slot (c + 1)) := by
          rw [← Protocol.Γ_1_eq_vote_time]
          exact (a_le_Γ_neg1_succ S.hc S.E.Δ_pos c).trans
            ((Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (c + 1)).le.trans
              (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos (c + 1)).le)
        have hprevRead : S.a c ≤ Protocol.vote_time S.E d :=
          hnextOpening.trans (vote_time_mono_slots S.E hdlo)
        have hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon :=
          (le_add_of_nonneg_right S.E.Δ_pos.le).trans hdhor
        have hprevSG := ih.2 (hprevRead.trans hvoteHor)
          ((strictEventIndex_mono rho hprevRead).trans_lt hdbefore)
        have hlastLe : S.hc.opening_slot (c + 1) - 1 ≤ d :=
          hlastBounds.2.le.trans hdlo
        have hlastRead := vote_time_mono_slots S.E hlastLe
        have hlastCone := ih.1 _ hlastBounds.1 hlastBounds.2
          (by
            intro heq
            rw [heq, opening_slot_succ_eq S.hc a.round]
            exact Nat.le_sub_one_of_lt
              (Nat.add_lt_add_left (Nat.lt_of_succ_le hR) _))
          ((add_le_add hlastRead (le_refl S.E.Δ)).trans hdhor)
          ((strictEventIndex_mono rho hlastRead).trans_lt hdbefore)
        have hfold : ∀ n, S.hc.opening_slot (c + 1) - 1 ≤ n → n ≤ d →
            (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w n)) ∧
              NamedHonestVotesCone S rho n (fun X => Block.Preceq T X) := by
          intro n hn
          induction n, hn using Nat.le_induction with
          | base => intro _; exact hlastCone
          | succ n hn ihSlot =>
              intro hntop
              have hprev := ihSlot (Nat.le_of_succ_le hntop)
              have hnlo : S.hc.opening_slot (c + 1) ≤ n + 1 := by
                by_cases hopenZero : S.hc.opening_slot (c + 1) = 0
                · simp only [hopenZero, Nat.zero_le]
                · have hopenOne : 1 ≤ S.hc.opening_slot (c + 1) :=
                    Nat.one_le_iff_ne_zero.mpr hopenZero
                  calc
                    S.hc.opening_slot (c + 1) =
                        S.hc.opening_slot (c + 1) - 1 + 1 :=
                      (Nat.sub_add_cancel hopenOne).symm
                    _ ≤ n + 1 := Nat.add_le_add_right hn 1
              have hnhi : n + 1 < S.hc.opening_slot (c + 1 + 1) :=
                hntop.trans_lt hdhi
              have hround : S.hc.round_of (n + 1) = c + 1 := by
                rcases eq_or_lt_of_le hnlo with heq | hlt
                · rw [← heq]
                  exact round_of_opening_slot_eq_schedule S.hc (c + 1)
                · exact round_of_eq_of_opening_succ_le_of_lt_next_opening
                    S.hc hlt hnhi
              have hnRead := vote_time_mono_slots S.E hntop
              have hnHor : Protocol.confirmation_time S.E n ≤ rho.horizon := by
                rw [← vote_time_succ_add_delta_eq_confirmation_time S.E n]
                exact (add_le_add hnRead (le_refl S.E.Δ)).trans hdhor
              have hnPost : S.E.t_GST ≤ Protocol.vote_time S.E n :=
                hopenPost.trans (vote_time_mono_slots S.E
                  (hsourceOpen.trans (hlastBounds.1.trans hn)))
              have hnSourceRead : S.a a.round ≤
                  Protocol.vote_time S.E (n + 1) :=
                (Assembly.a_mono S hc).trans
                  (hnextOpening.trans (vote_time_mono_slots S.E hnlo))
              apply hseed.checkpointVoteStep_of_previousSGHistory_of_frame_named
                adm hcom hbelow hfirst hframe ready (hlastPos.trans_le hn)
                  hnPost hnHor hnSourceRead
                    ((strictEventIndex_mono rho hnRead).trans_lt hdbefore)
                      (by rw [hround]; exact Nat.add_le_add_right hc 1)
                        hprev.2
              simpa only [hround, Nat.add_sub_cancel] using hprevSG
        exact hfold d hlastLe (Nat.le_refl d)
      refine ⟨fun d hdlo hdhi _ hhor hbefore =>
        hnextVotes d hdlo hdhi hhor hbefore, ?_⟩
      intro hhor hbefore
      have hprevAction := Assembly.a_mono S (Nat.le_succ c)
      have hprevSG := ih.2 (hprevAction.trans hhor)
        ((strictEventIndex_mono rho hprevAction).trans_lt hbefore)
      have hopenHi : S.hc.opening_slot (c + 1) <
          S.hc.opening_slot (c + 1 + 1) := by
        rw [opening_slot_succ_eq S.hc (c + 1)]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_of_lt hR)
      have hopenAction : Protocol.vote_time S.E
          (S.hc.opening_slot (c + 1)) + S.E.Δ ≤ S.a (c + 1) := by
        rw [← opening_confirmation_time_eq_action S (c + 1),
          ← vote_time_succ_add_delta_eq_confirmation_time]
        exact add_le_add (vote_time_mono_slots S.E (Nat.le_succ _))
          (le_refl S.E.Δ)
      have hopenRead : Protocol.vote_time S.E
          (S.hc.opening_slot (c + 1)) ≤ S.a (c + 1) :=
        (le_add_of_nonneg_right S.E.Δ_pos.le).trans hopenAction
      have hopenCone := hnextVotes _ (Nat.le_refl _) hopenHi
        (hopenAction.trans hhor)
        ((strictEventIndex_mono rho hopenRead).trans_lt hbefore)
      exact hseed.sgEmissionsCompatible_laterRound_of_frame_named
        adm hcom hbelow hfirst hframe ready hc hprevSG hopenCone.2 hhor hbefore

#print axioms PrefixFGSelectorConeAt.checkpointProtection_and_SGHistory_of_source_of_frame_named

/-- `confirmationWitness_of_source_of_frame` over the fully named regime frame. -/
theorem PrefixFGSelectorConeAt.confirmationWitness_of_source_of_frame_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a c : NamedAttestation V} {ta tc : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : GradeRoundReady S rho a.round)
    (hpostPrev : S.E.t_GST ≤ S.a (a.round - 1))
    (hG1 : ∀ w ∈ rho.honest, ∃ Q : Block V,
      namedG1At S rho w a.round Q)
    (hc : c.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho c.val_index (Object.attest c) tc)
    (hrow : c.height_pair.erase.height? = some (blocked + 1))
    (hcr : a.round ≤ c.round)
    (hbefore : strictEventIndex rho (S.a c.round) < first) :
    fgConfirmationWitness S
      (actionStoreAt S rho c.val_index c.round) = some T := by
  rcases eq_or_lt_of_le hcr with heq | hlt
  · exact hseed.confirmationWitness_of_sameRound_honestHeightRow_of_frame_named
      adm hcom hbelow hfirst hframe ready hc hemit hrow heq
  let r := c.round - 1
  have hr : a.round ≤ r := Nat.le_sub_one_of_lt hlt
  have hsucc : r + 1 = c.round := Nat.sub_add_cancel
    ((Nat.succ_le_succ (Nat.zero_le a.round)).trans hlt)
  have htime : tc = S.a c.round := (Proofs.Optimistic.emits_attest_shape S hemit).2
  have hhor : S.a (r + 1) ≤ rho.horizon := by
    obtain ⟨k, hk, _⟩ := hemit
    have hin := (adm.in_horizon (Event.tick c.val_index tc)
      (List.mem_of_getElem? hk)).2
    simpa only [Event.time, htime, hsucc] using hin
  have hbefore' : strictEventIndex rho (S.a (r + 1)) < first := by
    simpa only [hsucc] using hbefore
  have hprev := hseed.checkpointProtection_and_SGHistory_of_source_of_frame_named
    adm hcom hbelow hfirst hframe hc0 ready hpostPrev hG1 hr
  have hcurrent := hseed.checkpointProtection_and_SGHistory_of_source_of_frame_named
    adm hcom hbelow hfirst hframe hc0 ready hpostPrev hG1
      (hr.trans (Nat.le_succ r))
  have hprevAction := Assembly.a_mono S (Nat.le_succ r)
  have hsg := hprev.2 (hprevAction.trans hhor)
    ((strictEventIndex_mono rho hprevAction).trans_lt hbefore')
  have hopenHi : S.hc.opening_slot (r + 1) <
      S.hc.opening_slot (r + 1 + 1) := by
    rw [opening_slot_succ_eq S.hc (r + 1)]
    exact Nat.lt_add_of_pos_right (by have hR := S.hc.R_ge_two; omega)
  have hopenAction : Protocol.vote_time S.E
      (S.hc.opening_slot (r + 1)) + S.E.Δ ≤ S.a (r + 1) := by
    rw [← opening_confirmation_time_eq_action S (r + 1),
      ← vote_time_succ_add_delta_eq_confirmation_time]
    exact add_le_add (vote_time_mono_slots S.E (Nat.le_succ _))
      (le_refl S.E.Δ)
  have hopenRead : Protocol.vote_time S.E
      (S.hc.opening_slot (r + 1)) ≤ S.a (r + 1) :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans hopenAction
  have hgf := (hcurrent.1 _ (Nat.le_refl _) hopenHi (by
      intro heq'
      exact False.elim ((Nat.not_succ_le_self r) (heq'.symm ▸ hr)))
    (hopenAction.trans hhor)
    ((strictEventIndex_mono rho hopenRead).trans_lt hbefore')).2
  have hpost : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot (r + 1)) := by
    rw [← Protocol.Γ_1_eq_vote_time]
    have hpostSource : S.E.t_GST ≤ S.a a.round :=
      ready.1.trans ((NamedOutageClosure.early_le_domain S a.round).trans
        (FrameForward.domain_le_a S a.round .g2))
    have hpostR : S.E.t_GST ≤ S.a r :=
      hpostSource.trans (Assembly.a_mono S hr)
    exact hpostR.trans
      ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
        ((action_add_delta_le_next_Γ_neg1 S r).trans
          ((Proofs.HealingLemmas.Γ_neg1_lt_Γ_0
            S.hc S.E.Δ_pos (r + 1)).le.trans
            (Proofs.HealingLemmas.Γ_0_lt_Γ_1
              S.hc S.E.Δ_pos (r + 1)).le)))
  have hconfHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (r + 1)) ≤ rho.horizon := by
    rwa [opening_confirmation_time_eq_action]
  obtain ⟨D, L, hU, hD, hDsource, hDheight, hL, hLentry,
      hLheight, hLD, _⟩ :=
    honestHeightRow_confirmationWitness S adm hc hemit hrow
  have hDsource' : actionFGSource S
      (actionStoreAt S rho c.val_index (r + 1)) = some D.erase := by
    simpa only [hsucc] using hDsource
  have hDnode := nodeFGSource_of_actionFGSource_history
    S rho c.val_index (r + 1) hDsource'
  obtain ⟨Q, hQ⟩ : ∃ Q, PhaseGrades.nodeQ2 S
      (actionReadAt S rho c.val_index (r + 1)) (r + 1) = some Q := by
    cases hQ : PhaseGrades.nodeQ2 S
        (actionReadAt S rho c.val_index (r + 1)) (r + 1) with
    | none =>
        have hQ' : Protocol.grade2_block_with
            (NamedProfile.gradeContract
              (actionReadAt S rho c.val_index (r + 1)).cache)
            S.E S.hc
            (actionReadAt S rho c.val_index (r + 1)).st.core.toHealing
            (r + 1) = none := by
          simpa only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
            Protocol.grade2_block_with] using hQ
        rw [PhaseGrades.nodeFGSource, Protocol.fg_source_with.eq_def,
          hQ'] at hDnode
        cases hDnode
    | some Q => exact ⟨Q, rfl⟩
  have hsourceCompat : Block.compatible D.erase T = true := by
    rcases actionFGSource_genuineClear_or_selectedG2_named
        S rho c.val_index (r + 1) hQ hDsource' with
      hclear | hselected
    · obtain ⟨B, hgenuine, -, -, -, hDB⟩ := hclear
      have hopen : 0 < S.hc.opening_slot (r + 1) :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.zero_lt_of_lt S.hc.R_ge_two)
      have hheads : ∀ x ∈ rho.honest,
          x ∈ S.E.committee (S.hc.opening_slot (r + 1)) →
          Block.Preceq T
            (voterHeadAt S rho x (S.hc.opening_slot (r + 1))) := by
        intro x hx hxc
        obtain ⟨X, hTX, hXrun, hXemit⟩ := hgf x hx hxc
        obtain ⟨H, hHerase, hHrun, hHemit⟩ :=
          WeakGoldfish.voterHead_runBlock_and_emits S
            adm.toNamedAdmissibleCore hx hopen hxc
              ((vote_time_le_confirmation_time S.E _).trans hconfHor)
        have heqVote := Proofs.Optimistic.emits_gfVote_unique S
          adm.toNamedScheduleWellFormed hXemit hHemit rfl
        have hroot : X.root = H.root := by
          simpa only [Proofs.NamedWire.erase_root] using
            congrArg GoldfishVote.head heqVote
        have hXH : X = H :=
          adm.toNamedRootCollisionFree.root_injective
            X H hXrun hHrun X H
              (Or.inl (Proofs.NamedAncestry.named_self X))
              (Or.inr (Proofs.NamedAncestry.named_self H)) hroot
        rw [← hHerase, ← hXH]
        exact hTX
      have hTB := WeakGoldfish.genuineConfirmation_compatible_of_priorProtectedHeads
        S adm.toNamedAdmissibleCore hcom hc hopen hpost hconfHor
          hgenuine hheads
      exact compatible_ancestor_left_named_history hDB
        (by simpa only [Block.compatible, Bool.or_comm] using hTB)
    · rw [hselected]
      have hgrade := selectedQ2_storeGrade_at_g2Domain S adm hQ
      have hwindow := hseed.relativeCarrierWindow_of_previousSG_of_frame_named
        adm hfirst hframe ready hr hsg hhor hbefore' .g2
      have hmajority : Internal.NamedOutageEntry.GradeFormingMajority
          S rho (r + 1) :=
        gradeFormingMajority_of_admissible_belowOneThird S adm hbelow
          (Nat.succ_pos r)
          ((FrameForward.domain_le_a S (r + 1) .g2).trans hhor)
      obtain ⟨u, hu, hQu⟩ := relativeGrade_has_roundCarrier
        S adm.toNamedAdmissibleCore hwindow hmajority hc
          (by simpa only [PhaseGrades.storeGrade,
            PhaseGrades.phaseGrade] using hgrade)
      obtain ⟨huHon, b, _, hbround, hemitB⟩ :=
        (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu
      have hawake : (S.node u).awake r = true := by
        simpa only [hbround] using Proofs.Optimistic.emits_attest_awake S hemitB
      have hemitAction := honest_emits_exact_actionAttestationAt_of_awake
        S adm.toNamedScheduleWellFormed huHon r hawake
          ((Assembly.a_mono S (Nat.le_succ r)).trans hhor)
      exact compatible_ancestor_left_named_history hQu
        (hsg u huHon hemitAction)
  obtain ⟨K, hK, hKentry, hKheight0, hKCfg, hKrun⟩ :=
    action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
  have hKheight : (Protocol.derive_named S.E S.cfg K).h =
      blocked + 1 := hKheight0.trans hseed.sourceDerivedHeight
  have hKT : K.erase = T := hKentry.trans hseed.checkpointDerived.symm
  have hKtarget : (Protocol.derive_named S.E S.cfg K).T_h =
      K.erase :=
    (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKCfg hKheight0).trans
      hKentry.symm
  have hLrun := actionBody_runBlock_named_history S adm hc hL
  have hLK : Block.compatible L.erase K.erase = true :=
    compatible_ancestor_left_named_history hLD
      (by simpa only [hKT] using hsourceCompat)
  have hnamedCompat : NamedBlock.compatible K L = true := by
    simp only [Block.compatible, Bool.or_eq_true] at hLK
    simp only [NamedBlock.compatible, Bool.or_eq_true]
    rcases hLK with hpre | hpre
    · exact Or.inr (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hLrun hKrun hpre)
    · exact Or.inl (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hKrun hLrun hpre)
  have heqWitness : T =
      (Protocol.derive_named S.E S.cfg L).T_h := by
    apply fgConfirmationWitness_eq_of_compatible_of_height_eq S
      hnamedCompat (hKheight.trans hLheight.symm)
    · exact (hKtarget.trans hKT).symm
    · rfl
  exact heqWitness ▸ hU

#print axioms PrefixFGSelectorConeAt.confirmationWitness_of_source_of_frame_named

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
