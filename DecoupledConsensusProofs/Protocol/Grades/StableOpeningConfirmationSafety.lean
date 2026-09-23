module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.ClaimOneClauseProducers
public import DecoupledConsensusProofs.Protocol.Grades.BoundedChainPrebuild
public import DecoupledConsensusProofs.Protocol.Grades.OutageEnvEmitted
public import DecoupledConsensusProofs.Execution.ViabilityHistoryIndices
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapAction
public import DecoupledConsensusProofs.Protocol.Grades.SeedRelativeGrade
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryProposalConfirmationRead

@[expose] public section

/-!
# Stable opening viability from confirmation safety

The stable raw G2 root has an honest SG supporter. The bounded healthy-prefix
confirmation fold puts that emitted SG block and every height-crossing target
on one named chain. At an opening-vote read, compare the stable root with the
target at height `h_max - 1`: the maximum carrier is the viability witness when
the target is above the stable root, and the stable root itself is the witness
when the target is below it.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

theorem history_cone_witness_at_strict_read
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (n : Nat) (C : NamedBlock V)
    (hhistory : LayerAHistoryIdx S rho n C)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    (w : V) (hw : w ∈ rho.honest) (t : Time) (i : Nat)
    (hi : NamedRun.stateBeforeTime S rho t = NamedRun.stateBefore S rho i)
    (hin : i ≤ n)
    (H : NamedBlock V)
    (hH : H ∈ (NamedRun.stateBeforeTime S rho t w).st.bodies)
    (hHC : NamedBlock.Preceq H C) :
    ∃ W ∈ (NamedRun.stateBeforeTime S rho t w).st.core.T,
      Block.Preceq H.erase W ∧
        (NamedRun.stateBeforeTime S rho t w).st.core.h_max - 1 ≤
          ((NamedRun.stateBeforeTime S rho t w).st.core.σ W).h := by
  have hHi : H ∈ (NamedRun.stateBefore S rho i w).st.bodies := by
    rw [← hi]
    exact hH
  have hco := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t w).1.1.1
  have hHT : H.erase ∈ (NamedRun.stateBeforeTime S rho t w).st.core.T := by
    rw [hco.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hH
  have hHsigma :
      (NamedRun.stateBeforeTime S rho t w).st.core.σ H.erase =
        Protocol.derive_named S.E S.cfg H :=
    hco.2.2.2.2 H hH
  obtain ⟨M, hMi, hMheight⟩ :=
    NamedMaximumCarrier.maximum_carrier_stateBefore S rho i w
  have hM : M ∈ (NamedRun.stateBeforeTime S rho t w).st.bodies := by
    rw [hi]
    exact hMi
  have hMT : M.erase ∈ (NamedRun.stateBeforeTime S rho t w).st.core.T := by
    rw [hco.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hM
  have hMsigma :
      (NamedRun.stateBeforeTime S rho t w).st.core.σ M.erase =
        Protocol.derive_named S.E S.cfg M :=
    hco.2.2.2.2 M hM
  have hMheight' :
      (Protocol.derive_named S.E S.cfg M).h =
        (NamedRun.stateBeforeTime S rho t w).st.core.h_max := by
    simpa only [hi] using hMheight
  by_cases hsmall :
      (NamedRun.stateBeforeTime S rho t w).st.core.h_max ≤ 1
  · refine ⟨H.erase, hHT, Block.preceq_self _, ?_⟩
    rw [hHsigma]
    exact (Nat.sub_eq_zero_of_le hsmall) ▸ Nat.zero_le _
  · have hlarge : 1 <
        (NamedRun.stateBeforeTime S rho t w).st.core.h_max :=
      Nat.lt_of_not_ge hsmall
    have hpos : 1 ≤
        (NamedRun.stateBeforeTime S rho t w).st.core.h_max - 1 := by
      exact Nat.le_sub_of_add_le (Nat.succ_le_iff.mpr hlarge)
    have hlt :
        (NamedRun.stateBeforeTime S rho t w).st.core.h_max - 1 <
          (Protocol.derive_named S.E S.cfg M).h := by
      rw [hMheight']
      exact Nat.sub_lt (Nat.zero_lt_of_lt hlarge) (by decide)
    obtain ⟨X, hXM, hXheight, hXC⟩ :=
      NamedOutageHistory.ViabilityHistory.held_crossing_on_history
        S rho core n C hhistory i w hw hin hbad M hMi
          ((NamedRun.stateBeforeTime S rho t w).st.core.h_max - 1) hpos hlt
    rcases NamedOutageHistory.ViabilityHistoryTime.named_common_chain hHC hXC with
      hHX | hXH
    · refine ⟨M.erase, hMT, ?_, ?_⟩
      · exact Block.preceq_trans (Proofs.NamedWire.erase_preceq hHX)
          (Proofs.NamedWire.erase_preceq hXM)
      · rw [hMsigma, hMheight']
        exact Nat.sub_le _ _
    · refine ⟨H.erase, hHT, Block.preceq_self _, ?_⟩
      rw [hHsigma, ← hXheight]
      exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hXH

theorem history_root_compatible_at_strict_read
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (n : Nat) (C : NamedBlock V)
    (hhistory : LayerAHistoryIdx S rho n C)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    (w : V) (hw : w ∈ rho.honest) (t : Time) (i : Nat)
    (hi : NamedRun.stateBeforeTime S rho t = NamedRun.stateBefore S rho i)
    (hin : i ≤ n) (H : NamedBlock V) (hHC : NamedBlock.Preceq H C) :
    Block.compatible
      (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.toFG)
      H.erase = true := by
  obtain ⟨J, hJrun, hJi, hJe, hJC⟩ :=
    NamedOutageHistory.HistoryProofs.justification_on_history_chain
      S rho core n C hhistory i w hw hin hbad
  have hJ : J ∈ (NamedRun.stateBeforeTime S rho t w).st.bodies := by
    rw [hi]
    exact hJi
  obtain ⟨F, hFrun, hFi, hFe, hFC⟩ := hhistory.2.2.2 i w hw hin
  have hF : F ∈ (NamedRun.stateBeforeTime S rho t w).st.bodies := by
    rw [hi]
    exact hFi
  have hiw := congrFun hi w
  have hJe' : J.erase =
      (NamedRun.stateBeforeTime S rho t w).st.core.J := by
    rw [hiw]
    exact hJe
  have hFe' : F.erase =
      (NamedRun.stateBeforeTime S rho t w).st.core.F := by
    rw [hiw]
    exact hFe
  have hJcompat : Block.compatible J.erase H.erase = true :=
    Block.compatible_of_preceq_common
      (Proofs.NamedWire.erase_preceq hJC) (Proofs.NamedWire.erase_preceq hHC)
  have hFcompat : Block.compatible F.erase H.erase = true :=
    Block.compatible_of_preceq_common
      (Proofs.NamedWire.erase_preceq hFC) (Proofs.NamedWire.erase_preceq hHC)
  change Block.compatible
    (if (NamedRun.stateBeforeTime S rho t w).st.core.h_max =
        (NamedRun.stateBeforeTime S rho t w).st.core.h_j + 1 then
      (NamedRun.stateBeforeTime S rho t w).st.core.J
    else (NamedRun.stateBeforeTime S rho t w).st.core.F) H.erase = true
  split
  · simpa only [hJe'] using hJcompat
  · simpa only [hFe'] using hFcompat

private theorem stable_raw_preceq_confirmation_history
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (s : Round) (hs : 0 < s) (hmargin : FormationMargin S s b0)
    (v : V) (hv : v ∈ rho.honest) (raw : Block V)
    (hgrade : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc s .g2) v).st s .g2 raw = true)
    (C : NamedBlock V)
    (hhistory : LayerAJointHistoryIdxEmitted S rho (boundaryIdx rho b0) C) :
    ∀ H : NamedBlock V, NamedRun.blockInRun S rho H → H.erase = raw →
      NamedBlock.Preceq H C := by
  have hcapHor : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have hasCap : S.a s ≤ b0 :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hdomainCap : domain S.E S.hc s .g2 ≤ b0 :=
    (FrameForward.domain_le_a S s .g2).trans hasCap
  have hcovered : RoundCovered S rho s :=
    Or.inr ⟨.g2, NamedOutageHistory.OutageEnv.domain_g2_nonneg S hs,
      hdomainCap.trans hcapHor⟩
  have hawake : AwakeWindowMajority S.E (fun u => (S.node u).awake)
      rho.honest S.hc.η_SG s :=
    hsleep s hs hcovered
  have hroundOne : domain S.E S.hc 1 .g2 ≤ b0 := by
    exact (FrameForward.domain_le_a S 1 .g2).trans
      ((Assembly.a_mono S (Nat.succ_le_succ (Nat.zero_le s))).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
  have hT1 := protectedVoteSlots_before
    S rho b0 b1 hexec hcom hsleep hroundOne
  obtain ⟨x, hx⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  let d := S.hc.opening_slot s + 1
  have hd : 1 ≤ d := by
    dsimp only [d]
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hdCap : Protocol.vote_time S.E d + S.E.Δ ≤ b0 := by
    dsimp only [d]
    rw [Protocol.vote_time_succ_add_delta_eq_confirmation_time,
      ← Protocol.a_eq_confirmation_time S.hc S.E s]
    exact hasCap
  have hsNext : S.a s < Protocol.vote_time S.E (d + 1) := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact Proofs.HealingSurface.confirmationTime_lt_nextVote_of_lt S.E
      (show S.hc.opening_slot s < d by
        dsimp only [d]
        exact Nat.lt_succ_self _)
  have hsources := actionSources_preceq_voteDutyHead_before_of_T1
    S rho b0 b1 hexec hcom hsleep hroundOne hT1 hd hdCap hx
  have htransport :=
    Proofs.HealingSurface.WeakJoint.relativeCarrierWindowAt_of_awakeWindowHistory_of_delivery
      S hexec.core hexec.healthy hcapHor (base := 0) (r := s)
      (D := Protocol.voteDutyHead S rho x d) hs (Nat.zero_le _) hawake
      (by
        intro k hkbase hklt u hu hemit
        exact (hsources k ((action_strictMono S) hklt |>.trans hsNext)).1
          u hu hemit)
      (by
        intro w hw
        exact ((hsources s hsNext).2 w hw).1)
      .g2 hdomainCap
  have hcarrierAt := Proofs.HealingSurface.relativeGradeCarrierAt_of_awakeWindowMajority
    S hexec.core hs hawake htransport
  obtain ⟨k, hk, u, hu, hemit, hrawCarrier⟩ :=
    hcarrierAt v hv raw (by
      simpa only [storeGrade, phaseGrade, PhaseGrades.readAt] using hgrade)
  obtain ⟨i, hi, himem⟩ := hemit
  have hks : k < s := Proofs.HealingSurface.mem_latestWindow_lt hk
  have hasb0 : S.a s < b0 :=
    (NamedOutageHistory.JointHistoryGapsTime.setup_a_strictMono S
      (Nat.lt_succ_self s)).trans_le
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hkCap : S.a k < b0 := ((action_strictMono S) hks).trans hasb0
  have hibound : i < boundaryIdx rho b0 :=
    tick_index_lt_boundaryIdx rho hexec.core.sorted hi
      (by simpa only [NamedEvent.time] using hkCap)
  let a := actionAttestationAt S rho u k
  have hconfirmed : a.confirmed = some (actionSGBlockAt S rho u k).root := by
    exact (actionAttestationAt_shape S rho u k).2.2
  obtain ⟨K, hKrun, hKbody, hKroot, hKC⟩ :=
    hhistory.1.2.1 i u (S.a k) a hu hi himem hibound
      (actionSGBlockAt S rho u k).root hconfirmed
  have hcarrierMem : actionSGBlockAt S rho u k ∈
      (NamedRun.stateBeforeTime S rho (S.a k) u).st.core.T :=
    actionSGBlockAt_mem_storeBeforeTime S rho u k
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a k) u hcarrierMem
  obtain ⟨m, hm, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
    S rho hexec.core.sorted (S.a k)
  have hDprefix : D ∈ (NamedRun.stateBefore S rho m u).st.bodies := by
    rw [← hm]
    exact hDbody
  have hDrun : NamedRun.blockInRun S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu hDprefix
  have hDKroot : D.root = K.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase]
    exact hKroot.symm
  have hDK : D = K :=
    hexec.core.toNamedRootCollisionFree.root_injective D K hDrun hKrun D K
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (NamedOutageHistory.JointHistoryProducersTime.named_preceq_self K))
      hDKroot
  have hKe : K.erase = actionSGBlockAt S rho u k := by
    rw [← hDK, hDerase]
  intro H hHrun hHerase
  have hHKraw : Block.Preceq H.erase K.erase := by
    rw [hHerase, hKe]
    exact hrawCarrier
  have hHK : NamedBlock.Preceq H K :=
    NamedOutageHistory.JointHistoryProducersTime.named_of_erase_preceq
      S rho hexec.core hHrun hKrun hHKraw
  exact NamedOutageHistory.IdxDriverHelpers.named_preceq_trans hHK hKC

omit [DecidableEq V] [Fintype V] in
theorem strict_length_le_boundary
    (rho : NamedRun V) {t cap : Time} (ht : t ≤ cap) :
    (rho.events.filter (fun e => decide (e.time < t))).length ≤
      boundaryIdx rho cap := by
  have hsub := List.Sublist.filter (fun e : NamedEvent V => decide (e.time ≤ cap))
    (List.filter_sublist
      (p := fun e : NamedEvent V => decide (e.time < t)) (l := rho.events))
  have hs : (rho.events.filter (fun e => decide (e.time < t))).filter
      (fun e => decide (e.time ≤ cap)) =
        rho.events.filter (fun e => decide (e.time < t)) := by
    apply List.filter_eq_self.mpr
    intro e he
    simp only [decide_eq_true_eq]
    have het : e.time < t := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp he).2
    exact het.le.trans ht
  rw [hs] at hsub
  exact hsub.length_le

set_option maxHeartbeats 400000 in
/-- The stable raw G2 root has a processed descendant at the opening vote
read whose height reaches the local viability frontier. -/
theorem stableAt_rawG2_viableDescendant_at_openingVote
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hstable : stableAt S rho v s P) (hs : 0 < s) :
    ∃ G raw : Block V, Block.Preceq P G ∧ Block.Preceq G raw ∧
      (∀ w ∈ rho.honest, storeGrade S.E S.hc
        (readAt S rho (domain S.E S.hc s .g1) w).st s .g1 raw = true) ∧
        ∀ w ∈ rho.honest,
          Block.compatible
              (Protocol.get_fg_root
                (Internal.NamedRecoveryRead.voteDutyRead S rho w
                  (S.hc.opening_slot s)).st.core.toHealing.toFG) raw = true ∧
            ∃ W ∈ (Internal.NamedRecoveryRead.voteDutyRead S rho w
                (S.hc.opening_slot s)).st.core.T,
              Block.Preceq raw W ∧
                (Internal.NamedRecoveryRead.voteDutyRead S rho w
                  (S.hc.opening_slot s)).st.core.h_max - 1 ≤
                  ((Internal.NamedRecoveryRead.voteDutyRead S rho w
                    (S.hc.opening_slot s)).st.core.σ W).h := by
  have hcap : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have has : S.a s ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans (hmargin.trans hcap))
  obtain ⟨G, raw, hG, hgrade, hPG, hGraw⟩ :=
    stableAt_rawG2_grade S rho v s P hexec.core hv hs has hstable
  have hroundOne : domain S.E S.hc 1 .g2 ≤ b0 := by
    exact (FrameForward.domain_le_a S 1 .g2).trans
      ((Assembly.a_mono S (Nat.succ_le_succ (Nat.zero_le s))).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
  have hT1 := protectedVoteSlots_before
    S rho b0 b1 hexec hcom hsleep hroundOne
  have hconf := namedConfirmationIdxQueryEmitted_of_healthyPrefix_of_T1
    S rho b0 b1 hexec hcom hsleep hroundOne hT1
  obtain ⟨C, hhistory⟩ :=
    NamedOutageHistory.OutageEnv.layerA_joint_history_idx_emitted_of_outage
      S rho b0 b1 s hexec hsleep hmargin hcom hconf
        (boundaryIdx rho b0) (le_refl _)
  have hrawHistory := stable_raw_preceq_confirmation_history
    S rho b0 b1 hexec hcom hsleep s hs hmargin v hv raw hgrade C hhistory
  have hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q :=
    Proofs.NamedOutageInputs.boundary_faulty_lt_quorum S rho b0 b1 s
      hexec hmargin hsleep
  have hdomainCap : domain S.E S.hc s .g0 ≤ b0 :=
    (FrameForward.domain_le_a S s .g0).trans
      ((Assembly.a_mono S (Nat.le_succ s)).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
  have hdomainHor : domain S.E S.hc s .g0 ≤ rho.horizon :=
    hdomainCap.trans hcap
  have hdelivery : TwoCutoffDelivery S rho s :=
    twoCutoffDelivery_of_healthyPrefix S rho b0 hexec.healthy hdomainCap
  have hG1 : ∀ w ∈ rho.honest, storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc s .g1) w).st s .g1 raw = true := by
    intro w hw
    apply storeGrade_g1_of_storeGrade_g2_cross_reader
      S rho hexec.core s hdelivery hdomainHor v w hv hw raw hgrade
    exact claimOne_guard_at_stableRound S rho b0 b1 hexec hslash hs hmargin
      hv hw hG hGraw
  refine ⟨G, raw, hPG, hGraw, hG1, ?_⟩
  intro w hw
  have hfinalized := stableAt_finalized_below_raw_at_reader
    S rho b0 b1 hexec hslash hs hmargin hv hw hG hGraw
  have hG1named : namedG1At S rho w s raw := by
    simpa only [namedG1At] using hG1 w hw
  have hrawT : raw ∈
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc s .g1) w).st.core.T :=
    namedG1At_mem_domainTree S rho hG1named
  obtain ⟨H, hHbody, hHraw⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (domain S.E S.hc s .g1) w hrawT
  have hdeadline : domain S.E S.hc s .g1 + S.E.Δ ≤
      Protocol.vote_time S.E (S.hc.opening_slot s) := by
    rw [domain_g1_eq_opening]
    rfl
  have hvoteCap : Protocol.vote_time S.E (S.hc.opening_slot s) ≤ b0 := by
    exact (Protocol.vote_time_le_confirmation_time S.E _).trans
      ((by rw [← Protocol.a_eq_confirmation_time]
           exact (Assembly.a_mono S (Nat.le_succ s)).trans
             ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)) :
        Protocol.confirmation_time S.E (S.hc.opening_slot s) ≤ b0)
  have hheld := (NamedHealthyHeadReady.healthy_head_body_at_read
    S rho hexec.core b0 hexec.healthy w hw w hw H
      (domain S.E S.hc s .g1)
      (Protocol.vote_time S.E (S.hc.opening_slot s))
      (Protocol.vote_time S.E (S.hc.opening_slot s))
      hHbody hdeadline (le_refl _) hvoteCap (by
        rw [hHraw]
        exact hfinalized.2)).1
  have hHrun : NamedRun.blockInRun S rho H := by
    obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
      S rho hexec.core.sorted (Protocol.vote_time S.E (S.hc.opening_slot s))
    have hHi : H ∈ (NamedRun.stateBefore S rho i w).st.bodies := by
      have hiw := congrFun hi w
      rw [← hiw]
      exact hheld
    exact Proofs.NamedRuntime.blockInRun_of_direct S rho (Or.inr ⟨w, hw, i, hHi⟩)
  have hHC : NamedBlock.Preceq H C := hrawHistory H hHrun hHraw
  let t := Protocol.vote_time S.E (S.hc.opening_slot s)
  let i := (rho.events.filter (fun e => decide (e.time < t))).length
  have hi : NamedRun.stateBeforeTime S rho t = NamedRun.stateBefore S rho i := by
    exact strict_read_eq_index S rho hexec.core.sorted t
  have hin : i ≤ boundaryIdx rho b0 := by
    exact strict_length_le_boundary rho hvoteCap
  have hwit := history_cone_witness_at_strict_read
    S rho hexec.core (boundaryIdx rho b0) C hhistory.1.1 hbad
      w hw t i hi hin H hheld hHC
  have hrootCompat := history_root_compatible_at_strict_read
    S rho hexec.core (boundaryIdx rho b0) C hhistory.1.1 hbad
      w hw t i hi hin H hHC
  rw [hHraw] at hwit
  rw [hHraw] at hrootCompat
  constructor
  · simpa only [t, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hrootCompat
  · simpa only [t, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hwit

#print axioms stableAt_rawG2_viableDescendant_at_openingVote







end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
