module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PreparedV4FGRootHeadCore
public import DecoupledConsensusProofs.Protocol.Grades.WeakConfirmationReadAnchorsNamed
public import DecoupledConsensusProofs.Protocol.Grades.RoundVoterTransportTwoCutoffAfter

@[expose] public section

/-! # Prepared V4 confirmation anchors -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic Statements
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem actionTime_lt_nextVote_of_lt_confirmation_v4_anchor
    (S : Setup V) {r : Round} {s : Slot}
    (h : S.a r < Protocol.confirmation_time S.E s) :
    S.a r < Protocol.vote_time S.E (s + 1) := by
  exact (action_time_lt_proposal_of_lt_previous_confirmation
    S (s := s + 1) (Nat.zero_lt_succ s)
      (by simpa only [Nat.add_sub_cancel] using h)).trans
        (proposal_time_lt_vote_time S.E (s + 1))

private theorem preparedFGRoot_preceq_voterHeadAt_same_v4
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    {s : Slot} (hs : start ≤ s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq
      (Protocol.get_fg_root
        (NamedRecoveryRead.confirmationInputRead S rho w s).st.core.toHealing.toFG)
      (voterHeadAt S rho x s) := by
  have hcutpos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hmajority := honestWeightMajority_of_finiteWindowsFrom
    S hawake hcutpos (hboot.settled.trans hs) (Nat.le_succ s) hhor
  have hread : min (S.a (base + S.hc.η_SG))
      (Protocol.vote_time S.E start) ≤ Protocol.confirmation_time S.E s :=
    (min_le_right _ _).trans ((vote_time_mono_slots S.E hs).trans
      (vote_time_le_confirmation_time S.E s))
  have hslot := SettledBootstrapPreparedV4.protectedVoteSlots_core
    S adm hcom hboot hawake hfinality hhor s hs (Nat.le_succ s)
  change Block.Preceq
    (Protocol.get_fg_root
      (rho.storeBeforeTime S w
        (Protocol.confirmation_time S.E s)).toHealing.toFG)
    (voteDutyHead S rho x s)
  rcases WeakFG.fgRoot_confirmationWitness_at_read
      S adm hmajority hw (Protocol.confirmation_time S.E s) with
    hgen | ⟨C, hC, hJ, a, ta, ha, hemit, ht, hpair, hT⟩
  · rw [hgen]
    exact Protocol.preceq_genesis _
  · have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
    by_cases hold : a.round < base + S.hc.η_SG
    · have holdRoot := WeakJoint.oldFGRoot_preceq_of_finiteBootstrap_at_read
        S adm hboot.oldRows hfinality hboot.frontierSeed hboot.fgAll hw
        hread hC hJ ha hemit hold hpair hT
      exact Block.preceq_trans holdRoot (hslot.1.heads x hx)
    · have haTime : S.a a.round < Protocol.vote_time S.E (s + 1) := by
        exact actionTime_lt_nextVote_of_lt_confirmation_v4_anchor S (by
          rw [← htime]
          exact ht)
      exact ((SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hhor hs (Nat.le_succ s) hx
          a.round (Nat.le_of_not_gt hold) haTime).2 a.val_index ha).2 _ hT

private theorem preparedG1Raw_preceq_voterHeadAt_same_v4
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    {s : Slot} (hs : start ≤ s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest)
    {r : Round}
    (hround : S.hc.round_of
      (S.E.slotOf (Protocol.confirmation_time S.E s)) = r)
    {raw : Block V}
    (hframe : (DecoupledConsensusModel.Protocol.readFrame
      (NamedRecoveryRead.confirmationInputRead S rho w s).cache
      (NamedRecoveryRead.confirmationInputRead S rho w s).st.core.toHealing r).g1 =
        some (some raw)) :
    Block.Preceq raw (voterHeadAt S rho x s) := by
  let t := Protocol.confirmation_time S.E s
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hcutpos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hroundCut : base + S.hc.η_SG ≤ r := by
    rw [← hround]
    change base + S.hc.η_SG ≤
      (S.E.slotOf (Protocol.confirmation_time S.E s)) / S.hc.R
    rw [slotOf_confirmation_time]
    exact (Nat.le_div_iff_mul_le hRpos).2
      ((hboot.settled.trans hs).trans (Nat.le_succ s))
  have hr : 0 < r := hcutpos.trans_le hroundCut
  have hspan : base ≤ r - S.hc.η_SG := Nat.le_sub_of_add_le hroundCut
  have hbasePred : base ≤ r - 1 :=
    hspan.trans (Nat.sub_le_sub_left S.hc.η_SG_ge_one r)
  have hroundT : S.hc.round_of (S.E.slotOf t) = r := by
    simpa only [t] using hround
  have ht0 : (0 : Time) ≤ t := confirmation_time_nonneg S.E s
  have hcut : t = Protocol.support_cutoff S.E (S.E.slotOf t) := by
    dsimp only [t]
    rw [slotOf_confirmation_time]
    exact Protocol.confirmation_time_eq_support_cutoff_succ S.E s
  have hopen : opening S.E S.hc r < t := by
    simpa only [NamedOutageClosure.clockRoundAt, hroundT] using
      NamedOutageClosure.opening_lt_support_cutoff S t ht0 hcut
  have hdomain : domain S.E S.hc r .g1 < t := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact hopen
  have htop : t ≤ opening S.E S.hc (r + 1) := by
    simpa only [NamedOutageClosure.clockRoundAt, hroundT] using
      (NamedOutageClosure.clockRound_lt_opening_succ S t).le
  have hdomainHor : domain S.E S.hc r .g1 ≤ rho.horizon :=
    hdomain.le.trans (by simpa only [t] using hhor)
  have hgrade := WeakSG.phaseGrade_of_preparedFrame_g1
    S rho adm w hw r hr t hroundT hdomain htop hdomainHor (by
      simpa only [NamedRecoveryRead.confirmationInputRead,
        NamedActionReads.confirmationReadAt, t] using hframe)
  have hpostEarly : S.E.t_GST ≤ early S.E S.hc r .g2 := by
    exact hboot.basePost.trans (Assembly.a_mono S hbasePred) |>.trans
      (le_add_of_nonneg_right S.E.Δ_pos.le) |>.trans
        (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
          (Nat.sub_lt hr (by decide)))
  have hdelivery : TwoCutoffDelivery S rho r :=
    twoCutoffDelivery_of_core S adm hpostEarly
  have hfg := preparedFGRoot_preceq_voterHeadAt_same_v4
    S adm hcom hboot hawake hfinality hs hhor hw hx
  have hslot := SettledBootstrapPreparedV4.protectedVoteSlots_core
    S adm hcom hboot hawake hfinality hhor s hs (Nat.le_succ s)
  have hFmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.F
      (NamedRun.stateBeforeTime S rho t w).st.core.F :=
    NamedOutageClosure.incl_strict_F_mono S rho
      adm.toNamedScheduleWellFormed w hdomain.le
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho t w
  have hFroot : Block.Preceq
      (NamedRun.stateBeforeTime S rho t w).st.core.F
      (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F (st :=
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.toFG) hFJ
  have hFhead : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.F
      (voteDutyHead S rho x s) := by
    exact Block.preceq_trans hFmono (Block.preceq_trans hFroot (by
      simpa only [NamedRecoveryRead.confirmationInputRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        t] using hfg))
  have hprevHor : S.a (r - 1) ≤ rho.horizon := by
    have hprev : S.a (r - 1) + S.E.Δ ≤ early S.E S.hc r .g1 :=
      (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
        (Nat.sub_lt hr (by decide))).trans
        (NamedOutageClosure.q10_early_g2_le_early_g1 S r)
    exact (le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (hprev.trans ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
        S r).trans hdomainHor))
  have hcarrier := relativeGradeCarrierAt_of_awakeWindowMajority
    S adm hr (hawake r hroundCut hprevHor) (p := .g1) (by
      intro y hy u hu k hk huk
      have hklt : k < r := mem_latestWindow_lt hk
      have hbaseK : base ≤ k :=
        hspan.trans (WeakSG.mem_latestWindow_lower_bound hk)
      have hdeadline : S.a k + S.E.Δ ≤ early S.E S.hc r .g1 :=
        (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt).trans
          (NamedOutageClosure.q10_early_g2_le_early_g1 S r)
      have hactionConf : S.a k < t :=
        (lt_of_lt_of_le (Int.lt_add_of_pos_right _ S.E.Δ_pos) hdeadline).trans
          ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1 S r).trans_lt
            hdomain)
      have hactionTime : S.a k < Protocol.vote_time S.E (s + 1) :=
        actionTime_lt_nextVote_of_lt_confirmation_v4_anchor S
          (by simpa only [t] using hactionConf)
      have hem := honest_emits_exact_actionAttestationAt_of_awake S
        adm.toNamedScheduleWellFormed hu k huk (by
          exact (le_add_of_nonneg_right S.E.Δ_pos.le).trans
            (hdeadline.trans
              ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                S r).trans hdomainHor)))
      have hAhead : Block.Preceq (actionSGBlockAt S rho u k)
          (voterHeadAt S rho x s) := by
        by_cases hold : k < base + S.hc.η_SG
        · exact Block.preceq_trans (hboot.sgBoot k hbaseK hold u hu hem)
            (hslot.1.heads x hx)
        · exact (SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
            S adm hcom hboot hawake hfinality hhor hs (Nat.le_succ s) hx
              k (Nat.le_of_not_gt hold) hactionTime).1 u hu hem
      have hfgY := preparedFGRoot_preceq_voterHeadAt_same_v4
        S adm hcom hboot hawake hfinality hs hhor hy hx
      have hFmonoY : Block.Preceq
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) y).st.core.F
          (NamedRun.stateBeforeTime S rho t y).st.core.F :=
        NamedOutageClosure.incl_strict_F_mono S rho
          adm.toNamedScheduleWellFormed y hdomain.le
      have hFJY := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho t y
      have hFrootY : Block.Preceq
          (NamedRun.stateBeforeTime S rho t y).st.core.F
          (Protocol.get_fg_root
            (NamedRun.stateBeforeTime S rho t y).st.core.toHealing.toFG) :=
        Proofs.Records.preceq_get_fg_root_of_F (st :=
          (NamedRun.stateBeforeTime S rho t y).st.core.toHealing.toFG) hFJY
      have hFheadY : Block.Preceq
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) y).st.core.F
          (voteDutyHead S rho x s) := by
        exact Block.preceq_trans hFmonoY (Block.preceq_trans hFrootY (by
          simpa only [NamedRecoveryRead.confirmationInputRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
            t] using hfgY))
      exact NamedOutageClosure.honestRoundVote_interpreted_at_reader_of_twoCutoff_compatible_after
        S rho adm hboot.basePost hdelivery r k hbaseK .g1 hk y hy hdomainHor hdeadline
          ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u k).mpr
            ⟨hu, actionAttestationAt S rho u k,
              (actionAttestationAt_shape S rho u k).1,
              (actionAttestationAt_shape S rho u k).2.1, hem⟩)
          (Block.compatible_of_preceq_common hFheadY hAhead))
  obtain ⟨k, hk, u, hu, hemit, hraw⟩ := hcarrier w hw raw (by
    simpa only [PhaseGrades.phaseGrade] using hgrade)
  have hklt : k < r := mem_latestWindow_lt hk
  have hbaseK : base ≤ k :=
    hspan.trans (WeakSG.mem_latestWindow_lower_bound hk)
  have hactionConf : S.a k < t := by
    have hdeadline := NamedOutageClosure.action_delta_le_early
      S S.hc.R_ge_three hklt
    calc
      S.a k < S.a k + S.E.Δ := Int.lt_add_of_pos_right _ S.E.Δ_pos
      _ ≤ early S.E S.hc r .g2 := hdeadline
      _ ≤ early S.E S.hc r .g1 :=
        NamedOutageClosure.q10_early_g2_le_early_g1 S r
      _ ≤ domain S.E S.hc r .g1 :=
        NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1 S r
      _ < t := hdomain
  have hactionTime : S.a k < Protocol.vote_time S.E (s + 1) :=
    actionTime_lt_nextVote_of_lt_confirmation_v4_anchor S
      (by simpa only [t] using hactionConf)
  by_cases hold : k < base + S.hc.η_SG
  · exact Block.preceq_trans hraw
      (Block.preceq_trans (hboot.sgBoot k hbaseK hold u hu hemit)
        (hslot.1.heads x hx))
  · exact Block.preceq_trans hraw
      ((SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hhor hs (Nat.le_succ s) hx
          k (Nat.le_of_not_gt hold) hactionTime).1 u hu hemit)

/-- Every prepared confirmation anchor is below every honest voter head of the
same post-cut slot. -/
theorem SettledBootstrapPreparedV4.preparedConfirmationAnchor_preceq_voterHeadAt_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    {s : Slot} (hs : start ≤ s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq
      (namedConfirmationAnchor S
        (Internal.NamedRecoveryRead.confirmationInputRead S rho w s))
      (voterHeadAt S rho x s) := by
  rcases confirmationAnchorAt_cases S rho w s with
    hfg | ⟨raw, A, hframe, hactive, hA⟩
  · rw [show namedConfirmationAnchor S
        (Internal.NamedRecoveryRead.confirmationInputRead S rho w s) =
        confirmationAnchorAt S rho w s by rfl, hfg]
    exact preparedFGRoot_preceq_voterHeadAt_same_v4
      S adm hcom hboot hawake hfinality hs hhor hw hx
  · rw [show namedConfirmationAnchor S
        (Internal.NamedRecoveryRead.confirmationInputRead S rho w s) =
        confirmationAnchorAt S rho w s by rfl, hA]
    have hAraw : Block.Preceq A raw := by
      unfold activePrefix at hactive
      exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
    exact Block.preceq_trans hAraw
      (preparedG1Raw_preceq_voterHeadAt_same_v4
        S adm hcom hboot hawake hfinality hs hhor hw hx (r :=
          S.hc.round_of (S.E.slotOf (Protocol.confirmation_time S.E s)))
          rfl hframe)

#print axioms SettledBootstrapPreparedV4.preparedConfirmationAnchor_preceq_voterHeadAt_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
