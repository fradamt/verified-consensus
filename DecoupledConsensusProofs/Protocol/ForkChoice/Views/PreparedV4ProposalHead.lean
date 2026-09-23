module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.PreparedV4ConfirmationAnchor
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakProposalHeadNamed

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Prepared V4 proposal parents -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic Statements Proofs.HealingLemmas
open Internal.NamedRecoveryRead Internal.PhaseGrades
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem preparedV4_voteTime_lt_nextProposal
    (E : Env V) (s : Slot) :
    Protocol.vote_time E s < Protocol.proposal_time E (s + 1) := by
  apply lt_trans ?_ (support_cutoff_lt_proposal_time_succ E s)
  rw [← vote_time_add_delta]
  exact Int.lt_add_of_pos_right _ E.Δ_pos

/-- A proposal read's FG root is below every protected head at the previous
vote duty. -/
theorem SettledBootstrapPreparedV4.fgRootAtRead_preceq_voteDutyHead_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start last d : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : start ≤ d) (hupper : d ≤ last + 1)
    {t : Time}
    (hread : min (S.a (base + S.hc.η_SG))
      (Protocol.vote_time S.E start) ≤ t)
    (ht : t ≤ Protocol.vote_time S.E (d + 1))
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w t).core.toHealing.toFG)
      (voterHeadAt S rho x d) := by
  have hcutPos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hmajority : HonestWeightMajority S rho.honest :=
    honestWeightMajority_of_finiteWindowsFrom
      S hawake hcutPos (hboot.settled.trans hd) hupper hhor
  have hslot := SettledBootstrapPreparedV4.protectedVoteSlots_core
    S adm hcom hboot hawake hfinality hhor d hd hupper
  rcases WeakFG.fgRoot_confirmationWitness_at_read S adm hmajority hw t with
    hgen | ⟨C, hC, hJ, a, ta, ha, hemit, hat, hpair, hT⟩
  · rw [hgen]
    exact Protocol.preceq_genesis _
  · have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
    by_cases hold : a.round < base + S.hc.η_SG
    · have hrootP := WeakJoint.oldFGRoot_preceq_of_finiteBootstrap_at_read
        S adm hboot.oldRows hfinality hboot.frontierSeed hboot.fgAll hw
        hread hC hJ ha hemit hold hpair hT
      exact Block.preceq_trans hrootP (hslot.1.heads x hx)
    · have haTime : S.a a.round < Protocol.vote_time S.E (d + 1) := by
        rw [← htime]
        exact hat.trans_le ht
      exact ((SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hhor hd hupper hx
          a.round (Nat.le_of_not_gt hold) haTime).2 a.val_index ha).2 _ hT

/-- The prepared proposal anchor is below every protected previous vote head. -/
theorem SettledBootstrapPreparedV4.preparedProposalAnchor_preceq_voteDutyHead_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start last d : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : start ≤ d) (hupper : d ≤ last + 1)
    (hpropHor : Protocol.proposal_time S.E (d + 1) ≤ rho.horizon)
    (hprop : S.E.proposer (d + 1) ∈ rho.honest)
    {x : V} (hx : x ∈ rho.honest) :
    Block.Preceq
      (nodeAnchor S (proposerReadAt S rho (d + 1))
        (S.hc.round_of (proposerReadAt S rho (d + 1)).st.core.s))
      (voterHeadAt S rho x d) := by
  let s := d + 1
  let t := Protocol.proposal_time S.E s
  let w := S.E.proposer s
  let read := proposerReadAt S rho s
  let r := S.hc.round_of s
  have hw : w ∈ rho.honest := by simpa only [w, s] using hprop
  have htHor : t ≤ rho.horizon := by simpa only [t, s] using hpropHor
  have hroundT : S.hc.round_of (S.E.slotOf t) = r := by
    simpa only [t, r, Proofs.Optimistic.slotOf_proposal_time]
  have hreadRound : S.hc.round_of read.st.core.s = r := by
    simpa only [read, proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.slotOf_proposal_time, r, t]
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hcutpos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hroundCut : base + S.hc.η_SG ≤ r := by
    change base + S.hc.η_SG ≤ s / S.hc.R
    exact (Nat.le_div_iff_mul_le hRpos).2
      ((hboot.settled.trans hd).trans (Nat.le_succ d))
  have hr : 0 < r := hcutpos.trans_le hroundCut
  have hspan : base ≤ r - S.hc.η_SG := Nat.le_sub_of_add_le hroundCut
  have hbasePred : base ≤ r - 1 :=
    hspan.trans (Nat.sub_le_sub_left S.hc.η_SG_ge_one r)
  have hdomainLe : domain S.E S.hc r .g1 ≤ t := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact proposal_time_mono S.E (Nat.div_mul_le_self s S.hc.R)
  have htop : t ≤ opening S.E S.hc (r + 1) := by
    simpa only [NamedOutageClosure.clockRoundAt, hroundT] using
      (NamedOutageClosure.clockRound_lt_opening_succ S t).le
  have hdomainHor : domain S.E S.hc r .g1 ≤ rho.horizon :=
    hdomainLe.trans htHor
  have hread : min (S.a (base + S.hc.η_SG))
      (Protocol.vote_time S.E start) ≤ t :=
    (min_le_right _ _).trans
      ((vote_time_mono_slots S.E hd).trans
        (preparedV4_voteTime_lt_nextProposal S.E d).le)
  have hfg : Block.Preceq
      (Protocol.get_fg_root read.st.core.toHealing.toFG)
      (voterHeadAt S rho x d) := by
    simpa only [read, t, w, s, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      SettledBootstrapPreparedV4.fgRootAtRead_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hhor hd hupper hread
          (proposal_time_lt_vote_time S.E s).le hw hx
  rcases proposalAnchor_cases S rho s with hanchorFG |
      ⟨raw, A, hframe, hactive, hanchorA⟩
  · rw [show nodeAnchor S read (S.hc.round_of read.st.core.s) =
        Protocol.get_fg_root read.st.core.toHealing.toFG by
          simpa only [read, proposalDutyRead] using hanchorFG]
    exact hfg
  · have hanchorA' : nodeAnchor S read (S.hc.round_of read.st.core.s) = A := by
      simpa only [read, proposalDutyRead] using hanchorA
    rw [hanchorA']
    have hAraw : Block.Preceq A raw := by
      unfold activePrefix at hactive
      exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
    have hframeR := hframe
    change (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing
      (S.hc.round_of read.st.core.s)).g1 = some (some raw) at hframeR
    rw [hreadRound] at hframeR
    have hpostEarly : S.E.t_GST ≤ early S.E S.hc r .g2 := by
      exact hboot.basePost.trans (Assembly.a_mono S hbasePred) |>.trans
        (le_add_of_nonneg_right S.E.Δ_pos.le) |>.trans
          (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
            (Nat.sub_lt hr (by decide)))
    have hdelivery : TwoCutoffDelivery S rho r :=
      twoCutoffDelivery_of_core S adm hpostEarly
    have hFmono : Block.Preceq
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.F
        (NamedRun.stateBeforeTime S rho t w).st.core.F :=
      NamedOutageClosure.incl_strict_F_mono S rho
        adm.toNamedScheduleWellFormed w hdomainLe
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
        (voterHeadAt S rho x d) := by
      exact Block.preceq_trans hFmono (Block.preceq_trans hFroot (by
        simpa only [read, proposerReadAt, t, w,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
          using hfg))
    have hprevHor : S.a (r - 1) ≤ rho.horizon := by
      have hprev : S.a (r - 1) + S.E.Δ ≤ early S.E S.hc r .g1 :=
        (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
          (Nat.sub_lt hr (by decide))).trans
          (NamedOutageClosure.q10_early_g2_le_early_g1 S r)
      exact (le_add_of_nonneg_right S.E.Δ_pos.le).trans
        (hprev.trans ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
          S r).trans hdomainHor))
    have carrier_of_grade (C : Block V)
        (hgrade : phaseGrade S.E S.hc
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.F
          r .g1 C = true) :
        Block.Preceq C (voterHeadAt S rho x d) := by
      have hcarrier := relativeGradeCarrierAt_of_awakeWindowMajority
        S adm hr (hawake r hroundCut hprevHor) (p := .g1) (by
          intro y hy u hu k hk huk
          have hklt : k < r := mem_latestWindow_lt hk
          have hbaseK : base ≤ k :=
            hspan.trans (WeakSG.mem_latestWindow_lower_bound hk)
          have hdeadline : S.a k + S.E.Δ ≤ early S.E S.hc r .g1 :=
            (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt).trans
              (NamedOutageClosure.q10_early_g2_le_early_g1 S r)
          have hactionTime : S.a k < Protocol.vote_time S.E s := by
            exact (Int.lt_add_of_pos_right _ S.E.Δ_pos).trans_le
              (hdeadline.trans
                ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                  S r).trans (hdomainLe.trans
                    (proposal_time_lt_vote_time S.E s).le)))
          have hem := honest_emits_exact_actionAttestationAt_of_awake S
            adm.toNamedScheduleWellFormed hu k huk (by
              exact (le_add_of_nonneg_right S.E.Δ_pos.le).trans
                (hdeadline.trans
                  ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                    S r).trans hdomainHor)))
          have hAhead : Block.Preceq (actionSGBlockAt S rho u k)
              (voterHeadAt S rho x d) := by
            by_cases hold : k < base + S.hc.η_SG
            · exact Block.preceq_trans (hboot.sgBoot k hbaseK hold u hu hem)
                ((SettledBootstrapPreparedV4.protectedVoteSlots_core
                  S adm hcom hboot hawake hfinality hhor d hd hupper).1.heads x hx)
            · exact (SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
                S adm hcom hboot hawake hfinality hhor hd hupper hx
                  k (Nat.le_of_not_gt hold) hactionTime).1 u hu hem
          have hfgY := SettledBootstrapPreparedV4.fgRootAtRead_preceq_voteDutyHead_core
            S adm hcom hboot hawake hfinality hhor hd hupper hread
              (proposal_time_lt_vote_time S.E s).le hy hx
          have hFmonoY : Block.Preceq
              (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) y).st.core.F
              (NamedRun.stateBeforeTime S rho t y).st.core.F :=
            NamedOutageClosure.incl_strict_F_mono S rho
              adm.toNamedScheduleWellFormed y hdomainLe
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
              (voterHeadAt S rho x d) :=
            Block.preceq_trans hFmonoY (Block.preceq_trans hFrootY hfgY)
          exact NamedOutageClosure.honestRoundVote_interpreted_at_reader_of_twoCutoff_compatible_after
            S rho adm hboot.basePost hdelivery r k hbaseK .g1 hk y hy
              hdomainHor hdeadline
              ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u k).mpr
                ⟨hu, actionAttestationAt S rho u k,
                  (actionAttestationAt_shape S rho u k).1,
                  (actionAttestationAt_shape S rho u k).2.1, hem⟩)
              (Block.compatible_of_preceq_common hFheadY hAhead))
      obtain ⟨k, hk, u, hu, hemit, hC⟩ := hcarrier w hw C
        (by simpa only [PhaseGrades.phaseGrade] using hgrade)
      have hklt : k < r := mem_latestWindow_lt hk
      have hbaseK : base ≤ k :=
        hspan.trans (WeakSG.mem_latestWindow_lower_bound hk)
      have hactionTime : S.a k < Protocol.vote_time S.E s := by
        calc
          S.a k < S.a k + S.E.Δ := Int.lt_add_of_pos_right _ S.E.Δ_pos
          _ ≤ early S.E S.hc r .g2 :=
            NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt
          _ ≤ early S.E S.hc r .g1 :=
            NamedOutageClosure.q10_early_g2_le_early_g1 S r
          _ ≤ domain S.E S.hc r .g1 :=
            NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1 S r
          _ ≤ t := hdomainLe
          _ < Protocol.vote_time S.E s := proposal_time_lt_vote_time S.E s
      by_cases hold : k < base + S.hc.η_SG
      · exact Block.preceq_trans hC
          (Block.preceq_trans (hboot.sgBoot k hbaseK hold u hu hemit)
            ((SettledBootstrapPreparedV4.protectedVoteSlots_core
              S adm hcom hboot hawake hfinality hhor d hd hupper).1.heads x hx))
      · exact Block.preceq_trans hC
          ((SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
            S adm hcom hboot hawake hfinality hhor hd hupper hx
              k (Nat.le_of_not_gt hold) hactionTime).1 u hu hemit)
    rcases eq_or_lt_of_le hdomainLe with hopen | hinterior
    · have hframeStore := preparedFrame_g1_eq_storeRoot_at_opening
        S rho adm w hw r hr t hroundT hopen hdomainHor
      have hframe' :
          (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing r).g1 =
            some (some raw) := by
        simpa only [read, proposerReadAt, t, w] using hframeR
      let domainRead := PhaseGrades.readAt S rho (domain S.E S.hc r .g1) w
      have hframeStore' :
          (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing r).g1 =
            some ((storeRoot S.E S.hc domainRead.st r .g1).map
              (fun X => DecoupledConsensusModel.Protocol.clipGrade X read.st.core.F)) := by
        simpa only [read, domainRead, proposerReadAt, t, w,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
          using hframeStore
      cases hroot : storeRoot S.E S.hc domainRead.st r .g1 with
      | none =>
          simp only [hroot, Option.map_none] at hframeStore'
          rw [hframe'] at hframeStore'
          cases hframeStore'
      | some C =>
          have hrawEq : raw = DecoupledConsensusModel.Protocol.clipGrade C read.st.core.F := by
            have heq := hframe'.symm.trans
              (by simpa only [hroot, Option.map_some] using hframeStore')
            exact Option.some.inj (Option.some.inj heq)
          have hCgrade : phaseGrade S.E S.hc
              domainRead.st.core.toHealing.gradeView domainRead.st.core.F
              r .g1 C = true :=
            (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hroot)).2
          exact Block.preceq_trans hAraw (by
            rw [hrawEq]
            exact Block.preceq_trans
              (NamedOutageClosure.q10_clip_preceq C read.st.core.F)
              (carrier_of_grade C (by
                simpa only [domainRead, PhaseGrades.readAt] using hCgrade)))
    · have hgrade := WeakSG.phaseGrade_of_preparedFrame_g1
        S rho adm w hw r hr t hroundT hinterior htop hdomainHor (raw := raw) (by
          simpa only [read, proposerReadAt, t, w] using hframeR)
      exact Block.preceq_trans hAraw (carrier_of_grade raw hgrade)

/-- Every protected prior block stays below the next prepared honest proposal
parent after the V4 cut. -/
theorem SettledBootstrapPreparedV4.protected_preceq_proposedParent_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start last d : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : start ≤ d) (hupper : d ≤ last + 1)
    (hpropHor : Protocol.proposal_time S.E (d + 1) ≤ rho.horizon)
    (hprop : S.E.proposer (d + 1) ∈ rho.honest)
    {B : Block V} (hB : ProtectedVoteSlot S rho d B) :
    Block.Preceq B (proposedParent S rho (d + 1)) := by
  let p := S.E.proposer (d + 1)
  let t := Protocol.proposal_time S.E (d + 1)
  let read := proposerReadAt S rho (d + 1)
  let st := read.st.core
  let votes := (Protocol.proposer_view st.toHealing.toFG.toSG.toGoldfishStore st.s).toFinset
  let support :=
    (Protocol.proposer_support_view st.toHealing.toFG.toSG.toGoldfishStore st.s).toFinset
  let tree := Protocol.get_filtered_block_tree st.toHealing.toFG
  have hp : p ∈ rho.honest := by simpa only [p] using hprop
  have hcutpos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hdPos : 0 < d :=
    (Nat.mul_pos hcutpos hRpos).trans_le (hboot.settled.trans hd)
  have hcut : Protocol.support_cutoff S.E d ≤ rho.horizon := by
    rw [Protocol.confirmation_time_eq_support_cutoff_succ] at hhor
    exact (support_cutoff_mono S.E hupper).trans hhor
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E d := by
    have hbaseLt : base < base + S.hc.η_SG :=
      Nat.lt_of_succ_le (Nat.add_le_add_left S.hc.η_SG_ge_one base)
    exact hboot.basePost.trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
        ((action_add_delta_le_openingProposal_of_round_lt S hbaseLt).trans
          ((proposal_time_mono S.E (hboot.settled.trans hd)).trans
            (proposal_time_lt_vote_time S.E d).le)))
  have hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon := by
    apply le_trans ?_ hcut
    rw [← vote_time_add_delta]
    exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
  have hread : min (S.a (base + S.hc.η_SG))
      (Protocol.vote_time S.E start) ≤ t :=
    (min_le_right _ _).trans
      ((vote_time_mono_slots S.E hd).trans
        (preparedV4_voteTime_lt_nextProposal S.E d).le)
  have hroots : ∀ y ∈ rho.honest, Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyStore S rho p (d + 1)).toHealing.toFG)
      (voteDutyHead S rho y d) := by
    intro y hy
    simpa only [Internal.NamedRecoveryRead.voteDutyStore, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      SettledBootstrapPreparedV4.fgRootAtRead_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hhor hd hupper
          (t := Protocol.vote_time S.E (d + 1))
          ((min_le_right _ _).trans (vote_time_mono_slots S.E
            (hd.trans (Nat.le_succ d)))) (le_refl _) hp hy
  let R := Protocol.get_fg_root
    (Internal.NamedRecoveryRead.voteDutyRead S rho p (d + 1)).st.core.toHealing.toFG
  have hconeR : NamedHonestVotesCone S rho d (fun X => Block.Preceq R X) := by
    intro y hy hyCommittee
    obtain ⟨Y, hYerase, hYrun, hYemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S adm hy hdPos hyCommittee hvoteHor
    refine ⟨Y, ?_, hYrun, hYemit⟩
    rw [hYerase]
    simpa only [R, Internal.NamedRecoveryRead.voteDutyStore] using hroots y hy
  have havailable : HonestHeadsAvailableBefore S rho d p
      (Protocol.support_cutoff S.E d) :=
    honestHeadsAvailableBefore_of_namedPostHealingCone_core
      S adm hp hpost hcut (B := R) (Block.preceq_self R) hconeR
  have hresolve0 := headsResolveIn_storeBeforeTime_of_availableBefore_at_core
    S adm hp d (support_cutoff_le_proposal_time_succ S.E d) havailable
  have hresolve : HeadsResolveIn S rho d st.T st.timestamp_block := by
    simpa only [st, read, proposerReadAt, t, p,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hresolve0
  have hslot : st.s = d + 1 := by
    simpa only [st, read, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      (Proofs.Optimistic.slotOf_proposal_time S.E (d + 1))
  have hsupportSub : support ⊆ votes := by
    intro u hu
    simp only [support, votes, Protocol.proposer_support_view,
      Protocol.proposer_view, List.mem_toFinset, List.mem_filter] at hu ⊢
    exact hu.1
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed t
  have hgf : st.gf_votes = (rho.stateBefore S n p).st.core.gf_votes := by
    dsimp only [st, read, proposerReadAt, t, p,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
    exact congrArg (fun z => (z (S.E.proposer (d + 1))).st.core.gf_votes) hn
  have hne : ∀ y ∈ S.E.committee d, y ∈ rho.honest →
      Protocol.equivocates votes y = false := by
    intro y _ hy
    have hno := Proofs.Optimistic.pool_no_honest_equivocation_of_core
      S adm p n d hy
    simpa only [votes, Protocol.proposer_view, hslot, Nat.add_sub_cancel,
      hgf, Protocol.NamedStore.pool, Protocol.Store.pool,
      Protocol.Store.toHealing, List.toFinset] using hno
  have hvote : ∀ y ∈ S.E.committee d, y ∈ rho.honest →
      ∃ X : Block V, Block.Preceq B X ∧
        X.slot ≤ d ∧
        (⟨y, d, X.root⟩ : GoldfishVote V) ∈ support ∧
        Block.find? st.T X.root = some X := by
    intro y hyCommittee hyHonest
    obtain ⟨X, hBX, hXrun, hXemit⟩ := hB.cone y hyHonest hyCommittee
    have hhead : HonestHead S rho d X.erase :=
      ⟨y, hyHonest, hyCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    obtain ⟨hfind, -⟩ := hresolve X.erase hhead
    have hcutVote := Protocol.gfVote_in_cutoff_view_after_gst
      S adm hyHonest hdPos hpost hXemit rfl hp t t
        (support_cutoff_le_proposal_time_succ S.E d)
        (support_cutoff_le_proposal_time_succ S.E d) hcut
    have hcutVote' := hcutVote
    rw [beforeCutoff, Finset.mem_filter] at hcutVote'
    have hpool : (⟨y, d, X.erase.root⟩ : GoldfishVote V) ∈
        (rho.storeBeforeTime S p t).core.gf_votes d := by
      simpa only [Protocol.Store.pool, List.mem_toFinset] using hcutVote'.1
    have hXmem : X.erase ∈ (rho.storeBeforeTime S p t).T := by
      simpa only [st, read, proposerReadAt, t, p,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Run.storeBeforeTime] using (Proofs.HealingLemmas.find?_mem hfind)
    have hXslot : X.erase.slot ≤ d :=
      Proofs.Optimistic.emitted_vote_head_slot_le_of_store_mem S adm hyHonest hp hXemit rfl
        hXmem (by rfl)
    have hraw : (⟨y, d, X.erase.root⟩ : GoldfishVote V) ∈ votes := by
      change (⟨y, d, X.erase.root⟩ : GoldfishVote V) ∈
        (st.gf_votes (st.s - 1)).toFinset
      rw [hslot, Nat.add_sub_cancel]
      simpa only [st, read, proposerReadAt, t, p,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Run.storeBeforeTime] using List.mem_toFinset.mpr hpool
    have hsupport : (⟨y, d, X.erase.root⟩ : GoldfishVote V) ∈ support := by
      simp only [support, Protocol.proposer_support_view,
        List.mem_toFinset, List.mem_filter, hslot, Nat.add_sub_cancel]
      refine ⟨?_, ?_⟩
      · simpa only [votes, Protocol.proposer_view, hslot,
          Nat.add_sub_cancel, Protocol.Store.toHealing] using
          List.mem_toFinset.mp hraw
      · change decide (Protocol.resolved st.toHealing.T
          (⟨y, d, X.erase.root⟩ : GoldfishVote V) = true) = true
        simp only [Protocol.resolved, Protocol.Store.toHealing, hfind]
        simp [hXslot]
    exact ⟨X.erase, hBX, hXslot, hsupport, hfind⟩
  have hcone : ConeSupport S.E st.T votes support votes (st.s - 1)
      rho.honest (fun X => Block.Preceq B X) := by
    have hcone0 := Proofs.Optimistic.coneSupport_of_named_votes
      (E := S.E) (T := st.T) (votes := votes) (support := support)
      (late := votes) (s := d) (Hon := rho.honest)
      (tgt := fun X => Block.Preceq B X) (hcom d)
        (subset_refl _) hsupportSub hne hvote
    simpa only [hslot, Nat.add_sub_cancel] using hcone0
  have hvalid : Protocol.VoteSetValid S.E (st.s - 1) votes := by
    simpa only [st, read, votes, Internal.NamedRecoveryRead.proposalDutyStore,
      proposalDutyRead] using
      (Protocol.proposerDutyStore_proposer_view_valid_core
        S adm (d + 1))
  have hpos : 0 < ((S.E.committee d) ∩ rho.honest).card := by
    have hc := hcom d
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have hxCommittee := (Finset.mem_inter.mp hx).1
  have hxHonest := (Finset.mem_inter.mp hx).2
  obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
    WeakGoldfish.voterHead_runBlock_and_emits
      S adm hxHonest hdPos hxCommittee hvoteHor
  have hBX : Block.Preceq B X.erase := by
    rw [hXerase]
    exact hB.heads x hxHonest
  have hXhead : HonestHead S rho d X.erase :=
    ⟨x, hxHonest, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
  obtain ⟨hXfind, -⟩ := hresolve X.erase hXhead
  have hXT : X.erase ∈ st.T := Proofs.HealingLemmas.find?_mem hXfind
  obtain ⟨X', hX'body, hX'erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho t p (by
      simpa only [st, read, proposerReadAt, t, p,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
        using hXT)
  obtain ⟨m, hm, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted t
  have hX'prefix : X' ∈ (NamedRun.stateBefore S rho m p).st.bodies := by
    rw [← congrFun hm p]
    exact hX'body
  have hX'run : RunBlock S rho X' :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hp hX'prefix
  have hX'eq : X' = X := by
    apply adm.toNamedRootCollisionFree.root_injective X' X hX'run hXrun
      X' X (Or.inl (Proofs.NamedAncestry.named_self X'))
        (Or.inr (Proofs.NamedAncestry.named_self X))
    rw [← Proofs.NamedWire.erase_root X', ← Proofs.NamedWire.erase_root X, hX'erase]
  have hXbody : X ∈ (rho.storeBeforeTime S p t).bodies := by
    rw [← hX'eq]
    exact hX'body
  have hXview : (st.σ X.erase).h =
      (Protocol.derive_named S.E S.cfg X).h := by
    have hv := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho t p X hXbody
    simpa only [st, read, proposerReadAt, t, p,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      congrArg (fun z => z.h) hv
  have hband : st.h_max - 1 ≤ (st.σ X.erase).h := by
    rw [hXview]
    by_cases hlarge : 1 < st.h_max
    · have hmajority := honestWeightMajority_of_finiteWindowsFrom
        S hawake hcutpos (hboot.settled.trans hd) hupper hhor
      obtain ⟨a, ta, D, K, ha, hemit, hat, hrow, hfgK, -, -, hKentry,
          hKrun, hKheight⟩ := frontier_confirmationWitness_core_entry
        S adm hmajority (v := p) (time := t) (by
          simpa only [st, read, proposerReadAt, t, p,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
            using hlarge)
      have haTime : S.a a.round < Protocol.vote_time S.E (d + 1) := by
        have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
        rw [← htime]
        exact hat.trans (proposal_time_lt_vote_time S.E (d + 1))
      have hPhead : Block.Preceq P.erase (voterHeadAt S rho x d) :=
        (SettledBootstrapPreparedV4.protectedVoteSlots_core
          S adm hcom hboot hawake hfinality hhor d hd hupper).1.heads x hxHonest
      have hPX : Block.Preceq P.erase X.erase := by
        rw [hXerase]
        exact hPhead
      obtain ⟨P', hP'X, hP'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift X hPX
      have hP'run : RunBlock S rho P' :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hP'X
      have hP'eq : P' = P := by
        apply adm.toNamedRootCollisionFree.root_injective P' P hP'run hboot.runBlock
          P' P (Or.inl (Proofs.NamedAncestry.named_self P'))
            (Or.inr (Proofs.NamedAncestry.named_self P))
        rw [← Proofs.NamedWire.erase_root P', ← Proofs.NamedWire.erase_root P, hP'erase]
      have hPheight : (Protocol.derive_named S.E S.cfg P).h ≤
          (Protocol.derive_named S.E S.cfg X).h := by
        apply Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
        rw [← hP'eq]
        exact hP'X
      by_cases hold : a.round < base + S.hc.η_SG
      · by_cases hpre : a.round < fresh
        · have hbound := hboot.oldRows a ta _ ha hemit hpre hrow
          have hbound' : st.h_max - 1 ≤ cap := by
            simpa only [st, read, proposerReadAt, t, p,
              NamedActionReads.confirmationReadAt,
              NamedActionReads.confirmationReadFrom,
              Protocol.NamedStore.setClock] using hbound
          exact hbound'.trans (hboot.heightCap.trans hPheight)
        · have hKP := hboot.fgAll a ta _
              (Protocol.derive_named S.E S.cfg K).T_h
              ha hemit hrow (Nat.le_of_not_gt hpre) hold hfgK
          rw [hKentry] at hKP
          have hKX : Block.Preceq K.erase X.erase :=
            Block.preceq_trans hKP hPX
          obtain ⟨K', hK'X, hK'erase⟩ :=
            Proofs.NamedAncestry.erased_ancestor_lift X hKX
          have hK'run : RunBlock S rho K' :=
            Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hK'X
          have hK'eq : K' = K := by
            apply adm.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
              K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
                (Or.inr (Proofs.NamedAncestry.named_self K))
            rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
          have hKheight' : (Protocol.derive_named S.E S.cfg K).h =
              st.h_max - 1 := by
            simpa only [st, read, proposerReadAt, t, p,
              NamedActionReads.confirmationReadAt,
              NamedActionReads.confirmationReadFrom,
              Protocol.NamedStore.setClock] using hKheight
          rw [← hKheight']
          apply Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
          rw [← hK'eq]
          exact hK'X
      · have hsource :=
          ((SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
            S adm hcom hboot hawake hfinality hhor hd hupper hxHonest
              a.round (Nat.le_of_not_gt hold) haTime).2 a.val_index ha).2 _ hfgK
        have hKX : Block.Preceq K.erase X.erase := by
          rw [← hKentry, hXerase]
          simpa only [voteDutyHead] using hsource
        obtain ⟨K', hK'X, hK'erase⟩ :=
          Proofs.NamedAncestry.erased_ancestor_lift X hKX
        have hK'run : RunBlock S rho K' :=
          Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hK'X
        have hK'eq : K' = K := by
          apply adm.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
            K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
              (Or.inr (Proofs.NamedAncestry.named_self K))
          rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
        have hKheight' : (Protocol.derive_named S.E S.cfg K).h =
            st.h_max - 1 := by
          simpa only [st, read, proposerReadAt, t, p,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using hKheight
        rw [← hKheight']
        apply Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
        rw [← hK'eq]
        exact hK'X
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hlarge)]
      exact Nat.zero_le _
  have hFJ : Block.Preceq st.F st.J := by
    simpa only [st, read, proposerReadAt, t, p,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho t p
  have hrootX : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) X.erase := by
    simpa only [st, read, proposerReadAt, t, p,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      hXerase] using
      SettledBootstrapPreparedV4.fgRootAtRead_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hhor hd hupper hread
          (proposal_time_lt_vote_time S.E (d + 1)).le hp hxHonest
  have hFX : Block.Preceq st.F X.erase :=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st := st.toHealing.toFG) hFJ) hrootX
  have hXcandidate : X.erase ∈ tree := by
    simp only [tree, Protocol.get_filtered_block_tree,
      Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hXT, hFX⟩, X.erase, hXT, Block.preceq_self _, hband⟩, hrootX⟩
  have hpc : ParentClosed st := by
    simpa only [st, read, proposerReadAt, t, p,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho t p
  have hrootAnchor : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG)
      (nodeAnchor S read (S.hc.round_of st.s)) := by
    exact NamedOutageClosure.fg_root_preceq_anchor S.E S.hc st.toHealing
      (S.hc.round_of st.s)
      (DecoupledConsensusModel.Protocol.readFrame read.cache st.toHealing
        (S.hc.round_of st.s)).g1
  have hanchorX := SettledBootstrapPreparedV4.preparedProposalAnchor_preceq_voteDutyHead_core
    S adm hcom hboot hawake hfinality hhor hd hupper hpropHor hprop hxHonest
  have hanchorX' : Block.Preceq
      (nodeAnchor S read (S.hc.round_of st.s)) X.erase := by
    simpa only [read, st, hXerase] using hanchorX
  have hcompat : Block.compatible
      (nodeAnchor S read (S.hc.round_of st.s)) B = true :=
    Block.compatible_of_preceq_common hanchorX' hBX
  have hpath : Block.Preceq (nodeAnchor S read (S.hc.round_of st.s)) B →
      ∀ C : Block V,
        Block.Preceq (nodeAnchor S read (S.hc.round_of st.s)) C →
        C ≠ nodeAnchor S read (S.hc.round_of st.s) →
        Block.Preceq C B → C ∈ tree := by
    intro _ C hAC _ hCB
    have hCX : Block.Preceq C X.erase := Block.preceq_trans hCB hBX
    have hCT : C ∈ st.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff st).mp hpc).2
        C X.erase hXT hCX
    exact Proofs.Records.mem_filtered_of_preceq hFJ hXcandidate hCT hCX
      (Block.preceq_trans hrootAnchor hAC)
  have hhead := Protocol.goldfish_fork_choice_captures_supporter_majority
    S.E st.σ st.h_max st.T tree st.s votes support (st.s - 1)
      (ConeSupport.sub hcone)
      (Protocol.supporterMajority_of_cone S.E hcone hvalid)
      hcompat hpath
  rw [proposedParent_eq_get_head_with_anchor]
  change Block.Preceq B
    (Protocol.get_head_in_tree_with_layer
      (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
      tree votes support (st.s - 1))
  rw [Proofs.Optimistic.get_head_in_tree_split_with]
  simpa only [Internal.PhaseGrades.nodeAnchor, Internal.PhaseGrades.nodeRead,
    tree, votes, support] using hhead

#print axioms SettledBootstrapPreparedV4.protected_preceq_proposedParent_core
#print axioms SettledBootstrapPreparedV4.fgRootAtRead_preceq_voteDutyHead_core
#print axioms SettledBootstrapPreparedV4.preparedProposalAnchor_preceq_voteDutyHead_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
