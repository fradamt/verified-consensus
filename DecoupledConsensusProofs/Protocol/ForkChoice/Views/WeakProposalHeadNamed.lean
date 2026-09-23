module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Head.PreparedProposalReadBridge
public import DecoupledConsensusProofs.Execution.WeakProposalReadAnchorsNamed
public import DecoupledConsensusProofs.Protocol.ChainState.FGRootWitness
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapSG
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeilingStep
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.GoldfishCone

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Prepared weak-genesis proposal parents -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic Statements
open Internal.NamedRecoveryRead Internal.PhaseGrades
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

namespace WeakGenesis

theorem preparedProposalAnchor_preceq_voteDutyHead_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {last d : Slot} (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1)
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
  have hdomainLe : domain S.E S.hc r .g1 ≤ t := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact proposal_time_mono S.E (Nat.div_mul_le_self s S.hc.R)
  have htop : t ≤ opening S.E S.hc (r + 1) := by
    simpa only [NamedOutageClosure.clockRoundAt, hroundT] using
      (NamedOutageClosure.clockRound_lt_opening_succ S t).le
  have hdomainHor : domain S.E S.hc r .g1 ≤ rho.horizon :=
    hdomainLe.trans htHor
  have hfg : Block.Preceq
      (Protocol.get_fg_root read.st.core.toHealing.toFG)
      (voterHeadAt S rho x d) := by
    simpa only [read, t, w, s, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      (fgRootAtRead_preceq_voteDutyHead_of_gstZero_named
        S h.core h.committees h.gstZero h.windows hhor hd hupper
          (t := t) ((proposal_time_lt_vote_time S.E s).le) hw hx)
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
    by_cases hr0 : r = 0
    · have htne : t ≠ domain S.E S.hc 0 .g1 := by
        have htpos : 0 < t := by
          unfold t s Protocol.proposal_time Env.t slotStart
          push_cast
          nlinarith [S.E.Δ_pos]
        have hzero : domain S.E S.hc 0 .g1 = 0 := by
          unfold domain opening Phase.domainOffset Protocol.proposal_time
            Env.t slotStart Protocol.HealConfig.opening_slot
          norm_num
        rw [hzero]
        exact ne_of_gt htpos
      have hno := confirmationRead_g1_round_zero_no_root
        S h.core w t (by simpa only [hr0] using hroundT) htne (root := raw)
      exact False.elim (hno (by
        simpa only [read, proposerReadAt, t, w, hr0] using hframeR))
    · have hr : 0 < r := Nat.pos_of_ne_zero hr0
      have hpostEarly : S.E.t_GST ≤ early S.E S.hc r .g2 := by
        rw [h.gstZero]
        exact (Proofs.HealingLemmas.a_nonneg S (r - 1)).trans
          (le_add_of_nonneg_right S.E.Δ_pos.le) |>.trans
            (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
              (Nat.sub_lt hr (by decide)))
      have hdelivery : TwoCutoffDelivery S rho r :=
        twoCutoffDelivery_of_core S h.core hpostEarly
      have hFmono : Block.Preceq
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.F
          (NamedRun.stateBeforeTime S rho t w).st.core.F :=
        NamedOutageClosure.incl_strict_F_mono S rho
          h.core.toNamedScheduleWellFormed w hdomainLe
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
          S h.core hr (h.windows r hr hprevHor) (p := .g1) (by
            intro y hy u hu k hk huk
            have hklt : k < r := mem_latestWindow_lt hk
            have hdeadline : S.a k + S.E.Δ ≤ early S.E S.hc r .g1 :=
              (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt).trans
                (NamedOutageClosure.q10_early_g2_le_early_g1 S r)
            have hactionTime : S.a k < Protocol.vote_time S.E s := by
              exact (Int.lt_add_of_pos_right _ S.E.Δ_pos).trans_le
                (hdeadline.trans ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                  S r).trans (hdomainLe.trans (proposal_time_lt_vote_time S.E s).le)))
            have hAhead := (actionSources_preceq_voteDutyHead_of_gstZero
              S h.core h.committees h.gstZero h.windows hhor hd hupper hx
                k hactionTime).1 u hu
              (honest_emits_exact_actionAttestationAt_of_awake S
                h.core.toNamedScheduleWellFormed hu k huk (by
                  exact (le_add_of_nonneg_right S.E.Δ_pos.le).trans
                    (hdeadline.trans
                      ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                        S r).trans hdomainHor))))
            have hfgY := fgRootAtRead_preceq_voteDutyHead_of_gstZero_named
              S h.core h.committees h.gstZero h.windows hhor hd hupper
                (t := domain S.E S.hc r .g1)
                ((hdomainLe.trans (proposal_time_lt_vote_time S.E s).le)) hy hx
            have hFJY := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
              S rho (domain S.E S.hc r .g1) y
            have hFrootY : Block.Preceq
                (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) y).st.core.F
                (Protocol.get_fg_root
                  (NamedRun.stateBeforeTime S rho
                    (domain S.E S.hc r .g1) y).st.core.toHealing.toFG) :=
              Proofs.Records.preceq_get_fg_root_of_F (st :=
                (NamedRun.stateBeforeTime S rho
                  (domain S.E S.hc r .g1) y).st.core.toHealing.toFG) hFJY
            have hFheadY : Block.Preceq
                (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) y).st.core.F
                (voterHeadAt S rho x d) :=
              Block.preceq_trans hFrootY (by
                simpa only [Run.storeBeforeTime] using hfgY)
            exact NamedOutageClosure.honestRoundVote_interpreted_at_reader_of_twoCutoff_compatible
              S rho h.core h.gstZero hdelivery r k .g1 hk y hy hdomainHor hdeadline
                ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u k).mpr
                  ⟨hu, actionAttestationAt S rho u k,
                    (actionAttestationAt_shape S rho u k).1,
                    (actionAttestationAt_shape S rho u k).2.1,
                    honest_emits_exact_actionAttestationAt_of_awake S
                      h.core.toNamedScheduleWellFormed hu k huk (by
                        exact (le_add_of_nonneg_right S.E.Δ_pos.le).trans
                          (hdeadline.trans
                            ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                              S r).trans hdomainHor)))⟩)
                (Block.compatible_of_preceq_common hFheadY hAhead))
        obtain ⟨k, hk, u, hu, hemit, hC⟩ := hcarrier w hw C
          (by simpa only [PhaseGrades.phaseGrade] using hgrade)
        have hklt : k < r := mem_latestWindow_lt hk
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
        exact Block.preceq_trans hC
          ((actionSources_preceq_voteDutyHead_of_gstZero
            S h.core h.committees h.gstZero h.windows hhor hd hupper hx
              k hactionTime).1 u hu hemit)
      rcases eq_or_lt_of_le hdomainLe with hopen | hinterior
      · have hframeStore := preparedFrame_g1_eq_storeRoot_at_opening
          S rho h.core w hw r hr t hroundT hopen hdomainHor
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
          S rho h.core w hw r hr t hroundT hinterior
            htop hdomainHor (raw := raw) (by
              simpa only [read, proposerReadAt, t, w] using hframeR)
        exact Block.preceq_trans hAraw (carrier_of_grade raw hgrade)

/-- Every protected prior block stays below the next prepared honest proposal
parent in the weak-genesis regime. -/
theorem protected_preceq_proposedParent_of_gstZero_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {last d : Slot} (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1)
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
  have hdPos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hcut : Protocol.support_cutoff S.E d ≤ rho.horizon := by
    rw [Protocol.confirmation_time_eq_support_cutoff_succ] at hhor
    exact (support_cutoff_mono S.E hupper).trans hhor
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E d := by
    rw [h.gstZero]
    exact vote_time_nonneg S.E d
  have hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon := by
    apply le_trans ?_ hcut
    rw [← vote_time_add_delta]
    exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
  have hroots : ∀ y ∈ rho.honest, Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyStore S rho p (d + 1)).toHealing.toFG)
      (voteDutyHead S rho y d) := by
    intro y hy
    simpa only [Internal.NamedRecoveryRead.voteDutyStore, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using fgRootAtRead_preceq_voteDutyHead_of_gstZero_named
        S h.core h.committees h.gstZero h.windows hhor hd hupper
          (t := Protocol.vote_time S.E (d + 1)) (le_refl _) hp hy
  let R := Protocol.get_fg_root
    (Internal.NamedRecoveryRead.voteDutyRead S rho p (d + 1)).st.core.toHealing.toFG
  have hconeR : NamedHonestVotesCone S rho d (fun X => Block.Preceq R X) := by
    intro y hy hyCommittee
    obtain ⟨Y, hYerase, hYrun, hYemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S h.core hy hdPos hyCommittee hvoteHor
    refine ⟨Y, ?_, hYrun, hYemit⟩
    rw [hYerase]
    simpa only [R, Internal.NamedRecoveryRead.voteDutyStore] using hroots y hy
  have havailable : HonestHeadsAvailableBefore S rho d p
      (Protocol.support_cutoff S.E d) :=
    honestHeadsAvailableBefore_of_namedPostHealingCone_core
      S h.core hp hpost hcut (B := R) (Block.preceq_self R) hconeR
  have hresolve0 := headsResolveIn_storeBeforeTime_of_availableBefore_at_core
    S h.core hp d (support_cutoff_le_proposal_time_succ S.E d) havailable
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
    S h.core.toNamedScheduleWellFormed t
  have hgf : st.gf_votes = (rho.stateBefore S n p).st.core.gf_votes := by
    dsimp only [st, read, proposerReadAt, t, p,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
    exact congrArg (fun z => (z (S.E.proposer (d + 1))).st.core.gf_votes) hn
  have hne : ∀ y ∈ S.E.committee d, y ∈ rho.honest →
      Protocol.equivocates votes y = false := by
    intro y _ hy
    have hno := Proofs.Optimistic.pool_no_honest_equivocation_of_core
      S h.core p n d hy
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
      S h.core hyHonest hdPos hpost hXemit rfl hp t t
        (support_cutoff_le_proposal_time_succ S.E d)
        (support_cutoff_le_proposal_time_succ S.E d) hcut
    have hcutVote' := hcutVote
    rw [beforeCutoff, Finset.mem_filter] at hcutVote'
    have hpool : (⟨y, d, X.erase.root⟩ : GoldfishVote V) ∈
        (rho.storeBeforeTime S p t).core.gf_votes d := by
      simpa only [Protocol.Store.pool, List.mem_toFinset] using hcutVote'.1
    have hraw : (⟨y, d, X.erase.root⟩ : GoldfishVote V) ∈ votes := by
      change (⟨y, d, X.erase.root⟩ : GoldfishVote V) ∈
        (st.gf_votes (st.s - 1)).toFinset
      rw [hslot, Nat.add_sub_cancel]
      simpa only [st, read, proposerReadAt, t, p,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Run.storeBeforeTime] using List.mem_toFinset.mpr hpool
    have hXmem : X.erase ∈ (rho.storeBeforeTime S p t).T := by
      simpa only [st, read, proposerReadAt, t, p,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
        (Proofs.HealingLemmas.find?_mem hfind)
    have hXslot : X.erase.slot ≤ d :=
      Proofs.Optimistic.emitted_vote_head_slot_le_of_store_mem S h.core
        hyHonest hp hXemit rfl hXmem (by rfl)
    have hsupport : (⟨y, d, X.erase.root⟩ : GoldfishVote V) ∈ support := by
      simp only [support, Protocol.proposer_support_view,
        List.mem_toFinset, List.mem_filter, hslot, Nat.add_sub_cancel]
      refine ⟨?_, ?_⟩
      · simpa only [votes, Protocol.proposer_view, hslot,
          Nat.add_sub_cancel, Protocol.Store.toHealing] using
          List.mem_toFinset.mp hraw
      · change decide (Protocol.resolved st.toHealing.T
          (⟨y, d, X.erase.root⟩ : GoldfishVote V) = true) = true
        simp [Protocol.resolved, Protocol.Store.toHealing, hfind, hXslot]
    exact ⟨X.erase, hBX, hXslot, hsupport, hfind⟩
  have hcone : ConeSupport S.E st.T votes support votes (st.s - 1)
      rho.honest (fun X => Block.Preceq B X) := by
    have hcone0 := Proofs.Optimistic.coneSupport_of_named_votes
      (E := S.E) (T := st.T) (votes := votes) (support := support)
      (late := votes) (s := d) (Hon := rho.honest)
      (tgt := fun X => Block.Preceq B X) (h.committees d)
        (subset_refl _) hsupportSub hne hvote
    simpa only [hslot, Nat.add_sub_cancel] using hcone0
  have hvalid : Protocol.VoteSetValid S.E (st.s - 1) votes := by
    simpa only [st, read, votes, Internal.NamedRecoveryRead.proposalDutyStore,
      proposalDutyRead] using
      (Protocol.proposerDutyStore_proposer_view_valid_core
        S h.core (d + 1))
  have hpos : 0 < ((S.E.committee d) ∩ rho.honest).card := by
    have hc := h.committees d
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have hxCommittee := (Finset.mem_inter.mp hx).1
  have hxHonest := (Finset.mem_inter.mp hx).2
  obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
    WeakGoldfish.voterHead_runBlock_and_emits
      S h.core hxHonest hdPos hxCommittee hvoteHor
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
    h.core.toNamedScheduleWellFormed.sorted t
  have hX'prefix : X' ∈ (NamedRun.stateBefore S rho m p).st.bodies := by
    rw [← congrFun hm p]
    exact hX'body
  have hX'run : RunBlock S rho X' :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hp hX'prefix
  have hX'eq : X' = X := by
    apply h.core.toNamedRootCollisionFree.root_injective X' X hX'run hXrun
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
    · have hmajority := honestWeightMajority_of_finiteWindows S h.windows hhor
      obtain ⟨a, ta, D, K, ha, hemit, hat, -, hfgK, -, -, hKentry,
          hKrun, hKheight⟩ := frontier_confirmationWitness_core_entry
        S h.core hmajority (v := p) (time := t) (by
          simpa only [st, read, proposerReadAt, t, p,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
            using hlarge)
      have haTime : S.a a.round < Protocol.vote_time S.E (d + 1) := by
        have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
        rw [← htime]
        exact hat.trans (proposal_time_lt_vote_time S.E (d + 1))
      have hsafe0 := ((actionSources_preceq_voteDutyHead_of_gstZero
        S h.core h.committees h.gstZero h.windows hhor hd hupper hxHonest
          a.round haTime).2 a.val_index ha).2 _ hfgK
      have hsafe : Block.Preceq K.erase X.erase := by
        rw [← hKentry, hXerase]
        simpa only [voteDutyHead] using hsafe0
      obtain ⟨K', hK'X, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift X hsafe
      have hK'run : RunBlock S rho K' :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hK'X
      have hK'eq : K' = K := by
        apply h.core.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
          K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
            (Or.inr (Proofs.NamedAncestry.named_self K))
        rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
      have hstHmax : st.h_max = (rho.storeBeforeTime S p t).core.h_max := by
        rfl
      rw [hstHmax, ← hKheight]
      exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg (by
        rw [← hK'eq]
        exact hK'X)
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
      fgRootAtRead_preceq_voteDutyHead_of_gstZero_named
        S h.core h.committees h.gstZero h.windows hhor hd hupper
          (t := t) ((proposal_time_lt_vote_time S.E (d + 1)).le) hp hxHonest
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
  have hanchorX := preparedProposalAnchor_preceq_voteDutyHead_of_gstZero
    S h hhor hd hupper hpropHor hprop hxHonest
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

#print axioms protected_preceq_proposedParent_of_gstZero_named
#print axioms preparedProposalAnchor_preceq_voteDutyHead_of_gstZero

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
