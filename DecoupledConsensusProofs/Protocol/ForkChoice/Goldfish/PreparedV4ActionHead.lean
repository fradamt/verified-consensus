module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.PreparedV4ProposalHead
public import DecoupledConsensusProofs.Execution.PreparedV4ConfirmationReadBand
public import DecoupledConsensusProofs.Protocol.ForkChoice.Head.WeakActionReadCore
public import DecoupledConsensusProofs.Protocol.Store.WeakSGReadBounds

@[expose] public section

/-! # Prepared V4 action heads -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Internal.NamedRecoveryRead Protocol Proofs.Optimistic
  HealingLemmas Statements
open Internal.PhaseGrades DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem preparedV4_sgSource_deadline_le_proposal
    (S : Setup V) {s : Slot} {k : Round}
    (hk : k < S.hc.round_of s) :
    S.a k + S.E.Δ ≤ Protocol.proposal_time S.E s :=
  (action_add_delta_le_openingProposal_of_round_lt S hk).trans
    (proposal_time_mono S.E (Nat.div_mul_le_self s S.hc.R))
private theorem preparedV4_actionAnchor_eq_readSgRoot
    (S : Setup V) (rho : Run V) (v : V) {r : Round} {q : Slot}
    (ha : S.a r = Protocol.support_cutoff S.E q) :
    healAnchor S.E S.hc (actionStoreAt S rho v r).toHealing =
      Protocol.get_sg_root S.E S.hc
        (rho.storeBeforeTime S v (S.a r)).toHealing (S.hc.round_of q) := by
  rw [healAnchor_eq_get_sg_root]
  have hslot := actionStoreAt_slot_of_action_eq_cutoff S rho v r q ha
  change Protocol.get_sg_root S.E S.hc (actionStoreAt S rho v r).toHealing
    (S.hc.round_of (actionStoreAt S rho v r).s) = _
  rw [hslot]
  unfold actionStoreAt actionReadAt NamedActionReads.actionReadAt
  rfl

private theorem coneSupport_actionStoreAt_after_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {q : Slot} (hq : 0 < q)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E q)
    (hhor : Protocol.support_cutoff S.E q ≤ rho.horizon)
    {tgt : Block V → Prop}
    (hnames : NamedHonestVotesCone S rho q tgt)
    {v : V} (hv : v ∈ rho.honest) {r : Round}
    (ha : S.a r = Protocol.support_cutoff S.E q)
    (hresolve : HeadsResolveIn S rho q
      (actionStoreAt S rho v r).T
      (actionStoreAt S rho v r).timestamp_block) :
    let ast := actionStoreAt S rho v r
    let raw := ast.pool q
    let support := raw.filter (fun u => Protocol.resolved ast.T u = true)
    ConeSupport S.E ast.T raw support raw q rho.honest tgt := by
  dsimp only
  apply Proofs.Optimistic.coneSupport_of_named_votes (hcom q) (subset_refl _)
  · exact Finset.filter_subset _ _
  · obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toNamedScheduleWellFormed (S.a r)
    intro x _ hx
    have hno := Proofs.Optimistic.pool_no_honest_equivocation_of_core
      S adm v n q hx
    rw [actionStoreAt_pool S rho v r q]
    have hstore : rho.storeBeforeTime S v (S.a r) =
        (rho.stateBefore S n v).st :=
      congrArg NamedNodeState.st (congrFun hn v)
    rw [hstore]
    exact hno
  · intro x hxCommittee hxHonest
    obtain ⟨X, hX, hXrun, hXemit⟩ := hnames x hxHonest hxCommittee
    obtain ⟨hfind, -⟩ := hresolve X.erase
      ⟨x, hxHonest, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    have hcut := gfVote_in_cutoff_view_after_gst
      S adm hxHonest hq hpost hXemit rfl hv
        (S.a r) (S.a r) (by rw [ha]) (by rw [ha]) hhor
    have hpre : (⟨x, q, X.erase.root⟩ : GoldfishVote V) ∈
        (rho.storeBeforeTime S v (S.a r)).pool q :=
      (Finset.mem_filter.mp hcut).1
    have hpool : (⟨x, q, X.erase.root⟩ : GoldfishVote V) ∈
        (actionStoreAt S rho v r).pool q := by
      rw [actionStoreAt_pool S rho v r q]
      exact hpre
    have hslot : X.erase.slot ≤ q :=
      Proofs.Optimistic.emitted_vote_head_slot_le_of_store_mem S adm
        hxHonest hv hXemit rfl (by
          rw [← Protocol.actionStoreAt_T S rho v r]
          exact Proofs.HealingLemmas.find?_mem hfind)
        (Proofs.HealingLemmas.find?_root hfind)
    refine ⟨X.erase, hX, hslot, Finset.mem_filter.mpr ⟨hpool, ?_⟩, hfind⟩
    simp [Protocol.resolved, hfind, hslot]

private theorem preparedV4_actionReadFGRoot_preceq_head
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

private theorem preparedV4_actionAnchor_preceq_head
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start last : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    {r : Round} (hd : start ≤ S.hc.opening_slot r + 1)
    (hupper : S.hc.opening_slot r + 1 ≤ last + 1)
    (hactHor : S.a r ≤ rho.horizon)
    {v x : V} (hv : v ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
        S.E S.hc (actionStoreAt S rho v r).toHealing
        (S.hc.round_of (actionStoreAt S rho v r).s))
      (voterHeadAt S rho x (S.hc.opening_slot r + 1)) := by
  let p := S.hc.opening_slot r
  let q := p + 1
  let t := S.a r
  let read := confirmationInputRead S rho v p
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hcutpos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hroundCut : base + S.hc.η_SG ≤ r := by
    have hopen : S.hc.opening_slot (base + S.hc.η_SG) ≤ p + 1 := by
      simpa only [q, p] using hboot.settled.trans hd
    have hdiv : base + S.hc.η_SG ≤ (p + 1) / S.hc.R :=
      (Nat.le_div_iff_mul_le hRpos).2 (by
        simpa only [Protocol.HealConfig.opening_slot, p] using hopen)
    have hround : (p + 1) / S.hc.R = r := by
      simpa only [p, Protocol.HealConfig.round_of] using
        Proofs.HealingLemmas.round_of_opening_succ S.hc r
    rw [hround] at hdiv
    exact hdiv
  have hr : 0 < r := hcutpos.trans_le hroundCut
  have hspan : base ≤ r - S.hc.η_SG := Nat.le_sub_of_add_le hroundCut
  have hbasePred : base ≤ r - 1 :=
    hspan.trans (Nat.sub_le_sub_left S.hc.η_SG_ge_one r)
  have hroundT : S.hc.round_of (S.E.slotOf t) = r := by
    simpa only [t, ← opening_confirmation_time_eq_action S r,
      Proofs.Optimistic.slotOf_confirmation_time] using
        Proofs.HealingLemmas.round_of_opening_succ S.hc r
  have hreadRound : S.hc.round_of read.st.core.s = r := by
    simpa only [read, p, confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      t, ← opening_confirmation_time_eq_action S r,
      Proofs.Optimistic.slotOf_confirmation_time] using
        Proofs.HealingLemmas.round_of_opening_succ S.hc r
  have hdomain : domain S.E S.hc r .g1 < t := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    change Protocol.proposal_time S.E p < t
    dsimp only [t]
    rw [← opening_confirmation_time_eq_action S r]
    exact (proposal_time_mono S.E (Nat.le_succ p)).trans_lt
      (proposal_time_succ_lt_confirmation_time S.E p)
  have htop : t ≤ opening S.E S.hc (r + 1) := by
    simpa only [NamedOutageClosure.clockRoundAt, hroundT] using
      (NamedOutageClosure.clockRound_lt_opening_succ S t).le
  have hdomainHor : domain S.E S.hc r .g1 ≤ rho.horizon :=
    hdomain.le.trans hactHor
  have hreadMin : min (S.a (base + S.hc.η_SG))
      (Protocol.vote_time S.E start) ≤ t := by
    exact (min_le_left _ _).trans (Assembly.a_mono S hroundCut)
  have hnextVote : t ≤ Protocol.vote_time S.E (q + 1) := by
    have ha : S.a r = Protocol.support_cutoff S.E q := by
      simpa only [q, p] using Protocol.a_eq_support_cutoff_succ S.hc S.E r
    change S.a r ≤ Protocol.vote_time S.E (q + 1)
    rw [ha]
    exact ((support_cutoff_lt_view_freeze S.E q).trans
      (view_freeze_lt_vote_time_succ S.E q)).le
  have hfg : Block.Preceq
      (Protocol.get_fg_root read.st.core.toHealing.toFG)
      (voterHeadAt S rho x q) := by
    simpa only [read, t, p, confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      preparedV4_actionReadFGRoot_preceq_head
        S adm hcom hboot hawake hfinality hhor hd hupper hreadMin
          hnextVote hv hx
  rcases confirmationAnchorAt_cases S rho v p with
    hanchorFG | ⟨raw, A, hframe, hactive, hanchorA⟩
  · rw [show Protocol.get_sg_root_with
        (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
        S.E S.hc (actionStoreAt S rho v r).toHealing
        (S.hc.round_of (actionStoreAt S rho v r).s) =
        Protocol.get_fg_root read.st.core.toHealing.toFG by
          rw [show Protocol.get_sg_root_with
              (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
              S.E S.hc (actionStoreAt S rho v r).toHealing
              (S.hc.round_of (actionStoreAt S rho v r).s) =
            namedConfirmationAnchor S read by
              simpa only [read, p] using
                actionAnchor_eq_openingConfirmationAnchor_core S rho v r]
          simpa only [read, confirmationAnchorAt] using hanchorFG]
    exact hfg
  · have hAraw : Block.Preceq A raw := by
      unfold activePrefix at hactive
      exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
    have hframeR : (DecoupledConsensusModel.Protocol.readFrame
        read.cache read.st.core.toHealing r).g1 = some (some raw) := by
      simpa only [read, hreadRound] using hframe
    have hgrade := WeakSG.phaseGrade_of_preparedFrame_g1
      S rho adm v hv r hr t hroundT hdomain htop hdomainHor
        (raw := raw) (by
          simpa only [read, confirmationInputRead,
            NamedActionReads.confirmationReadAt, t, p] using hframeR)
    have hpostEarly : S.E.t_GST ≤ early S.E S.hc r .g2 := by
      exact hboot.basePost.trans (Assembly.a_mono S hbasePred) |>.trans
        (le_add_of_nonneg_right S.E.Δ_pos.le) |>.trans
          (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
            (Nat.sub_lt hr (by decide)))
    have hdelivery : TwoCutoffDelivery S rho r :=
      twoCutoffDelivery_of_core S adm hpostEarly
    have hprevHor : S.a (r - 1) ≤ rho.horizon := by
      have hprev : S.a (r - 1) + S.E.Δ ≤ early S.E S.hc r .g1 :=
        (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
          (Nat.sub_lt hr (by decide))).trans
          (NamedOutageClosure.q10_early_g2_le_early_g1 S r)
      exact (le_add_of_nonneg_right S.E.Δ_pos.le).trans
        (hprev.trans ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
          S r).trans hdomainHor))
    have hslot := SettledBootstrapPreparedV4.protectedVoteSlots_core
      S adm hcom hboot hawake hfinality hhor q hd hupper
    have hcarrier := relativeGradeCarrierAt_of_awakeWindowMajority
      S adm hr (hawake r hroundCut hprevHor) (p := .g1) (by
        intro y hy u hu k hk huk
        have hklt : k < r := mem_latestWindow_lt hk
        have hbaseK : base ≤ k :=
          hspan.trans (WeakSG.mem_latestWindow_lower_bound hk)
        have hdeadline : S.a k + S.E.Δ ≤ early S.E S.hc r .g1 :=
          (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt).trans
            (NamedOutageClosure.q10_early_g2_le_early_g1 S r)
        have hactionTime : S.a k < Protocol.vote_time S.E (q + 1) :=
          (Int.lt_add_of_pos_right _ S.E.Δ_pos).trans_le
            (hdeadline.trans
              ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                S r).trans (hdomain.le.trans hnextVote)))
        have hem := honest_emits_exact_actionAttestationAt_of_awake S
          adm.toNamedScheduleWellFormed hu k huk (by
            exact (le_add_of_nonneg_right S.E.Δ_pos.le).trans
              (hdeadline.trans
                ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                  S r).trans hdomainHor)))
        have hAhead : Block.Preceq (actionSGBlockAt S rho u k)
            (voterHeadAt S rho x q) := by
          by_cases hold : k < base + S.hc.η_SG
          · exact Block.preceq_trans (hboot.sgBoot k hbaseK hold u hu hem)
              (hslot.1.heads x hx)
          · exact (SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
              S adm hcom hboot hawake hfinality hhor hd hupper hx
                k (Nat.le_of_not_gt hold) hactionTime).1 u hu hem
        have hfgY := preparedV4_actionReadFGRoot_preceq_head
          S adm hcom hboot hawake hfinality hhor hd hupper hreadMin
            hnextVote hy hx
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
            (voterHeadAt S rho x q) :=
          Block.preceq_trans hFmonoY (Block.preceq_trans hFrootY hfgY)
        exact NamedOutageClosure.honestRoundVote_interpreted_at_reader_of_twoCutoff_compatible_after
          S rho adm hboot.basePost hdelivery r k hbaseK .g1 hk y hy
            hdomainHor hdeadline
            ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u k).mpr
              ⟨hu, actionAttestationAt S rho u k,
                (actionAttestationAt_shape S rho u k).1,
                (actionAttestationAt_shape S rho u k).2.1, hem⟩)
            (Block.compatible_of_preceq_common hFheadY hAhead))
    obtain ⟨k, hk, u, hu, hemit, hraw⟩ := hcarrier v hv raw
      (by simpa only [PhaseGrades.phaseGrade] using hgrade)
    have hklt : k < r := mem_latestWindow_lt hk
    have hbaseK : base ≤ k :=
      hspan.trans (WeakSG.mem_latestWindow_lower_bound hk)
    have hactionTime : S.a k < Protocol.vote_time S.E (q + 1) := by
      calc
        S.a k < S.a k + S.E.Δ := Int.lt_add_of_pos_right _ S.E.Δ_pos
        _ ≤ early S.E S.hc r .g2 :=
          NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt
        _ ≤ early S.E S.hc r .g1 :=
          NamedOutageClosure.q10_early_g2_le_early_g1 S r
        _ ≤ domain S.E S.hc r .g1 :=
          NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1 S r
        _ < t := hdomain
        _ ≤ Protocol.vote_time S.E (q + 1) := hnextVote
    have hrawHead : Block.Preceq raw (voterHeadAt S rho x q) := by
      by_cases hold : k < base + S.hc.η_SG
      · exact Block.preceq_trans hraw
          (Block.preceq_trans (hboot.sgBoot k hbaseK hold u hu hemit)
            (hslot.1.heads x hx))
      · exact Block.preceq_trans hraw
          ((SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
            S adm hcom hboot hawake hfinality hhor hd hupper hx
              k (Nat.le_of_not_gt hold) hactionTime).1 u hu hemit)
    rw [show Protocol.get_sg_root_with
        (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
        S.E S.hc (actionStoreAt S rho v r).toHealing
        (S.hc.round_of (actionStoreAt S rho v r).s) = A by
      rw [show Protocol.get_sg_root_with
          (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
          S.E S.hc (actionStoreAt S rho v r).toHealing
          (S.hc.round_of (actionStoreAt S rho v r).s) =
        namedConfirmationAnchor S read by
          simpa only [read, p] using
            actionAnchor_eq_openingConfirmationAnchor_core S rho v r]
      simpa only [read, confirmationAnchorAt] using hanchorA]
    exact Block.preceq_trans hAraw hrawHead


private theorem preparedV4_defaultActionAnchor_preceq_head
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start last : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    {r : Round} (hd : start ≤ S.hc.opening_slot r + 1)
    (hupper : S.hc.opening_slot r + 1 ≤ last + 1)
    (hactHor : S.a r ≤ rho.horizon)
    {v x : V} (hv : v ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq
      (Protocol.get_sg_root S.E S.hc
        (rho.storeBeforeTime S v (S.a r)).toHealing
        (S.hc.round_of (S.hc.opening_slot r + 1)))
      (voterHeadAt S rho x (S.hc.opening_slot r + 1)) := by
  let q := S.hc.opening_slot r + 1
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hcutpos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hround : base + S.hc.η_SG ≤ S.hc.round_of q := by
    change base + S.hc.η_SG ≤ q / S.hc.R
    exact (Nat.le_div_iff_mul_le hRpos).2 (hboot.settled.trans hd)
  have hspan : base ≤ S.hc.round_of q - S.hc.η_SG :=
    Nat.le_sub_of_add_le hround
  have hslot := SettledBootstrapPreparedV4.protectedVoteSlots_core
    S adm hcom hboot hawake hfinality hhor q hd (by
      simpa only [q] using hupper)
  have hlo : Protocol.vote_time S.E q ≤ S.a r :=
    (next_vote_time_lt_action S r).le
  have hhi : S.a r ≤ Protocol.vote_time S.E (q + 1) := by
    rw [show S.a r = Protocol.support_cutoff S.E q by
      simpa only [q] using Protocol.a_eq_support_cutoff_succ S.hc S.E r]
    exact ((support_cutoff_lt_view_freeze S.E q).trans
      (view_freeze_lt_vote_time_succ S.E q)).le
  have hproposalLo : Protocol.proposal_time S.E q ≤ S.a r :=
    (proposal_time_lt_vote_time S.E q).le.trans hlo
  have hsource (k : Round) (hk : k < S.hc.round_of q) :
      S.a k < Protocol.vote_time S.E (q + 1) :=
    (Int.lt_add_of_pos_right _ S.E.Δ_pos).trans_le
      ((preparedV4_sgSource_deadline_le_proposal S hk).trans
        (hproposalLo.trans hhi))
  have hmajority := honestWeightMajority_of_finiteWindowsFrom
    S hawake hcutpos (hboot.settled.trans hd) (by simpa only [q] using hupper) hhor
  apply WeakSG.getSgRoot_preceq_of_windowHistory_at_read
    S adm hmajority hspan ?_ hv (time := S.a r)
      (pre := (rho.storeBeforeTime S v (S.a r)).core) rfl ?_ ?_
  · intro k hk hklt u hu hemit
    by_cases hold : k < base + S.hc.η_SG
    · exact Block.preceq_trans (hboot.sgBoot k hk hold u hu hemit)
        (hslot.1.heads x hx)
    · exact (SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hhor hd (by simpa only [q] using hupper)
          hx k (Nat.le_of_not_gt hold) (hsource k hklt)).1 u hu hemit
  · intro hr
    have hprevious : S.a (S.hc.round_of q - 1) ≤ rho.horizon :=
      (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
        ((preparedV4_sgSource_deadline_le_proposal S
          (Nat.sub_lt hr (by decide : 0 < (1 : Nat)))).trans
            (hproposalLo.trans hactHor))
    exact WeakSG.sgWindowMajority_stateBeforeTime S adm hv rfl
      (hawake _ hround hprevious)
      (fun k hk => hboot.basePost.trans
        (Assembly.a_mono S (hspan.trans
          (WeakSG.mem_latestWindow_lower_bound hk))))
      (fun k hk => (preparedV4_sgSource_deadline_le_proposal S
        (mem_latestWindow_lt hk)).trans hproposalLo)
      hactHor
  · have hread : min (S.a (base + S.hc.η_SG))
        (Protocol.vote_time S.E start) ≤ S.a r :=
      (min_le_right _ _).trans ((vote_time_mono_slots S.E hd).trans hlo)
    exact preparedV4_actionReadFGRoot_preceq_head
      S adm hcom hboot hawake hfinality hhor hd
        (by simpa only [q] using hupper) (t := S.a r) hread hhi hv hx
private theorem protectedBlock_preceq_defaultActionHead_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {q : Slot} {v : V} {r : Round}
    (ha : S.a r = Protocol.support_cutoff S.E q)
    {B : Block V}
    (hcone :
      let ast := actionStoreAt S rho v r
      let raw := ast.pool q
      let support := raw.filter (fun u => Protocol.resolved ast.T u = true)
      ConeSupport S.E ast.T raw support raw q rho.honest
        (fun X => Block.Preceq B X))
    (hcompat : Block.compatible
      (healAnchor S.E S.hc (actionStoreAt S rho v r).toHealing) B = true)
    (hpath : Block.Preceq
        (healAnchor S.E S.hc (actionStoreAt S rho v r).toHealing) B →
      ∀ C : Block V,
        Block.Preceq
            (healAnchor S.E S.hc (actionStoreAt S rho v r).toHealing) C →
          C ≠ healAnchor S.E S.hc (actionStoreAt S rho v r).toHealing →
          Block.Preceq C B →
          C ∈ Protocol.get_filtered_block_tree
            (actionStoreAt S rho v r).toHealing.toFG) :
    Block.Preceq B (actionHead S.E S.hc (actionStoreAt S rho v r).toHealing) := by
  let ast := actionStoreAt S rho v r
  let raw := ast.pool q
  let support := raw.filter (fun u => Protocol.resolved ast.T u = true)
  have hslot : ast.s = q := by
    simpa only [ast] using actionStoreAt_slot_of_action_eq_cutoff S rho v r q ha
  have hvalid0 := voteSetValid_pool_stateBeforeTime
    S adm.toNamedScheduleWellFormed v (S.a r) q
  have hvalid : Protocol.VoteSetValid S.E q raw := by
    simpa only [ast, raw, actionStoreAt_pool S rho v r q] using hvalid0
  have hout : Block.Preceq B
      (Protocol.get_head_hc S.E S.hc ast.toHealing raw support q) := by
    rw [Proofs.Optimistic.get_head_split]
    exact goldfish_fork_choice_captures_supporter_majority
      S.E ast.σ ast.h_max ast.T
        (Protocol.get_filtered_block_tree ast.toHealing.toFG) ast.s
        raw support q (ConeSupport.sub hcone)
        (supporterMajority_of_cone S.E hcone hvalid) hcompat hpath
  simpa only [actionHead, ast, raw, support,
    Protocol.Store.toHealing, hslot] using hout
private theorem defaultActionPath_to_ancestor_of_candidate_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {r : Round} {B E : Block V}
    (hE : E ∈ Protocol.get_filtered_block_tree
      (actionStoreAt S rho v r).toHealing.toFG)
    (hBE : Block.Preceq B E) :
    ∀ C : Block V,
      Block.Preceq
          (healAnchor S.E S.hc (actionStoreAt S rho v r).toHealing) C →
        C ≠ healAnchor S.E S.hc (actionStoreAt S rho v r).toHealing →
        Block.Preceq C B →
        C ∈ Protocol.get_filtered_block_tree
          (actionStoreAt S rho v r).toHealing.toFG := by
  let pre := rho.storeBeforeTime S v (S.a r)
  let ast := actionStoreAt S rho v r
  have hpc : ParentClosed pre.core :=
    Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho (S.a r) v
  have hFJpre : Block.Preceq pre.F pre.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      S rho (S.a r) v
  have hFJ : Block.Preceq ast.F ast.J := by
    simpa only [ast, pre] using hFJpre
  intro C hAC _ hCB
  have hET : E ∈ ast.T := Proofs.Records.get_filtered_block_tree_subset _ hE
  have hETpre : E ∈ pre.T := by
    rw [← actionStoreAt_T S rho v r]
    exact hET
  have hCTpre : C ∈ pre.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff pre.core).mp hpc).2 C E hETpre
      (Block.preceq_trans hCB hBE)
  have hCT : C ∈ ast.T := by
    rw [actionStoreAt_T S rho v r]
    exact hCTpre
  apply Proofs.Records.mem_filtered_of_preceq
    (st := ast.toHealing.toFG) hFJ hE hCT
      (Block.preceq_trans hCB hBE)
  exact Block.preceq_trans
    (StoreFinality.get_fg_root_preceq_get_sg_root S.E S.hc ast.st.core) hAC

set_option maxHeartbeats 400000 in
/-- A common ancestor of the current honest prepared vote heads is below the
actual prepared action head after the V4 cut. -/
theorem SettledBootstrapPreparedV4.commonAncestor_preceq_actionHead_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start last : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    {r : Round} (hd : start ≤ S.hc.opening_slot r + 1)
    (hupper : S.hc.opening_slot r + 1 ≤ last + 1)
    (hactHor : S.a r ≤ rho.horizon) {v : V} (hv : v ∈ rho.honest)
    {B : Block V}
    (hheads : ∀ x ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho x (S.hc.opening_slot r + 1))) :
    Block.Preceq B
      (actionHead S.E S.hc (actionStoreAt S rho v r).toHealing) := by
  let p := S.hc.opening_slot r
  let q := p + 1
  let ast := actionStoreAt S rho v r
  let pre := rho.storeBeforeTime S v (S.a r)
  let R := Protocol.get_fg_root ast.toHealing.toFG
  have hqpos : 0 < q := Nat.zero_lt_succ _
  have ha : S.a r = Protocol.support_cutoff S.E q := by
    simpa only [q, p] using Protocol.a_eq_support_cutoff_succ S.hc S.E r
  have hcutHor : Protocol.support_cutoff S.E q ≤ rho.horizon := by
    rw [← ha]
    exact hactHor
  have hvoteHor : Protocol.vote_time S.E q ≤ rho.horizon := by
    have hvoteCut : Protocol.vote_time S.E q ≤
        Protocol.support_cutoff S.E q := by
      rw [← Proofs.Optimistic.vote_time_add_delta]
      exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
    exact hvoteCut.trans hcutHor
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hcutpos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hroundCut : base + S.hc.η_SG ≤ r := by
    have hopen : S.hc.opening_slot (base + S.hc.η_SG) ≤ p + 1 := by
      simpa only [q, p] using hboot.settled.trans hd
    have hdiv : base + S.hc.η_SG ≤ (p + 1) / S.hc.R :=
      (Nat.le_div_iff_mul_le hRpos).2 (by
        simpa only [Protocol.HealConfig.opening_slot, p] using hopen)
    have hround : (p + 1) / S.hc.R = r := by
      simpa only [p, Protocol.HealConfig.round_of] using
        Proofs.HealingLemmas.round_of_opening_succ S.hc r
    rw [hround] at hdiv
    exact hdiv
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E q :=
    hboot.basePost.trans ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      ((action_add_delta_le_openingProposal_of_round_lt S
        (Nat.lt_of_succ_le ((Nat.add_le_add_left S.hc.η_SG_ge_one base).trans
          hroundCut))).trans
        ((proposal_time_mono S.E (Nat.le_succ p)).trans
          (proposal_time_lt_vote_time S.E q).le)))
  have hupper' : q ≤ last + 1 := by simpa only [q, p] using hupper
  have hreadMin : min (S.a (base + S.hc.η_SG))
      (Protocol.vote_time S.E start) ≤ S.a r :=
    (min_le_left _ _).trans (Assembly.a_mono S hroundCut)
  have hnextVote : S.a r ≤ Protocol.vote_time S.E (q + 1) := by
    rw [ha]
    exact ((support_cutoff_lt_view_freeze S.E q).trans
      (view_freeze_lt_vote_time_succ S.E q)).le
  have hsg : ∀ x ∈ rho.honest, Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract ast.cache) S.E S.hc ast.toHealing
        (S.hc.round_of ast.s))
      (voterHeadAt S rho x q) := by
    intro x hx
    simpa only [ast, q, p] using preparedV4_actionAnchor_preceq_head
      S adm hcom hboot hawake hfinality hhor hd hupper hactHor hv hx
  have hrootHeads : ∀ x ∈ rho.honest,
      Block.Preceq R (voterHeadAt S rho x q) := by
    intro x hx
    have hroot := preparedV4_actionReadFGRoot_preceq_head
      S adm hcom hboot hawake hfinality hhor hd hupper'
        hreadMin hnextVote hv hx
    simpa only [R, ast, pre] using hroot
  have hnamesRoot : NamedHonestVotesCone S rho q
      (fun X => Block.Preceq R X) := by
    intro x hx hcommittee
    obtain ⟨X, hXe, hXrun, hXemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S adm hx hqpos hcommittee hvoteHor
    exact ⟨X, by simpa only [hXe] using hrootHeads x hx, hXrun, hXemit⟩
  have hnames : NamedHonestVotesCone S rho q
      (fun X => Block.Preceq B X) := by
    intro x hx hcommittee
    obtain ⟨X, hXe, hXrun, hXemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S adm hx hqpos hcommittee hvoteHor
    exact ⟨X, by simpa only [hXe, q, p] using hheads x hx, hXrun, hXemit⟩
  have hresolve := headsResolveIn_actionStore_core
    S adm hv hpost hcutHor ha (B := R) (Block.preceq_self R) hnamesRoot
  have hcone := coneSupport_actionStoreAt_after_core
    S adm hcom hqpos hpost hcutHor hnames hv ha hresolve
  have hpositive : 0 < ((S.E.committee q) ∩ rho.honest).card := by
    have hc := hcom q
    omega
  obtain ⟨x, hxq⟩ := Finset.card_pos.mp hpositive
  have hxc : x ∈ S.E.committee q := (Finset.mem_inter.mp hxq).1
  have hx : x ∈ rho.honest := (Finset.mem_inter.mp hxq).2
  obtain ⟨X, hXe, hXrun, hXemit⟩ :=
    WeakGoldfish.voterHead_runBlock_and_emits
      S adm hx hqpos hxc hvoteHor
  have hXhead : HonestHead S rho q X.erase :=
    ⟨x, hx, hxc, ⟨X, rfl, hXrun⟩, hXemit⟩
  have hfind : Block.find? ast.T X.erase.root = some X.erase := by
    simpa only [ast] using (hresolve X.erase hXhead).1
  have hXmem : X.erase ∈ ast.T := Proofs.HealingLemmas.find?_mem hfind
  have hXmemPre : X.erase ∈ pre.core.T := by
    have hT : ast.T = (rho.storeBeforeTime S v (S.a r)).T := by
      simpa only [ast] using actionStoreAt_T S rho v r
    rw [hT] at hXmem
    simpa only [pre] using hXmem
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
      S rho (S.a r) v hXmemPre
  have hDrun : RunBlock S rho D := by
    obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
      S rho adm.toNamedScheduleWellFormed.sorted (S.a r)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [← hi]
    exact hDbody
  have hDX : D = X := by
    apply adm.toNamedRootCollisionFree.root_injective
      D X hDrun hXrun D X (Or.inl (Proofs.NamedAncestry.named_self D))
        (Or.inr (Proofs.NamedAncestry.named_self X))
    rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root X, hDerase]
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
    S rho (S.a r) v X (by simpa only [← hDX] using hDbody)
  have hbandPre : pre.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg X).h := by
    by_cases hlarge : 1 < pre.core.h_max
    · have hmajority := honestWeightMajority_of_finiteWindowsFrom
        S hawake hcutpos (hboot.settled.trans hd) hupper' hhor
      obtain ⟨a, ta, C, K, haK, hemit, hat, hrow, hfgK, -, -, hKentry,
          hKrun, hKheight⟩ := frontier_confirmationWitness_core_entry
        S adm hmajority (v := v) (time := S.a r) (by
          simpa only [pre] using hlarge)
      have hPhead : Block.Preceq P.erase (voterHeadAt S rho x q) :=
        (SettledBootstrapPreparedV4.protectedVoteSlots_core
          S adm hcom hboot hawake hfinality hhor q hd hupper').1.heads x hx
      have hPX : Block.Preceq P.erase X.erase := by
        rw [hXe]
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
        · have hbound := hboot.oldRows a ta _ haK hemit hpre hrow
          have hbound' : pre.core.h_max - 1 ≤ cap := by
            simpa only [pre] using hbound
          exact hbound'.trans (hboot.heightCap.trans hPheight)
        · have hKP := hboot.fgAll a ta _
              (Protocol.derive_named S.E S.cfg K).T_h
              haK hemit hrow (Nat.le_of_not_gt hpre) hold hfgK
          rw [hKentry] at hKP
          have hKX : Block.Preceq K.erase X.erase := Block.preceq_trans hKP hPX
          obtain ⟨K', hK'X, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift X hKX
          have hK'run : RunBlock S rho K' :=
            Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hK'X
          have hK'eq : K' = K := by
            apply adm.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
              K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
                (Or.inr (Proofs.NamedAncestry.named_self K))
            rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
          have hKheight' : (Protocol.derive_named S.E S.cfg K).h =
              pre.core.h_max - 1 := by simpa only [pre] using hKheight
          rw [← hKheight']
          apply Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
          rw [← hK'eq]
          exact hK'X
      · have htime : S.a a.round < Protocol.vote_time S.E (q + 1) := by
          simpa only [(emits_attest_shape S hemit).2] using hat.trans_le hnextVote
        have hsource :=
          ((SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
            S adm hcom hboot hawake hfinality hhor hd hupper' hx
              a.round (Nat.le_of_not_gt hold) htime).2 a.val_index haK).2 _ hfgK
        have hKX : Block.Preceq K.erase X.erase := by
          rw [← hKentry, hXe]
          simpa only [voteDutyHead] using hsource
        obtain ⟨K', hK'X, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift X hKX
        have hK'run : RunBlock S rho K' :=
          Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hK'X
        have hK'eq : K' = K := by
          apply adm.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
            K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
              (Or.inr (Proofs.NamedAncestry.named_self K))
          rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
        have hKheight' : (Protocol.derive_named S.E S.cfg K).h =
            pre.core.h_max - 1 := by simpa only [pre] using hKheight
        rw [← hKheight']
        apply Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
        rw [← hK'eq]
        exact hK'X
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hlarge)]
      exact Nat.zero_le _
  have hheight : pre.core.h_max - 1 ≤ (pre.core.σ X.erase).h := by
    have hviewHeight : (pre.core.σ X.erase).h =
        (Protocol.derive_named S.E S.cfg X).h := by
      simpa only [pre] using congrArg (fun st => st.h) hview
    rw [hviewHeight]
    exact hbandPre
  have hrootX : Block.Preceq R X.erase := by
    simpa only [hXe] using hrootHeads x hx
  have hFJ : Block.Preceq pre.core.F pre.core.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      S rho (S.a r) v
  have hFX : Block.Preceq pre.core.F X.erase := by
    have hFroot : Block.Preceq pre.core.F R :=
      Proofs.Records.preceq_get_fg_root_of_F (st := pre.core.toHealing.toFG) hFJ
    exact Block.preceq_trans hFroot hrootX
  have hcandidate : X.erase ∈
      Protocol.get_filtered_block_tree ast.toHealing.toFG := by
    rw [actionStoreAt_filteredTree S rho v r]
    change X.erase ∈ Protocol.get_filtered_block_tree pre.core.toHealing.toFG
    simp only [Protocol.get_filtered_block_tree,
      Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hXmemPre, hFX⟩, X.erase, hXmemPre,
      Block.preceq_self _, hheight⟩, hrootX⟩
  have hBX : Block.Preceq B X.erase := by
    simpa only [hXe, q, p] using hheads x hx
  have hdefaultAnchor := preparedV4_defaultActionAnchor_preceq_head
    S adm hcom hboot hawake hfinality hhor hd hupper hactHor hv hx
  have hdefaultAnchor' : Block.Preceq
      (healAnchor S.E S.hc ast.toHealing) (voterHeadAt S rho x q) := by
    rw [preparedV4_actionAnchor_eq_readSgRoot S rho v ha]
    simpa only [q, p] using hdefaultAnchor
  apply protectedBlock_preceq_defaultActionHead_core
    S adm ha hcone
      (Block.compatible_of_preceq_common hdefaultAnchor' (by
        simpa only [q, p] using hheads x hx))
  intro _
  exact defaultActionPath_to_ancestor_of_candidate_core
    S adm hcandidate hBX

set_option maxHeartbeats 400000 in
/-- A common ancestor of the current honest prepared vote heads is below the
actual prepared action head after the V4 cut. -/
theorem SettledBootstrapPreparedV4.commonAncestor_preceq_actionHeadAt_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start last : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    {r : Round} (hd : start ≤ S.hc.opening_slot r + 1)
    (hupper : S.hc.opening_slot r + 1 ≤ last + 1)
    (hactHor : S.a r ≤ rho.horizon) {v : V} (hv : v ∈ rho.honest)
    {B : Block V}
    (hheads : ∀ x ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho x (S.hc.opening_slot r + 1))) :
    Block.Preceq B (actionHeadAt S rho v r) := by
  let p := S.hc.opening_slot r
  let q := p + 1
  let ast := actionStoreAt S rho v r
  let pre := rho.storeBeforeTime S v (S.a r)
  let R := Protocol.get_fg_root ast.toHealing.toFG
  have hqpos : 0 < q := Nat.zero_lt_succ _
  have ha : S.a r = Protocol.support_cutoff S.E q := by
    simpa only [q, p] using Protocol.a_eq_support_cutoff_succ S.hc S.E r
  have hcutHor : Protocol.support_cutoff S.E q ≤ rho.horizon := by
    rw [← ha]
    exact hactHor
  have hvoteHor : Protocol.vote_time S.E q ≤ rho.horizon := by
    have hvoteCut : Protocol.vote_time S.E q ≤
        Protocol.support_cutoff S.E q := by
      rw [← Proofs.Optimistic.vote_time_add_delta]
      exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
    exact hvoteCut.trans hcutHor
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hcutpos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hroundCut : base + S.hc.η_SG ≤ r := by
    have hopen : S.hc.opening_slot (base + S.hc.η_SG) ≤ p + 1 := by
      simpa only [q, p] using hboot.settled.trans hd
    have hdiv : base + S.hc.η_SG ≤ (p + 1) / S.hc.R :=
      (Nat.le_div_iff_mul_le hRpos).2 (by
        simpa only [Protocol.HealConfig.opening_slot, p] using hopen)
    have hround : (p + 1) / S.hc.R = r := by
      simpa only [p, Protocol.HealConfig.round_of] using
        Proofs.HealingLemmas.round_of_opening_succ S.hc r
    rw [hround] at hdiv
    exact hdiv
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E q :=
    hboot.basePost.trans ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      ((action_add_delta_le_openingProposal_of_round_lt S
        (Nat.lt_of_succ_le ((Nat.add_le_add_left S.hc.η_SG_ge_one base).trans
          hroundCut))).trans
        ((proposal_time_mono S.E (Nat.le_succ p)).trans
          (proposal_time_lt_vote_time S.E q).le)))
  have hupper' : q ≤ last + 1 := by simpa only [q, p] using hupper
  have hreadMin : min (S.a (base + S.hc.η_SG))
      (Protocol.vote_time S.E start) ≤ S.a r :=
    (min_le_left _ _).trans (Assembly.a_mono S hroundCut)
  have hnextVote : S.a r ≤ Protocol.vote_time S.E (q + 1) := by
    rw [ha]
    exact ((support_cutoff_lt_view_freeze S.E q).trans
      (view_freeze_lt_vote_time_succ S.E q)).le
  have hsg : ∀ x ∈ rho.honest, Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract ast.cache) S.E S.hc ast.toHealing
        (S.hc.round_of ast.s))
      (voterHeadAt S rho x q) := by
    intro x hx
    simpa only [ast, q, p] using preparedV4_actionAnchor_preceq_head
      S adm hcom hboot hawake hfinality hhor hd hupper hactHor hv hx
  have hrootHeads : ∀ x ∈ rho.honest,
      Block.Preceq R (voterHeadAt S rho x q) := by
    intro x hx
    have hroot := preparedV4_actionReadFGRoot_preceq_head
      S adm hcom hboot hawake hfinality hhor hd hupper'
        hreadMin hnextVote hv hx
    simpa only [R, ast, pre] using hroot
  have hnamesRoot : NamedHonestVotesCone S rho q
      (fun X => Block.Preceq R X) := by
    intro x hx hcommittee
    obtain ⟨X, hXe, hXrun, hXemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S adm hx hqpos hcommittee hvoteHor
    exact ⟨X, by simpa only [hXe] using hrootHeads x hx, hXrun, hXemit⟩
  have hnames : NamedHonestVotesCone S rho q
      (fun X => Block.Preceq B X) := by
    intro x hx hcommittee
    obtain ⟨X, hXe, hXrun, hXemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S adm hx hqpos hcommittee hvoteHor
    exact ⟨X, by simpa only [hXe, q, p] using hheads x hx, hXrun, hXemit⟩
  have hresolve := headsResolveIn_actionStore_core
    S adm hv hpost hcutHor ha (B := R) (Block.preceq_self R) hnamesRoot
  have hcone := coneSupport_actionStoreAt_after_core
    S adm hcom hqpos hpost hcutHor hnames hv ha hresolve
  have hpositive : 0 < ((S.E.committee q) ∩ rho.honest).card := by
    have hc := hcom q
    omega
  obtain ⟨x, hxq⟩ := Finset.card_pos.mp hpositive
  have hxc : x ∈ S.E.committee q := (Finset.mem_inter.mp hxq).1
  have hx : x ∈ rho.honest := (Finset.mem_inter.mp hxq).2
  obtain ⟨X, hXe, hXrun, hXemit⟩ :=
    WeakGoldfish.voterHead_runBlock_and_emits
      S adm hx hqpos hxc hvoteHor
  have hXhead : HonestHead S rho q X.erase :=
    ⟨x, hx, hxc, ⟨X, rfl, hXrun⟩, hXemit⟩
  have hfind : Block.find? ast.T X.erase.root = some X.erase := by
    simpa only [ast] using (hresolve X.erase hXhead).1
  have hXmem : X.erase ∈ ast.T := Proofs.HealingLemmas.find?_mem hfind
  have hXmemPre : X.erase ∈ pre.core.T := by
    have hT : ast.T = (rho.storeBeforeTime S v (S.a r)).T := by
      simpa only [ast] using actionStoreAt_T S rho v r
    rw [hT] at hXmem
    simpa only [pre] using hXmem
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
      S rho (S.a r) v hXmemPre
  have hDrun : RunBlock S rho D := by
    obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
      S rho adm.toNamedScheduleWellFormed.sorted (S.a r)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [← hi]
    exact hDbody
  have hDX : D = X := by
    apply adm.toNamedRootCollisionFree.root_injective
      D X hDrun hXrun D X (Or.inl (Proofs.NamedAncestry.named_self D))
        (Or.inr (Proofs.NamedAncestry.named_self X))
    rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root X, hDerase]
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
    S rho (S.a r) v X (by simpa only [← hDX] using hDbody)
  have hbandPre : pre.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg X).h := by
    by_cases hlarge : 1 < pre.core.h_max
    · have hmajority := honestWeightMajority_of_finiteWindowsFrom
        S hawake hcutpos (hboot.settled.trans hd) hupper' hhor
      obtain ⟨a, ta, C, K, haK, hemit, hat, hrow, hfgK, -, -, hKentry,
          hKrun, hKheight⟩ := frontier_confirmationWitness_core_entry
        S adm hmajority (v := v) (time := S.a r) (by
          simpa only [pre] using hlarge)
      have hPhead : Block.Preceq P.erase (voterHeadAt S rho x q) :=
        (SettledBootstrapPreparedV4.protectedVoteSlots_core
          S adm hcom hboot hawake hfinality hhor q hd hupper').1.heads x hx
      have hPX : Block.Preceq P.erase X.erase := by
        rw [hXe]
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
        · have hbound := hboot.oldRows a ta _ haK hemit hpre hrow
          have hbound' : pre.core.h_max - 1 ≤ cap := by
            simpa only [pre] using hbound
          exact hbound'.trans (hboot.heightCap.trans hPheight)
        · have hKP := hboot.fgAll a ta _
              (Protocol.derive_named S.E S.cfg K).T_h
              haK hemit hrow (Nat.le_of_not_gt hpre) hold hfgK
          rw [hKentry] at hKP
          have hKX : Block.Preceq K.erase X.erase := Block.preceq_trans hKP hPX
          obtain ⟨K', hK'X, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift X hKX
          have hK'run : RunBlock S rho K' :=
            Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hK'X
          have hK'eq : K' = K := by
            apply adm.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
              K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
                (Or.inr (Proofs.NamedAncestry.named_self K))
            rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
          have hKheight' : (Protocol.derive_named S.E S.cfg K).h =
              pre.core.h_max - 1 := by simpa only [pre] using hKheight
          rw [← hKheight']
          apply Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
          rw [← hK'eq]
          exact hK'X
      · have htime : S.a a.round < Protocol.vote_time S.E (q + 1) := by
          simpa only [(emits_attest_shape S hemit).2] using hat.trans_le hnextVote
        have hsource :=
          ((SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
            S adm hcom hboot hawake hfinality hhor hd hupper' hx
              a.round (Nat.le_of_not_gt hold) htime).2 a.val_index haK).2 _ hfgK
        have hKX : Block.Preceq K.erase X.erase := by
          rw [← hKentry, hXe]
          simpa only [voteDutyHead] using hsource
        obtain ⟨K', hK'X, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift X hKX
        have hK'run : RunBlock S rho K' :=
          Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hK'X
        have hK'eq : K' = K := by
          apply adm.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
            K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
              (Or.inr (Proofs.NamedAncestry.named_self K))
          rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
        have hKheight' : (Protocol.derive_named S.E S.cfg K).h =
            pre.core.h_max - 1 := by simpa only [pre] using hKheight
        rw [← hKheight']
        apply Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
        rw [← hK'eq]
        exact hK'X
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hlarge)]
      exact Nat.zero_le _
  have hheight : pre.core.h_max - 1 ≤ (pre.core.σ X.erase).h := by
    have hviewHeight : (pre.core.σ X.erase).h =
        (Protocol.derive_named S.E S.cfg X).h := by
      simpa only [pre] using congrArg (fun st => st.h) hview
    rw [hviewHeight]
    exact hbandPre
  have hrootX : Block.Preceq R X.erase := by
    simpa only [hXe] using hrootHeads x hx
  have hFJ : Block.Preceq pre.core.F pre.core.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      S rho (S.a r) v
  have hFX : Block.Preceq pre.core.F X.erase := by
    have hFroot : Block.Preceq pre.core.F R :=
      Proofs.Records.preceq_get_fg_root_of_F (st := pre.core.toHealing.toFG) hFJ
    exact Block.preceq_trans hFroot hrootX
  have hcandidate : X.erase ∈
      Protocol.get_filtered_block_tree ast.toHealing.toFG := by
    rw [actionStoreAt_filteredTree S rho v r]
    change X.erase ∈ Protocol.get_filtered_block_tree pre.core.toHealing.toFG
    simp only [Protocol.get_filtered_block_tree,
      Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hXmemPre, hFX⟩, X.erase, hXmemPre,
      Block.preceq_self _, hheight⟩, hrootX⟩
  have hBX : Block.Preceq B X.erase := by
    simpa only [hXe, q, p] using hheads x hx
  apply WeakAction.protectedBlock_preceq_actionHead_of_cone_compatible
    S adm ha hcone
      (Block.compatible_of_preceq_common (by
        simpa only [q, p] using hsg x hx) (by
        simpa only [q, p] using hheads x hx))
  intro _
  exact WeakAction.actionPath_to_ancestor_of_candidate
    S adm hcandidate hBX

#print axioms SettledBootstrapPreparedV4.commonAncestor_preceq_actionHeadAt_core

#print axioms SettledBootstrapPreparedV4.commonAncestor_preceq_actionHead_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
