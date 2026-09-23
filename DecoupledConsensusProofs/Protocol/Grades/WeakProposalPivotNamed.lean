module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakProposalCandidateNamed
public import DecoupledConsensusProofs.Execution.PreparedProtectedProposalPivot
public import DecoupledConsensusProofs.Execution.CommonAncestorBound

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Prepared protected weak-genesis proposal pivots -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic Statements
open Internal.NamedRecoveryRead Internal.PhaseGrades
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

namespace WeakGenesis

private theorem preparedVoterAnchor_preceq_voteDutyHead_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {last d : Slot} (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1)
    (hvoteHor : Protocol.vote_time S.E (d + 1) ≤ rho.horizon)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq (voterAnchorAt S rho w (d + 1))
      (voterHeadAt S rho x d) := by
  let s := d + 1
  let t := Protocol.vote_time S.E s
  let read := voteDutyRead S rho w s
  let r := S.hc.round_of s
  have hroundT : S.hc.round_of (S.E.slotOf t) = r := by
    simpa only [t, r, Proofs.Optimistic.slotOf_vote_time]
  have hreadRound : S.hc.round_of read.st.core.s = r := by
    simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.slotOf_vote_time, r, t]
  have hdomain : domain S.E S.hc r .g1 < t := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (proposal_time_mono S.E (Nat.div_mul_le_self s S.hc.R)).trans_lt
      (proposal_time_lt_vote_time S.E s)
  have htop : t ≤ opening S.E S.hc (r + 1) := by
    simpa only [NamedOutageClosure.clockRoundAt, hroundT] using
      (NamedOutageClosure.clockRound_lt_opening_succ S t).le
  have hdomainHor : domain S.E S.hc r .g1 ≤ rho.horizon :=
    hdomain.le.trans hvoteHor
  have hfg : Block.Preceq
      (Protocol.get_fg_root read.st.core.toHealing.toFG)
      (voterHeadAt S rho x d) := by
    simpa only [read, t, s, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      voteDutyHead] using
      fgRootAtRead_preceq_voteDutyHead_of_gstZero_named
        S h.core h.committees h.gstZero h.windows hhor hd hupper
          (t := t) (le_refl _) hw hx
  rcases voterAnchorAt_cases S rho w s with hanchorFG |
      ⟨raw, A, hframe, hactive, hanchorA⟩
  · rw [show voterAnchorAt S rho w s =
        Protocol.get_fg_root read.st.core.toHealing.toFG by
          simpa only [read] using hanchorFG]
    exact hfg
  · have hanchorA' : voterAnchorAt S rho w s = A := by
      simpa only [read] using hanchorA
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
        have hdomain0 : domain S.E S.hc 0 .g1 < t := by
          simpa only [hr0] using hdomain
        exact ne_of_gt hdomain0
      have hno := confirmationRead_g1_round_zero_no_root
        S h.core w t (by simpa only [hr0] using hroundT) htne (root := raw)
      exact False.elim (hno (by
        simpa only [read, voteDutyRead, t, hr0] using hframeR))
    · have hr : 0 < r := Nat.pos_of_ne_zero hr0
      have hgrade := WeakSG.phaseGrade_of_preparedFrame_g1
        S rho h.core w hw r hr t hroundT hdomain htop hdomainHor
          (raw := raw) (by
            simpa only [read, voteDutyRead, t] using hframeR)
      have hpostEarly : S.E.t_GST ≤ early S.E S.hc r .g2 := by
        rw [h.gstZero]
        exact (Proofs.HealingLemmas.a_nonneg S (r - 1)).trans
          (le_add_of_nonneg_right S.E.Δ_pos.le) |>.trans
            (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
              (Nat.sub_lt hr (by decide)))
      have hdelivery : TwoCutoffDelivery S rho r :=
        twoCutoffDelivery_of_core S h.core hpostEarly
      have hprevHor : S.a (r - 1) ≤ rho.horizon := by
        have hprev : S.a (r - 1) + S.E.Δ ≤ early S.E S.hc r .g1 :=
          (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
            (Nat.sub_lt hr (by decide))).trans
            (NamedOutageClosure.q10_early_g2_le_early_g1 S r)
        exact (le_add_of_nonneg_right S.E.Δ_pos.le).trans
          (hprev.trans ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
            S r).trans hdomainHor))
      have hcarrier := relativeGradeCarrierAt_of_awakeWindowMajority
        S h.core hr (h.windows r hr hprevHor) (p := .g1) (by
          intro y hy u hu k hk huk
          have hklt : k < r := mem_latestWindow_lt hk
          have hdeadline : S.a k + S.E.Δ ≤ early S.E S.hc r .g1 :=
            (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt).trans
              (NamedOutageClosure.q10_early_g2_le_early_g1 S r)
          have hactionTime : S.a k < Protocol.vote_time S.E s :=
            (Int.lt_add_of_pos_right _ S.E.Δ_pos).trans_le
              (hdeadline.trans
                ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                  S r).trans hdomain.le))
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
              (t := domain S.E S.hc r .g1) hdomain.le hy hx
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
              simpa only [Run.storeBeforeTime, voteDutyHead] using hfgY)
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
      obtain ⟨k, hk, u, hu, hemit, hraw⟩ := hcarrier w hw raw
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
          _ < t := hdomain
      exact Block.preceq_trans hAraw (Block.preceq_trans hraw
        ((actionSources_preceq_voteDutyHead_of_gstZero
          S h.core h.committees h.gstZero h.windows hhor hd hupper hx
            k hactionTime).1 u hu hemit))

/-- The later weak-genesis vote has one named protected pivot shared by the
prepared proposer and voter reads. -/
theorem exists_preparedProtectedProposalPivot_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {d : Slot} (hd : 1 ≤ d)
    (hhor : Protocol.confirmation_time S.E (d + 1) ≤ rho.horizon)
    (hprop : S.E.proposer (d + 1) ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest) :
    ∃ A : NamedBlock V, PreparedProtectedProposalPivot S rho d v A := by
  let s := d + 1
  let tp := Protocol.proposal_time S.E s
  let tv := Protocol.vote_time S.E s
  let p := S.E.proposer s
  let source := proposerReadAt S rho s
  let target := voteDutyRead S rho v s
  have hdPos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hp : p ∈ rho.honest := by simpa only [p, s] using hprop
  have hvoteHor : tv ≤ rho.horizon := by
    simpa only [tv] using (vote_time_le_confirmation_time S.E s).trans hhor
  have hproposalHor : tp ≤ rho.horizon := by
    exact (by simpa only [tp, tv] using
      (proposal_time_lt_vote_time S.E s).le.trans hvoteHor)
  have hvotePrev : Protocol.vote_time S.E d ≤ rho.horizon :=
    (vote_time_mono_slots S.E (Nat.le_succ d)).trans hvoteHor
  have hupper : d ≤ (d + 1) + 1 := Nat.le_add_right d 2
  let sourceAnchor := nodeAnchor S source (S.hc.round_of source.st.core.s)
  let targetAnchor := voterAnchorAt S rho v s
  have hsourceHeads : ∀ x ∈ rho.honest,
      Block.Preceq sourceAnchor (voterHeadAt S rho x d) := by
    intro x hx
    simpa only [sourceAnchor, source, s, voteDutyHead] using
      preparedProposalAnchor_preceq_voteDutyHead_of_gstZero
        S h hhor hd hupper hproposalHor hprop hx
  have htargetHeads : ∀ x ∈ rho.honest,
      Block.Preceq targetAnchor (voterHeadAt S rho x d) := by
    intro x hx
    exact preparedVoterAnchor_preceq_voteDutyHead_of_gstZero
      S h hhor hd hupper hvoteHor hv hx
  have protected_of_heads {C : Block V}
      (hheads : ∀ x ∈ rho.honest,
        Block.Preceq C (voterHeadAt S rho x d)) :
      ProtectedVoteSlot S rho d C := by
    refine ⟨hheads, ?_⟩
    intro x hx hxCommittee
    obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S h.core hx hdPos hxCommittee hvotePrev
    exact ⟨X, by simpa only [hXerase] using hheads x hx, hXrun, hXemit⟩
  have hsource : ProtectedVoteSlot S rho d sourceAnchor :=
    protected_of_heads hsourceHeads
  have htarget : ProtectedVoteSlot S rho d targetAnchor :=
    protected_of_heads htargetHeads
  have hpos : 0 < ((S.E.committee d) ∩ rho.honest).card := by
    have hc := h.committees d
    omega
  obtain ⟨x0, hx0⟩ := Finset.card_pos.mp hpos
  have hx0Committee := (Finset.mem_inter.mp hx0).1
  have hx0Honest := (Finset.mem_inter.mp hx0).2
  obtain ⟨G, hG, hmax⟩ := greatest_member_of_common_ancestor_bound
    (ProtectedVoteSlot S rho d) hsource
      (fun C hC => hC.heads x0 hx0Honest)
  obtain ⟨X0, hX0erase, hX0run, hX0emit⟩ :=
    WeakGoldfish.voterHead_runBlock_and_emits
      S h.core hx0Honest hdPos hx0Committee hvotePrev
  have hGX0 : Block.Preceq G X0.erase := by
    rw [hX0erase]
    exact hG.heads x0 hx0Honest
  obtain ⟨A, hAX0, hAerased⟩ := Proofs.NamedAncestry.erased_ancestor_lift X0 hGX0
  have hArun : RunBlock S rho A :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hX0run hAX0
  have hAprotected : ProtectedVoteSlot S rho d A.erase := by
    rw [hAerased]
    exact hG
  have hsourceAnchor : Block.Preceq sourceAnchor A.erase := by
    rw [hAerased]
    exact hmax sourceAnchor hsource
  have htargetAnchor : Block.Preceq targetAnchor A.erase := by
    rw [hAerased]
    exact hmax targetAnchor htarget
  have availableAt (w : V) (hw : w ∈ rho.honest) :
      HonestHeadsAvailableBefore S rho d w (Protocol.support_cutoff S.E d) := by
    let R := Protocol.get_fg_root
      (voteDutyRead S rho w s).st.core.toHealing.toFG
    have hRheads : ∀ x ∈ rho.honest,
        Block.Preceq R (voterHeadAt S rho x d) := by
      intro x hx
      simpa only [R, s, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        voteDutyHead] using
        fgRootAtRead_preceq_voteDutyHead_of_gstZero_named
          S h.core h.committees h.gstZero h.windows hhor hd hupper
            (t := tv) (by rfl) hw hx
    have hconeR : NamedHonestVotesCone S rho d (fun X => Block.Preceq R X) := by
      intro x hx hxCommittee
      obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
        WeakGoldfish.voterHead_runBlock_and_emits
          S h.core hx hdPos hxCommittee hvotePrev
      exact ⟨X, by simpa only [hXerase] using hRheads x hx, hXrun, hXemit⟩
    have hpost : S.E.t_GST ≤ Protocol.vote_time S.E d := by
      rw [h.gstZero]
      exact vote_time_nonneg S.E d
    have hcut : Protocol.support_cutoff S.E d ≤ rho.horizon :=
      (support_cutoff_le_vote_time_succ S.E d).trans hvoteHor
    exact honestHeadsAvailableBefore_of_namedPostHealingCone_core
      S h.core hw hpost hcut (B := R) (Block.preceq_self R) hconeR
  have bodyAt (w : V) (hw : w ∈ rho.honest) (time : Time)
      (hcutTime : Protocol.support_cutoff S.E d ≤ time) :
      A ∈ (rho.storeBeforeTime S w time).bodies := by
    have hresolve := headsResolveIn_storeBeforeTime_of_availableBefore_at_core
      S h.core hw d hcutTime (availableAt w hw)
    have hX0head : HonestHead S rho d X0.erase :=
      ⟨x0, hx0Honest, hx0Committee, ⟨X0, rfl, hX0run⟩, hX0emit⟩
    obtain ⟨hfind, -⟩ := hresolve X0.erase hX0head
    have hX0T : X0.erase ∈ (rho.storeBeforeTime S w time).core.T :=
      Proofs.HealingLemmas.find?_mem hfind
    have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho time w
    have hAT : A.erase ∈ (rho.storeBeforeTime S w time).core.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
        A.erase X0.erase hX0T (by simpa only [hAerased] using hGX0)
    obtain ⟨A', hA'body, hA'erase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho time w hAT
    obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      h.core.toNamedScheduleWellFormed.sorted time
    have hA'prefix : A' ∈ (NamedRun.stateBefore S rho n w).st.bodies := by
      rw [← congrFun hn w]
      exact hA'body
    have hA'run : RunBlock S rho A' :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hw hA'prefix
    have hA'eq : A' = A := by
      apply h.core.toNamedRootCollisionFree.root_injective A' A hA'run hArun
        A' A (Or.inl (Proofs.NamedAncestry.named_self A'))
          (Or.inr (Proofs.NamedAncestry.named_self A))
      rw [← Proofs.NamedWire.erase_root A', ← Proofs.NamedWire.erase_root A, hA'erase]
    rw [← hA'eq]
    exact hA'body
  have hsourceBody0 := bodyAt p hp tp
    (by simpa only [tp, s] using support_cutoff_le_proposal_time_succ S.E d)
  have hsourceBody : A ∈ source.st.bodies := by
    simpa only [source, proposerReadAt, tp, p, s,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hsourceBody0
  have htargetBody0 := bodyAt v hv tv
    (by simpa only [tv, s] using support_cutoff_le_vote_time_succ S.E d)
  have htargetBody : A ∈ target.st.bodies := by
    simpa only [target, voteDutyRead, tv, s,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      htargetBody0
  have bandAt (w : V) (hw : w ∈ rho.honest) (time : Time)
      (htime : time ≤ tv) :
      (rho.storeBeforeTime S w time).core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg A).h := by
    by_cases hlarge : 1 < (rho.storeBeforeTime S w time).core.h_max
    · have hmajority := honestWeightMajority_of_finiteWindows S h.windows hhor
      obtain ⟨a, ta, D, K, ha, hemit, hat, -, hfgK, -, -, hKentry,
          hKrun, hKheight⟩ := frontier_confirmationWitness_core_entry
        S h.core hmajority hlarge
      have haTime : S.a a.round < Protocol.vote_time S.E s := by
        have hta : ta = S.a a.round := (emits_attest_shape S hemit).2
        rw [← hta]
        exact hat.trans_le htime
      have hKheads : ∀ x ∈ rho.honest,
          Block.Preceq K.erase (voterHeadAt S rho x d) := by
        intro x hx
        have hsafe := ((actionSources_preceq_voteDutyHead_of_gstZero
          S h.core h.committees h.gstZero h.windows hhor hd hupper hx
            a.round haTime).2 a.val_index ha).2 _ hfgK
        rw [← hKentry]
        simpa only [voteDutyHead] using hsafe
      have hKprotected : ProtectedVoteSlot S rho d K.erase :=
        protected_of_heads hKheads
      have hKG : Block.Preceq K.erase G := hmax K.erase hKprotected
      have hKA : Block.Preceq K.erase A.erase := by simpa only [hAerased] using hKG
      obtain ⟨K', hK'A, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hKA
      have hK'run : RunBlock S rho K' :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hArun hK'A
      have hK'eq : K' = K := by
        apply h.core.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
          K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
            (Or.inr (Proofs.NamedAncestry.named_self K))
        rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
      rw [← hKheight]
      exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg (by
        rw [← hK'eq]
        exact hK'A)
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hlarge)]
      exact Nat.zero_le _
  have hsourceBand0 := bandAt p hp tp
    (by simpa only [tp, tv, s] using (proposal_time_lt_vote_time S.E s).le)
  have hsourceBand : source.st.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg A).h := by
    simpa only [source, proposerReadAt, tp, p, s,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hsourceBand0
  have htargetBand0 := bandAt v hv tv (le_refl _)
  have htargetBand : target.st.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg A).h := by
    simpa only [target, voteDutyRead, tv, s,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      htargetBand0
  have hparent := protected_preceq_proposedParent_of_gstZero_named
    S h hhor hd hupper hproposalHor hprop hAprotected
  exact ⟨A, hAprotected, hsourceAnchor, htargetAnchor,
    hsourceBody, htargetBody, hsourceBand, htargetBand, hparent⟩

#print axioms exists_preparedProtectedProposalPivot_of_gstZero

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
