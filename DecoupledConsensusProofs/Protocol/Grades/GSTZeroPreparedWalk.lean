module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.WeakGenesisGSTZeroActionSources
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain
public import DecoupledConsensusProofs.Protocol.Grades.RoundVoterTransportTwoCutoff
public import DecoupledConsensusProofs.Protocol.Grades.Inclusions
public import DecoupledConsensusProofs.Objects.WeakFGRoot
public import DecoupledConsensusProofs.Protocol.Grades.WeakGenesis
public import DecoupledConsensusProofs.Protocol.Grades.Q10Frame
public import DecoupledConsensusProofs.Protocol.Grades.Interpolation
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent
public import DecoupledConsensusProofs.Protocol.Handlers.HeadExtendsStable

@[expose] public section

/-! # Clean GST-zero prepared-walk bounds -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Statements
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Clean additive restatement of the prepared stable-root bound. -/
theorem preparedStableRoot_preceq_confWalk_positive
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} (hr : 0 < r) {t : Time}
    (hround : S.hc.round_of (S.E.slotOf t) = r)
    (hopen : opening S.E S.hc r < t)
    (htop : t ≤ opening S.E S.hc (r + 1))
    (htHor : t ≤ rho.horizon) (s : Slot) {G : Block V}
    (hG : DecoupledConsensusModel.Protocol.frameStableRoot
      (NamedActionReads.confirmationReadAt S rho v t).cache S.E S.hc
      (NamedActionReads.confirmationReadAt S rho v t).st.core.toHealing r = some G) :
    Block.Preceq G
      (namedConfirmationWalk S
        (NamedActionReads.confirmationReadAt S rho v t) s) := by
  let n := NamedActionReads.confirmationReadAt S rho v t
  have ht1 : domain S.E S.hc r .g1 < t := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact hopen
  have hhorg1 : domain S.E S.hc r .g1 ≤ rho.horizon := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact hopen.le.trans htHor
  change (match ((DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2.bind id).bind
      (activePrefix (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)) with
    | some Q => some Q
    | none => some (Protocol.get_fg_root n.st.core.toHealing.toFG)) = some G at hG
  have hfinish {X : Block V} (hroot : Block.Preceq X
      (anchor S.E S.hc n.st.core.toHealing r
        (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1)) :
      Block.Preceq X (namedConfirmationWalk S n s) := by
    apply Block.preceq_trans hroot
    unfold namedConfirmationWalk
    dsimp only
    have hclock : S.hc.round_of n.st.core.s = r := by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hround
    rw [hclock]
    exact ghost_preceq _ _ _ _
  cases hslot : (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2.bind id with
  | none =>
      simp only [hslot] at hG
      have hfgG : Protocol.get_fg_root n.st.core.toHealing.toFG = G :=
        Option.some.inj hG
      rw [← hfgG]
      apply hfinish
      unfold anchor
      cases hroot : (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1 with
      | none => simp only [hroot]; exact Block.preceq_self _
      | some opt =>
          cases opt with
          | none => simp only [hroot]; exact Block.preceq_self _
          | some root =>
              cases hactive : activePrefix
                  (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) root with
              | none =>
                  simp only [hroot, hactive, Option.getD_none]
                  exact Block.preceq_self _
              | some A =>
                  simp only [hactive, Option.getD_some]
                  exact Proofs.Records.preceq_get_fg_root_of_mem_filtered
                    (NamedProposalParent.activePrefix_mem _ root A hactive)
  | some raw =>
      rw [hslot] at hG
      cases hactive : activePrefix
          (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) raw with
      | none =>
          simp [Option.bind, hactive] at hG
          have hfgG : Protocol.get_fg_root n.st.core.toHealing.toFG = G := hG
          rw [← hfgG]
          apply hfinish
          unfold anchor
          cases hroot : (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1 with
          | none => simp only [hroot]; exact Block.preceq_self _
          | some opt =>
              cases opt with
              | none => simp only [hroot]; exact Block.preceq_self _
              | some root =>
                  cases hanchor : activePrefix
                      (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) root with
                  | none =>
                      simp only [hroot, hanchor, Option.getD_none]
                      exact Block.preceq_self _
                  | some A =>
                      simp only [hanchor, Option.getD_some]
                      exact Proofs.Records.preceq_get_fg_root_of_mem_filtered
                        (NamedProposalParent.activePrefix_mem _ root A hanchor)
      | some Q =>
          simp [Option.bind, hactive] at hG
          have hQG : Q = G := hG
          subst G
          have hQmem := NamedProposalParent.activePrefix_mem _ raw Q hactive
          have hQraw : Block.Preceq Q raw := by
            unfold activePrefix at hactive
            exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
          have hg2Prepared :
              (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2 =
                some (some raw) := by
            cases hg : (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2 with
            | none => simp [hg] at hslot
            | some opt =>
                cases ho : opt with
                | none => simp [hg, ho] at hslot
                | some raw' =>
                    simp only [hg, ho, Option.bind_some, id_eq] at hslot
                    have hrawEq : raw' = raw := Option.some.inj hslot
                    subst raw'
                    simpa only [ho] using hg
          have ht2 : domain S.E S.hc r .g2 < t :=
            (NamedOutageClosure.q10_domain_g2_lt_domain_g1 S r).trans ht1
          have hhorg2 : domain S.E S.hc r .g2 ≤ rho.horizon :=
            ht2.le.trans htHor
          have hg2StrictBase := FrameCompleted.frame_phase_completed_in_round
            S rho core v hv r hr .g2 t ht2 htop hhorg2
          have hg2PreparedBase := NamedOutageClosure.frame_phase_prepared_eq
            S rho v r .g2 t hround _ hg2StrictBase
          have hg2Strict :
              (DecoupledConsensusModel.Protocol.readFrame
                (NamedRun.stateBeforeTime S rho t v).cache
                (NamedRun.stateBeforeTime S rho t v).st.core.toHealing r).g2 =
                some (some raw) := by
            have hbaseEq := hg2PreparedBase.symm.trans hg2Prepared
            rw [hbaseEq] at hg2StrictBase
            exact hg2StrictBase
          obtain ⟨root, hrootStrict, hQroot⟩ :=
            NamedOutageClosure.q10_g1_slot_of_g2_slot S rho core v hv r hr t
              ht1 htop hhorg1 hg2Strict hQraw (by
                simpa only [n, NamedActionReads.confirmationReadAt,
                  NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
                  using hQmem)
          have hrootPrepared := NamedOutageClosure.frame_phase_prepared_eq
            S rho v r .g1 t hround _ hrootStrict
          change (DecoupledConsensusModel.Protocol.readFrame
            (NamedActionReads.confirmationReadAt S rho v t).cache
            (NamedActionReads.confirmationReadAt S rho v t).st.core.toHealing r).g1 =
              some (some root) at hrootPrepared
          apply hfinish
          change Block.Preceq Q
            (anchor S.E S.hc
              (NamedActionReads.confirmationReadAt S rho v t).st.core.toHealing r
              (DecoupledConsensusModel.Protocol.readFrame
                (NamedActionReads.confirmationReadAt S rho v t).cache
                (NamedActionReads.confirmationReadAt S rho v t).st.core.toHealing r).g1)
          rw [hrootPrepared]
          change Block.Preceq Q
            ((activePrefix
              (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) root).getD
              (Protocol.get_fg_root n.st.core.toHealing.toFG))
          obtain ⟨A, hA, hQA⟩ :=
            NamedOutageClosure.q10_activePrefix_dominates hQmem hQroot
          rw [hA]
          exact hQA

#print axioms preparedStableRoot_preceq_confWalk_positive

/-- The prepared stable-root bound from genesis, including the empty
round-zero frame. -/
theorem preparedStableRoot_preceq_confWalk_of_gstZero_clean
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {v : V} (hv : v ∈ rho.honest) {s : Slot}
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {G : Block V}
    (hG : (NamedProfile.gradeContract
      (NamedRecoveryRead.confirmationInputRead S rho v s).cache).stableRoot
        S.E S.hc
        (NamedRecoveryRead.confirmationInputRead S rho v s).st.core.toHealing
        (S.hc.round_of
          (NamedRecoveryRead.confirmationInputRead S rho v s).st.core.s) = some G) :
    Block.Preceq G
      (namedConfirmationWalk S
        (NamedRecoveryRead.confirmationInputRead S rho v s) s) := by
  let t := Protocol.confirmation_time S.E s
  let r := S.hc.round_of (S.E.slotOf t)
  let n := NamedRecoveryRead.confirmationInputRead S rho v s
  by_cases hr0 : r = 0
  · have hclock : S.hc.round_of n.st.core.s = 0 := by
      simpa only [n, NamedRecoveryRead.confirmationInputRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        t, r] using hr0
    change DecoupledConsensusModel.Protocol.frameStableRoot n.cache S.E S.hc
      n.st.core.toHealing (S.hc.round_of n.st.core.s) = some G at hG
    rw [hclock] at hG
    change (match ((DecoupledConsensusModel.Protocol.readFrame
        n.cache n.st.core.toHealing 0).g2.bind id).bind
        (activePrefix
          (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)) with
      | some Q => some Q
      | none => some (Protocol.get_fg_root n.st.core.toHealing.toFG)) = some G at hG
    have hfinish : Block.Preceq
        (Protocol.get_fg_root n.st.core.toHealing.toFG)
        (namedConfirmationWalk S n s) := by
      unfold namedConfirmationWalk
      exact Block.preceq_trans
        (fg_root_preceq_get_sg_root_with_frame
          n.cache S.E S.hc n.st.core.toHealing
            (S.hc.round_of n.st.core.s))
        (ghost_preceq _ _ _ _)
    cases hg2 : (DecoupledConsensusModel.Protocol.readFrame
        n.cache n.st.core.toHealing 0).g2 with
    | none =>
        simp only [hg2, Option.bind_none] at hG
        rw [← Option.some.inj hG]
        exact hfinish
    | some opt =>
        cases opt with
        | none =>
            simp only [hg2, Option.bind_some, id_eq, Option.bind_none] at hG
            rw [← Option.some.inj hG]
            exact hfinish
        | some raw =>
            have hround : S.hc.round_of (S.E.slotOf t) = 0 := by
              simpa only [r] using hr0
            have ht0 : (0 : Time) ≤ t := confirmation_time_nonneg S.E s
            have htime : t ≠ domain S.E S.hc 0 .g2 := by
              have hdomain : domain S.E S.hc 0 .g2 = -S.E.Δ := by
                unfold domain opening Phase.domainOffset Protocol.proposal_time
                  Env.t slotStart Protocol.HealConfig.opening_slot
                norm_num
              rw [hdomain]
              nlinarith [S.E.Δ_pos]
            have hno := confirmationRead_g2_round_zero_no_root
              S h.core v t hround htime (root := raw)
            apply False.elim
            apply hno
            simpa only [n, NamedRecoveryRead.confirmationInputRead,
              NamedActionReads.confirmationReadAt, t] using hg2
  · have hr : 0 < r := Nat.pos_of_ne_zero hr0
    have ht0 : (0 : Time) ≤ t := confirmation_time_nonneg S.E s
    have hcut : t = Protocol.support_cutoff S.E (S.E.slotOf t) := by
      dsimp only [t]
      rw [slotOf_confirmation_time]
      exact Protocol.confirmation_time_eq_support_cutoff_succ S.E s
    have hopen : opening S.E S.hc r < t :=
      NamedOutageClosure.opening_lt_support_cutoff S t ht0 hcut
    have htop : t ≤ opening S.E S.hc (r + 1) := by
      simpa only [r, NamedOutageClosure.clockRoundAt] using
        (NamedOutageClosure.clockRound_lt_opening_succ S t).le
    apply preparedStableRoot_preceq_confWalk_positive
      S h.core hv hr (rfl : S.hc.round_of (S.E.slotOf t) = r)
        hopen htop (by simpa only [t] using hhor) s
    simpa only [NamedRecoveryRead.confirmationInputRead,
      NamedActionReads.confirmationReadAt, t, r,
      slotOf_confirmation_time,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hG

#print axioms preparedStableRoot_preceq_confWalk_of_gstZero_clean

private theorem confirmationTime_lt_nextVote_local
    (E : Env V) {q d : Slot} (hqd : q < d) :
    Protocol.confirmation_time E q < Protocol.vote_time E (d + 1) := by
  have hnext : Protocol.vote_time E (d + 1) =
      Protocol.vote_time E d + 4 * E.Δ := by
    unfold Protocol.vote_time Env.t slotStart
    push_cast
    ring
  rw [← vote_time_succ_add_delta_eq_confirmation_time E q, hnext]
  have hle := vote_time_mono_slots E (Nat.succ_le_of_lt hqd)
  have harith : ∀ a b z : Int, a ≤ b → 0 < z → a + z < b + 4 * z := by
    intro a b z hab hz
    omega
  exact harith _ _ _ hle E.Δ_pos

private theorem confirmationTime_mono_local
    (E : Env V) {q d : Slot} (hqd : q ≤ d) :
    Protocol.confirmation_time E q ≤ Protocol.confirmation_time E d := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact support_cutoff_mono E (Nat.add_le_add_right hqd 1)

/-- The prepared confirmation FG root stays below every protected later
vote-duty head. -/
theorem preparedFGRoot_preceq_voteDutyHead_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {last q d : Slot}
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hqd : q < d) (hupper : d ≤ last + 1)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq
      (Protocol.get_fg_root
        (NamedRecoveryRead.confirmationInputRead S rho w q).st.core.toHealing.toFG)
      (voteDutyHead S rho x d) := by
  have hmajority := honestWeightMajority_of_finiteWindows S h.windows hhor
  change Block.Preceq
    (Protocol.get_fg_root
      (rho.storeBeforeTime S w
        (Protocol.confirmation_time S.E q)).toHealing.toFG)
    (voteDutyHead S rho x d)
  rcases WeakFG.fgRoot_confirmationWitness_at_read
      S h.core hmajority hw (Protocol.confirmation_time S.E q) with
    hgen | ⟨_, _, _, a, ta, ha, hemit, ht, _, hT⟩
  · rw [hgen]
    exact Protocol.preceq_genesis _
  · have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
    have haTime : S.a a.round < Protocol.vote_time S.E (d + 1) := by
      rw [← htime]
      exact ht.trans (confirmationTime_lt_nextVote_local S.E hqd)
    exact ((actionSources_preceq_voteDutyHead_of_gstZero
      S h.core h.committees h.gstZero h.windows hhor
        (Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt hqd)) hupper hx
        a.round haTime).2 a.val_index ha).2 _ hT

#print axioms preparedFGRoot_preceq_voteDutyHead_of_gstZero

/-- A completed G1 raw block in a prepared confirmation read is below every
later protected vote-duty head. -/
theorem preparedG1Raw_preceq_voteDutyHead_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {last q d : Slot}
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hqd : q < d) (hupper : d ≤ last + 1)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest)
    {r : Round}
    (hround : S.hc.round_of
      (S.E.slotOf (Protocol.confirmation_time S.E q)) = r)
    {raw : Block V}
    (hframe : (DecoupledConsensusModel.Protocol.readFrame
      (NamedRecoveryRead.confirmationInputRead S rho w q).cache
      (NamedRecoveryRead.confirmationInputRead S rho w q).st.core.toHealing r).g1 =
        some (some raw)) :
    Block.Preceq raw (voteDutyHead S rho x d) := by
  let t := Protocol.confirmation_time S.E q
  by_cases hr0 : r = 0
  · have hround0 : S.hc.round_of (S.E.slotOf t) = 0 := by
      simpa only [t, hr0] using hround
    have htime : t ≠ domain S.E S.hc 0 .g1 := by
      have hdomain : domain S.E S.hc 0 .g1 = 0 := by
        unfold domain opening Phase.domainOffset Protocol.proposal_time
          Env.t slotStart Protocol.HealConfig.opening_slot
        norm_num
      rw [hdomain]
      unfold t Protocol.confirmation_time Env.t slotStart
      push_cast
      nlinarith [S.E.Δ_pos]
    exact False.elim ((confirmationRead_g1_round_zero_no_root
      S h.core w t hround0 htime) (by
        simpa only [NamedRecoveryRead.confirmationInputRead,
          NamedActionReads.confirmationReadAt, t, hr0] using hframe))
  · have hr : 0 < r := Nat.pos_of_ne_zero hr0
    have hroundT : S.hc.round_of (S.E.slotOf t) = r := by
      simpa only [t] using hround
    have ht0 : (0 : Time) ≤ t := confirmation_time_nonneg S.E q
    have hcut : t = Protocol.support_cutoff S.E (S.E.slotOf t) := by
      dsimp only [t]
      rw [slotOf_confirmation_time]
      exact Protocol.confirmation_time_eq_support_cutoff_succ S.E q
    have hopen : opening S.E S.hc r < t := by
      simpa only [NamedOutageClosure.clockRoundAt, hroundT] using
        NamedOutageClosure.opening_lt_support_cutoff S t ht0 hcut
    have hdomain : domain S.E S.hc r .g1 < t := by
      rw [NamedOutageClosure.domain_g1_eq_opening]
      exact hopen
    have htop : t ≤ opening S.E S.hc (r + 1) := by
      simpa only [NamedOutageClosure.clockRoundAt, hroundT] using
        (NamedOutageClosure.clockRound_lt_opening_succ S t).le
    have hqLast : q ≤ last :=
      Nat.lt_succ_iff.mp (lt_of_lt_of_le hqd hupper)
    have hdomainHor : domain S.E S.hc r .g1 ≤ rho.horizon :=
      hdomain.le.trans (by simpa only [t] using
        (confirmationTime_mono_local S.E hqLast).trans hhor)
    have hgrade := WeakSG.phaseGrade_of_preparedFrame_g1
      S rho h.core w hw r hr t hroundT hdomain htop hdomainHor (by
        simpa only [NamedRecoveryRead.confirmationInputRead,
          NamedActionReads.confirmationReadAt, t] using hframe)
    have hpostEarly : S.E.t_GST ≤ early S.E S.hc r .g2 := by
      rw [h.gstZero]
      have hrPred : r - 1 < r := Nat.sub_lt hr (by decide)
      exact (Proofs.HealingLemmas.a_nonneg S (r - 1)).trans
        (le_add_of_nonneg_right S.E.Δ_pos.le) |>.trans
          (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hrPred)
    have hdelivery : TwoCutoffDelivery S rho r :=
      twoCutoffDelivery_of_core S h.core hpostEarly
    have hfg := preparedFGRoot_preceq_voteDutyHead_of_gstZero
      S h hhor hqd hupper hw hx
    have hFmono : Block.Preceq
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.F
        (NamedRun.stateBeforeTime S rho t w).st.core.F :=
      NamedOutageClosure.incl_strict_F_mono S rho
        h.core.toNamedScheduleWellFormed w hdomain.le
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
        (voteDutyHead S rho x d) := by
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
      S h.core hr (h.windows r hr hprevHor) (p := .g1) (by
        intro y hy u hu k hk huk
        have hklt : k < r := mem_latestWindow_lt hk
        have hdeadline : S.a k + S.E.Δ ≤ early S.E S.hc r .g1 :=
          (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt).trans
            (NamedOutageClosure.q10_early_g2_le_early_g1 S r)
        have hactionTime : S.a k < Protocol.vote_time S.E (d + 1) :=
          (lt_of_lt_of_le (Int.lt_add_of_pos_right _ S.E.Δ_pos) hdeadline).trans
            ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1 S r).trans_lt
              (hdomain.trans (confirmationTime_lt_nextVote_local S.E hqd)))
        have hAhead := (actionSources_preceq_voteDutyHead_of_gstZero
          S h.core h.committees h.gstZero h.windows hhor
            (Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt hqd)) hupper hx
            k hactionTime).1 u hu
          (honest_emits_exact_actionAttestationAt_of_awake S
            h.core.toNamedScheduleWellFormed hu k huk (by
              exact (le_add_of_nonneg_right S.E.Δ_pos.le).trans
                (hdeadline.trans
                  ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                    S r).trans hdomainHor))))
        have hfgY := preparedFGRoot_preceq_voteDutyHead_of_gstZero
          S h hhor hqd hupper hy hx
        have hFmonoY : Block.Preceq
            (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) y).st.core.F
            (NamedRun.stateBeforeTime S rho t y).st.core.F :=
          NamedOutageClosure.incl_strict_F_mono S rho
            h.core.toNamedScheduleWellFormed y hdomain.le
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
            (voteDutyHead S rho x d) := by
          exact Block.preceq_trans hFmonoY (Block.preceq_trans hFrootY (by
            simpa only [NamedRecoveryRead.confirmationInputRead,
              NamedActionReads.confirmationReadAt,
              NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
              t] using hfgY))
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
    obtain ⟨k, hk, u, hu, hemit, hraw⟩ := hcarrier w hw raw (by
      simpa only [PhaseGrades.phaseGrade] using hgrade)
    have hklt : k < r := mem_latestWindow_lt hk
    have hactionTime : S.a k < Protocol.vote_time S.E (d + 1) := by
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
        _ < Protocol.vote_time S.E (d + 1) :=
          confirmationTime_lt_nextVote_local S.E hqd
    exact Block.preceq_trans hraw
      ((actionSources_preceq_voteDutyHead_of_gstZero
        S h.core h.committees h.gstZero h.windows hhor
          (Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt hqd)) hupper hx
          k hactionTime).1 u hu hemit)

#print axioms preparedG1Raw_preceq_voteDutyHead_of_gstZero

/-- The prepared confirmation anchor is below every later protected
vote-duty head. -/
theorem preparedConfirmationAnchor_preceq_voteDutyHead_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {last q d : Slot}
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hqd : q < d) (hupper : d ≤ last + 1)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq
      (namedConfirmationAnchor S
        (NamedRecoveryRead.confirmationInputRead S rho w q))
      (voteDutyHead S rho x d) := by
  rcases confirmationAnchorAt_cases S rho w q with hfg | ⟨raw, A, hframe, hactive, hA⟩
  · rw [show namedConfirmationAnchor S
        (NamedRecoveryRead.confirmationInputRead S rho w q) =
        confirmationAnchorAt S rho w q by rfl, hfg]
    exact preparedFGRoot_preceq_voteDutyHead_of_gstZero
      S h hhor hqd hupper hw hx
  · rw [show namedConfirmationAnchor S
        (NamedRecoveryRead.confirmationInputRead S rho w q) =
        confirmationAnchorAt S rho w q by rfl, hA]
    have hAraw : Block.Preceq A raw := by
      unfold activePrefix at hactive
      exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
    exact Block.preceq_trans hAraw
      (preparedG1Raw_preceq_voteDutyHead_of_gstZero
        S h hhor hqd hupper hw hx (r :=
          S.hc.round_of (S.E.slotOf (Protocol.confirmation_time S.E q)))
          rfl hframe)

#print axioms preparedConfirmationAnchor_preceq_voteDutyHead_of_gstZero

/-- Every prepared confirmation walk is below every later protected
vote-duty head. A walk that moves past its anchor is genuine; a walk that
does not move uses the prepared anchor bound. -/
theorem preparedConfirmationWalk_preceq_voteDutyHead_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {last q d : Slot}
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hqd : q < d) (hupper : d ≤ last + 1)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq
      (namedConfirmationWalk S
        (NamedRecoveryRead.confirmationInputRead S rho w q) q)
      (voteDutyHead S rho x d) := by
  let read := NamedRecoveryRead.confirmationInputRead S rho w q
  let contract := NamedProfile.gradeContract read.cache
  let st := confStore S rho w q
  let A := confAnchorWith contract S.E S.hc st
  let W := confWalkWith contract S.E S.hc st q
  change Block.Preceq W (voteDutyHead S rho x d)
  by_cases hWA : W = A
  · have hanchor := preparedConfirmationAnchor_preceq_voteDutyHead_of_gstZero
      S h hhor hqd hupper hw hx
    rw [hWA]
    simpa only [A, contract, st, read, confAnchorWith,
      Proofs.Optimistic.confStore_eq_confirmationInputRead] using hanchor
  · have helig : confEligible S.E st q W = true := by
      rcases ghost_eligible A (confTree st) (confScore S.E st q)
          (confEligible S.E st q) with hA | helig
      · exact False.elim (hWA (by simpa only [W, A, confWalkWith] using hA))
      · simpa only [W, confWalkWith] using helig
    have hselected : (Protocol.update_confirmation_with contract S.E S.hc st q).live_confirmed =
        W := by
      rw [update_confirmation_with_live_confirmed, if_pos (by
        simpa only [W] using helig)]
    have hgenuine : GenuineConfirmationWith contract S.E S.hc st q W :=
      ⟨hselected, by simpa only [W] using helig⟩
    have hslot := (protectedVoteSlots_of_gstZero_v2
      S h.core h.committees h.gstZero h.windows hhor d
        (Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt hqd)) hupper).2
      q hqd w hw W (by
        simpa only [contract, st, read,
          Proofs.Optimistic.confStore_eq_confirmationInputRead] using hgenuine)
    exact hslot.heads x hx

#print axioms preparedConfirmationWalk_preceq_voteDutyHead_of_gstZero

/-- Every exposed confirmed record has a first slot after which all honest
vote-duty heads extend it. -/
theorem latestConfirmed_preceq_laterVoteDutyHead_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    (hzero : Protocol.confirmation_time S.E 0 ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) (n : Nat) :
    ∃ first : Slot, Protocol.confirmation_time S.E first ≤ rho.horizon ∧
      ∀ last, first ≤ last → Protocol.confirmation_time S.E last ≤ rho.horizon →
        ∀ x ∈ rho.honest,
          Block.Preceq (rho.stateBefore S n v).st.core.latest_confirmed
            (voteDutyHead S rho x (last + 1)) := by
  rcases ConfirmationOrigin.stateBefore_latest_confirmed_origin S rho v n with
    hgen | ⟨i, C, _hi, hsel, hvalue⟩ | ⟨i, _hi, hroot⟩
  · refine ⟨0, hzero, ?_⟩
    intro last _ _ x _
    change (rho.stateBefore S n v).st.core.latest_confirmed = Block.genesis at hgen
    rw [hgen]
    exact Protocol.preceq_genesis _
  · obtain ⟨q, hqevent, hchoice, hqhor⟩ :=
      Proofs.UserConfirmation.selectionAt_slot S h.core.toNamedScheduleWellFormed hsel
    refine ⟨q, hqhor, ?_⟩
    intro last hqLast hlastHor x hx
    have hqSucc : q < last + 1 := Nat.lt_succ_of_le hqLast
    change (rho.stateBefore S n v).st.core.latest_confirmed = C at hvalue
    rw [hvalue]
    rcases hchoice with hwalk | hsg
    · rw [← hwalk]
      exact preparedConfirmationWalk_preceq_voteDutyHead_of_gstZero
        S h hlastHor hqSucc (le_refl _) hv hx
    · have hstate := stateBefore_tick_eq_stateBeforeTime
        S h.core.toNamedScheduleWellFormed hqevent
      let read := NamedRecoveryRead.confirmationInputRead S rho v q
      have hsg' := hsg
      simp only [userSGCandidateAtIndex, hstate, slotOf_confirmation_time,
        Nat.add_sub_cancel, NamedProfile.gradeContract,
        DecoupledConsensusModel.Protocol.frameContract] at hsg'
      have hsgRead : (if confirmationEligible S.E read.st.core q
          (namedConfirmationWalk S read q) = true then none
        else DecoupledConsensusModel.Protocol.frameSGCandidate read.cache
          S.E S.hc read.st.core.toHealing q) = some C := by
        simpa only [read, NamedRecoveryRead.confirmationInputRead,
          NamedActionReads.confirmationReadAt] using hsg'
      by_cases helig : confirmationEligible S.E read.st.core q
          (namedConfirmationWalk S read q) = true
      · have hnone : (none : Option (Block V)) = some C := by
          simpa only [helig, if_pos] using hsgRead
        contradiction
      · have hselect : DecoupledConsensusModel.Protocol.frameSGCandidate read.cache
            S.E S.hc read.st.core.toHealing q = some C := by
          simpa only [helig, if_neg] using hsgRead
        have hselect' : ((DecoupledConsensusModel.Protocol.readFrame read.cache
            read.st.core.toHealing (S.hc.round_of read.st.core.s)).g2.bind id).bind
              (activePrefix
                (Protocol.get_filtered_block_tree read.st.core.toHealing.toFG)) =
            some C := by
          simpa only [DecoupledConsensusModel.Protocol.frameSGCandidate,
            Protocol.Store.toHealing] using hselect
        have hstable : (NamedProfile.gradeContract read.cache).stableRoot
            S.E S.hc read.st.core.toHealing
              (S.hc.round_of read.st.core.s) = some C := by
          change DecoupledConsensusModel.Protocol.frameStableRoot read.cache S.E S.hc
            read.st.core.toHealing (S.hc.round_of read.st.core.s) = some C
          unfold DecoupledConsensusModel.Protocol.frameStableRoot
          rw [hselect']
        exact Block.preceq_trans
          (preparedStableRoot_preceq_confWalk_of_gstZero_clean
            S h hv hqhor hstable)
          (preparedConfirmationWalk_preceq_voteDutyHead_of_gstZero
            S h hlastHor hqSucc (le_refl _) hv hx)
  · obtain ⟨time, hievent, hpos, hcut, hG⟩ := hroot
    let q := S.E.slotOf time - 1
    have hqk : q + 1 = S.E.slotOf time := Nat.sub_add_cancel hpos
    have htimeq : time = Protocol.confirmation_time S.E q := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ, hqk]
      exact hcut
    have hqhor : Protocol.confirmation_time S.E q ≤ rho.horizon := by
      rw [← htimeq]
      exact (h.core.toNamedScheduleWellFormed.in_horizon _
        (List.mem_of_getElem? hievent)).2
    refine ⟨q, hqhor, ?_⟩
    intro last hqLast hlastHor x hx
    have hstate : rho.stateBefore S i v = rho.stateBeforeTime S time v :=
      stateBefore_tick_eq_stateBeforeTime S h.core.toNamedScheduleWellFormed hievent
    have hG' : (NamedProfile.gradeContract
        (NamedRecoveryRead.confirmationInputRead S rho v q).cache).stableRoot
          S.E S.hc
          (NamedRecoveryRead.confirmationInputRead S rho v q).st.core.toHealing
          (S.hc.round_of
            (NamedRecoveryRead.confirmationInputRead S rho v q).st.core.s) =
        some (rho.stateBefore S n v).st.core.latest_confirmed := by
      change DecoupledConsensusModel.Protocol.frameStableRoot
        (NamedActionReads.confirmationReadFrom S
          (rho.stateBefore S i v) time).cache S.E S.hc
        (NamedActionReads.confirmationReadFrom S
          (rho.stateBefore S i v) time).st.core.toHealing
        (S.hc.round_of (NamedActionReads.confirmationReadFrom S
          (rho.stateBefore S i v) time).st.core.s) =
          some (rho.stateBefore S n v).st.core.latest_confirmed at hG
      rw [hstate, htimeq] at hG
      simpa only [NamedRecoveryRead.confirmationInputRead,
        NamedActionReads.confirmationReadAt] using hG
    exact Block.preceq_trans
      (preparedStableRoot_preceq_confWalk_of_gstZero_clean
        S h hv hqhor hG')
      (preparedConfirmationWalk_preceq_voteDutyHead_of_gstZero
        S h hlastHor (Nat.lt_succ_of_le hqLast) (le_refl _) hv hx)

#print axioms latestConfirmed_preceq_laterVoteDutyHead_of_gstZero

/-- The confirmed-record bound at a strict prepared read. -/
theorem storeBeforeTime_latestConfirmed_preceq_laterVoteDutyHead_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    (hzero : Protocol.confirmation_time S.E 0 ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) (t : Time) :
    ∃ first : Slot, Protocol.confirmation_time S.E first ≤ rho.horizon ∧
      ∀ last, first ≤ last → Protocol.confirmation_time S.E last ≤ rho.horizon →
        ∀ x ∈ rho.honest,
          Block.Preceq (rho.storeBeforeTime S v t).latest_confirmed
            (voteDutyHead S rho x (last + 1)) := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S h.core.toNamedScheduleWellFormed t
  have hbound := latestConfirmed_preceq_laterVoteDutyHead_of_gstZero
    S h hzero hv n
  simpa only [Run.storeBeforeTime, hn] using hbound

#print axioms storeBeforeTime_latestConfirmed_preceq_laterVoteDutyHead_of_gstZero

/-- At every honest GST-zero confirmation read, the exposed confirmed record
and the prepared walk lie on one chain. -/
theorem latestConfirmed_compatible_confWalk_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {v : V} (hv : v ∈ rho.honest) {s : Slot}
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    Block.compatible
      (NamedRecoveryRead.confirmationInputRead S rho v s).st.core.latest_confirmed
      (namedConfirmationWalk S
        (NamedRecoveryRead.confirmationInputRead S rho v s) s) = true := by
  have hzero : Protocol.confirmation_time S.E 0 ≤ rho.horizon :=
    (confirmationTime_mono_local S.E (Nat.zero_le s)).trans hhor
  obtain ⟨first, hfirst, hbound⟩ :=
    storeBeforeTime_latestConfirmed_preceq_laterVoteDutyHead_of_gstZero
      S h hzero hv (Protocol.confirmation_time S.E s)
  let last := max first s
  have hlastHor : Protocol.confirmation_time S.E last ≤ rho.horizon := by
    rcases le_total first s with hs | hs
    · simpa only [last, max_eq_right hs] using hhor
    · simpa only [last, max_eq_left hs] using hfirst
  have hrecord : Block.Preceq
      (NamedRecoveryRead.confirmationInputRead S rho v s).st.core.latest_confirmed
      (voteDutyHead S rho v (last + 1)) := by
    simpa only [NamedRecoveryRead.confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hbound last (Nat.le_max_left _ _) hlastHor v hv
  have hwalk : Block.Preceq
      (namedConfirmationWalk S
        (NamedRecoveryRead.confirmationInputRead S rho v s) s)
      (voteDutyHead S rho v (last + 1)) :=
    preparedConfirmationWalk_preceq_voteDutyHead_of_gstZero
      S h hlastHor (Nat.lt_succ_of_le (Nat.le_max_right first s))
        (le_refl _) hv hv
  exact Block.compatible_of_preceq_common hrecord hwalk

#print axioms latestConfirmed_compatible_confWalk_of_gstZero

/-- The complete prepared carrier window from genesis. -/
theorem carrierWindowAt_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho) :
    Internal.CarrierWindowAt S rho 0 := by
  intro v hv s _ hhor
  constructor
  · intro G hG
    exact preparedStableRoot_preceq_confWalk_of_gstZero_clean
      S h hv hhor hG
  · exact latestConfirmed_compatible_confWalk_of_gstZero
      S h hv hhor

#print axioms carrierWindowAt_of_gstZero

/-- Weak genesis discharges the proof-layer head-extension field from time
zero. -/
theorem honestHeadExtendsStableFrom_zero_of_weakGenesis
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho) :
    Internal.HonestHeadExtendsStableFrom S rho 0 :=
  honestHeadExtendsStable_of_weakGenesis_of_carrierWindow
    S h.core h.gstZero h.committees h.windows
      (carrierWindowAt_of_gstZero S h)

#print axioms honestHeadExtendsStableFrom_zero_of_weakGenesis

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
