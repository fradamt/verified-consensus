module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.PreparedFrameAfterDeadline
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.SGLifetimeNamed
public import DecoupledConsensusProofs.Protocol.Schedule.StableRootSuffixOrigin

@[expose] public section

/-!
# Stable roots after the recovery progress deadline

This leaf carries a stable root written after the true post-deadline round
boundary to a later carrier head.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Internal.NamedRecoveryRead
open Internal.HealingSurface Internal.PhaseGrades
open Protocol Proofs.Optimistic Proofs.HealingLemmas DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem confirmationTime_mono_stableRoot
    (E : Env V) {s t : Slot} (hst : s ≤ t) :
    Protocol.confirmation_time E s ≤ Protocol.confirmation_time E t := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact support_cutoff_mono E (Nat.add_le_add_right hst 1)

private theorem confirmationTime_le_nextVote_stableRoot
    (E : Env V) {s t : Slot} (hst : s < t) :
    Protocol.confirmation_time E s ≤ Protocol.vote_time E (t + 1) := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ]
  exact (support_cutoff_le_vote_time_succ E (s + 1)).trans
    (vote_time_mono_slots E (Nat.succ_le_succ (Nat.succ_le_of_lt hst)))

private theorem runBlock_of_body_stateBeforeTime_stableRoot
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {v : V} (hv : v ∈ rho.honest) {t : Time} {B : NamedBlock V}
    (hB : B ∈ (rho.stateBeforeTime S t v).st.bodies) : RunBlock S rho B := by
  obtain ⟨j, hj, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S sch t
  apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := j)
  rw [← hj]
  exact hB

/-- A stable root written in clock round `D + 2` or later is below the later
carrier proposal identified by all honest opening heads. -/
theorem stableRootAt_preceq_carrier_after_progressDeadline
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round} {P : NamedBlock V}
    (hheads : ∀ w ∈ rho.honest,
      voterHeadAt S rho w (S.hc.opening_slot m) = P.erase)
    (hstartHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {i : Nat} {R : Block V}
    (hroot : StableRecord.StableRootAt S rho v i R)
    {q' : Slot}
    (hq' : rho.events[i]? = some
      (.tick v (Protocol.confirmation_time S.E q')))
    (hqpost : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) <
      Protocol.confirmation_time S.E q')
    (hqround : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤
      S.hc.round_of (q' + 1))
    (hqstart : q' < S.hc.opening_slot m) :
    Block.Preceq R P.erase := by
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  obtain ⟨time, hi, hpos, hcut, hframe⟩ := hroot
  have htime : time = Protocol.confirmation_time S.E q' := by
    have he : Event.tick v time =
        Event.tick v (Protocol.confirmation_time S.E q') :=
      Option.some.inj (hi.symm.trans hq')
    simpa only [Event.time] using congrArg Event.time he
  have hstate : rho.stateBefore S i v = rho.stateBeforeTime S time v :=
    stateBefore_tick_eq_stateBeforeTime S adm.toNamedScheduleWellFormed hi
  let n := confirmationInputRead S rho v q'
  let r := S.hc.round_of (q' + 1)
  have hround : S.hc.round_of n.st.core.s = r := by
    simp only [n, confirmationInputRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.slotOf_confirmation_time, r]
  have hframeAt : DecoupledConsensusModel.Protocol.frameStableRoot
      (NamedActionReads.confirmationReadAt S rho v time).cache S.E S.hc
      (NamedActionReads.confirmationReadAt S rho v time).st.core.toHealing
      (S.hc.round_of (S.E.slotOf time)) = some R := by
    rw [hstate] at hframe
    simpa only [NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hframe
  have hframe' : DecoupledConsensusModel.Protocol.frameStableRoot n.cache S.E S.hc
      n.st.core.toHealing r = some R := by
    rw [htime] at hframeAt
    simpa only [n, confirmationInputRead, NamedActionReads.confirmationReadAt,
      Proofs.Optimistic.slotOf_confirmation_time, r] using hframeAt
  have hqHor : Protocol.confirmation_time S.E q' ≤ rho.horizon := by
    exact (adm.in_horizon _ (List.mem_of_getElem? hq')).2
  have hDread : S.a D ≤ Protocol.confirmation_time S.E q' := hqpost.le
  have hDslot : S.hc.opening_slot D + 1 ≤ S.hc.opening_slot m := by
    have hDq : S.hc.opening_slot D < q' := by
      apply lt_of_not_ge
      intro hqD
      have hmono := confirmationTime_mono_stableRoot S.E hqD
      exact (not_le_of_gt hqpost) (by
        simpa only [D, opening_confirmation_time_eq_action] using hmono)
    exact (Nat.succ_le_of_lt hDq).trans (Nat.le_of_lt hqstart)
  have hnext : Protocol.confirmation_time S.E q' ≤
      Protocol.vote_time S.E (S.hc.opening_slot m + 1) :=
    confirmationTime_le_nextVote_stableRoot S.E hqstart
  have hstartVoteHor : Protocol.vote_time S.E
      (S.hc.opening_slot m) + S.E.Δ ≤ rho.horizon := by
    calc
      Protocol.vote_time S.E (S.hc.opening_slot m) + S.E.Δ ≤
          Protocol.confirmation_time S.E (S.hc.opening_slot m) := by
        unfold Protocol.vote_time Protocol.confirmation_time Env.t slotStart
        push_cast
        nlinarith [S.E.Δ_pos]
      _ ≤ rho.horizon := hstartHor
  change (match ((DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2.bind id).bind
      (DecoupledConsensusModel.Protocol.activePrefix
        (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)) with
    | some Q => some Q
    | none => some (Protocol.get_fg_root n.st.core.toHealing.toFG)) = some R at hframe'
  cases hslot : (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2.bind id with
  | none =>
      simp only [hslot] at hframe'
      have hfg : Protocol.get_fg_root n.st.core.toHealing.toFG = R :=
        Option.some.inj hframe'
      rw [← hfg]
      have hrootHead := fgRoot_preceq_previousHead_after_GST
        S adm hcom hbelow hrec hdelay hpost hDread hqHor hDslot hnext
          hstartVoteHor hv hv
      have hrootHead' : Block.Preceq
          (Protocol.get_fg_root n.st.core.toHealing.toFG)
          (voteDutyHead S rho v (S.hc.opening_slot m)) := by
        simpa only [n, confirmationInputRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
          Protocol.Store.toHealing, Protocol.get_fg_root,
          Run.storeBeforeTime] using hrootHead
      rw [show voteDutyHead S rho v (S.hc.opening_slot m) = P.erase by
        simpa only [Protocol.voteDutyHead] using hheads v hv] at hrootHead'
      exact hrootHead'
  | some raw =>
      rw [hslot] at hframe'
      cases hactive : DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) raw with
      | none =>
          simp [Option.bind, hactive] at hframe'
          have hfg : Protocol.get_fg_root n.st.core.toHealing.toFG = R := hframe'
          rw [← hfg]
          have hrootHead := fgRoot_preceq_previousHead_after_GST
            S adm hcom hbelow hrec hdelay hpost hDread hqHor hDslot hnext
              hstartVoteHor hv hv
          have hrootHead' : Block.Preceq
              (Protocol.get_fg_root n.st.core.toHealing.toFG)
              (voteDutyHead S rho v (S.hc.opening_slot m)) := by
            simpa only [n, confirmationInputRead, NamedActionReads.confirmationReadAt,
              NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
              Protocol.Store.toHealing, Protocol.get_fg_root,
              Run.storeBeforeTime] using hrootHead
          rw [show voteDutyHead S rho v (S.hc.opening_slot m) = P.erase by
            simpa only [Protocol.voteDutyHead] using hheads v hv] at hrootHead'
          exact hrootHead'
      | some Q =>
          simp [Option.bind, hactive] at hframe'
          have hQR : Q = R := hframe'
          subst R
          have hrTwo : D + 2 ≤ r := by simpa only [D, r] using hqround
          have hDEq : D = fgSafetyProgressDeadline S rho rGST gap delayExtra := rfl
          have hrEq : r = S.hc.round_of (q' + 1) := rfl
          clear_value D r
          have hrPos : 0 < r :=
            lt_of_lt_of_le (Nat.zero_lt_succ (D + 1)) hrTwo
          have hrOne : 1 ≤ r := Nat.succ_le_iff.mpr hrPos
          have htwo : 2 ≤ r := (Nat.le_add_left 2 D).trans hrTwo
          have hrPred : r - 1 + 1 = r := Nat.sub_add_cancel hrOne
          have hrPredPos : 0 < r - 1 :=
            Nat.sub_pos_iff_lt.mpr (lt_of_lt_of_le Nat.one_lt_two htwo)
          have ht0 : (0 : Time) ≤ Protocol.confirmation_time S.E q' :=
            Proofs.Optimistic.confirmation_time_nonneg S.E q'
          have htCut : Protocol.confirmation_time S.E q' =
              Protocol.support_cutoff S.E
                (S.E.slotOf (Protocol.confirmation_time S.E q')) := by
            rw [Proofs.Optimistic.slotOf_confirmation_time,
              Protocol.confirmation_time_eq_support_cutoff_succ]
          have hopen : DecoupledConsensusModel.Protocol.opening S.E S.hc r <
              Protocol.confirmation_time S.E q' :=
            by
              simpa only [NamedOutageClosure.clockRoundAt,
                Proofs.Optimistic.slotOf_confirmation_time, ← hrEq] using
                  NamedOutageClosure.opening_lt_support_cutoff S
                    (Protocol.confirmation_time S.E q') ht0 htCut
          have htop : Protocol.confirmation_time S.E q' ≤
              DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1) := by
            simpa only [NamedOutageClosure.clockRoundAt,
              Proofs.Optimistic.slotOf_confirmation_time, ← hrEq] using
              (NamedOutageClosure.clockRound_lt_opening_succ S
                (Protocol.confirmation_time S.E q')).le
          have htG2 : domain S.E S.hc r .g2 <
              Protocol.confirmation_time S.E q' :=
            (NamedOutageClosure.q10_domain_g2_lt_domain_g1 S r).trans (by
              simpa only [NamedOutageClosure.domain_g1_eq_opening] using hopen)
          have hdomainHor : domain S.E S.hc r .g2 ≤ rho.horizon :=
            htG2.le.trans hqHor
          have hg2Base := FrameCompleted.frame_phase_completed_in_round
            S rho adm.toNamedAdmissibleCore v hv r hrPos .g2
              (Protocol.confirmation_time S.E q') htG2 htop hdomainHor
          have hg2Prepared := NamedOutageClosure.frame_phase_prepared_eq
            S rho v r .g2 (Protocol.confirmation_time S.E q')
              (by simpa only [Proofs.Optimistic.slotOf_confirmation_time] using hrEq.symm) _ hg2Base
          have hg2Frame :
              (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2 =
                some ((DecoupledConsensusModel.Protocol.freezeRoot S.E
                  (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
                  (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F
                  S.hc.η_SG r (early S.E S.hc r .g2)
                  (late S.E S.hc r .g2)).map
                    (fun B => DecoupledConsensusModel.Protocol.clipGrade B
                      (NamedRun.stateBeforeTime S rho
                        (Protocol.confirmation_time S.E q') v).st.core.F)) := by
            simpa only [n, confirmationInputRead] using hg2Prepared
          have hg2Some :
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
          rw [hg2Some] at hg2Frame
          cases hfreeze : DecoupledConsensusModel.Protocol.freezeRoot S.E
              (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
              (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F
              S.hc.η_SG r (early S.E S.hc r .g2)
              (late S.E S.hc r .g2) with
          | none => simp [hfreeze] at hg2Frame
          | some source =>
              have hrawEq : raw = DecoupledConsensusModel.Protocol.clipGrade source
                  (NamedRun.stateBeforeTime S rho
                    (Protocol.confirmation_time S.E q') v).st.core.F := by
                simpa only [hfreeze, Option.map_some, Option.some.injEq] using hg2Frame
              have hsourceGrade : DecoupledConsensusModel.Protocol.gradeBool S.E
                  (NamedRun.stateBeforeTime S rho
                    (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
                  (NamedRun.stateBeforeTime S rho
                    (domain S.E S.hc r .g2) v).st.core.F
                  S.hc.η_SG r (early S.E S.hc r .g2)
                  (late S.E S.hc r .g2) source = true := by
                exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hfreeze)).2
              have hwindow : RelativeCarrierWindowAt S rho (r - 1) .g2 := by
                apply relativeCarrierWindowAt_after_recovery_deadline
                  S adm hcom hbelow hrec hdelay hpost
                · simpa only [← hDEq] using Nat.le_sub_of_add_le
                    ((Nat.add_le_add_left (Nat.le_succ 1) D).trans hrTwo)
                · simpa only [hrPred] using hdomainHor
              have hmajority : Internal.NamedOutageEntry.GradeFormingMajority
                  S rho (r - 1 + 1) := by
                simpa only [hrPred] using
                  gradeFormingMajority_of_admissible_belowOneThird
                    S adm hbelow hrPos hdomainHor
                    (hpost.trans (Assembly.a_mono S (by
                      have hGSTdead : rGST ≤ D := by
                        rw [hDEq]
                        unfold fgSafetyProgressDeadline
                        exact (Nat.le_add_right rGST 1).trans
                          (Nat.le_add_right (rGST + 1) _)
                      exact hGSTdead.trans (Nat.le_sub_of_add_le
                        ((Nat.add_le_add_left (Nat.le_succ 1) D).trans hrTwo)))))
              obtain ⟨u, hu, hsourceCarrier⟩ := relativeGrade_has_roundCarrier
                S adm.toNamedAdmissibleCore hwindow hmajority hv
                  (by simpa only [hrPred] using hsourceGrade)
              have huHon : u ∈ rho.honest :=
                ((Proofs.NamedOutageInputs.honestRoundVoters_iff
                  S rho u (r - 1)).mp hu).1
              have hQraw : Block.Preceq Q raw := by
                unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
                exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
              have hQCarrier : Block.Preceq Q
                  (actionSGBlockAt S rho u (r - 1)) :=
                Block.preceq_trans hQraw (Block.preceq_trans
                  (hrawEq ▸ NamedOutageClosure.clip_preceq source
                    (NamedRun.stateBeforeTime S rho
                      (Protocol.confirmation_time S.E q') v).st.core.F)
                  hsourceCarrier)
              have hrToM : r ≤ m := by
                have hslotLe : q' + 1 ≤ S.hc.opening_slot m :=
                  Nat.succ_le_of_lt hqstart
                have hdiv : (q' + 1) / S.hc.R ≤
                    S.hc.opening_slot m / S.hc.R :=
                  Nat.div_le_div_right hslotLe
                have hcancel : m * S.hc.R / S.hc.R = m :=
                  by simpa only [Nat.mul_comm] using
                    Nat.mul_div_right m (Nat.zero_lt_of_lt S.hc.R_ge_two)
                rw [hrEq]
                simpa only [Protocol.HealConfig.round_of,
                  Protocol.HealConfig.opening_slot, hcancel] using hdiv
              have hsubTwo : r - 2 + 2 = r := Nat.sub_add_cancel htwo
              have hsub : r - 2 + 1 = r - 1 := by
                apply Nat.eq_sub_of_add_eq
                simpa only [Nat.add_assoc, one_add_one_eq_two] using hsubTwo
              have hfirstInterior : S.hc.opening_slot ((r - 2) + 1) + 1 ≤
                  S.hc.opening_slot m := by
                have hRpos : 0 < S.hc.R :=
                  Nat.zero_lt_of_lt S.hc.R_ge_two
                have hrPredLt : r - 1 < m :=
                  (Nat.sub_lt hrPos (by decide)).trans_le hrToM
                have hmul : (r - 1) * S.hc.R < m * S.hc.R :=
                  Nat.mul_lt_mul_of_pos_right hrPredLt hRpos
                unfold Protocol.HealConfig.opening_slot
                rw [hsub]
                exact Nat.succ_le_of_lt hmul
              have hcarrierHead := actionSGBlock_preceq_voterHeadAt_after_GST
                S adm hcom hbelow hrec hdelay hpost (c := r - 2)
                  (by simpa only [← hDEq] using Nat.le_sub_of_add_le hrTwo)
                    hfirstInterior
                    hstartVoteHor huHon hv
              have hcarrierHead' : Block.Preceq
                  (actionSGBlockAt S rho u (r - 1)) P.erase := by
                rw [hsub] at hcarrierHead
                rw [hheads v hv] at hcarrierHead
                exact hcarrierHead
              exact Block.preceq_trans hQCarrier hcarrierHead'

#print axioms stableRootAt_preceq_carrier_after_progressDeadline

/-- In the two clock rounds at the recovery boundary, a stable root is either
already below the later carrier or has named height at most the frontier cap
at the progress deadline. -/
theorem stableRootAt_namedHeight_le_cap_of_boundaryRounds_runBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round} {P : NamedBlock V}
    (hheads : ∀ w ∈ rho.honest, voterHeadAt S rho w (S.hc.opening_slot m) = P.erase)
    (hstartHor : Protocol.confirmation_time S.E (S.hc.opening_slot m) ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {i : Nat} {R : Block V}
    (hroot : StableRecord.StableRootAt S rho v i R)
    {q' : Slot}
    (hq' : rho.events[i]? = some (.tick v (Protocol.confirmation_time S.E q')))
    (hqpost : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) <
      Protocol.confirmation_time S.E q')
    (hqround : S.hc.round_of (q' + 1) ≤
      fgSafetyProgressDeadline S rho rGST gap delayExtra + 1)
    (hqstart : q' < S.hc.opening_slot m) :
    Block.Preceq R P.erase ∨
      ∃ Rn : NamedBlock V, Rn.erase = R ∧
        RunBlock S rho Rn ∧
        (Protocol.derive_named S.E S.cfg Rn).h ≤
          honestHMaxAt S rho
            (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra)) := by
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  obtain ⟨time, hi, hpos, hcut, hframe⟩ := hroot
  have htime : time = Protocol.confirmation_time S.E q' := by
    have he : Event.tick v time =
        Event.tick v (Protocol.confirmation_time S.E q') :=
      Option.some.inj (hi.symm.trans hq')
    simpa only [Event.time] using congrArg Event.time he
  have hstate : rho.stateBefore S i v = rho.stateBeforeTime S time v :=
    stateBefore_tick_eq_stateBeforeTime S adm.toNamedScheduleWellFormed hi
  let n := confirmationInputRead S rho v q'
  let r := S.hc.round_of (q' + 1)
  have hframeAt : DecoupledConsensusModel.Protocol.frameStableRoot
      (NamedActionReads.confirmationReadAt S rho v time).cache S.E S.hc
      (NamedActionReads.confirmationReadAt S rho v time).st.core.toHealing
      (S.hc.round_of (S.E.slotOf time)) = some R := by
    rw [hstate] at hframe
    simpa only [NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hframe
  have hframe' : DecoupledConsensusModel.Protocol.frameStableRoot n.cache S.E S.hc
      n.st.core.toHealing r = some R := by
    rw [htime] at hframeAt
    simpa only [n, confirmationInputRead, NamedActionReads.confirmationReadAt,
      Proofs.Optimistic.slotOf_confirmation_time, r] using hframeAt
  have hqHor : Protocol.confirmation_time S.E q' ≤ rho.horizon :=
    (adm.in_horizon _ (List.mem_of_getElem? hq')).2
  have hDread : S.a D ≤ Protocol.confirmation_time S.E q' := hqpost.le
  have hDslot : S.hc.opening_slot D + 1 ≤ S.hc.opening_slot m := by
    have hDq : S.hc.opening_slot D < q' := by
      apply lt_of_not_ge
      intro hqD
      have hmono := confirmationTime_mono_stableRoot S.E hqD
      exact (not_le_of_gt hqpost) (by
        simpa only [D, opening_confirmation_time_eq_action] using hmono)
    exact (Nat.succ_le_of_lt hDq).trans (Nat.le_of_lt hqstart)
  have hnext : Protocol.confirmation_time S.E q' ≤
      Protocol.vote_time S.E (S.hc.opening_slot m + 1) :=
    confirmationTime_le_nextVote_stableRoot S.E hqstart
  have hstartVoteHor : Protocol.vote_time S.E
      (S.hc.opening_slot m) + S.E.Δ ≤ rho.horizon := by
    calc
      Protocol.vote_time S.E (S.hc.opening_slot m) + S.E.Δ ≤
          Protocol.confirmation_time S.E (S.hc.opening_slot m) := by
        unfold Protocol.vote_time Protocol.confirmation_time Env.t slotStart
        nlinarith [S.E.Δ_pos]
      _ ≤ rho.horizon := hstartHor
  change (match ((DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2.bind id).bind
      (DecoupledConsensusModel.Protocol.activePrefix
        (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)) with
    | some Q => some Q
    | none => some (Protocol.get_fg_root n.st.core.toHealing.toFG)) = some R at hframe'
  cases hslot : (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2.bind id with
  | none =>
      left
      simp only [hslot] at hframe'
      have hfg : Protocol.get_fg_root n.st.core.toHealing.toFG = R :=
        Option.some.inj hframe'
      rw [← hfg]
      have hrootHead := fgRoot_preceq_previousHead_after_GST
        S adm hcom hbelow hrec hdelay hpost hDread hqHor hDslot hnext
          hstartVoteHor hv hv
      have hrootHead' : Block.Preceq
          (Protocol.get_fg_root n.st.core.toHealing.toFG)
          (voteDutyHead S rho v (S.hc.opening_slot m)) := by
        simpa only [n, confirmationInputRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
          Protocol.Store.toHealing, Protocol.get_fg_root,
          Run.storeBeforeTime] using hrootHead
      simpa only [Protocol.voteDutyHead, hheads v hv] using hrootHead'
  | some raw =>
      rw [hslot] at hframe'
      cases hactive : DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) raw with
      | none =>
          left
          simp [Option.bind, hactive] at hframe'
          have hfg : Protocol.get_fg_root n.st.core.toHealing.toFG = R := hframe'
          rw [← hfg]
          have hrootHead := fgRoot_preceq_previousHead_after_GST
            S adm hcom hbelow hrec hdelay hpost hDread hqHor hDslot hnext
              hstartVoteHor hv hv
          have hrootHead' : Block.Preceq
              (Protocol.get_fg_root n.st.core.toHealing.toFG)
              (voteDutyHead S rho v (S.hc.opening_slot m)) := by
            simpa only [n, confirmationInputRead, NamedActionReads.confirmationReadAt,
              NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
              Protocol.Store.toHealing, Protocol.get_fg_root,
              Run.storeBeforeTime] using hrootHead
          simpa only [Protocol.voteDutyHead, hheads v hv] using hrootHead'
      | some Q =>
          right
          simp [Option.bind, hactive] at hframe'
          have hQR : Q = R := hframe'
          subst R
          have hRpos : 0 < S.hc.R :=
            Nat.zero_lt_of_lt S.hc.R_ge_two
          have hDr : D ≤ r := by
            unfold r Protocol.HealConfig.round_of
            apply (Nat.le_div_iff_mul_le hRpos).mpr
            have hle : S.hc.opening_slot D ≤ q' + 1 :=
              (Nat.le_of_lt (by
                apply lt_of_not_ge
                intro hqD
                have hmono := confirmationTime_mono_stableRoot S.E hqD
                exact (not_le_of_gt hqpost) (by
                  simpa only [D, opening_confirmation_time_eq_action] using hmono))).trans
                (Nat.le_succ q')
            simpa only [Protocol.HealConfig.opening_slot, Nat.mul_comm] using hle
          have hrUpper : r ≤ D + 1 := by simpa only [D, r] using hqround
          have hDpos : 0 < D := by
            dsimp only [D, fgSafetyProgressDeadline]
            exact (Nat.zero_lt_succ rGST).trans_le
              (Nat.le_add_right (rGST + 1) _)
          have hrPos : 0 < r := hDpos.trans_le hDr
          have ht0 : (0 : Time) ≤ Protocol.confirmation_time S.E q' :=
            Proofs.Optimistic.confirmation_time_nonneg S.E q'
          have htCut : Protocol.confirmation_time S.E q' =
              Protocol.support_cutoff S.E
                (S.E.slotOf (Protocol.confirmation_time S.E q')) := by
            rw [Proofs.Optimistic.slotOf_confirmation_time,
              Protocol.confirmation_time_eq_support_cutoff_succ]
          have hrEq : r = S.hc.round_of (q' + 1) := rfl
          have hopen : DecoupledConsensusModel.Protocol.opening S.E S.hc r <
              Protocol.confirmation_time S.E q' := by
            simpa only [NamedOutageClosure.clockRoundAt,
              Proofs.Optimistic.slotOf_confirmation_time, ← hrEq] using
                NamedOutageClosure.opening_lt_support_cutoff S
                  (Protocol.confirmation_time S.E q') ht0 htCut
          have htop : Protocol.confirmation_time S.E q' ≤
              DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1) := by
            simpa only [NamedOutageClosure.clockRoundAt,
              Proofs.Optimistic.slotOf_confirmation_time, ← hrEq] using
                (NamedOutageClosure.clockRound_lt_opening_succ S
                  (Protocol.confirmation_time S.E q')).le
          have htG2 : domain S.E S.hc r .g2 <
              Protocol.confirmation_time S.E q' :=
            (NamedOutageClosure.q10_domain_g2_lt_domain_g1 S r).trans (by
              simpa only [NamedOutageClosure.domain_g1_eq_opening] using hopen)
          have hdomainHor : domain S.E S.hc r .g2 ≤ rho.horizon :=
            htG2.le.trans hqHor
          have hg2Base := FrameCompleted.frame_phase_completed_in_round
            S rho adm.toNamedAdmissibleCore v hv r hrPos .g2
              (Protocol.confirmation_time S.E q') htG2 htop hdomainHor
          have hg2Prepared := NamedOutageClosure.frame_phase_prepared_eq
            S rho v r .g2 (Protocol.confirmation_time S.E q')
              (by simpa only [Proofs.Optimistic.slotOf_confirmation_time] using hrEq.symm)
              _ hg2Base
          have hg2Frame :
              (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2 =
                some ((DecoupledConsensusModel.Protocol.freezeRoot S.E
                  (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
                  (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F
                  S.hc.η_SG r (early S.E S.hc r .g2)
                  (late S.E S.hc r .g2)).map
                    (fun B => DecoupledConsensusModel.Protocol.clipGrade B
                      (NamedRun.stateBeforeTime S rho
                        (Protocol.confirmation_time S.E q') v).st.core.F)) := by
            simpa only [n, confirmationInputRead] using hg2Prepared
          have hg2Some :
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
          rw [hg2Some] at hg2Frame
          cases hfreeze : DecoupledConsensusModel.Protocol.freezeRoot S.E
              (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
              (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F
              S.hc.η_SG r (early S.E S.hc r .g2)
              (late S.E S.hc r .g2) with
          | none => simp [hfreeze] at hg2Frame
          | some source =>
              have hrawEq : raw = DecoupledConsensusModel.Protocol.clipGrade source
                  (NamedRun.stateBeforeTime S rho
                    (Protocol.confirmation_time S.E q') v).st.core.F := by
                simpa only [hfreeze, Option.map_some, Option.some.injEq] using hg2Frame
              have hsourceGrade : DecoupledConsensusModel.Protocol.gradeBool S.E
                  (NamedRun.stateBeforeTime S rho
                    (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
                  (NamedRun.stateBeforeTime S rho
                    (domain S.E S.hc r .g2) v).st.core.F
                  S.hc.η_SG r (early S.E S.hc r .g2)
                  (late S.E S.hc r .g2) source = true := by
                exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hfreeze)).2
              have hQraw : Block.Preceq Q raw := by
                unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
                exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
              have hQsource : Block.Preceq Q source :=
                Block.preceq_trans hQraw (hrawEq ▸
                  NamedOutageClosure.clip_preceq source
                    (NamedRun.stateBeforeTime S rho
                      (Protocol.confirmation_time S.E q') v).st.core.F)
              have hQcore : Q ∈ (rho.stateBeforeTime S
                  (Protocol.confirmation_time S.E q') v).st.core.T := by
                have hQfiltered :=
                  (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1
                have hQprepared := Proofs.Records.get_filtered_block_tree_subset _ hQfiltered
                simpa only [n, confirmationInputRead,
                  NamedActionReads.confirmationReadAt,
                  NamedActionReads.confirmationReadFrom,
                  Protocol.NamedStore.setClock, Run.storeBeforeTime] using hQprepared
              obtain ⟨Qn, hQerase, hQrun⟩ :=
                Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
                  adm.toNamedScheduleWellFormed hv
                  (Protocol.confirmation_time S.E q') hQcore
              refine ⟨Qn, hQerase, hQrun, ?_⟩
              rcases eq_or_lt_of_le hDr with hEq | hLt
              · have hrEqD : r = D := hEq.symm
                have hsourceCore : source ∈
                    (rho.stateBeforeTime S (domain S.E S.hc D .g2) v).st.core.T := by
                  have hs := (Finset.mem_filter.mp
                    (Proofs.Engine.deepest?_mem hfreeze)).1
                  simpa only [hrEqD, Protocol.HealingStore.gradeView,
                    Protocol.Store.toHealing] using hs
                obtain ⟨Sn, hSbody, hSerase⟩ :=
                  Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
                  S rho (domain S.E S.hc D .g2) v hsourceCore
                have hSrun := runBlock_of_body_stateBeforeTime_stableRoot
                  S adm.toNamedScheduleWellFormed hv hSbody
                have hnamed : NamedBlock.Preceq Qn Sn :=
                  Protocol.namedPreceq_of_runBlock_erase_preceq
                    adm hQrun hSrun (by simpa only [hQerase, hSerase] using hQsource)
                have hheight := (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hnamed).trans
                  ((Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime S rho
                    (domain S.E S.hc D .g2) v Sn hSbody).trans
                    ((storeBeforeTime_hMax_le_storeAt S adm.toNamedScheduleWellFormed
                      v (domain S.E S.hc D .g2)).trans
                      ((localHMax_le_honestHMaxAt S rho
                        (domain S.E S.hc D .g2) hv).trans
                        (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
                          (FrameForward.domain_le_a S D .g2)))))
                simpa only [D] using hheight
              · have hrEqSucc : r = D + 1 :=
                  Nat.le_antisymm hrUpper (Nat.succ_le_of_lt hLt)
                have hwindow : RelativeCarrierWindowAt S rho D .g2 := by
                  apply relativeCarrierWindowAt_after_recovery_deadline
                    S adm hcom hbelow hrec hdelay hpost (c := D) (le_refl D)
                  simpa only [hrEqSucc] using hdomainHor
                have hmajority : Internal.NamedOutageEntry.GradeFormingMajority
                    S rho (D + 1) :=
                  gradeFormingMajority_of_admissible_belowOneThird S adm hbelow
                    (Nat.succ_pos D) (by simpa only [hrEqSucc] using hdomainHor)
                    (by
                      simpa only [Nat.add_sub_cancel] using
                        hpost.trans (Assembly.a_mono S (by
                          dsimp only [D]
                          unfold fgSafetyProgressDeadline
                          exact (Nat.le_add_right rGST 1).trans
                            (Nat.le_add_right (rGST + 1) _))))
                obtain ⟨u, hu, hsourceCarrier⟩ := relativeGrade_has_roundCarrier
                  S adm.toNamedAdmissibleCore hwindow hmajority hv
                    (by simpa only [hrEqSucc] using hsourceGrade)
                have huHon : u ∈ rho.honest :=
                  ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u D).mp hu).1
                have hCcore : actionSGBlockAt S rho u D ∈
                    (rho.stateBeforeTime S (S.a D) u).st.core.T := by
                  simpa only [Run.storeBeforeTime] using
                    actionSGBlockAt_mem_storeBeforeTime S rho u D
                obtain ⟨Cn, hCbody, hCerase⟩ :=
                  Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
                    S rho (S.a D) u hCcore
                have hCrun := runBlock_of_body_stateBeforeTime_stableRoot
                  S adm.toNamedScheduleWellFormed huHon hCbody
                have hQcarrier : Block.Preceq Q (actionSGBlockAt S rho u D) :=
                  Block.preceq_trans hQsource hsourceCarrier
                have hnamed : NamedBlock.Preceq Qn Cn :=
                  Protocol.namedPreceq_of_runBlock_erase_preceq
                    adm hQrun hCrun (by simpa only [hQerase, hCerase] using hQcarrier)
                have hheight := (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hnamed).trans
                  ((Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime S rho
                    (S.a D) u Cn hCbody).trans
                    ((storeBeforeTime_hMax_le_storeAt S adm.toNamedScheduleWellFormed
                      u (S.a D)).trans
                      (localHMax_le_honestHMaxAt S rho (S.a D) huHon)))
                simpa only [D] using hheight

#print axioms stableRootAt_namedHeight_le_cap_of_boundaryRounds_runBlock



end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
