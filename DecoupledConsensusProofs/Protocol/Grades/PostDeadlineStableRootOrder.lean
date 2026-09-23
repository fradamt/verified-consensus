module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.HandoverStableRootAfterDeadline
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationPolicy

@[expose] public section

/-!
# Stable-root order after the recovery progress deadline

This leaf exposes the head-order statement inside the carrier-specific handover
proof. It also derives compatibility of two stable roots written after the
deadline.
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

private theorem confirmationTime_mono_laterHead
    (E : Env V) {s t : Slot} (hst : s ≤ t) :
    Protocol.confirmation_time E s ≤ Protocol.confirmation_time E t := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact support_cutoff_mono E (Nat.add_le_add_right hst 1)

private theorem confirmationTime_le_nextVote_laterHead
    (E : Env V) {s t : Slot} (hst : s < t) :
    Protocol.confirmation_time E s ≤ Protocol.vote_time E (t + 1) := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ]
  exact (support_cutoff_le_vote_time_succ E (s + 1)).trans
    (vote_time_mono_slots E (Nat.succ_le_succ (Nat.succ_le_of_lt hst)))

/-- A stable root written in clock round `D + 2` or later is below every
later honest voter head. -/
theorem stableRootAt_preceq_laterVoterHead_after_progressDeadline
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {v : V} (hv : v ∈ rho.honest) {i : Nat} {R : Block V}
    (hroot : StableRecord.StableRootAt S rho v i R)
    {q' : Slot}
    (hq' : rho.events[i]? = some
      (.tick v (Protocol.confirmation_time S.E q')))
    (hqpost : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) <
      Protocol.confirmation_time S.E q')
    (hqround : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤
      S.hc.round_of (q' + 1))
    {d : Slot} (hqd : q' < d)
    (hdhor : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq R (voterHeadAt S rho w d) := by
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
  have hDslot : S.hc.opening_slot D + 1 ≤ d := by
    have hDq : S.hc.opening_slot D < q' := by
      apply lt_of_not_ge
      intro hqD
      have hmono := confirmationTime_mono_laterHead S.E hqD
      exact (not_le_of_gt hqpost) (by
        simpa only [D, opening_confirmation_time_eq_action] using hmono)
    exact (Nat.succ_le_of_lt hDq).trans (Nat.le_of_lt hqd)
  have hnext : Protocol.confirmation_time S.E q' ≤
      Protocol.vote_time S.E (d + 1) :=
    confirmationTime_le_nextVote_laterHead S.E hqd
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
          hdhor hv hw
      simpa only [n, confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.Store.toHealing, Protocol.get_fg_root,
        Run.storeBeforeTime, Protocol.voteDutyHead] using hrootHead
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
              hdhor hv hw
          simpa only [n, confirmationInputRead, NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
            Protocol.Store.toHealing, Protocol.get_fg_root,
            Run.storeBeforeTime, Protocol.voteDutyHead] using hrootHead
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
              have hsubTwo : r - 2 + 2 = r := Nat.sub_add_cancel htwo
              have hsub : r - 2 + 1 = r - 1 := by
                apply Nat.eq_sub_of_add_eq
                simpa only [Nat.add_assoc, one_add_one_eq_two] using hsubTwo
              have hfirstInterior : S.hc.opening_slot ((r - 2) + 1) + 1 ≤ d := by
                have hRpos : 0 < S.hc.R :=
                  Nat.zero_lt_of_lt S.hc.R_ge_two
                have hroundFloor : S.hc.opening_slot r ≤ q' + 1 := by
                  rw [hrEq]
                  unfold Protocol.HealConfig.opening_slot Protocol.HealConfig.round_of
                  simpa only [Nat.mul_comm] using Nat.mul_div_le (q' + 1) S.hc.R
                have hmul : (r - 1) * S.hc.R < r * S.hc.R :=
                  Nat.mul_lt_mul_of_pos_right
                    (Nat.sub_lt hrPos (by decide)) hRpos
                unfold Protocol.HealConfig.opening_slot
                rw [hsub]
                exact (Nat.succ_le_of_lt hmul).trans
                  (hroundFloor.trans (Nat.succ_le_of_lt hqd))
              have hcarrierHead := actionSGBlock_preceq_voterHeadAt_after_GST
                S adm hcom hbelow hrec hdelay hpost (c := r - 2)
                  (by simpa only [← hDEq] using Nat.le_sub_of_add_le hrTwo)
                    hfirstInterior hdhor huHon hw
              rw [hsub] at hcarrierHead
              exact Block.preceq_trans hQCarrier hcarrierHead

#print axioms stableRootAt_preceq_laterVoterHead_after_progressDeadline

/-- Two stable roots written at the same honest node after the recovery
progress deadline are compatible when the second write is later. -/
theorem postDeadlineStableRoots_compatible
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {v : V} (hv : v ∈ rho.honest)
    {i j : Nat} {q' q'' : Slot} {A B : Block V}
    (hA : StableRecord.StableRootAt S rho v i A)
    (hAi : rho.events[i]? = some
      (.tick v (Protocol.confirmation_time S.E q')))
    (hB : StableRecord.StableRootAt S rho v j B)
    (hBj : rho.events[j]? = some
      (.tick v (Protocol.confirmation_time S.E q'')))
    (hslots : q' < q'')
    (hpostA : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) <
      Protocol.confirmation_time S.E q')
    (hroundA : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤
      S.hc.round_of (q' + 1))
    (hroundB : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤
      S.hc.round_of (q'' + 1)) :
    Block.compatible A B = true := by
  have hBHor : Protocol.confirmation_time S.E q'' ≤ rho.horizon :=
    (adm.in_horizon _ (List.mem_of_getElem? hBj)).2
  have hdhor : Protocol.vote_time S.E (q'' + 1) + S.E.Δ ≤ rho.horizon := by
    simpa only [vote_time_succ_add_delta_eq_confirmation_time] using hBHor
  have hpostB : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) <
      Protocol.confirmation_time S.E q'' :=
    hpostA.trans_le
      (confirmationTime_mono_laterHead S.E (Nat.le_of_lt hslots))
  have hAHead := stableRootAt_preceq_laterVoterHead_after_progressDeadline
    S adm hcom hbelow hrec hdelay hpost hv hA hAi hpostA hroundA
      (d := q'' + 1) (hslots.trans (Nat.lt_succ_self q'')) hdhor hv
  have hBHead := stableRootAt_preceq_laterVoterHead_after_progressDeadline
    S adm hcom hbelow hrec hdelay hpost hv hB hBj hpostB hroundB
      (d := q'' + 1) (Nat.lt_succ_self q'') hdhor hv
  exact Block.compatible_of_preceq_common hAHead hBHead

#print axioms postDeadlineStableRoots_compatible





end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
