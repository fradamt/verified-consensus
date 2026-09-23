module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.HandoverStableRootAfterDeadline
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HandoverStableRootCap
public import DecoupledConsensusProofs.Execution.HandoverStableRootNoReturn
public import DecoupledConsensusProofs.Execution.HandoverHeightNamedDirect
public import DecoupledConsensusProofs.Execution.ProposalConfirmationPreparedLiveNamed
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroPreparedWalk

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Retained stable update at the healed carrier opening -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.Optimistic Proofs.HealingLemmas DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem inclusive_index_of_event_time_le_updatedStable
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {t : Time} {i : Nat} {e : Event V} (he : rho.events[i]? = some e)
    (hte : e.time ≤ t) : i < inclusiveEventIndex rho t := by
  have hmem : e ∈ rho.events.filter (fun e => decide (e.time ≤ t)) :=
    List.mem_filter.mpr ⟨List.mem_of_getElem? he, by simpa using hte⟩
  have hfilter : rho.events.filter (fun e => decide (e.time ≤ t)) =
      rho.events.take (inclusiveEventIndex rho t) := by
    simpa only [inclusiveEventIndex] using
      Proofs.Optimistic.filter_eq_take S sch _ (Proofs.Optimistic.downward_le t)
  rw [hfilter] at hmem
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
  have hjlt : j < inclusiveEventIndex rho t := by
    have h := (List.getElem?_eq_some_iff.mp hj).1
    rw [List.length_take] at h
    omega
  rw [List.getElem?_take_of_lt hjlt] at hj
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  have hij : i = j :=
    (List.Nodup.getElem_inj_iff (NamedScheduleWellFormed.nodup sch)).mp
      (by rw [hie, hje])
  simpa only [hij] using hjlt

private theorem confirmation_slot_lt_updatedStable
    (E : Env V) {d s : Slot}
    (h : Protocol.confirmation_time E d < Protocol.confirmation_time E s) :
    d < s := by
  by_contra hnot
  have hsd : s ≤ d := Nat.le_of_not_gt hnot
  have hmono : Protocol.confirmation_time E s ≤
      Protocol.confirmation_time E d := by
    simpa only [Protocol.confirmation_time, Protocol.proposal_time] using
      Int.add_le_add_right (proposal_time_mono E hsd) (6 * E.Δ)
  exact (not_lt_of_ge hmono) h





/-- Closed Route-A P6 under the  post-recovery window. -/
theorem updatedStable_preceq_walk_at_openingConfirmation
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round} {P : NamedBlock V}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      2 * progressLag' gap delayExtra +
      max (1 + S.hc.η_SG) (gap + 3) ≤ m)
    (hcarrier : ProposerCarrierAt S rho m)
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P)
    (hheads : ∀ w ∈ rho.honest,
      voterHeadAt S rho w (S.hc.opening_slot m) = P.erase)
    (hheights : HandoverHeights S rho
      (fgSafetyProgressDeadline S rho rGST gap delayExtra +
        2 * progressLag' gap delayExtra + 1)
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 1)
      (S.hc.opening_slot m) P)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {G : Block V}
    (hG : DecoupledConsensusModel.Protocol.frameStableRoot
      (confirmationInputRead S rho v (S.hc.opening_slot m)).cache S.E S.hc
      (confirmationInputRead S rho v
        (S.hc.opening_slot m)).st.core.toHealing
      (S.hc.round_of (S.E.slotOf (Protocol.confirmation_time S.E
        (S.hc.opening_slot m)))) = some G) :
    Block.Preceq (Protocol.advance_confirmed
      (confirmationInputRead S rho v
        (S.hc.opening_slot m)).st.core.latest_stable G) P.erase := by
  classical
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let start := S.hc.opening_slot m
  let t := Protocol.confirmation_time S.E start
  let old := (confirmationInputRead S rho v start).st.core.latest_stable
  have hmOld : D + 2 * progressLag' gap delayExtra + 1 + S.hc.η_SG ≤ m := by
    have hmax : 1 + S.hc.η_SG ≤ max (1 + S.hc.η_SG) (gap + 3) :=
      le_max_left _ _
    have hold := (Nat.add_le_add_left hmax
      (D + 2 * progressLag' gap delayExtra)).trans (by
        simpa only [D, Nat.add_assoc] using hm)
    simpa only [Nat.add_assoc] using hold
  have hmTwo : D + 2 ≤ m := by
    have hlag : 1 ≤ progressLag' gap delayExtra := progressLag'_pos gap
    have htwolag : 2 ≤ 2 * progressLag' gap delayExtra := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left 2 hlag
    have htail : 2 ≤ 2 * progressLag' gap delayExtra + 1 + S.hc.η_SG :=
      htwolag.trans (by
        simpa only [Nat.add_assoc] using
          Nat.le_add_right (2 * progressLag' gap delayExtra) (1 + S.hc.η_SG))
    exact (Nat.add_le_add_left htail D).trans (by
      simpa only [D, Nat.add_assoc] using hmOld)
  have hmPos : 2 ≤ m := (Nat.le_add_left 2 D).trans hmTwo
  have hstartPos : 0 < start := by
    unfold start Protocol.HealConfig.opening_slot
    exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_two hmPos)
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hvoteHor : Protocol.vote_time S.E start ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E start).trans hhor
  have hvoteDelta : Protocol.vote_time S.E start + S.E.Δ ≤ rho.horizon := by
    rw [vote_time_add_delta]
    exact (support_cutoff_le_confirmation_time S.E start).trans hhor
  have hdeadlineSlot : S.hc.opening_slot D + 1 ≤ start := by
    have hstep : S.hc.opening_slot D + 1 < S.hc.opening_slot (D + 1) := by
      simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
        using Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two)
          (D * S.hc.R)
    exact hstep.le.trans (by
      simpa only [start, Protocol.HealConfig.opening_slot] using
        Nat.mul_le_mul_right S.hc.R
          ((Nat.le_succ (D + 1)).trans (by
            simpa only [Nat.add_assoc] using hmTwo)))
  have hdeadlineRead : S.a D ≤ t := by
    have hDm : D ≤ m := (Nat.le_add_right D 2).trans hmTwo
    calc
      S.a D ≤ S.a m := (action_strictMono S).monotone hDm
      _ = t := by
        simpa only [t, start] using
          (opening_confirmation_time_eq_action S m).symm
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E start := by
    have hGSTdead : rGST ≤ D := by
      unfold D fgSafetyProgressDeadline
      exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
    have hround : S.hc.opening_slot D + 2 ≤ start := by
      have hstep : S.hc.opening_slot D + 2 ≤
          S.hc.opening_slot (D + 1) := by
        simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add_left S.hc.R_ge_two (D * S.hc.R)
      exact hstep.trans (by
        simpa only [start, Protocol.HealConfig.opening_slot, Nat.one_mul] using
          Nat.mul_le_mul_right S.hc.R
            ((Nat.le_succ (D + 1)).trans (by
              simpa only [Nat.add_assoc] using hmTwo)))
    have hdeadlineProposal : S.a D ≤ Protocol.proposal_time S.E start :=
      (action_lt_proposal_time_two_after S D).le.trans
        (proposal_time_mono S.E hround)
    exact hpost.trans (((action_strictMono S).monotone hGSTdead).trans
      (hdeadlineProposal.trans (proposal_time_lt_vote_time S.E start).le))
  have hcone : NamedHonestVotesCone S rho start
      (fun X => Block.Preceq P.erase X) :=
    honestProposal_openingVoteCone_after_SG_healing_named
      S adm hcom (by simpa only [D] using hmTwo) hcarrier
        (by simpa only [start] using hvoteHor) (by simpa only [start] using hP)
        (by simpa only [start] using hheads)
  obtain ⟨hanchor, hcandidate⟩ :=
    honestProposal_confirmationReadFacts_after_SG_healing_named
      S adm hcom hbelow hrec hdelay hpost (by simpa only [D] using hmTwo)
        (by simpa only [start] using hhor) hcarrier
        (by simpa only [start] using hP) v hv
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (confirmationInputRead S rho v start).st.core.toHealing.toFG) P.erase := by
    have hrootHead := fgRoot_preceq_previousHead_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hdeadlineRead hhor hdeadlineSlot
        (le_refl _) hvoteDelta hv hv
    have hrootHead' : Block.Preceq
        (Protocol.get_fg_root
          (confirmationInputRead S rho v start).st.core.toHealing.toFG)
        (voterHeadAt S rho v start) := by
      simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.voteDutyHead] using hrootHead
    rw [hheads v hv] at hrootHead'
    exact hrootHead'
  have hgenuine := genuineConfirmationAndPreceq_of_postHealingCone
    S adm hcom hstartPos hpostVote hhor hv hcone hroot hanchor hcandidate
  have hlive := honestProposal_confirmationSeedPrepared_live_after_SG_healing_named
    S adm hcom hbelow hrec hdelay hpost hmOld hcarrier hP hhor v hv
  have hwalk : namedConfirmationWalk S
      (confirmationInputRead S rho v start) start = P.erase := by
    let contract := NamedProfile.gradeContract
      (confirmationInputRead S rho v start).cache
    let st := confStore S rho v start
    have hliveFormula := update_confirmation_with_live_confirmed
      contract S.E S.hc st start
    rw [if_pos (by simpa only [contract, st] using hgenuine.1.genuine)] at hliveFormula
    have hselected :
        (Protocol.update_confirmation_with contract S.E S.hc st start).live_confirmed =
          P.erase := by simpa only [contract, st, start] using hlive
    exact (by simpa only [contract, st, namedConfirmationWalk,
      confWalkWith, confStore_eq_confirmationInputRead] using
        hliveFormula.symm.trans hselected)
  have hGle : Block.Preceq G P.erase := by
    let rr := S.hc.round_of (S.E.slotOf t)
    have hRle : S.hc.R ≤ S.E.slotOf t := by
      simp only [t, Proofs.Optimistic.slotOf_confirmation_time]
      have hRleStart : S.hc.R ≤ start := by
        calc
          S.hc.R = 1 * S.hc.R := (Nat.one_mul _).symm
          _ ≤ m * S.hc.R := Nat.mul_le_mul_right S.hc.R
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le Nat.zero_lt_two hmPos))
          _ = start := by rfl
      exact hRleStart.trans (Nat.le_succ start)
    have hrr : 0 < rr := Nat.div_pos hRle
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
    have ht0 : (0 : Time) ≤ t := by
      exact Proofs.Optimistic.confirmation_time_nonneg S.E start
    have htcut : t = Protocol.support_cutoff S.E (S.E.slotOf t) := by
      dsimp only [t]
      rw [Proofs.Optimistic.slotOf_confirmation_time,
        Protocol.confirmation_time_eq_support_cutoff_succ]
    have hopen : opening S.E S.hc rr < t :=
      NamedOutageClosure.opening_lt_support_cutoff S t ht0 htcut
    have htop : t ≤ opening S.E S.hc (rr + 1) := by
      simpa only [rr, NamedOutageClosure.clockRoundAt] using
        (NamedOutageClosure.clockRound_lt_opening_succ S t).le
    have hrootWalk := WeakGenesis.preparedStableRoot_preceq_confWalk_positive
      S adm.toNamedAdmissibleCore hv hrr (rfl : S.hc.round_of (S.E.slotOf t) = rr)
        hopen htop (by simpa only [t, start] using hhor) start
        (by simpa only [t, start, rr] using hG)
    have hreadEq : NamedActionReads.confirmationReadAt S rho v t =
        confirmationInputRead S rho v start := by
      simp only [t, confirmationInputRead]
    rw [hreadEq, hwalk] at hrootWalk
    exact hrootWalk
  by_cases hkeep : Block.Preceq G old
  · have hold : Block.Preceq old P.erase := by
      let nidx := strictEventIndex rho t
      have hstate : NamedRun.stateBeforeTime S rho t v =
          NamedRun.stateBefore S rho nidx v := by
        simpa only [nidx] using congrFun
          (NamedOutageClosure.strict_read_eq_index S rho
            adm.toNamedScheduleWellFormed.sorted t) v
      have hcurrent : old = (rho.stateBefore S nidx v).st.latest_stable := by
        unfold old confirmationInputRead NamedActionReads.confirmationReadAt
          NamedActionReads.confirmationReadFrom
        rw [hstate]
        rfl
      have horigin := StableRecord.stateBefore_latest_stable_rootOrigin
        S rho v nidx
      rcases horigin with hgen | ⟨i, hi, hrootOld⟩
      · rw [hcurrent, hgen]
        exact Protocol.preceq_genesis _
      · have hrootOld' : StableRecord.StableRootAt S rho v i old := by
          simpa only [hcurrent] using hrootOld
        have hrootData := hrootOld'
        obtain ⟨time, hevent, hpos, hcut, hframe⟩ := hrootData
        let q' := S.E.slotOf time - 1
        have hsucc : q' + 1 = S.E.slotOf time := by
          exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)
        have htimeConf : time = Protocol.confirmation_time S.E q' := by
          rw [hcut, Protocol.confirmation_time_eq_support_cutoff_succ, hsucc]
        have hevent' : rho.events[i]? =
            some (.tick v (Protocol.confirmation_time S.E q')) := by
          simpa only [htimeConf] using hevent
        have htimeStart : time < t :=
          time_lt_of_index_lt_strictEventIndex S adm.toNamedScheduleWellFormed
            hi hevent
        have hqstart : q' < start :=
          confirmation_slot_lt_updatedStable S.E (by
            simpa only [htimeConf, t] using htimeStart)
        by_cases hpre : time ≤ S.a D
        · have hiD : i < inclusiveEventIndex rho (S.a D) :=
            inclusive_index_of_event_time_le_updatedStable S
              adm.toNamedScheduleWellFormed hevent hpre
          have hcap := stableRootAt_namedHeight_le_cap_of_before_runBlock
            S adm hv hiD (le_refl _) hrootOld'
          have hiD2 : i < inclusiveEventIndex rho (S.a (D + 2)) :=
            hiD.trans_le (inclusiveEventIndex_mono rho
              (Assembly.a_mono S (Nat.le_add_right D 2)))
          exact False.elim ((capBoundedStableRoot_not_retained_at_postRecoveryCarrier S adm hcom hbelow hrec hdelay hpost
            hm (by simpa only [start] using hhor) hv
              (by simpa only [D] using hiD2) hrootOld'
              (by simpa only [D] using hcap)) (by rfl))
        · have hqpost : S.a D < Protocol.confirmation_time S.E q' := by
            rw [← htimeConf]
            exact lt_of_not_ge hpre
          let rr := S.hc.round_of (q' + 1)
          by_cases hboundary : rr ≤ D + 1
          · have hbound := stableRootAt_namedHeight_le_cap_of_boundaryRounds_runBlock
              S adm hcom hbelow hrec hdelay hpost hheads hhor hv hrootOld'
                hevent' (by simpa only [D] using hqpost)
                (by simpa only [rr, D] using hboundary) hqstart
            rcases hbound with hle | hcap
            · exact hle
            · have hclockTop : time < opening S.E S.hc (rr + 1) := by
                simpa only [rr, htimeConf, NamedOutageClosure.clockRoundAt,
                  Proofs.Optimistic.slotOf_confirmation_time] using
                    NamedOutageClosure.clockRound_lt_opening_succ S time
              have hopenMono : opening S.E S.hc (rr + 1) ≤
                  opening S.E S.hc (D + 2) := by
                exact Int.mul_le_mul_of_nonneg_left
                  (Int.ofNat_le.mpr (Nat.mul_le_mul_right S.hc.R
                    (Nat.succ_le_succ hboundary)))
                  (show (0 : Int) ≤ 4 * S.E.Δ by nlinarith [S.E.Δ_pos])
              have hopenAction : opening S.E S.hc (D + 2) < S.a (D + 2) := by
                simpa only [NamedOutageClosure.domain_g1_eq_opening] using
                  FrameForward.opening_lt_a S (D + 2)
              have htimeD2 : time ≤ S.a (D + 2) :=
                ((hclockTop.trans_le hopenMono).trans hopenAction).le
              have hiD2 : i < inclusiveEventIndex rho (S.a (D + 2)) :=
                inclusive_index_of_event_time_le_updatedStable S
                  adm.toNamedScheduleWellFormed hevent htimeD2
              exact False.elim ((capBoundedStableRoot_not_retained_at_postRecoveryCarrier S adm hcom hbelow hrec hdelay hpost
                hm (by simpa only [start] using hhor) hv
                  (by simpa only [D] using hiD2) hrootOld'
                  (by simpa only [D] using hcap)) (by rfl))
          · have hlate : D + 2 ≤ rr :=
              Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hboundary)
            exact stableRootAt_preceq_carrier_after_progressDeadline
              S adm hcom hbelow hrec hdelay hpost hheads hhor hv hrootOld'
                hevent' (by simpa only [D] using hqpost)
                (by simpa only [D, rr] using hlate) hqstart
    change Block.Preceq (Protocol.advance_confirmed old G) P.erase
    unfold Protocol.advance_confirmed
    rw [if_pos (show Block.preceq G old = true from hkeep)]
    exact hold
  · change Block.Preceq (Protocol.advance_confirmed old G) P.erase
    unfold Protocol.advance_confirmed
    rw [if_neg (show Block.preceq G old ≠ true from hkeep)]
    exact hGle


#print axioms updatedStable_preceq_walk_at_openingConfirmation



end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
