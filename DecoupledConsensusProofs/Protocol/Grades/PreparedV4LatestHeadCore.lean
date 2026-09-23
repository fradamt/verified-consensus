module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.HandoverPreparedV4
public import DecoupledConsensusProofs.Objects.HandoverPreparedV3
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroPreparedWalk
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmedRecordSuffixOrigin
public import DecoupledConsensusProofs.Objects.PreparedV4ProtectedVoteSlotsCore

@[expose] public section

/-! # Prepared V4 latest-confirmed common-head bound -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem preparedV4_confirmationTime_mono_latest
    (E : Env V) {s t : Slot} (h : s ≤ t) :
    Protocol.confirmation_time E s ≤ Protocol.confirmation_time E t := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact support_cutoff_mono E (Nat.add_le_add_right h 1)

private noncomputable def preparedV4_afterIndex_latest
    (rho : Run V) (t : Time) : Nat :=
  (rho.events.filter (fun e => decide (e.time ≤ t))).length

private theorem preparedV4_stateBefore_afterIndex_latest
    (S : Setup V) {rho : Run V} (sch : NamedScheduleWellFormed S rho)
    (t : Time) (v : V) :
    rho.stateBefore S (preparedV4_afterIndex_latest rho t) v =
      Run.stateAt S rho t v := by
  exact congrFun (Proofs.Optimistic.stateAt_eq_take S sch t).symm v

private theorem preparedV4_confirmationTime_lt_of_afterIndex_le_latest
    (S : Setup V) {rho : Run V} (sch : NamedScheduleWellFormed S rho)
    {start q : Slot} {v : V} {i : Nat}
    (hmi : preparedV4_afterIndex_latest rho
      (Protocol.confirmation_time S.E start) ≤ i)
    (hget : rho.events[i]? = some
      (Event.tick v (Protocol.confirmation_time S.E q))) :
    start < q := by
  by_contra hnot
  have hle := preparedV4_confirmationTime_mono_latest
    S.E (Nat.le_of_not_gt hnot)
  have hp := filter_false_of_index_ge S sch
    (fun e => decide (e.time ≤ Protocol.confirmation_time S.E start))
    (downward_le _) hmi hget
  simp only [Event.time, decide_eq_false_iff_not] at hp
  exact hp hle

private theorem preparedV4_genuineWith_of_genuineAt_latest
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {q : Slot} {v : V} (hv : v ∈ rho.honest)
    (hqhor : Protocol.confirmation_time S.E q ≤ rho.horizon)
    (hg : GenuineConfirmationAt S rho v q) :
    GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v q).cache)
      S.E S.hc (confStore S rho v q) q
      (rho.storeAt S v
        (Protocol.confirmation_time S.E q)).live_confirmed := by
  constructor
  · simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead] using
      (live_confirmed_eq_update S sch hv q hqhor).symm
  · exact hg.2

/-- A V4 confirmed record after the seed refresh is below every sufficiently
later honest head. The suffix-origin split never reopens the source run. -/
theorem SettledBootstrapPreparedV4.latest_has_voteHead_bound_core_of_pins
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hlatest : SettledBootstrapPreparedV4.LatestSeed S rho start P)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hstartHor : Protocol.confirmation_time S.E start ≤ rho.horizon)
    (protectedVoteSlots_core_of_pins :
      ∀ {last : Slot},
      Protocol.confirmation_time S.E last ≤ rho.horizon →
      ∀ d, start ≤ d → d ≤ last + 1 →
        ProtectedVoteSlot S rho d P.erase ∧
        (∀ q, S.hc.opening_slot (base + S.hc.η_SG) ≤ q → q < d →
          ∀ w ∈ rho.honest, ∀ B,
          GenuineConfirmationWith
            (NamedProfile.gradeContract
              (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
            S.E S.hc (confStore S rho w q) q B →
            ProtectedVoteSlot S rho d B))
    (genuineConfirmation_core_of_pins :
      ∀ q, start ≤ q →
        Protocol.confirmation_time S.E q ≤ rho.horizon →
        ∀ v ∈ rho.honest, GenuineConfirmationAt S rho v q)
    {v : V} (hv : v ∈ rho.honest) {t : Time}
    (ht : Protocol.confirmation_time S.E start ≤ t) :
    ∃ first : Slot, start ≤ first ∧
      Protocol.confirmation_time S.E first ≤ rho.horizon ∧
      ∀ last, first ≤ last →
        Protocol.confirmation_time S.E last ≤ rho.horizon →
        ∀ x ∈ rho.honest,
          Block.Preceq (rho.storeAt S v t).core.latest_confirmed
            (voterHeadAt S rho x (last + 1)) := by
  let m := preparedV4_afterIndex_latest rho
    (Protocol.confirmation_time S.E start)
  let n := (rho.events.filter (fun e => decide (e.time ≤ t))).length
  have hmn : m ≤ n := by
    dsimp only [m, preparedV4_afterIndex_latest]
    exact (Protocol.filter_time_prefix ht rho.events
      (Protocol.pairwise_time_le
        S adm.toNamedScheduleWellFormed)).length_le
  have hn : (rho.storeAt S v t).core.latest_confirmed =
      (rho.stateBefore S n v).st.core.latest_confirmed := by
    simp only [Run.storeAt, Proofs.Optimistic.stateAt_eq_take
      S adm.toNamedScheduleWellFormed, n]
  have hseedState : (rho.stateBefore S m v).st =
      rho.storeAt S v (Protocol.confirmation_time S.E start) := by
    simpa only [Run.storeAt] using congrArg NamedNodeState.st
      (preparedV4_stateBefore_afterIndex_latest
        S adm.toNamedScheduleWellFormed
          (Protocol.confirmation_time S.E start) v)
  have hseed : (rho.stateBefore S m v).st.core.latest_confirmed = P.erase := by
    rw [hseedState]
    change (rho.storeAt S v
      (Protocol.confirmation_time S.E start)).latest_confirmed = P.erase
    rw [latest_confirmed_eq_update
      S adm.toNamedScheduleWellFormed hv start hstartHor]
    simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead] using
      hlatest v hv
  have hstable : Block.Preceq
      (rho.stateBefore S m v).st.core.latest_stable P.erase := by
    have h := ConfirmationOrigin.stateBefore_stable_below_confirmed S rho v m
    change Block.Preceq (rho.stateBefore S m v).st.core.latest_stable
      (rho.stateBefore S m v).st.core.latest_confirmed at h
    rwa [hseed] at h
  have hP : ∀ last, start ≤ last →
      Protocol.confirmation_time S.E last ≤ rho.horizon →
      ∀ x ∈ rho.honest,
        Block.Preceq P.erase (voterHeadAt S rho x (last + 1)) := by
    intro last hlast hlastHor x hx
    exact (protectedVoteSlots_core_of_pins hlastHor
      (last + 1) (hlast.trans (Nat.le_succ _)) (le_refl _)).1.heads x hx
  rcases ConfirmationOrigin.stateBefore_latest_confirmed_origin_after_prefix
      S rho v n m hmn with
    hsame | hstableValue | ⟨i, C, hmi, _, hsel, hvalue⟩ |
      ⟨i, hmi, _, hroot⟩
  · refine ⟨start, le_rfl, hstartHor, ?_⟩
    change (rho.stateBefore S n v).st.core.latest_confirmed =
      (rho.stateBefore S m v).st.core.latest_confirmed at hsame
    intro last hlast hlastHor x hx
    rw [hn, hsame, hseed]
    exact hP last hlast hlastHor x hx
  · refine ⟨start, le_rfl, hstartHor, ?_⟩
    change (rho.stateBefore S n v).st.core.latest_confirmed =
      (rho.stateBefore S m v).st.core.latest_stable at hstableValue
    intro last hlast hlastHor x hx
    rw [hn, hstableValue]
    exact Block.preceq_trans hstable (hP last hlast hlastHor x hx)
  · obtain ⟨q, hqevent, hchoice, hqhor⟩ :=
      Proofs.UserConfirmation.selectionAt_slot
        S adm.toNamedScheduleWellFormed hsel
    change (rho.stateBefore S n v).st.core.latest_confirmed = C at hvalue
    have hstartq := preparedV4_confirmationTime_lt_of_afterIndex_le_latest
      S adm.toNamedScheduleWellFormed hmi hqevent
    have hg := genuineConfirmation_core_of_pins
      q hstartq.le hqhor v hv
    rcases hchoice with hwalk | hsg
    · have hC : (rho.storeAt S v
          (Protocol.confirmation_time S.E q)).live_confirmed = C :=
        hg.1.trans hwalk
      refine ⟨q, hstartq.le, hqhor, ?_⟩
      intro last hlast hlastHor x hx
      rw [hn, hvalue, ← hC]
      exact ((protectedVoteSlots_core_of_pins hlastHor
        (last + 1) (hstartq.le.trans (hlast.trans (Nat.le_succ _)))
          (le_refl _)).2 q (hboot.settled.trans hstartq.le)
            (Nat.lt_succ_of_le hlast) v hv _
            (preparedV4_genuineWith_of_genuineAt_latest
              S adm.toNamedScheduleWellFormed hv hqhor hg)).heads x hx
    · have hstate := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
        S adm.toNamedScheduleWellFormed hqevent
      have hcontract : Protocol.GradeContract.confirmationSG
          (NamedProfile.gradeContract
            (NamedActionReads.confirmationReadFrom S
              (rho.stateBeforeTime S
                (Protocol.confirmation_time S.E q) v)
              (Protocol.confirmation_time S.E q)).cache) =
          Protocol.ConfirmationSGCandidate.optional
            (DecoupledConsensusModel.Protocol.frameSGCandidate
              (NamedActionReads.confirmationReadFrom S
                (rho.stateBeforeTime S
                  (Protocol.confirmation_time S.E q) v)
                (Protocol.confirmation_time S.E q)).cache) := rfl
      have helig : confirmationEligible S.E
          (NamedActionReads.confirmationReadFrom S
            (rho.stateBeforeTime S
              (Protocol.confirmation_time S.E q) v)
            (Protocol.confirmation_time S.E q)).st.core q
          (namedConfirmationWalk S
            (NamedActionReads.confirmationReadFrom S
              (rho.stateBeforeTime S
                (Protocol.confirmation_time S.E q) v)
              (Protocol.confirmation_time S.E q)) q) = true := by
        simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
          NamedActionReads.confirmationReadAt] using hg.2
      simp only [userSGCandidateAtIndex, hstate, slotOf_confirmation_time,
        Nat.add_sub_cancel, hcontract, helig, if_pos] at hsg
      contradiction
  · obtain ⟨time, hievent, hqpos, hqtime, hGval⟩ := hroot
    have hstateEq : rho.stateBefore S i v =
        rho.stateBeforeTime S time v :=
      Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
        S adm.toNamedScheduleWellFormed hievent
    set q := S.E.slotOf time - 1 with hqdef
    have hqk : q + 1 = S.E.slotOf time := Nat.sub_add_cancel hqpos
    have htimeq : time = Protocol.confirmation_time S.E q := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ, hqk]
      exact hqtime
    have hqevent : rho.events[i]? = some
        (Event.tick v (Protocol.confirmation_time S.E q)) := by
      rw [← htimeq]
      exact hievent
    have hstartq := preparedV4_confirmationTime_lt_of_afterIndex_le_latest
      S adm.toNamedScheduleWellFormed hmi hqevent
    have hqhor : Protocol.confirmation_time S.E q ≤ rho.horizon := by
      rw [← htimeq]
      exact (adm.in_horizon _ (List.mem_of_getElem? hievent)).2
    let r := S.hc.round_of (S.E.slotOf time)
    change DecoupledConsensusModel.Protocol.frameStableRoot
      (NamedActionReads.confirmationReadFrom S
        (rho.stateBefore S i v) time).cache S.E S.hc
      (NamedActionReads.confirmationReadFrom S
        (rho.stateBefore S i v) time).st.core.toHealing
      (S.hc.round_of
        (NamedActionReads.confirmationReadFrom S
          (rho.stateBefore S i v) time).st.core.s) =
        some (rho.stateBefore S n v).st.core.latest_confirmed at hGval
    rw [hstateEq] at hGval
    have hGconfAt : DecoupledConsensusModel.Protocol.frameStableRoot
        (NamedActionReads.confirmationReadAt S rho v time).cache
        S.E S.hc
        (NamedActionReads.confirmationReadAt S rho v time).st.core.toHealing r =
          some (rho.stateBefore S n v).st.core.latest_confirmed := by
      simpa only [NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock, r] using hGval
    have hr : 0 < r := by
      have hcutPos : 0 < base + S.hc.η_SG :=
        Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
      have hRleStart : S.hc.R ≤ start := by
        calc
          S.hc.R = 1 * S.hc.R := by omega
          _ ≤ (base + S.hc.η_SG) * S.hc.R :=
            Nat.mul_le_mul_right S.hc.R
              (Nat.succ_le_iff.mpr hcutPos)
          _ ≤ start := hboot.settled
      have hRle : S.hc.R ≤ S.E.slotOf time := by
        rw [← hqk]
        exact hRleStart.trans (Nat.le_succ_of_le hstartq.le)
      exact Nat.div_pos hRle
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
    have ht0 : (0 : Time) ≤ time := by
      rw [htimeq]
      exact Proofs.Optimistic.confirmation_time_nonneg S.E q
    have hopen : DecoupledConsensusModel.Protocol.opening S.E S.hc r < time :=
      NamedOutageClosure.opening_lt_support_cutoff S time ht0 hqtime
    have htop : time ≤ DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1) := by
      simpa only [r, NamedOutageClosure.clockRoundAt] using
        (NamedOutageClosure.clockRound_lt_opening_succ S time).le
    have hwalk := WeakGenesis.preparedStableRoot_preceq_confWalk_positive
      S adm hv hr (rfl : S.hc.round_of (S.E.slotOf time) = r)
      hopen htop (by simpa only [htimeq] using hqhor) q hGconfAt
    have hg := genuineConfirmation_core_of_pins
      q hstartq.le hqhor v hv
    rw [htimeq] at hwalk
    have hgSelected : (rho.storeAt S v
        (Protocol.confirmation_time S.E q)).live_confirmed =
        namedConfirmationWalk S
          (NamedActionReads.confirmationReadAt S rho v
            (Protocol.confirmation_time S.E q)) q := by
      simpa only [Internal.NamedRecoveryRead.confirmationInputRead] using hg.1
    rw [← hgSelected] at hwalk
    refine ⟨q, hstartq.le, hqhor, ?_⟩
    intro last hlast hlastHor x hx
    rw [hn]
    refine Block.preceq_trans hwalk ?_
    exact ((protectedVoteSlots_core_of_pins hlastHor
      (last + 1) (hstartq.le.trans (hlast.trans (Nat.le_succ _)))
        (le_refl _)).2 q (hboot.settled.trans hstartq.le)
          (Nat.lt_succ_of_le hlast) v hv _
          (preparedV4_genuineWith_of_genuineAt_latest
            S adm.toNamedScheduleWellFormed hv hqhor hg)).heads x hx

#print axioms SettledBootstrapPreparedV4.latest_has_voteHead_bound_core_of_pins


/-- Item 1 is available; only the later genuine-confirmation producer remains
pinned. -/
theorem SettledBootstrapPreparedV4.latest_has_voteHead_bound_core_of_genuine_pin
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hlatest : SettledBootstrapPreparedV4.LatestSeed S rho start P)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hstartHor : Protocol.confirmation_time S.E start ≤ rho.horizon)
    (genuineConfirmation_core_of_pins :
      ∀ q, start ≤ q →
        Protocol.confirmation_time S.E q ≤ rho.horizon →
        ∀ v ∈ rho.honest, GenuineConfirmationAt S rho v q)
    {v : V} (hv : v ∈ rho.honest) {t : Time}
    (ht : Protocol.confirmation_time S.E start ≤ t) :
    ∃ first : Slot, start ≤ first ∧
      Protocol.confirmation_time S.E first ≤ rho.horizon ∧
      ∀ last, first ≤ last →
        Protocol.confirmation_time S.E last ≤ rho.horizon →
        ∀ x ∈ rho.honest,
          Block.Preceq (rho.storeAt S v t).core.latest_confirmed
            (voterHeadAt S rho x (last + 1)) := by
  exact SettledBootstrapPreparedV4.latest_has_voteHead_bound_core_of_pins
    S adm hcom hboot hlatest hawake hfinality hstartHor
      (fun hhor => SettledBootstrapPreparedV4.protectedVoteSlots_core
        S adm hcom hboot hawake hfinality hhor)
      genuineConfirmation_core_of_pins hv ht

#print axioms SettledBootstrapPreparedV4.latest_has_voteHead_bound_core_of_genuine_pin

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
