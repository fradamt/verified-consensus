module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroPreparedWalk
public import DecoupledConsensusProofs.Objects.AdmissibleCore
public import DecoupledConsensusProofs.Execution.WeakGenesisCanonicalProposalDutyClosed
public import DecoupledConsensusProofs.Execution.WeakGenesisLatestAtProposalClosed
public import DecoupledConsensusProofs.Execution.WeakGenesisGSTZeroActionSources
public import DecoupledConsensusProofs.Objects.WeakLiveConfirmationCore
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistory
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmedOutput
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Generic.SlotFreshness
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Execution.GSTZeroSafetyTenFields

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Named GST-zero six-field bypass

This leaf assembles the six safety fields that follow from the protected
vote-head chain without importing the red pre-rewrite cone.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Statements
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Store-at wrapper for the indexed latest-record bound. -/
theorem latestConfirmedAt_preceq_laterVoteDutyHead_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    (hzero : Protocol.confirmation_time S.E 0 ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) (t : Time) :
    ∃ first : Slot, Protocol.confirmation_time S.E first ≤ rho.horizon ∧
      ∀ last, first ≤ last →
        Protocol.confirmation_time S.E last ≤ rho.horizon →
        ∀ x ∈ rho.honest,
          Block.Preceq (rho.storeAt S v t).latest_confirmed
            (voterHeadAt S rho x (last + 1)) := by
  obtain ⟨n, hn⟩ := Proofs.Bridges.stateAt_eq_stateBefore
    S h.core.toNamedScheduleWellFormed t
  have hbound := latestConfirmed_preceq_laterVoteDutyHead_of_gstZero
    S h hzero hv n
  simpa only [Run.storeAt, hn] using hbound

#print axioms latestConfirmedAt_preceq_laterVoteDutyHead_of_gstZero

/-- A run that ends before its first confirmation has no confirmed-record
write. -/
theorem latestConfirmedAt_eq_genesis_of_short_horizon
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (hshort : rho.horizon < Protocol.confirmation_time S.E 0)
    (v : V) (t : Time) :
    (rho.storeAt S v t).latest_confirmed = Block.genesis := by
  obtain ⟨n, hn⟩ := Proofs.Bridges.stateAt_eq_stateBefore S sch t
  rcases ConfirmationOrigin.stateBefore_latest_confirmed_origin S rho v n with
    hgen | ⟨i, C, _hi, hsel, _hvalue⟩ | ⟨i, hi, hroot⟩
  · simpa only [Run.storeAt, hn] using hgen
  · obtain ⟨q, _hqevent, _hchoice, hqhor⟩ :=
      Proofs.UserConfirmation.selectionAt_slot S sch hsel
    have hle : Protocol.confirmation_time S.E 0 ≤
        Protocol.confirmation_time S.E q := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ,
        Protocol.confirmation_time_eq_support_cutoff_succ]
      exact support_cutoff_mono S.E (Nat.succ_le_succ (Nat.zero_le q))
    exact False.elim ((not_le_of_gt hshort) (hle.trans hqhor))
  · obtain ⟨time, hievent, hpos, hcut, _hG⟩ := hroot
    let q := S.E.slotOf time - 1
    have hqk : q + 1 = S.E.slotOf time := Nat.sub_add_cancel hpos
    have htimeq : time = Protocol.confirmation_time S.E q := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ, hqk]
      exact hcut
    have hqhor : Protocol.confirmation_time S.E q ≤ rho.horizon := by
      rw [← htimeq]
      exact (sch.in_horizon _ (List.mem_of_getElem? hievent)).2
    have hle : Protocol.confirmation_time S.E 0 ≤
        Protocol.confirmation_time S.E q := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ,
        Protocol.confirmation_time_eq_support_cutoff_succ]
      exact support_cutoff_mono S.E (Nat.succ_le_succ (Nat.zero_le q))
    exact False.elim ((not_le_of_gt hshort) (hle.trans hqhor))

#print axioms latestConfirmedAt_eq_genesis_of_short_horizon

/-- All honest confirmed records are compatible from any start time. -/
theorem confirmationCompatibleFrom_of_weakGenesis_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho) (t0 : Time) :
    ConfirmationCompatibleFrom S rho t0 := by
  intro u hu v hv t t' _ht0 _ht0' _ht _ht'
  by_cases hzero : Protocol.confirmation_time S.E 0 ≤ rho.horizon
  · obtain ⟨a, ha, hA⟩ :=
      latestConfirmedAt_preceq_laterVoteDutyHead_of_gstZero
        S h hzero hu t
    obtain ⟨b, hb, hB⟩ :=
      latestConfirmedAt_preceq_laterVoteDutyHead_of_gstZero
        S h hzero hv t'
    have hhor : Protocol.confirmation_time S.E (max a b) ≤ rho.horizon := by
      rcases le_total a b with hab | hba
      · simpa only [max_eq_right hab] using hb
      · simpa only [max_eq_left hba] using ha
    exact Block.compatible_of_preceq_common
      (hA (max a b) (Nat.le_max_left _ _) hhor u hu)
      (hB (max a b) (Nat.le_max_right _ _) hhor u hu)
  · have hshort : rho.horizon < Protocol.confirmation_time S.E 0 :=
      lt_of_not_ge hzero
    rw [latestConfirmedAt_eq_genesis_of_short_horizon
          S h.core.toNamedScheduleWellFormed hshort u t,
      latestConfirmedAt_eq_genesis_of_short_horizon
          S h.core.toNamedScheduleWellFormed hshort v t']
    exact Block.compatible_of_preceq_common
      (Block.preceq_self _) (Block.preceq_self _)

#print axioms confirmationCompatibleFrom_of_weakGenesis_named

/-- Every positive honest proposal is the exact live confirmation and remains
below all later confirmed records. -/
theorem proposalConfirmedFrom_of_weakGenesis_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho) :
    ProposalConfirmedFrom S rho 0 := by
  intro s hs _hproposal hprop hhor
  have hpHor : Protocol.proposal_time S.E s ≤ rho.horizon :=
    (proposal_time_lt_vote_time S.E s).le.trans
      ((vote_time_le_confirmation_time S.E s).trans hhor)
  obtain ⟨B, hB, hslot, hemit⟩ := proposedBlockAt_emits_of_honest
    S h.core.toNamedScheduleWellFormed s hs hprop hpHor
  have hduty := canonicalProposalDuty_positive_of_gstZero_named
    S h hs hhor hprop hB
  have hlatest := latestAtProposalField_of_weakGenesis S rho h s hs hhor hprop
  obtain ⟨B', hB', hlatest'⟩ := hlatest
  have hBB' : B = B' := by
    exact Option.some.inj (hB.symm.trans hB')
  subst B'
  refine ⟨B, hslot, hemit, ?_, ?_⟩
  · intro v hv
    rw [Proofs.Optimistic.live_confirmed_eq_update
      S h.core.toNamedScheduleWellFormed hv s hhor]
    exact updateConfirmation_eq_proposedBlock_of_dutyExecution
      S h.committees hduty hv
  · intro v hv t ht hthor
    have hmono := confirmationMonotoneFrom S
      h.core.toNamedScheduleWellFormed 0
      (confirmationCompatibleFrom_of_weakGenesis_named S h 0)
    simpa only [hlatest' v hv] using
      hmono v hv (Protocol.confirmation_time S.E s) t
        (Proofs.Optimistic.confirmation_time_nonneg S.E s) ht hthor

#print axioms proposalConfirmedFrom_of_weakGenesis_named

/-- The named protected-head route supplies the available chain. -/
theorem availableChainFrom_of_weakGenesis_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho) :
    AvailableChainFrom S rho 0 := by
  have hcompat := confirmationCompatibleFrom_of_weakGenesis_named S h 0
  exact ⟨hcompat,
    confirmationMonotoneFrom S h.core.toNamedScheduleWellFormed 0 hcompat,
    proposalConfirmedFrom_of_weakGenesis_named S h⟩

#print axioms availableChainFrom_of_weakGenesis_named

/-- Clean named isolation of the actual prepared confirmation output bound. -/
theorem liveConfirmedSelection_preceq_voteDutyHead_of_weakGenesis_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {last q d : Slot}
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hqd : q < d) (hupper : d ≤ last + 1)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq
      (Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedRecoveryRead.confirmationInputRead S rho w q).cache)
        S.E S.hc (confStore S rho w q) q).live_confirmed
      (voterHeadAt S rho x d) := by
  have hd : 1 ≤ d :=
    (Nat.succ_le_succ (Nat.zero_le q)).trans (Nat.succ_le_of_lt hqd)
  let contract := NamedProfile.gradeContract
    (NamedRecoveryRead.confirmationInputRead S rho w q).cache
  by_cases hg : confEligible S.E (confStore S rho w q) q
      (confWalkWith contract S.E S.hc (confStore S rho w q) q) = true
  · exact ((protectedVoteSlots_of_gstZero_v2
      S h.core h.committees h.gstZero h.windows hhor d hd hupper).2
        q hqd w hw _ ⟨rfl, hg⟩).heads x hx
  · rw [update_confirmation_with_live_confirmed, if_neg hg]
    have hmajority := honestWeightMajority_of_finiteWindows S h.windows hhor
    have hroot : Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S w
            (Protocol.confirmation_time S.E q)).toHealing.toFG)
        (voterHeadAt S rho x d) := by
      rcases WeakFG.fgRoot_confirmationWitness_at_read
          S h.core hmajority hw (Protocol.confirmation_time S.E q) with
        hgen | ⟨C, hC, hJ, a, ta, ha, hemit, ht, hpair, hT⟩
      · rw [hgen]
        exact Protocol.preceq_genesis _
      · have hat : S.a a.round < Protocol.vote_time S.E (d + 1) := by
          have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
          rw [← htime]
          exact ht.trans (confirmationTime_lt_nextVote_of_lt S.E hqd)
        exact ((actionSources_preceq_voteDutyHead_of_gstZero
          S h.core h.committees h.gstZero h.windows hhor hd hupper hx
            a.round hat).2 a.val_index ha).2 _ hT
    simpa only [contract, confRoot, confStore, tickStore] using hroot

#print axioms liveConfirmedSelection_preceq_voteDutyHead_of_weakGenesis_named

/-- Any two actual prepared confirmation selections lie on one chain. -/
theorem actualConfirmationSelections_compatible_of_weakGenesis
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho) :
    ∀ v ∈ rho.honest, ∀ i B,
      ActualConfirmationSelection S rho v i B →
      ∀ w ∈ rho.honest, ∀ j C,
        ActualConfirmationSelection S rho w j C →
        Block.compatible B C = true := by
  have normalize : ∀ {v : V} {i : Nat} {B : Block V},
      ActualConfirmationSelection S rho v i B →
      ∃ q : Slot,
        Protocol.confirmation_time S.E q ≤ rho.horizon ∧
        (Protocol.update_confirmation_with
          (NamedProfile.gradeContract
            (NamedRecoveryRead.confirmationInputRead S rho v q).cache)
          S.E S.hc (confStore S rho v q) q).live_confirmed = B := by
    intro v i B hsel
    rcases hsel with ⟨time, hi, hpos, htime, hB⟩
    let q := S.E.slotOf time - 1
    have hqk : q + 1 = S.E.slotOf time := Nat.sub_add_cancel hpos
    have hconfirmation : time = Protocol.confirmation_time S.E q := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ, hqk]
      exact htime
    have hstate := stateBefore_tick_eq_stateBeforeTime
      S h.core.toNamedScheduleWellFormed hi
    have hhor := (h.core.toNamedScheduleWellFormed.in_horizon _
      (List.mem_of_getElem? hi)).2
    refine ⟨q, ?_, ?_⟩
    · simpa only [NamedEvent.time, hconfirmation] using hhor
    · change (confirmationDutyOutput S
        (rho.stateBefore S i v) time).core.live_confirmed = B at hB
      rw [hstate, hconfirmation] at hB
      simpa only [confirmationDutyOutput,
        Protocol.NamedDuties.update_confirmation_with,
        NamedRecoveryRead.confirmationInputRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedRun.stateBeforeTime, Run.storeBeforeTime,
        Protocol.NamedStore.setClock,
        Proofs.Optimistic.slotOf_confirmation_time, Nat.add_sub_cancel,
        confStore, tickStore] using hB
  intro v hv i B hB w hw j C hC
  obtain ⟨q, hqhor, hqB⟩ := normalize hB
  obtain ⟨r, hrhor, hrC⟩ := normalize hC
  have hhor : Protocol.confirmation_time S.E (max q r) ≤ rho.horizon := by
    rcases le_total q r with hqr | hrq
    · simpa only [max_eq_right hqr] using hrhor
    · simpa only [max_eq_left hrq] using hqhor
  have hleft := liveConfirmedSelection_preceq_voteDutyHead_of_weakGenesis_named
    S h hhor (Nat.lt_succ_of_le (Nat.le_max_left q r)) (le_refl _) hv hv
  have hright := liveConfirmedSelection_preceq_voteDutyHead_of_weakGenesis_named
    S h hhor (Nat.lt_succ_of_le (Nat.le_max_right q r)) (le_refl _) hw hv
  rw [hqB] at hleft
  rw [hrC] at hright
  exact Block.compatible_of_preceq_common hleft hright

#print axioms actualConfirmationSelections_compatible_of_weakGenesis

/-- Latest and live fields at a bounded read precede the selected vote head. -/
theorem confirmationFields_at_read_preceq_voteDutyHead_of_weakGenesis_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {last d : Slot}
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hupper : d ≤ last + 1) {t : Time}
    (ht : t < Protocol.confirmation_time S.E d)
    {v x : V} (hv : v ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq (rho.storeAt S v t).latest_confirmed
        (voterHeadAt S rho x d) ∧
    Block.Preceq (rho.storeAt S v t).live_confirmed
        (voterHeadAt S rho x d) := by
  obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.filtered_fold_eq_stateBefore
    S h.core.toNamedScheduleWellFormed
    (p := fun e => decide (e.time ≤ t)) (fun e f hk hf => by
      simp only [decide_eq_true_eq] at hf ⊢
      exact (Proofs.Bridges.time_le_of_key_le hk).trans hf)
  have hprefix : ∀ i e, i < n → rho.events[i]? = some e →
      e.time < Protocol.confirmation_time S.E d := by
    intro i e hi he
    exact (of_decide_eq_true (hbefore i e hi he)).trans_lt ht
  have slot_lt_of_time {q : Slot}
      (hqt : Protocol.confirmation_time S.E q <
        Protocol.confirmation_time S.E d) : q < d := by
    by_contra hnot
    have hdq := Nat.le_of_not_gt hnot
    have hvote := vote_time_mono_slots S.E (Nat.succ_le_succ hdq)
    have hconf : Protocol.confirmation_time S.E d ≤
        Protocol.confirmation_time S.E q := by
      rw [← vote_time_succ_add_delta_eq_confirmation_time,
        ← vote_time_succ_add_delta_eq_confirmation_time]
      exact Int.add_le_add_right hvote S.E.Δ
    exact (not_lt_of_ge hconf) hqt
  have confirmation_mono {a b : Slot} (hab : a ≤ b) :
      Protocol.confirmation_time S.E a ≤ Protocol.confirmation_time S.E b := by
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact support_cutoff_mono S.E (Nat.add_le_add_right hab 1)
  have hlatest : Block.Preceq
      (rho.stateBefore S n v).st.latest_confirmed
      (voterHeadAt S rho x d) := by
    rcases ConfirmationOrigin.stateBefore_latest_confirmed_origin S rho v n with
      hgen | ⟨i, C, hi, hsel, hvalue⟩ | ⟨i, hi, hroot⟩
    · rw [hgen]
      exact Protocol.preceq_genesis _
    · obtain ⟨q, hqevent, hchoice, _hqhor⟩ :=
        Proofs.UserConfirmation.selectionAt_slot
          S h.core.toNamedScheduleWellFormed hsel
      have hqd := slot_lt_of_time (hprefix i _ hi hqevent)
      rw [hvalue]
      rcases hchoice with hwalk | hsg
      · rw [← hwalk]
        exact preparedConfirmationWalk_preceq_voteDutyHead_of_gstZero
          S h hhor hqd hupper hv hx
      · have hstate := stateBefore_tick_eq_stateBeforeTime
          S h.core.toNamedScheduleWellFormed hqevent
        let read := NamedRecoveryRead.confirmationInputRead S rho v q
        have hsg' := hsg
        simp only [userSGCandidateAtIndex, hstate, slotOf_confirmation_time,
          Nat.add_sub_cancel, NamedProfile.gradeContract,
          DecoupledConsensusModel.Protocol.frameContract] at hsg'
        have hsgRead :
            (if confirmationEligible S.E read.st.core q
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
              S h hv
                ((confirmation_mono
                  (Nat.le_of_lt_succ (hqd.trans_le hupper))).trans hhor)
                hstable)
            (preparedConfirmationWalk_preceq_voteDutyHead_of_gstZero
              S h hhor hqd hupper hv hx)
    · obtain ⟨time, hievent, hpos, hcut, hG⟩ := hroot
      let q := S.E.slotOf time - 1
      have hqk : q + 1 = S.E.slotOf time := Nat.sub_add_cancel hpos
      have htimeq : time = Protocol.confirmation_time S.E q := by
        rw [Protocol.confirmation_time_eq_support_cutoff_succ, hqk]
        exact hcut
      have hqd := slot_lt_of_time (by
        rw [← htimeq]
        exact hprefix i _ hi hievent)
      have hstate : rho.stateBefore S i v = rho.stateBeforeTime S time v :=
        stateBefore_tick_eq_stateBeforeTime
          S h.core.toNamedScheduleWellFormed hievent
      have hG' : (NamedProfile.gradeContract
          (NamedRecoveryRead.confirmationInputRead S rho v q).cache).stableRoot
            S.E S.hc
            (NamedRecoveryRead.confirmationInputRead S rho v q).st.core.toHealing
            (S.hc.round_of
              (NamedRecoveryRead.confirmationInputRead S rho v q).st.core.s) =
          some (rho.stateBefore S n v).st.latest_confirmed := by
        change DecoupledConsensusModel.Protocol.frameStableRoot
          (NamedActionReads.confirmationReadFrom S
            (rho.stateBefore S i v) time).cache S.E S.hc
          (NamedActionReads.confirmationReadFrom S
            (rho.stateBefore S i v) time).st.core.toHealing
          (S.hc.round_of (NamedActionReads.confirmationReadFrom S
            (rho.stateBefore S i v) time).st.core.s) =
            some (rho.stateBefore S n v).st.latest_confirmed at hG
        rw [hstate, htimeq] at hG
        simpa only [NamedRecoveryRead.confirmationInputRead,
          NamedActionReads.confirmationReadAt] using hG
      exact Block.preceq_trans
        (preparedStableRoot_preceq_confWalk_of_gstZero_clean
          S h hv
            ((confirmation_mono
              (Nat.le_of_lt_succ (hqd.trans_le hupper))).trans hhor)
            hG')
        (preparedConfirmationWalk_preceq_voteDutyHead_of_gstZero
          S h hhor hqd hupper hv hx)
  have hprior : PriorSelectionsPreceqAtIndex
      S rho v n (voterHeadAt S rho x d) := by
    intro i time hin he hpos htime
    let q := S.E.slotOf time - 1
    have hqk : q + 1 = S.E.slotOf time := Nat.sub_add_cancel hpos
    have htimeq : time = Protocol.confirmation_time S.E q := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ, hqk]
      exact htime
    have hqd := slot_lt_of_time (by
      rw [← htimeq]
      exact hprefix i _ hin he)
    have hbound := liveConfirmedSelection_preceq_voteDutyHead_of_weakGenesis_named
      S h hhor hqd hupper hv hx
    have hstate := stateBefore_tick_eq_stateBeforeTime
      S h.core.toNamedScheduleWellFormed he
    change Block.Preceq
      (Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (rho.stateBefore S i v) time).cache)
        S.E S.hc
        (NamedActionReads.confirmationReadFrom S
          (rho.stateBefore S i v) time).st.core
        (S.E.slotOf time - 1)).live_confirmed
      (voterHeadAt S rho x d)
    rw [hstate, htimeq, slotOf_confirmation_time, Nat.add_sub_cancel]
    simpa only [
      NamedRecoveryRead.confirmationInputRead,
      NamedActionReads.confirmationReadAt, confStore, tickStore] using hbound
  have hlive := stateBefore_live_preceq_of_priorSelections
    S rho v (voterHeadAt S rho x d) n hprior
  have hread : NamedRun.readAt S rho t v =
      NamedRun.stateBefore S rho n v := by
    change ((rho.events.filter (fun e => decide (e.time ≤ t))).foldl
      (NamedWorld.step S) NamedWorld.init) v =
        ((rho.events.take n).foldl (NamedWorld.step S) NamedWorld.init) v
    exact congrFun hn v
  simpa only [Run.storeAt, hread] using And.intro hlatest hlive

#print axioms confirmationFields_at_read_preceq_voteDutyHead_of_weakGenesis_named

/-- All latest/live fields in a covered confirmation prefix are compatible. -/
theorem confirmationFields_compatible_at_reads_of_weakGenesis_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho) :
    ∀ last, Protocol.confirmation_time S.E last ≤ rho.horizon →
      ∀ t u, t ≤ Protocol.confirmation_time S.E last →
      u ≤ Protocol.confirmation_time S.E last →
      ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
      Block.compatible (rho.storeAt S v t).latest_confirmed
          (rho.storeAt S w u).latest_confirmed = true ∧
      Block.compatible (rho.storeAt S v t).live_confirmed
          (rho.storeAt S w u).live_confirmed = true ∧
      Block.compatible (rho.storeAt S v t).latest_confirmed
          (rho.storeAt S w u).live_confirmed = true := by
  intro last hhor t u ht hu v hv w hw
  have hnext : Protocol.confirmation_time S.E last <
      Protocol.confirmation_time S.E (last + 1) :=
    (confirmation_time_lt_proposal_time_of_add_two_le
      S.E (Nat.le_refl (last + 2))).trans
      (proposal_time_succ_lt_confirmation_time S.E (last + 1))
  have hleft :=
    confirmationFields_at_read_preceq_voteDutyHead_of_weakGenesis_named
      S h hhor (d := last + 1) (le_refl _) (ht.trans_lt hnext) hv hv
  have hright :=
    confirmationFields_at_read_preceq_voteDutyHead_of_weakGenesis_named
      S h hhor (d := last + 1) (le_refl _) (hu.trans_lt hnext) hw hv
  exact ⟨Block.compatible_of_preceq_common hleft.1 hright.1,
    Block.compatible_of_preceq_common hleft.2 hright.2,
    Block.compatible_of_preceq_common hleft.1 hright.2⟩

#print axioms confirmationFields_compatible_at_reads_of_weakGenesis_named

/-- Every finalized field has a finite source after which all honest vote
heads extend it. -/
theorem finalizedAt_preceq_laterVoteDutyHead_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    (hzero : Protocol.confirmation_time S.E 0 ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) (t : Time) :
    ∃ first : Slot, Protocol.confirmation_time S.E first ≤ rho.horizon ∧
      ∀ last, first ≤ last →
        Protocol.confirmation_time S.E last ≤ rho.horizon →
        ∀ x ∈ rho.honest,
          Block.Preceq (rho.storeAt S v t).F
            (voterHeadAt S rho x (last + 1)) := by
  have hmajority := honestWeightMajority_of_finiteWindows S h.windows hzero
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho (t + 1) v
  have hF : Block.Preceq
      (rho.storeBeforeTime S v (t + 1)).F
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v (t + 1)).toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F (st :=
      (rho.storeBeforeTime S v (t + 1)).toHealing.toFG) (by
        simpa only [Protocol.Store.toHealing] using hFJ)
  have hstore : rho.storeAt S v t = rho.storeBeforeTime S v (t + 1) := by
    have hbool (a b : Int) : decide (a ≤ b) = decide (a < b + 1) := by
      simp only [Int.lt_add_one_iff]
    have hfilter : rho.events.filter (fun e => decide (e.time ≤ t)) =
        rho.events.filter (fun e => decide (e.time < t + 1)) :=
      List.filter_congr (fun e _ => hbool e.time t)
    have hstate : NamedRun.readAt S rho t =
        NamedRun.stateBeforeTime S rho (t + 1) := by
      unfold NamedRun.readAt NamedRun.stateBeforeTime
      rw [hfilter]
    unfold Run.storeAt Run.storeBeforeTime
    rw [hstate]
  rw [hstore]
  rcases WeakFG.fgRoot_confirmationWitness_at_read
      S h.core hmajority hv (t + 1) with
    hgen | ⟨_, _, _, a, ta, ha, hemit, _, _, hT⟩
  · refine ⟨0, hzero, ?_⟩
    intro last _ _ x _
    rw [hgen] at hF
    exact Block.preceq_trans hF (Protocol.preceq_genesis _)
  · have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
    have hsourceHor :
        Protocol.confirmation_time S.E (S.hc.opening_slot a.round) ≤
          rho.horizon := by
      obtain ⟨i, hi, _⟩ := hemit
      have htimeHor := (h.core.toNamedScheduleWellFormed.in_horizon _
        (List.mem_of_getElem? hi)).2
      simpa only [NamedEvent.time, htime] using htimeHor
    refine ⟨S.hc.opening_slot a.round, hsourceHor, ?_⟩
    intro last hlast hlastHor x hx
    have hat : S.a a.round < Protocol.vote_time S.E ((last + 1) + 1) :=
      confirmationTime_lt_nextVote_of_lt S.E (Nat.lt_succ_of_le hlast)
    exact Block.preceq_trans hF
      (((actionSources_preceq_voteDutyHead_of_gstZero
        S h.core h.committees h.gstZero h.windows hlastHor
          (Nat.succ_pos last) (le_refl _) hx a.round hat).2
            a.val_index ha).2 _ hT)

#print axioms finalizedAt_preceq_laterVoteDutyHead_of_gstZero

/-- The latest confirmed record and finality share a protected later head. -/
theorem latestConfirmed_compatible_finalized_of_weakGenesis
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    (hzero : Protocol.confirmation_time S.E 0 ≤ rho.horizon)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (t u : Time) :
    Block.compatible (rho.storeAt S v t).latest_confirmed
      (rho.storeAt S w u).F = true := by
  obtain ⟨a, ha, hL⟩ :=
    latestConfirmedAt_preceq_laterVoteDutyHead_of_gstZero
      S h hzero hv t
  obtain ⟨b, hb, hF⟩ :=
    finalizedAt_preceq_laterVoteDutyHead_of_gstZero
      S h hzero hw u
  have hhor : Protocol.confirmation_time S.E (max a b) ≤ rho.horizon := by
    rcases le_total a b with hab | hba
    · simpa only [max_eq_right hab] using hb
    · simpa only [max_eq_left hba] using ha
  exact Block.compatible_of_preceq_common
    (hL (max a b) (Nat.le_max_left _ _) hhor v hv)
    (hF (max a b) (Nat.le_max_right _ _) hhor v hv)

#print axioms latestConfirmed_compatible_finalized_of_weakGenesis

/-- One exposed confirmed output has a finite protected vote-head bound. -/
theorem confirmedOutputAt_preceq_laterVoteDutyHead_of_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    (hzero : Protocol.confirmation_time S.E 0 ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) (t : Time) :
    ∃ first : Slot, Protocol.confirmation_time S.E first ≤ rho.horizon ∧
      ∀ last, first ≤ last →
        Protocol.confirmation_time S.E last ≤ rho.horizon →
        ∀ x ∈ rho.honest,
          Block.Preceq (confirmedOutputAt S rho v t)
            (voterHeadAt S rho x (last + 1)) := by
  obtain ⟨a, ha, hF⟩ :=
    finalizedAt_preceq_laterVoteDutyHead_of_gstZero S h hzero hv t
  obtain ⟨b, hb, hL⟩ :=
    latestConfirmedAt_preceq_laterVoteDutyHead_of_gstZero S h hzero hv t
  have hhor : Protocol.confirmation_time S.E (max a b) ≤ rho.horizon := by
    rcases le_total a b with hab | hba
    · simpa only [max_eq_right hab] using hb
    · simpa only [max_eq_left hba] using ha
  refine ⟨max a b, hhor, ?_⟩
  intro last hlast hlastHor x hx
  exact ConfirmedOutput.get_confirmed_preceq _
    (StableRecord.stableBelowConfirmed_storeAt
      S h.core.toNamedScheduleWellFormed v t)
    (hF last ((Nat.le_max_left _ _).trans hlast) hlastHor x hx)
    (hL last ((Nat.le_max_right _ _).trans hlast) hlastHor x hx)

#print axioms confirmedOutputAt_preceq_laterVoteDutyHead_of_gstZero

/-- Honest confirmed outputs are globally compatible, including when the run
ends before the first confirmation. -/
theorem confirmedOutputCompatibleFrom_of_weakGenesis_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho) :
    ConfirmedOutputCompatibleFrom S rho 0 := by
  intro u hu v hv t t' _ht0 _ht0' ht ht'
  by_cases hzero : Protocol.confirmation_time S.E 0 ≤ rho.horizon
  · obtain ⟨a, ha, hA⟩ :=
      confirmedOutputAt_preceq_laterVoteDutyHead_of_gstZero
        S h hzero hu t
    obtain ⟨b, hb, hB⟩ :=
      confirmedOutputAt_preceq_laterVoteDutyHead_of_gstZero
        S h hzero hv t'
    have hhor : Protocol.confirmation_time S.E (max a b) ≤ rho.horizon := by
      rcases le_total a b with hab | hba
      · simpa only [max_eq_right hab] using hb
      · simpa only [max_eq_left hba] using ha
    exact Block.compatible_of_preceq_common
      (hA (max a b) (Nat.le_max_left _ _) hhor u hu)
      (hB (max a b) (Nat.le_max_right _ _) hhor u hu)
  · have hshort : rho.horizon < Protocol.confirmation_time S.E 0 :=
      lt_of_not_ge hzero
    have hstore (x : V) (r : Time) :
        rho.storeAt S x r = rho.storeBeforeTime S x (r + 1) := by
      have hbool (a b : Int) : decide (a ≤ b) = decide (a < b + 1) := by
        simp only [Int.lt_add_one_iff]
      have hfilter : rho.events.filter (fun e => decide (e.time ≤ r)) =
          rho.events.filter (fun e => decide (e.time < r + 1)) :=
        List.filter_congr (fun e _ => hbool e.time r)
      have hstate : NamedRun.readAt S rho r =
          NamedRun.stateBeforeTime S rho (r + 1) := by
        unfold NamedRun.readAt NamedRun.stateBeforeTime
        rw [hfilter]
      unfold Run.storeAt Run.storeBeforeTime
      rw [hstate]
    have hfinalized (x : V) {r : Time}
        (hr : r < Protocol.confirmation_time S.E 0) :
        (rho.storeAt S x r).F = Block.genesis := by
      rw [hstore]
      have hread : r + 1 ≤ Protocol.confirmation_time S.E 0 :=
        Int.add_one_le_iff.mpr hr
      have htime (z : Int) (hz : 0 < z) :
          4 * z * 0 + 6 * z ≤ 4 * z * 2 := by omega
      have hproposal : r + 1 ≤ Protocol.proposal_time S.E 2 :=
        hread.trans (htime S.E.Δ S.E.Δ_pos)
      obtain ⟨D, hD, hDF, _⟩ :=
        Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime S rho (r + 1) x
      have hinv := Proofs.NamedRuntime.stateBeforeTime_invariants S rho (r + 1) x
      have hDT : D.erase ∈
          (rho.storeBeforeTime S x (r + 1)).core.T := by
        rw [Run.storeBeforeTime, hinv.1.1.1.1]
        exact Finset.mem_image_of_mem NamedBlock.erase hD
      have hslot : D.erase.slot < 2 :=
        Proofs.NamedSlotFreshness.block_slot_lt_of_mem_beforeTime_of_le_proposal
          S h.core (by decide) hproposal hDT
      change (rho.stateBeforeTime S (r + 1) x).st.core.F = Block.genesis
      rw [← hDF]
      cases D with
      | genesis => rfl
      | node p k root votes support ats val =>
        have hpmem : p.erase ∈
            (rho.storeBeforeTime S x (r + 1)).T :=
          Proofs.NamedSlotFreshness.ancestor_mem_storeBeforeTime S h.core hDT
            (Protocol.preceq_of_parent? rfl)
        have hpSlot : p.erase.slot < k :=
          Proofs.NamedSlotFreshness.parent_slot_lt_of_mem_storeBeforeTime
            S h.core hDT (by simp [NamedBlock.erase])
        have hp : p = (NamedBlock.genesis : NamedBlock V) := by
          have hpErase : p.erase = Block.genesis := by
            by_contra hnot
            have hpp :=
              Proofs.NamedSlotFreshness.parent_slot_lt_of_mem_storeBeforeTime
                S h.core hpmem hnot
            change k < 2 at hslot
            have hpZero : p.erase.slot = 0 := Nat.eq_zero_of_le_zero
              (Nat.le_of_lt_succ
                (hpSlot.trans_le (Nat.le_of_lt_succ hslot)))
            rw [hpZero] at hpp
            exact Nat.not_lt_zero _ hpp
          cases p with
          | genesis => rfl
          | node pp ps pr pv psv pa ppv =>
            simp only [NamedBlock.erase, reduceCtorEq] at hpErase
        subst p
        let D : NamedBlock V :=
          .node .genesis k root votes support ats val
        let parentState := Protocol.derive_named S.E S.cfg
          (NamedBlock.genesis : NamedBlock V)
        let folded := Protocol.fold_rows
          (Protocol.TimeoutBinding.targeted V)
          parentState D.erase D.attestations
        have hfields := NamedDerivationGeometry.fold_context_fields
          (Protocol.TimeoutBinding.targeted V) D.attestations
          { parentState with s := D.erase.slot }
        have hJfold : folded.J = Block.genesis := by
          change (D.attestations.foldl
            (Protocol.process_attestation_with
              (Protocol.TimeoutBinding.targeted V))
            { parentState with s := D.erase.slot }).J = Block.genesis
          rw [hfields.2.2.2.1]
          rfl
        have hFfold : folded.F = Block.genesis := by
          change (D.attestations.foldl
            (Protocol.process_attestation_with
              (Protocol.TimeoutBinding.targeted V))
            { parentState with s := D.erase.slot }).F = Block.genesis
          rw [hfields.2.2.2.2.2.1]
          rfl
        change (Protocol.process_height_events
          S.E S.cfg folded).F = Block.genesis
        rw [Protocol.process_height_events_F, Protocol.afterFin_F]
        split <;> assumption
    have hout (x : V) (r : Time) (hr : r ≤ rho.horizon) :
        confirmedOutputAt S rho x r = Block.genesis := by
      have hF := hfinalized x (hr.trans_lt hshort)
      have hL := latestConfirmedAt_eq_genesis_of_short_horizon
        S h.core.toNamedScheduleWellFormed hshort x r
      have hs := StableRecord.stableBelowConfirmed_storeAt
        S h.core.toNamedScheduleWellFormed x r
      have houtLatest := ConfirmedOutput.get_confirmed_eq_latest
        (rho.storeAt S x r).core hs (by
          change Block.Preceq (rho.storeAt S x r).F
            (rho.storeAt S x r).latest_confirmed
          rw [hF, hL]
          exact Block.preceq_self _)
      simpa only [confirmedOutputAt, hL] using houtLatest
    rw [hout u t ht, hout v t' ht']
    exact Block.compatible_of_preceq_common
      (Block.preceq_self _) (Block.preceq_self _)

#print axioms confirmedOutputCompatibleFrom_of_weakGenesis_named

/-- Confirmed outputs are monotone from genesis. -/
theorem confirmedOutputMonotoneFrom_of_weakGenesis_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho) :
    ConfirmedOutputMonotoneFrom S rho 0 := by
  apply ConfirmedOutput.confirmedOutputMonotoneFrom_of_cross
    S h.core.toNamedScheduleWellFormed
    (confirmationMonotoneFrom S h.core.toNamedScheduleWellFormed 0
      (confirmationCompatibleFrom_of_weakGenesis_named S h 0))
    (fun w _hw s _hs _hhor =>
      StableRecord.stableBelowConfirmed_storeAt
        S h.core.toNamedScheduleWellFormed w s)
  intro v hv t t' _ht htt' hhor
  by_cases hzero : Protocol.confirmation_time S.E 0 ≤ rho.horizon
  · exact latestConfirmed_compatible_finalized_of_weakGenesis
      S h hzero hv hv t t'
  · have hshort : rho.horizon < Protocol.confirmation_time S.E 0 :=
      lt_of_not_ge hzero
    rw [latestConfirmedAt_eq_genesis_of_short_horizon
      S h.core.toNamedScheduleWellFormed hshort v t]
    exact Block.compatible_of_preceq_common
      (Protocol.preceq_genesis _) (Block.preceq_self _)

#print axioms confirmedOutputMonotoneFrom_of_weakGenesis_named

/-- Every positive honest proposal remains below the finality-aware output. -/
theorem userProposalsConfirmedAfter_of_weakGenesis_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho) :
    UserProposalsConfirmedAfter S rho 0 := by
  intro s hs hhor hprop
  obtain ⟨B, hB, hat⟩ :=
    latestAtProposalField_of_weakGenesis S rho h s hs hhor hprop
  refine ⟨B, hB, hat, ?_⟩
  intro v hv t ht hthor
  have hcompat := confirmationCompatibleFrom_of_weakGenesis_named S h 0
  have hmono := confirmationMonotoneFrom S
    h.core.toNamedScheduleWellFormed 0 hcompat
  have hpre : Block.Preceq B.erase
      (rho.storeAt S v t).latest_confirmed := by
    simpa only [hat v hv] using
      hmono v hv (Protocol.confirmation_time S.E s) t
        (Proofs.Optimistic.confirmation_time_nonneg S.E s) ht hthor
  have hzero : Protocol.confirmation_time S.E 0 ≤ rho.horizon := by
    have hfirst : Protocol.confirmation_time S.E 0 ≤
        Protocol.confirmation_time S.E s := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ,
        Protocol.confirmation_time_eq_support_cutoff_succ]
      exact support_cutoff_mono S.E
        (Nat.succ_le_succ (Nat.zero_le s))
    exact hfirst.trans hhor
  have hcross := latestConfirmed_compatible_finalized_of_weakGenesis
    S h hzero hv hv (Protocol.confirmation_time S.E s) t
  rw [hat v hv] at hcross
  exact ConfirmedOutput.preceq_get_confirmed_of_latest _
    (StableRecord.stableBelowConfirmed_storeAt
      S h.core.toNamedScheduleWellFormed v t)
    hpre hcross

#print axioms userProposalsConfirmedAfter_of_weakGenesis_named

end WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- GST-zero safety with only the four directed Claim 1 fields left as
hypotheses. -/
theorem gstZeroSafety_of_fourFields
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest) (hgst : S.E.t_GST = 0)
    (hawake : ∀ r, 0 < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (havailableConfirmations : AvailableConfirmationsFrom S rho 0)
    (hliveMonotone : ∀ v ∈ rho.honest, ∀ t t', t ≤ t' →
      Block.Preceq (rho.storeAt S v t).live_confirmed
        (rho.storeAt S v t').live_confirmed)
    (hliveAtConfirmation : ∀ s, 0 < s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t,
      t < Protocol.confirmation_time S.E s →
      Block.Preceq (rho.storeAt S u t).live_confirmed
        (rho.storeAt S v
          (Protocol.confirmation_time S.E s)).live_confirmed)
    (hproposalReads : ∀ s, 0 < s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      S.E.proposer s ∈ rho.honest → HonestProposalReadSafety S rho s) :
    GSTZeroGuarantees S rho := by
  let h : WeakGenesis S rho :=
    { execution := ExecutionValid.ofNamedAdmissibleCore adm
      synchrony := adm.toNamedSynchrony
      committees := hcom
      gstZero := hgst
      windows := hawake }
  exact gstZeroSafety_of_tenFields S adm hcom hgst hawake
    (WeakGenesis.availableChainFrom_of_weakGenesis_named S h)
    havailableConfirmations
    (WeakGenesis.actualConfirmationSelections_compatible_of_weakGenesis S h)
    (WeakGenesis.confirmationFields_compatible_at_reads_of_weakGenesis_named S h)
    hliveMonotone hliveAtConfirmation hproposalReads
    (WeakGenesis.confirmedOutputCompatibleFrom_of_weakGenesis_named S h)
    (WeakGenesis.confirmedOutputMonotoneFrom_of_weakGenesis_named S h)
    (WeakGenesis.userProposalsConfirmedAfter_of_weakGenesis_named S h)

#print axioms gstZeroSafety_of_fourFields

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
