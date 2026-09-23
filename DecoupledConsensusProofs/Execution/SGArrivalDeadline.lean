module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrival
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrivalStampCarrier

@[expose] public section

/-! Deadline form of the available SG arrival transport.

`Proofs.NamedSGArrival.healthy_emitted_sg_at_next_g2` consumes its `FormationMargin`
hypothesis exactly once, through `formation_margin_action_deadline`, which
yields the weaker `S.a a.round + Δ ≤ b0`. The asynchrony-resilience closure has
that action deadline for the round below the outage but not the margin, so it
needs the same transport stated at the deadline.

`NamedSGArrival` now carries that split itself, so this module is a one-line
delegation. It is kept as the name the closure reads. -/
namespace DecoupledConsensusModel.Proofs.NamedOutageClosure.SGArrivalDeadline
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.NamedOutageHistory
variable {V : Type} [DecidableEq V] [Fintype V]

private theorem opening_le_action (S : Setup V) (q : Round) :
    opening S.E S.hc q ≤ S.a q := by
  unfold opening Setup.a Protocol.HealConfig.a Protocol.proposal_time Env.t slotStart
  simp only [Protocol.HealConfig.opening_slot]
  push_cast
  nlinarith [S.E.Δ_pos]

private theorem early_next_g2_lt_opening (S : Setup V) (q : Round) :
    early S.E S.hc (q + 1) .g2 < opening S.E S.hc (q + 1) := by
  unfold early Phase.earlyOffset
  nlinarith [S.E.Δ_pos]

private theorem round_bounds_of_clock (S : Setup V) (q r : Round)
    (st : Protocol.NamedStore V)
    (hclock : st.core.s = S.E.slotOf st.core.t)
    (hlo : opening S.E S.hc q ≤ st.core.t)
    (hhi : st.core.t < opening S.E S.hc r) :
    q ≤ S.hc.round_of st.core.s ∧ S.hc.round_of st.core.s < r := by
  have hR : 0 < S.hc.R := Nat.zero_lt_of_lt S.hc.R_ge_two
  have hslot := Protocol.slot_le_slotOf_of_proposal_time_le S.E hlo
  rw [← hclock] at hslot
  refine ⟨(Nat.le_div_iff_mul_le hR).mpr hslot, ?_⟩
  by_contra hn
  have hr : r ≤ S.hc.round_of st.core.s := Nat.le_of_not_gt hn
  have hcur : S.hc.opening_slot (S.hc.round_of st.core.s) ≤ st.core.s :=
    Nat.div_mul_le_self st.core.s S.hc.R
  have hro : S.hc.opening_slot r ≤ st.core.s :=
    (Nat.mul_le_mul_right S.hc.R hr).trans hcur
  have ht0 : 0 ≤ st.core.t :=
    (Proofs.Optimistic.proposal_time_nonneg S.E (S.hc.opening_slot q)).trans hlo
  have hTslot : Protocol.proposal_time S.E st.core.s ≤ st.core.t := by
    rw [hclock]
    exact Protocol.proposal_time_slotOf_le S.E ht0
  exact (not_lt_of_ge ((Protocol.proposal_time_mono S.E hro).trans hTslot)) hhi

private theorem delivery_round_before_next_early
    (S : Setup V) (rho : NamedRun V) (sch : NamedScheduleWellFormed S rho)
    {i : Nat} {reader : V} {o : NamedObject V} {td : Time} (q : Round)
    (he : rho.events[i]? = some (.deliver reader o td))
    (hlo : S.a q ≤ td) (hhi : td < early S.E S.hc (q + 1) .g2) :
    S.hc.round_of (NamedRun.stateBefore S rho i reader).st.core.s = q := by
  have hmem := List.mem_of_getElem? he
  have hr : reader ∈ rho.honest := sch.honest_only _ hmem
  have htick := sch.tick_total reader hr (S.a q)
    (Proofs.HealingLemmas.publicTime_a S q) (Proofs.HealingLemmas.a_nonneg S q)
    (hlo.trans (sch.in_horizon _ hmem).2)
  have hclock := SGArrival.tick_le_clock_before_delivery S rho sch he htick hlo
  have hup := Proofs.NamedRuntime.stateBefore_clock_le_event S rho sch.sorted he
    (sch.in_horizon _ hmem).1 reader
  have hb := round_bounds_of_clock S q (q + 1)
    (NamedRun.stateBefore S rho i reader).st
    (SGArrival.stateBefore_slot_clock S rho i reader)
    ((opening_le_action S q).trans hclock)
    (hup.trans_lt (hhi.trans (early_next_g2_lt_opening S q)))
  exact Nat.le_antisymm (Nat.lt_succ_iff.mp hb.2) hb.1

private theorem delayed_call_input
    (S : Setup V) (rho : NamedRun V) (sch : NamedScheduleWellFormed S rho)
    {i : Nat} {reader : V} {a : NamedAttestation V} {td : Time}
    (hcall : NamedRun.actualHandlesAt S rho i reader (.attest a) td)
    (hlo : S.a a.round ≤ td)
    (hhi : td < early S.E S.hc (a.round + 1) .g2) :
    ∃ input : Protocol.NamedStore V,
      Proofs.NamedStore.Coherent S.E S.cfg input ∧ SGArrival.Data td input ∧
      S.hc.round_of input.core.s = a.round ∧
      ∀ b : NamedAttestation V,
        b ∈ (Protocol.NamedAdmission.admit_row S.hc input a).sg_rows b.round →
        b ∈ (NamedRun.stateBefore S rho (i + 1) reader).st.sg_rows b.round := by
  rcases hcall.1 with hdirect | ⟨B, k, before, hF1⟩
  · rcases hdirect with ⟨t, he, hem⟩ | ⟨t, he⟩
    · have hemit : NamedRun.emits S rho reader (.attest a) t := ⟨i, he, hem⟩
      obtain ⟨j, hj, _, hrow, _, hround, htime, hawake⟩ :=
        Proofs.NamedOutageInputs.emitted_attestation_stages S rho hemit
      have hij : j = i := by
        obtain ⟨_, hgetj⟩ := List.getElem?_eq_some_iff.mp hj
        obtain ⟨_, hgeti⟩ := List.getElem?_eq_some_iff.mp he
        exact (List.Nodup.getElem_inj_iff sch.nodup).mp (by rw [hgetj, hgeti])
      subst j
      have ht : t = td := SGArrival.handle_event_time S rho hcall he
      rcases htime with rfl
      rcases ht.symm with rfl
      let n := actionReadFrom S (NamedRun.stateBefore S rho i reader) a.round
      have hpre := (SGArrival.data_at_event S rho sch he reader).1
      have hd : SGArrival.Data (S.a a.round) n.st :=
        SGArrival.confirmation_data _ S _ _ _
          (SGArrival.clock_data S _ _ _ le_rfl hpre)
      refine ⟨n.st,
        (Proofs.NamedOutageInputs.action_read_invariant S rho i reader a.round).1.1,
        hd, hround.symm, ?_⟩
      intro b hb
      rw [Proofs.NamedRuntime.stateBefore_tick S rho he,
        SGArrival.action_tick_store S reader _ a.round hawake]
      change b ∈ (Protocol.NamedAdmission.admit_row S.hc n.st
        (Protocol.NamedDuties.attest_with (NamedProfile.gradeContract n.cache)
          S.E S.hc (S.node reader) n.st n.record).2.2).sg_rows b.round
      rwa [hrow]
    · have ht : t = td := SGArrival.handle_event_time S rho hcall he
      subst t
      refine ⟨(NamedRun.stateBefore S rho i reader).st,
        (Proofs.NamedRuntime.stateBefore_invariants S rho i reader).1.1.1,
        (SGArrival.data_at_event S rho sch he reader).1,
        delivery_round_before_next_early S rho sch a.round he hlo hhi, ?_⟩
      intro b hb
      rw [Proofs.NamedReceiptCallsBase.delivery_result S rho he]
      exact hb
  · have hbefore : Proofs.NamedStore.Coherent S.E S.cfg before ∧
        SGArrival.Data td before ∧ S.hc.round_of before.core.s = a.round := by
      rcases hF1.1 with ⟨t, he, rfl⟩ | ⟨t, he, hem, rfl⟩
      · have ht : t = td := SGArrival.handle_event_time S rho hcall he
        subst t
        exact ⟨(Proofs.NamedRuntime.stateBefore_invariants S rho i reader).1.1.1,
          (SGArrival.data_at_event S rho sch he reader).1,
          delivery_round_before_next_early S rho sch a.round he hlo hhi⟩
      · have ht : t = td := SGArrival.handle_event_time S rho hcall he
        subst t
        refine ⟨NamedStore.coherent_clock S.E S.cfg _ td
          (Proofs.NamedRuntime.stateBefore_invariants S rho i reader).1.1.1,
          SGArrival.clock_data S td _ td le_rfl
            (SGArrival.data_at_event S rho sch he reader).1, ?_⟩
        have hb := round_bounds_of_clock S a.round (a.round + 1)
          (Protocol.NamedStore.setClock S.E
            (NamedRun.stateBefore S rho i reader).st td) rfl
          ((opening_le_action S a.round).trans hlo)
          (hhi.trans (early_next_g2_lt_opening S a.round))
        exact Nat.le_antisymm (Nat.lt_succ_iff.mp hb.2) hb.1
    let input := Execution.NamedReceiptCalls.f1Input S before B k
    have hcore := NamedStore.coherent_process_block S.E S.hc S.cfg before B hbefore.1
    have hcoh : Proofs.NamedStore.Coherent S.E S.cfg input :=
      NamedAdmission.coherent_admit_rows S.E S.hc S.cfg _
        (B.attestations.take k) hcore
    have hd : SGArrival.Data td input := SGArrival.rows_data S td _
      (B.attestations.take k) hcore
      (SGArrival.core_block_data S td before B hbefore.2.1)
    have hround : S.hc.round_of input.core.s = a.round := by
      rw [(NamedReceiptCallsF1.actual_f1_clock S rho i reader B k a before hF1).2]
      exact hbefore.2.2
    refine ⟨input, hcoh, hd, hround, ?_⟩
    intro b hb
    apply SGArrival.block_call_rows_after_event S rho hF1.1 b
    rw [(NamedReceiptCallsF1.actual_carried_call S rho i reader B k a before hF1).2.2.2.2]
    exact NamedReceiptCallsF1.admit_rows_mem_mono S.hc _
      (B.attestations.drop (k + 1)) b hb

private theorem honest_row_after_delayed_call
    (S : Setup V) (rho : NamedRun V) (sch : NamedScheduleWellFormed S rho)
    (auth : NamedUnforgeable S rho)
    {i : Nat} {reader : V} {a : NamedAttestation V} {td : Time}
    (ha : a.val_index ∈ rho.honest)
    (hem : NamedRun.emits S rho a.val_index (.attest a) (S.a a.round))
    (hcall : NamedRun.actualHandlesAt S rho i reader (.attest a) td)
    (hlo : S.a a.round ≤ td)
    (hhi : td < early S.E S.hc (a.round + 1) .g2) :
    a ∈ (NamedRun.stateBefore S rho (i + 1) reader).st.sg_rows a.round := by
  obtain ⟨input, hcoh, hd, hround, hpost⟩ :=
    delayed_call_input S rho sch hcall hlo hhi
  have hpool := SGArrival.honest_input_pool_row S rho sch auth ha hem
    i reader input td hcoh hd hpost
  have hsub : Protocol.round_votes input.core a.erase ⊆ {a.confirmed} := by
    intro key hk
    obtain ⟨b, hb, hv, hkey⟩ := Proofs.Optimistic.mem_round_votes.mp hk
    have he := (hpool b hb hv).1
    subst b
    exact Finset.mem_singleton.mpr hkey.symm
  by_cases hduplicate : a.confirmed ∈ Protocol.round_votes input.core a.erase
  · obtain ⟨b, hb, hv, _⟩ := Proofs.Optimistic.mem_round_votes.mp hduplicate
    have hheld := (hpool b hb hv).2
    exact hpost a
      (NamedReceiptCallsF1.admit_row_mem_mono S.hc input a a hheld)
  · have hcard : (Protocol.round_votes input.core a.erase).card ≤ 1 := by
      simpa only [Finset.card_singleton] using Finset.card_le_card hsub
    have hguard : ¬ (a.round < S.hc.round_of input.core.s - S.hc.η_SG ∨
        S.hc.round_of input.core.s < a.round ∨
        a.confirmed ∈ Protocol.round_votes input.core a.erase ∨
        (Protocol.round_votes input.core a.erase).card = 2) := by
      rw [hround]
      simp only [not_or]
      exact ⟨Nat.not_lt.mpr (Nat.sub_le _ _), Nat.lt_irrefl _,
        hduplicate, by omega⟩
    have hpre : a.erase ∉ input.core.sg_pool a.round := by
      intro hmem
      exact hduplicate
        (Proofs.Optimistic.mem_round_votes.mpr ⟨a.erase, hmem, rfl, rfl⟩)
    have hnew : a.erase ∈
        (Protocol.on_sg_vote S.hc input.core a.erase).sg_pool a.round := by
      dsimp only [Protocol.on_sg_vote]
      simp only [show a.erase.round = a.round from rfl,
        show a.erase.confirmed = a.confirmed from rfl]
      rw [if_neg hguard]
      simp [Protocol.Store.sg_pool]
    exact hpost a
      (NamedAdmission.admitted_original_row S.hc input a hpre hnew)

/-- A delayed outage delivery before the next G2 early cutoff is present in
that strict raw view with its first receipt stamp. -/
theorem outage_emitted_sg_raw_at_next_g2
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) {a : NamedAttestation V}
    (ha : a.val_index ∈ rho.honest)
    (hem : NamedRun.emits S rho a.val_index (.attest a) (S.a a.round))
    {i : Nat} {reader : V} {td : Time}
    (hlo : S.a a.round ≤ td)
    (hhi : td < early S.E S.hc (a.round + 1) .g2)
    (hcall : NamedRun.actualHandlesAt S rho i reader (.attest a) td) :
    Protocol.sgVote a.erase ∈ rawInputs
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (a.round + 1) .g2) reader).st.core.toHealing.gradeView
      S.hc.η_SG (a.round + 1)
      (early S.E S.hc (a.round + 1) .g2) a.val_index := by
  have hrow := honest_row_after_delayed_call S rho
    hexec.core.toNamedScheduleWellFormed hexec.core.toNamedUnforgeable
    ha hem hcall hlo hhi
  obtain ⟨e, he, _, het⟩ := hcall.2
  obtain ⟨_, stamp, hstampBound, hstampEvent⟩ :=
    Proofs.NamedSGArrival.held_row_own_and_stamp_at_event S rho
      hexec.core.toNamedScheduleWellFormed he reader a.round a hrow
  have heEarly : e.time < early S.E S.hc (a.round + 1) .g2 := by
    simpa only [het] using hhi
  have heCut : e.time < domain S.E S.hc (a.round + 1) .g2 :=
    heEarly.trans_le (SGArrival.early_le_domain S (a.round + 1))
  let n := (rho.events.filter (fun event => decide
    (event.time < domain S.E S.hc (a.round + 1) .g2))).length
  have hread : NamedRun.stateBeforeTime S rho
      (domain S.E S.hc (a.round + 1) .g2) = NamedRun.stateBefore S rho n := by
    exact Proofs.Optimistic.stateBeforeTime_eq_take S
      hexec.core.toNamedScheduleWellFormed _
  have hin : i < n := by
    by_contra hnot
    have hni : n ≤ i := Nat.le_of_not_gt hnot
    have hle := Proofs.Optimistic.le_time_of_index_ge S
      hexec.core.toNamedScheduleWellFormed
      (t := domain S.E S.hc (a.round + 1) .g2) (j := i) (e := e) hni he
    exact (not_le_of_gt heCut) hle
  have hrowN := Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono S rho reader
    (Nat.succ_le_of_lt hin) hrow
  let target := NamedRun.stateBeforeTime S rho
    (domain S.E S.hc (a.round + 1) .g2) reader
  have hrowCut : a ∈ target.st.sg_rows a.round := by
    dsimp only [target]
    rw [hread]
    exact hrowN.1
  have hstampCut : target.st.core.timestamp_sg_vote
      (Protocol.sgVote a.erase) = some (stamp : Stamp) := by
    dsimp only [target]
    rw [hread]
    exact hrowN.2.trans hstampEvent
  have hoccur : occurrenceBefore
      (target.st.core.timestamp_sg_vote (Protocol.sgVote a.erase))
      (early S.E S.hc (a.round + 1) .g2) = true := by
    simp only [hstampCut, occurrenceBefore, decide_eq_true_eq]
    exact WithBot.coe_lt_coe.mpr (hstampBound.trans_lt heEarly)
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
    (domain S.E S.hc (a.round + 1) .g2) reader).1.1.1
  have hpool := NamedAdmission.pool_view_mem target.st hcoh.2.2.2.1 a hrowCut
  have hsg : Protocol.sgVote a.erase ∈
      target.st.core.toHealing.gradeView.sg_votes a.round :=
    Finset.mem_image_of_mem Protocol.sgVote hpool
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_biUnion.mpr ?_, rfl, hoccur⟩
  exact ⟨a.round, List.mem_toFinset.mpr
    (SGArrival.previous_round_in_window S a.round), hsg⟩

/-- The available transport at the action deadline. -/
theorem healthy_emitted_sg_at_next_g2_of_deadline (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) {a : NamedAttestation V}
    (ha : a.val_index ∈ rho.honest)
    (hem : NamedRun.emits S rho a.val_index (.attest a) (S.a a.round))
    (hdead : S.a a.round + S.E.Δ ≤ b0) :
    ∀ reader ∈ rho.honest,
      let r := a.round + 1
      let n := NamedRun.stateBeforeTime S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) reader
      a ∈ n.st.sg_rows a.round ∧
      occurrenceBefore (n.st.core.timestamp_sg_vote (Protocol.sgVote a.erase))
        (DecoupledConsensusModel.Protocol.early S.E S.hc r .g2) = true ∧
      Protocol.sgVote a.erase ∈ DecoupledConsensusModel.Protocol.rawInputs n.st.core.toHealing.gradeView
        S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g2) a.val_index :=
  Proofs.NamedSGArrival.healthy_emitted_sg_at_next_g2_of_deadline S rho b0 b1 hexec ha hem hdead

#print axioms healthy_emitted_sg_at_next_g2_of_deadline
#print axioms outage_emitted_sg_raw_at_next_g2

end DecoupledConsensusModel.Proofs.NamedOutageClosure.SGArrivalDeadline

end
