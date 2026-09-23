module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.RecoveryProposalWalkTransfer
public import DecoupledConsensusProofs.Protocol.ChainState.RecoverySourceSupport
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingContinuation
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalPivot
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.Handlers.HonestProposalAdmission
public import DecoupledConsensusProofs.Protocol.Schedule.AdoptionTransport
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalSnapshotBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Head.PreparedProposalReadBridge
public import DecoupledConsensusProofs.Protocol.Handlers.GoldfishVotePool

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Named prepared proposal-cap interfaces
The previous source used one total erased proposal and two erased duty stores. The
live interface binds the retained proposal body and reads both duties from
their prepared named reads. The source and target walks therefore use the
frozen declarations in `NamedProposalPivot.lean` directly.
-/






private theorem proposalDutyPool_eq_storeBeforeTime_pool
    (S : Setup V) (rho : Run V) (s : Slot) :
    (proposalDutyRead S rho (s + 1)).st.core.pool s =
      (Run.storeBeforeTime S rho (S.E.proposer (s + 1))
        (Protocol.proposal_time S.E (s + 1))).core.pool s := by
  rfl


private theorem slotOf_of_proposal_before_next_proposal
    (E : Env V) (s : Slot) {p : Time}
    (hlo : Protocol.proposal_time E s ≤ p)
    (hhi : p < Protocol.proposal_time E (s + 1)) :
    E.slotOf p = s := by
  have hbounds : ∀ a d q : Int, 0 < d → a ≤ q → q < a + 4 * d →
      0 ≤ q - a ∧ q - a < 4 * d := by
    intro a d q hd h1 h2
    omega
  have hnext : Protocol.proposal_time E (s + 1) = E.t s + 4 * E.Δ := by
    unfold Protocol.proposal_time Env.t slotStart
    push_cast
    ring
  have hhi' : p < E.t s + 4 * E.Δ := by rwa [← hnext]
  obtain ⟨h0, h1⟩ := hbounds (E.t s) E.Δ p E.Δ_pos hlo hhi'
  have hrw : p = 4 * E.Δ * (s : Time) + (p - E.t s) := by
    unfold Env.t slotStart
    ring
  rw [Env.slotOf, hrw]
  exact Proofs.Optimistic.slotOfTime_add E.Δ E.Δ_pos s _ h0 h1

private theorem gfVote_delivery_settled_at_proposalDuty
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hprop : S.E.proposer (s + 1) ∈ rho.honest)
    {i : Nat} {u : GoldfishVote V} {t : Time}
    (hi : rho.events[i]? = some
      (Event.deliver (S.E.proposer (s + 1)) (Object.gfVote u) t))
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.proposal_time S.E (s + 1)) :
    u ∈ (proposalDutyRead S rho (s + 1)).st.core.pool s ∨
      Protocol.equivocates
        ((proposalDutyRead S rho (s + 1)).st.core.pool s)
        u.val_index = true := by
  let pre := (rho.stateBefore S i (S.E.proposer (s + 1))).st.core
  have hpreTime : pre.t ≤ t := by
    simpa [pre, Event.time] using
      (Protocol.store_time_le_event_time S
        adm.toNamedScheduleWellFormed hi (S.E.proposer (s + 1)))
  have hclock0 : Protocol.proposal_time S.E s ≤ pre.t := by
    have hclock' := Protocol.tick_le_store_time S
      adm.toNamedScheduleWellFormed hi
      (adm.tick_total (S.E.proposer (s + 1)) hprop _
        (Proofs.Optimistic.publicTime_proposal_time S s)
        (Proofs.Optimistic.proposal_time_nonneg S.E s)
        (le_trans hlo
          (adm.in_horizon _ (List.mem_of_getElem? hi)).2))
      hlo
    simpa [pre] using hclock'
  have hslot : pre.s = s := by
    have hslot' := Proofs.NamedStoreBridge.slotOfClock_stateBefore
      S rho i (S.E.proposer (s + 1))
    unfold Proofs.Optimistic.SlotOfClock at hslot'
    rw [hslot']
    exact slotOf_of_proposal_before_next_proposal S.E s hclock0
      (lt_of_le_of_lt hpreTime hhi)
  have hclock : pre.t < Protocol.proposal_time S.E (s + 1) :=
    lt_of_le_of_lt hpreTime hhi
  have hcommittee : u.val_index ∈ S.E.committee u.slot := by
    have hwire := adm.wire i (S.E.proposer (s + 1)) (Object.gfVote u) t hi
    simpa only [Object.wellFormed, NamedReceipt.wellFormed,
      Protocol.vote_well_formed, decide_eq_true_eq] using hwire
  have hlocal := Protocol.on_goldfish_vote_checked_beforeCutoff_or_equivocates
    S.E pre u (Protocol.proposal_time S.E (s + 1)) hcommittee
    (Protocol.poolStamps_stateBefore S adm.toNamedScheduleWellFormed
      (S.E.proposer (s + 1)) i)
    (by rw [hus, hslot]; exact Nat.not_lt.mpr (Nat.sub_le s 1))
    (by rw [hus, hslot]; exact lt_irrefl s)
    hclock
  have hpost : (rho.stateBefore S (i + 1) (S.E.proposer (s + 1))).st.core =
      Protocol.on_goldfish_vote_checked S.E pre u := by
    rw [Proofs.NamedReceiptCallsBase.delivery_result S rho hi]
    rfl
  let Gamma := Protocol.proposal_time S.E (s + 1)
  let N := (rho.events.filter (fun e => decide (e.time < Gamma))).length
  have hiN : i < N := by
    by_contra hnot
    have hNle : N ≤ i := Nat.le_of_not_gt hnot
    have hGammae : Gamma ≤ t :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        (t := Gamma) (j := i)
        (e := Event.deliver (S.E.proposer (s + 1)) (Object.gfVote u) t)
        (by simpa [N] using hNle) hi
    exact (not_le_of_gt (by simpa only [Gamma] using hhi)) hGammae
  have hcarry : Protocol.PoolCarry
      (rho.stateBefore S (i + 1) (S.E.proposer (s + 1))).st.core
      (rho.stateBefore S N (S.E.proposer (s + 1))).st.core :=
    Protocol.pool_carry S adm.toNamedScheduleWellFormed
      (S.E.proposer (s + 1)) N (Nat.succ_le_of_lt hiN)
  have hpool :
      (rho.stateBefore S N (S.E.proposer (s + 1))).st.core.pool s ⊆
        (proposalDutyRead S rho (s + 1)).st.core.pool s := by
    rw [proposalDutyPool_eq_storeBeforeTime_pool]
    change (rho.stateBefore S N (S.E.proposer (s + 1))).st.core.pool s ⊆
      (rho.stateBeforeTime S Gamma (S.E.proposer (s + 1))).st.core.pool s
    rw [Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed Gamma]
  rw [← hpost] at hlocal
  rw [hus] at hlocal
  rcases hlocal with hmem | hequiv
  · apply Or.inl
    have hfinal := Protocol.beforeCutoff_subset_of_poolCarry hcarry
      s Gamma hmem
    exact hpool (Finset.mem_filter.mp hfinal).1
  · apply Or.inr
    have hsub : beforeCutoff
        (rho.stateBefore S (i + 1) (S.E.proposer (s + 1))).st.core.timestamp_vote
        Gamma ((rho.stateBefore S (i + 1) (S.E.proposer (s + 1))).st.core.pool s) ⊆
        (proposalDutyRead S rho (s + 1)).st.core.pool s :=
      (Protocol.beforeCutoff_subset_of_poolCarry hcarry s Gamma).trans
        (by intro x hx; exact hpool (Finset.mem_filter.mp hx).1)
    apply Protocol.equivocates_mono hsub u.val_index
    exact hequiv

/-! ## Post-GST raw snapshot settlement -/

/-- A processing result in a fully post-GST previous slot settles in the next
honest proposer's raw snapshot, with the protocol's two-vote-cap alternative.
-/
theorem gfVote_processes_settled_at_nextProposer_afterGST_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {u : GoldfishVote V} {s : Slot} {t : Time}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hprop : S.E.proposer (s + 1) ∈ rho.honest)
    (hproc : NamedRun.processes S rho (S.E.proposer (s + 1))
      (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.proposal_time S.E (s + 1))
    (hhor : Protocol.proposal_time S.E (s + 1) ≤ rho.horizon) :
    u ∈ (proposalDutyRead S rho (s + 1)).st.core.pool s ∨
      Protocol.equivocates
        ((proposalDutyRead S rho (s + 1)).st.core.pool s)
        u.val_index = true := by
  rcases hproc with hemit | ⟨i, hi⟩
  · apply Or.inl
    obtain ⟨hs, ht, -, hus'⟩ := Proofs.Optimistic.emits_gfVote_shape S hemit
    have hslot : S.E.slotOf t = s := by rw [← hus', hus]
    have ht' : t = Protocol.vote_time S.E s := by
      simpa only [hslot] using ht
    have hemit' : rho.emits S (S.E.proposer (s + 1)) (Object.gfVote u)
        (Protocol.vote_time S.E s) := by
      rwa [← ht']
    have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E s :=
      le_trans hpost (le_of_lt (by
        unfold Protocol.proposal_time Protocol.vote_time
        exact Int.lt_add_of_pos_right _ S.E.Δ_pos))
    have hcut := Protocol.support_cutoff_le_proposal_time_succ S.E s
    have hrecv := Protocol.canonicalSuffixGfVoteInCutoffView_core
      S adm hprop (by simpa only [hslot] using hs) hpostVote hemit' hus hprop
      (Protocol.proposal_time S.E (s + 1))
      (Protocol.proposal_time S.E (s + 1)) hcut hcut
      (le_trans hcut hhor)
    have hmem : u ∈ (rho.storeBeforeTime S (S.E.proposer (s + 1))
        (Protocol.proposal_time S.E (s + 1))).pool s :=
      (Finset.mem_filter.mp hrecv).1
    rw [proposalDutyPool_eq_storeBeforeTime_pool]
    exact hmem
  · exact gfVote_delivery_settled_at_proposalDuty
      S adm hprop hi hus hlo hhi


#print axioms gfVote_processes_settled_at_nextProposer_afterGST_core


/-! ## Prefix transport into the prepared proposal read -/

/-- The prepared proposal read and the erased proposer duty store hold the same
previous-slot pool: the tick staging writes only the clock and the slot. -/
private theorem proposalDutyPool_eq_proposerDutyPool
    (S : Setup V) (rho : Run V) (s : Slot) :
    (proposalDutyRead S rho (s + 1)).st.core.pool s =
      (Protocol.proposerDutyStore S rho (s + 1)).pool s := by
  rfl

/-- A vote already processed at an earlier proposer prefix is still in the
prepared proposal read's previous-slot pool. Absent in the earlier file, whose
proposal snapshot is the erased proposer duty store; the erased twin here is
`Protocol.gfVote_processed_after_event_at_proposerDuty`. -/
private theorem gfVote_processed_after_event_at_proposalDuty
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {i : Nat} {e : Event V} {u : GoldfishVote V} {s : Slot}
    (he : rho.events[i]? = some e) (hus : u.slot = s)
    (hprocessed : Object.processed
      (rho.stateBefore S (i + 1) (S.E.proposer (s + 1))).st
      (Object.gfVote u) = true)
    (hearly : e.time < Protocol.proposal_time S.E (s + 1)) :
    u ∈ (proposalDutyRead S rho (s + 1)).st.core.pool s := by
  rw [proposalDutyPool_eq_proposerDutyPool]
  exact Protocol.gfVote_processed_after_event_at_proposerDuty_core
    S adm he hus hprocessed hearly

#print axioms gfVote_processed_after_event_at_proposalDuty

/-- Every vote the next proposer holds at a prefix that closes before its own
proposal instant is still in its prepared proposal read. -/
private theorem proposalDutyPool_of_prefix
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho) {s : Slot} {k m : Nat}
    {e : Event V} (he : rho.events[k]? = some e)
    (hearly : e.time < Protocol.proposal_time S.E (s + 1))
    (hm : m ≤ k + 1) :
    (rho.stateBefore S m (S.E.proposer (s + 1))).st.core.pool s ⊆
      (proposalDutyRead S rho (s + 1)).st.core.pool s := by
  let Gamma := Protocol.proposal_time S.E (s + 1)
  let N := (rho.events.filter (fun x => decide (x.time < Gamma))).length
  have hkN : k < N := by
    by_contra hnot
    have hNle : N ≤ k := Nat.le_of_not_gt hnot
    have hGammae : Gamma ≤ e.time :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        (t := Gamma) (j := k) (e := e) (by simpa [N] using hNle) he
    exact (not_le_of_gt (by simpa only [Gamma] using hearly)) hGammae
  have hcarry : Protocol.PoolCarry
      (rho.stateBefore S m (S.E.proposer (s + 1))).st.core
      (rho.stateBefore S N (S.E.proposer (s + 1))).st.core :=
    Protocol.pool_carry S adm.toNamedScheduleWellFormed
      (S.E.proposer (s + 1)) N (le_trans hm (Nat.succ_le_of_lt hkN))
  have hpool :
      (rho.stateBefore S N (S.E.proposer (s + 1))).st.core.pool s ⊆
        (proposalDutyRead S rho (s + 1)).st.core.pool s := by
    rw [proposalDutyPool_eq_storeBeforeTime_pool]
    change (rho.stateBefore S N (S.E.proposer (s + 1))).st.core.pool s ⊆
      (rho.stateBeforeTime S Gamma (S.E.proposer (s + 1))).st.core.pool s
    rw [Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed Gamma]
  intro x hx
  refine hpool ?_
  simp only [Protocol.Store.pool, List.mem_toFinset] at hx ⊢
  exact hcarry.mem s x hx

/-- A delivery between one proposal instant and the next reads slot `s` in the
receiver's own store. -/
private theorem delivery_store_slot_before_next_proposal
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {i : Nat} {o : Object V} {s : Slot} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver w o t))
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.proposal_time S.E (s + 1)) :
    (rho.stateBefore S i w).st.core.s = s := by
  have hpreTime : (rho.stateBefore S i w).st.core.t ≤ t := by
    simpa [Event.time] using
      (Protocol.store_time_le_event_time S
        adm.toNamedScheduleWellFormed hi w)
  have hclock0 : Protocol.proposal_time S.E s ≤
      (rho.stateBefore S i w).st.core.t :=
    Protocol.tick_le_store_time S adm.toNamedScheduleWellFormed hi
      (adm.tick_total w hw _ (Proofs.Optimistic.publicTime_proposal_time S s)
        (Proofs.Optimistic.proposal_time_nonneg S.E s)
        (le_trans hlo (adm.in_horizon _ (List.mem_of_getElem? hi)).2))
      hlo
  have hslot := Proofs.NamedStoreBridge.slotOfClock_stateBefore S rho i w
  unfold Proofs.Optimistic.SlotOfClock at hslot
  rw [hslot]
  exact slotOf_of_proposal_before_next_proposal S.E s hclock0
    (lt_of_le_of_lt hpreTime hhi)

omit [Fintype V] in
private theorem capInputs_admit_rows_bodies (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).bodies = st.bodies := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
      change (Protocol.NamedAdmission.admit_rows hc
        (Protocol.NamedAdmission.admit_row hc st row) rows).bodies = _
      rw [ih, NamedAdmission.admit_row_bodies]

/-- A carried insertion that adds the erased body adds the named body too. -/
private theorem capInputs_carried_block_body_of_core
    (S : Setup V) (before : Protocol.NamedStore V) (B : NamedBlock V)
    (hnew : B.erase ∉ before.core.T)
    (hpost : B.erase ∈
      (Execution.NamedReceiptCalls.postCore S before B).core.T) :
    B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg
      before B).bodies := by
  have hcore : B ∈
      (Execution.NamedReceiptCalls.postCore S before B).bodies := by
    unfold Execution.NamedReceiptCalls.postCore
      Protocol.NamedStore.process_block_core at hpost ⊢
    by_cases hp : B.parent ∉ before.bodies
    · simp only [hp] at hpost ⊢
      exact False.elim (hnew hpost)
    · rw [if_neg hp] at hpost ⊢
      let after := Protocol.on_block_checked_using
        (fun current => Protocol.on_block_using S.E current B.erase
          (fun parentState => Protocol.named_transition S.E S.cfg parentState B))
        S.hc before.core B.erase
      change B.erase ∈ (Protocol.NamedStore.commitBlock before after B).core.T at hpost
      change B ∈ (Protocol.NamedStore.commitBlock before after B).bodies
      unfold Protocol.NamedStore.commitBlock at hpost ⊢
      split_ifs at hpost ⊢ with hcond
      · simp
      · have hafter : B.erase ∈ after.T := by simpa using hpost
        exact False.elim (hcond ⟨hnew, hafter⟩)
  rw [show Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg before B =
      Protocol.NamedAdmission.admit_carried .alsoCarried S.hc before
        (Execution.NamedReceiptCalls.postCore S before B) B by rfl]
  unfold Protocol.NamedAdmission.admit_carried
  split_ifs
  · rw [capInputs_admit_rows_bodies]
    exact hcore
  · exact hcore

/-- A named handler call on the next proposer, at any instant of slot `s`
before its own proposal read, settles the vote in that read's previous-slot
pool, with the protocol's two-vote-cap alternative.

The named runtime admits a third arrival shape the erased runtime did not have:
the vote can arrive inside an admitted carrying block. That arm is closed by
the checked carried fold (`block_carried_before_deadline_or_equivocates`) for a
delivered carrier, and by the proposer's own pool for a self-emitted carrier. -/
private theorem actual_gfVote_settled_at_proposalDuty
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hprop : S.E.proposer (s + 1) ∈ rho.honest)
    {j : Nat} {u : GoldfishVote V} {t : Time}
    (hactual : NamedRun.actualHandlesAt S rho j (S.E.proposer (s + 1))
      (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.proposal_time S.E (s + 1))
    (hhor : Protocol.proposal_time S.E (s + 1) ≤ rho.horizon) :
    u ∈ (proposalDutyRead S rho (s + 1)).st.core.pool s ∨
      Protocol.equivocates
        ((proposalDutyRead S rho (s + 1)).st.core.pool s)
        u.val_index = true := by
  obtain ⟨hidx, e, he, -, htime⟩ := hactual
  have hearly : e.time < Protocol.proposal_time S.E (s + 1) := by
    rw [htime]; exact hhi
  simp only [NamedRun.actualHandlesAtIndex, NamedRun.processesAtIndex] at hidx
  rcases hidx with (⟨t', hj, hem⟩ | ⟨t', hj⟩) | ⟨B, jrow, before, hcall⟩
  · have heq : Event.tick (S.E.proposer (s + 1)) t' = e :=
      Option.some.inj (hj.symm.trans he)
    have htt : t' = t := (congrArg Event.time heq).trans htime
    subst t'
    exact gfVote_processes_settled_at_nextProposer_afterGST_core
      S adm hpost hprop (Or.inl ⟨j, hj, hem⟩) hus hlo hhi hhor
  · have heq : Event.deliver (S.E.proposer (s + 1)) (Object.gfVote u) t' = e :=
      Option.some.inj (hj.symm.trans he)
    have htt : t' = t := (congrArg Event.time heq).trans htime
    subst t'
    exact gfVote_processes_settled_at_nextProposer_afterGST_core
      S adm hpost hprop (Or.inr ⟨j, hj⟩) hus hlo hhi hhor
  · obtain ⟨hblock, hnew, hcore, huindex⟩ := hcall
    have huErase : u ∈ B.erase.gf_votes := by
      rw [Proofs.NamedWire.erase_goldfish_votes]
      exact List.mem_of_getElem? huindex
    rcases hblock with ⟨t', hdeliver, hbefore⟩ | ⟨t', htick, hBemit, hbefore⟩
    · have heq : Event.deliver (S.E.proposer (s + 1)) (Object.block B) t' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      have hpreBodies : B ∉ before.bodies := by
        intro hB
        apply hnew
        have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j
          (S.E.proposer (s + 1))).1.1.1
        have hB' : B ∈ (rho.stateBefore S j (S.E.proposer (s + 1))).st.bodies := by
          simpa [hbefore] using hB
        rw [hbefore, hcoh.1]
        exact Finset.mem_image_of_mem NamedBlock.erase hB'
      have hpostBodies :=
        capInputs_carried_block_body_of_core S before B hnew hcore
      have hstamps : Protocol.PoolStamps before.core := by
        rw [hbefore]
        exact Protocol.poolStamps_stateBefore S
          adm.toNamedScheduleWellFormed (S.E.proposer (s + 1)) j
      have hslotStore : before.core.s = s := by
        rw [hbefore]
        exact delivery_store_slot_before_next_proposal S adm hprop hdeliver hlo hhi
      have hfresh : ¬ u.slot < before.core.s - 1 := by
        rw [hus, hslotStore]
        exact Nat.not_lt.mpr (Nat.sub_le s 1)
      have hfuture : ¬ before.core.s < u.slot := by
        rw [hslotStore, hus]
        exact Nat.lt_irrefl s
      have hcommittee : u.val_index ∈ S.E.committee u.slot := by
        have hwire := adm.wire j (S.E.proposer (s + 1)) (Object.block B) t hdeliver
        simp only [NamedReceipt.wellFormed, Bool.and_eq_true] at hwire
        have hall := hwire.2
        simp only [List.all_eq_true, decide_eq_true_eq] at hall
        exact hall u huErase
      have hclock : before.core.t < Protocol.proposal_time S.E (s + 1) := by
        have hle : before.core.t ≤ t := by
          rw [hbefore]
          simpa [Event.time] using
            (Protocol.store_time_le_event_time S
              adm.toNamedScheduleWellFormed hdeliver (S.E.proposer (s + 1)))
        exact lt_of_le_of_lt hle hhi
      have hlocal := Proofs.Optimistic.block_carried_before_deadline_or_equivocates
        S before B u (Protocol.proposal_time S.E (s + 1)) hstamps hpreBodies
        hpostBodies huErase hcommittee hfresh hfuture hclock
      have hstate := Proofs.NamedReceiptCallsBase.delivery_result S rho hdeliver
      let final := Protocol.NamedAdmission.on_block_with
        .alsoCarried S.E S.hc S.cfg before B
      have hfinalEq : (rho.stateBefore S (j + 1) (S.E.proposer (s + 1))).st = final := by
        rw [hstate]
        simp [final, hbefore, NamedReceipt.process]
      have hlocal' : u ∈ beforeCutoff
          (rho.stateBefore S (j + 1) (S.E.proposer (s + 1))).st.core.timestamp_vote
          (Protocol.proposal_time S.E (s + 1))
          ((rho.stateBefore S (j + 1) (S.E.proposer (s + 1))).st.core.pool u.slot) ∨
          Protocol.equivocates
            (beforeCutoff
              (rho.stateBefore S (j + 1) (S.E.proposer (s + 1))).st.core.timestamp_vote
              (Protocol.proposal_time S.E (s + 1))
              ((rho.stateBefore S (j + 1) (S.E.proposer (s + 1))).st.core.pool u.slot))
            u.val_index = true := by
        simpa only [final, hfinalEq] using hlocal
      rw [hus] at hlocal'
      have hsub : (beforeCutoff
          (rho.stateBefore S (j + 1) (S.E.proposer (s + 1))).st.core.timestamp_vote
          (Protocol.proposal_time S.E (s + 1))
          ((rho.stateBefore S (j + 1) (S.E.proposer (s + 1))).st.core.pool s)) ⊆
          (proposalDutyRead S rho (s + 1)).st.core.pool s := by
        intro x hx
        exact proposalDutyPool_of_prefix S adm he hearly (le_refl (j + 1))
          (Finset.mem_filter.mp hx).1
      rcases hlocal' with hmem | hequiv
      · exact Or.inl (hsub hmem)
      · exact Or.inr (Protocol.equivocates_mono hsub u.val_index hequiv)
    · have heq : Event.tick (S.E.proposer (s + 1)) t' = e :=
        Option.some.inj (htick.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      have hstamps : Protocol.PoolStamps before.core := by
        rw [hbefore]
        have hrawStamps := Protocol.poolStamps_stateBefore S
          adm.toNamedScheduleWellFormed (S.E.proposer (s + 1)) j
        have htle : (rho.stateBefore S j (S.E.proposer (s + 1))).st.core.t ≤ t := by
          simpa [Event.time] using
            (Protocol.store_time_le_event_time S
              adm.toNamedScheduleWellFormed htick (S.E.proposer (s + 1)))
        exact (Protocol.poolStep_tickStore _ _ _ htle hrawStamps).2
      have hproposal := congrArg Prod.snd
        (Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hBemit)
      have hgf0 : B.gf_votes =
          (NamedActionReads.confirmationReadFrom S
            (rho.stateBefore S j (S.E.proposer (s + 1))) t).st.core.gf_votes
            ((NamedActionReads.confirmationReadFrom S
              (rho.stateBefore S j (S.E.proposer (s + 1))) t).st.core.s - 1) := by
        unfold Protocol.NamedDuties.propose_block_with at hproposal
        split at hproposal
        · cases hproposal
        · rename_i B' hB'
          have hBB' : B' = B := Option.some.inj hproposal
          rw [← hBB']
          exact Proofs.Optimistic.proposal_with_gf_votes _ .poolAndCarried
            S.E S.hc (S.node (S.E.proposer (s + 1))) _ hB'
      have hgf : B.gf_votes = before.core.gf_votes (before.core.s - 1) := by
        simpa [hbefore] using hgf0
      have huPool : u ∈ before.core.gf_votes (before.core.s - 1) := by
        rw [← hgf]
        exact List.mem_of_getElem? huindex
      have huslot := hstamps.slot (before.core.s - 1) u huPool
      apply Or.inl
      refine proposalDutyPool_of_prefix S adm he hearly
        (le_of_lt (Nat.lt_succ_self j)) ?_
      have hmemPool : u ∈ before.core.gf_votes s := by
        rw [← hus, huslot]
        exact huPool
      simp only [Protocol.Store.pool, List.mem_toFinset]
      simpa [hbefore, Protocol.NamedStore.setClock] using hmemPool

/-- A vote accepted after GST and before the previous-slot freeze reaches the
next honest proposal snapshot, or the proposer already exposes equivocation. -/
theorem accepted_gfVote_settled_at_nextProposer_afterGST_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest)
    {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hprop : S.E.proposer (s + 1) ∈ rho.honest)
    {i : Nat} {u : GoldfishVote V} {t : Time}
    (hacc : NamedRun.acceptsAt S rho i v (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.view_freeze S.E s)
    (hhor : Protocol.proposal_time S.E (s + 1) ≤ rho.horizon) :
    u ∈ (proposalDutyRead S rho (s + 1)).st.core.pool s ∨
      Protocol.equivocates
        ((proposalDutyRead S rho (s + 1)).st.core.pool s)
        u.val_index = true := by
  by_cases halready : Object.processed
      (rho.stateBefore S (i + 1) (S.E.proposer (s + 1))).st
      (Object.gfVote u) = true
  · obtain ⟨e, he, -, het⟩ := hacc.1.2
    apply Or.inl
    apply gfVote_processed_after_event_at_proposalDuty S adm he hus halready
    exact lt_of_le_of_lt (le_of_eq het) (lt_trans hhi (by
      rw [← Protocol.view_freeze_add_delta_eq_proposal_time_succ S.E s]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos))
  · have hunaccepted : Object.processed
        (rho.stateBefore S (i + 1) (S.E.proposer (s + 1))).st
        (Object.gfVote u) = false :=
      Bool.eq_false_of_not_eq_true halready
    have hrelayHor : t + S.E.Δ ≤ rho.horizon := by
      apply le_trans _ hhor
      rw [← Protocol.view_freeze_add_delta_eq_proposal_time_succ S.E s]
      exact Int.add_le_add_right (le_of_lt hhi) S.E.Δ
    have hpostAcceptance : S.E.t_GST ≤ t := le_trans hpost hlo
    obtain ⟨t', hcausal, hdeadline, j, hactual⟩ :=
      Protocol.relay_gf_vote_after_gst_core S adm hv hprop hpostAcceptance
        hacc hunaccepted hrelayHor
    have hbeforeProposal : t' < Protocol.proposal_time S.E (s + 1) := by
      apply lt_trans hdeadline
      rw [← Protocol.view_freeze_add_delta_eq_proposal_time_succ S.E s]
      exact Int.add_lt_add_right hhi S.E.Δ
    exact actual_gfVote_settled_at_proposalDuty S adm hpost hprop hactual hus
      (le_trans hlo hcausal) hbeforeProposal hhor


#print axioms accepted_gfVote_settled_at_nextProposer_afterGST_core



/-- Post-GST replacement for the GST-zero raw-extra theorem. It is local to
one previous-slot window; it does not require a history before that window.

Named restatement: the proposal is the bound named block `P` of
`proposedBlockAt`, and the voter reads its prepared vote-duty read. -/
theorem voter_raw_extra_equivocates_proposal_afterGST_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {P : NamedBlock V} (hP : proposedBlockAt S rho s = some P)
    (hcandidate : P.erase ∈ Protocol.get_filtered_block_tree
      (voteDutyRead S rho v s).st.core.toHealing.toFG) :
    ∀ u ∈ Protocol.voter_view S.E
        (voteDutyRead S rho v s).st.core.toHealing.toFG.toSG.toGoldfishStore s,
      u ∉ P.erase.gf_votes.toFinset →
        Protocol.equivocates P.erase.gf_votes.toFinset u.val_index = true := by
  intro u hu hnot
  rw [Protocol.voter_view, Finset.mem_union] at hu
  rcases hu with hreceipt | hcarried
  · have hpredSucc : s - 1 + 1 = s :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hs))
    have hreceipt' : u ∈ beforeCutoff
        (Proofs.Optimistic.voteDutyStore S rho v ((s - 1) + 1)).timestamp_vote
        (Protocol.view_freeze S.E (s - 1))
        ((Proofs.Optimistic.voteDutyStore S rho v ((s - 1) + 1)).pool (s - 1)) := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, hpredSucc] using hreceipt
    obtain ⟨i, t, hacc, hus, hlo, hhi⟩ :=
      Protocol.WeakExecution.targetReceiptVotesAcceptedInWindow_of_admissible
        S adm hv (s - 1) u hreceipt'
    have hprop' : S.E.proposer ((s - 1) + 1) ∈ rho.honest := by
      simpa only [hpredSucc] using hprop
    have hsettled := accepted_gfVote_settled_at_nextProposer_afterGST_core
      (s := s - 1) S adm hv hpost hprop' hacc hus hlo hhi
        (by simpa only [hpredSucc] using hhor)
    rw [proposalDutyPool_eq_proposerDutyPool] at hsettled
    rw [hpredSucc] at hsettled
    have hraw : P.erase.gf_votes.toFinset =
        (Protocol.proposerDutyStore S rho s).pool (s - 1) := by
      rw [Proofs.NamedWire.erase_goldfish_votes,
        Protocol.proposedBlock_raw_eq_proposer_pool S rho s hP]
      simp only [proposerReadAt, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.proposerDutyStore, Run.storeBeforeTime,
        Proofs.Optimistic.tickStore, Proofs.Optimistic.slotOf_proposal_time]
    rcases hsettled with hmem | hequiv
    · exact False.elim (hnot (by simpa only [hraw] using hmem))
    · simpa only [hraw] using hequiv
  · rw [Finset.mem_biUnion] at hcarried
    obtain ⟨C, hC, huC⟩ := hcarried
    rw [Finset.mem_filter] at hC huC
    have hPvote : P.erase ∈ (voteDutyRead S rho v s).st.core.T :=
      Proofs.Records.get_filtered_block_tree_subset _ hcandidate
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toNamedScheduleWellFormed (Protocol.vote_time S.E s)
    have hPprefix : P.erase ∈ (rho.stateBefore S n v).st.core.T := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Run.storeBeforeTime, hn] using hPvote
    have hCprefix : C ∈ (rho.stateBefore S n v).st.core.T := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Run.storeBeforeTime, hn] using hC.1
    have hCP : C = P.erase := unique_slot_block_in_store_core S adm hs hprop
      hCprefix hPprefix
      (by simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.slotOf_vote_time] using hC.2)
      (by rw [Proofs.NamedWire.erase_slot, proposedBlockAt_slot S rho s hP])
    subst C
    exact False.elim (hnot (by
      simpa only [Proofs.NamedWire.erase_goldfish_votes] using huC.1))

theorem voter_raw_extra_equivocates_proposal_afterGST
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {P : NamedBlock V} (hP : proposedBlockAt S rho s = some P)
    (hcandidate : P.erase ∈ Protocol.get_filtered_block_tree
      (voteDutyRead S rho v s).st.core.toHealing.toFG) :
    ∀ u ∈ Protocol.voter_view S.E
        (voteDutyRead S rho v s).st.core.toHealing.toFG.toSG.toGoldfishStore s,
      u ∉ P.erase.gf_votes.toFinset →
        Protocol.equivocates P.erase.gf_votes.toFinset u.val_index = true :=
  voter_raw_extra_equivocates_proposal_afterGST_core
    S adm.toNamedAdmissibleCore hs hpost hprop hv hhor hP hcandidate

#print axioms voter_raw_extra_equivocates_proposal_afterGST_core

#print axioms voter_raw_extra_equivocates_proposal_afterGST

end HealingSurface
end Proofs
end DecoupledConsensusModel

end


