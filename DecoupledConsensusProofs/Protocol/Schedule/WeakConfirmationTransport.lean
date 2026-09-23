module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore

@[expose] public section

/-!
# Confirmation transport under core execution

Accepted votes are forwarded in both directions between the confirmation
reader and the next voter. This includes Byzantine votes and the checked
handler alternative that records equivocation. Full SG participation is not
required. A reader-local FG-root bound permits the supporting block relay.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGoldfish

open Internal Execution Protocol Protocol.WeakExecution

variable {V : Type} [DecidableEq V] [Fintype V]

theorem delivery_store_slot_before_freeze
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {i : Nat} {o : Object V} {s : Slot} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver w o t))
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.view_freeze S.E s) :
    (rho.stateBefore S i w).st.s = s := by
  have htick : Event.tick w (Protocol.proposal_time S.E s) ∈ rho.events :=
    adm.tick_total w hw _ (Proofs.Optimistic.publicTime_proposal_time S s)
      (Proofs.Optimistic.proposal_time_nonneg S.E s)
      (le_trans hlo (adm.in_horizon _ (List.mem_of_getElem? hi)).2)
  have hclock : Protocol.proposal_time S.E s ≤ (rho.stateBefore S i w).st.t :=
    tick_le_store_time S adm.toNamedScheduleWellFormed hi htick hlo
  have hup : (rho.stateBefore S i w).st.t ≤ t := by
    simpa [Event.time] using store_time_le_event_time S adm.toNamedScheduleWellFormed hi w
  have hslot := Proofs.NamedStoreBridge.slotOfClock_stateBefore S rho i w
  unfold Proofs.Optimistic.SlotOfClock at hslot
  show (rho.stateBefore S i w).st.core.s = s
  rw [hslot]
  exact slotOf_of_proposal_before_freeze S.E s hclock (lt_of_le_of_lt hup hhi)

theorem delivery_store_slot_before_confirmation
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {i : Nat} {o : Object V} {s : Slot} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver w o t))
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.confirmation_time S.E s) :
    (rho.stateBefore S i w).st.s = s ∨ (rho.stateBefore S i w).st.s = s + 1 := by
  have htick : Event.tick w (Protocol.proposal_time S.E s) ∈ rho.events :=
    adm.tick_total w hw _ (Proofs.Optimistic.publicTime_proposal_time S s)
      (Proofs.Optimistic.proposal_time_nonneg S.E s)
      (le_trans hlo (adm.in_horizon _ (List.mem_of_getElem? hi)).2)
  have hclock : Protocol.proposal_time S.E s ≤ (rho.stateBefore S i w).st.t :=
    tick_le_store_time S adm.toNamedScheduleWellFormed hi htick hlo
  have hup : (rho.stateBefore S i w).st.t ≤ t := by
    simpa [Event.time] using store_time_le_event_time S adm.toNamedScheduleWellFormed hi w
  have hslot := Proofs.NamedStoreBridge.slotOfClock_stateBefore S rho i w
  unfold Proofs.Optimistic.SlotOfClock at hslot
  show (rho.stateBefore S i w).st.core.s = s ∨
    (rho.stateBefore S i w).st.core.s = s + 1
  rw [hslot]
  exact slotOf_of_proposal_before_confirmation S.E s hclock
    (lt_of_le_of_lt hup hhi)


theorem gfVote_delivery_settled_at_confStore
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {i : Nat} {u : GoldfishVote V}
    {s : Slot} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver w (Object.gfVote u) t))
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.confirmation_time S.E s) :
    u ∈ confLate S.E (Proofs.Optimistic.confStore S rho w s) s ∨
      Protocol.equivocates
        (confLate S.E (Proofs.Optimistic.confStore S rho w s) s) u.val_index = true := by
  let pre := (rho.stateBefore S i w).st.core
  have hslot : pre.s = s ∨ pre.s = s + 1 :=
    delivery_store_slot_before_confirmation S adm hw hi hlo hhi
  have hclock : pre.t < Protocol.confirmation_time S.E s :=
    lt_of_le_of_lt
      (by simpa [pre, Event.time] using
        store_time_le_event_time S adm.toNamedScheduleWellFormed hi w)
      hhi
  have hfresh : ¬ u.slot < pre.s - 1 := by
    rcases hslot with hs | hs
    · rw [hus, hs]
      exact Nat.not_lt.mpr (Nat.sub_le s 1)
    · rw [hus, hs, Nat.add_sub_cancel]
      exact Nat.lt_irrefl s
  have hfuture : ¬ pre.s < u.slot := by
    rcases hslot with hs | hs
    · rw [hus, hs]
      exact Nat.lt_irrefl s
    · rw [hus, hs]
      exact Nat.not_lt.mpr (Nat.le_add_right s 1)
  have hcommittee : u.val_index ∈ S.E.committee u.slot := by
    have hwire := adm.wire i w (Object.gfVote u) t hi
    simpa only [Object.wellFormed, NamedReceipt.wellFormed,
      Protocol.vote_well_formed,
      decide_eq_true_eq] using hwire
  have hlocal := on_goldfish_vote_checked_beforeCutoff_or_equivocates
    S.E pre u (Protocol.confirmation_time S.E s) hcommittee
    (poolStamps_stateBefore S adm.toNamedScheduleWellFormed w i)
    hfresh hfuture hclock
  have hpost : (rho.stateBefore S (i + 1) w).st.core =
      Protocol.on_goldfish_vote_checked S.E pre u := by
    rw [Proofs.NamedReceiptCallsBase.delivery_result S rho hi]
    rfl
  let Γ := Protocol.confirmation_time S.E s
  let N := (rho.events.filter (fun e => decide (e.time < Γ))).length
  have hiN : i < N := by
    by_contra hnot
    have hNle : N ≤ i := Nat.le_of_not_gt hnot
    have hΓt : Γ ≤ t :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed (t := Γ)
        (j := i) (e := Event.deliver w (Object.gfVote u) t)
        (by simpa [N] using hNle) hi
    exact (not_le_of_gt hhi) hΓt
  have hcarry : PoolCarry (rho.stateBefore S (i + 1) w).st.core
      (rho.stateBefore S N w).st.core :=
    pool_carry S adm.toNamedScheduleWellFormed w N (Nat.succ_le_of_lt hiN)
  have hstore : Proofs.Optimistic.confStore S rho w s =
      Proofs.Optimistic.tickStore S (rho.stateBefore S N w).st.core Γ := by
    unfold Proofs.Optimistic.confStore Run.storeBeforeTime
    rw [congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed Γ) w)]
  have hfields :
      (Proofs.Optimistic.confStore S rho w s).timestamp_vote =
          (rho.stateBefore S N w).st.core.timestamp_vote ∧
        (Proofs.Optimistic.confStore S rho w s).gf_votes =
          (rho.stateBefore S N w).st.core.gf_votes := by
    rw [hstore]
    exact ⟨rfl, rfl⟩
  rw [← hpost] at hlocal
  rw [hus] at hlocal
  rcases hlocal with hmem | hequiv
  · apply Or.inl
    rw [confLate, hfields.1, Protocol.Store.pool, hfields.2]
    exact beforeCutoff_subset_of_poolCarry hcarry s Γ hmem
  · apply Or.inr
    apply equivocates_mono _ u.val_index hequiv
    intro x hx
    rw [confLate, hfields.1, Protocol.Store.pool, hfields.2]
    exact beforeCutoff_subset_of_poolCarry hcarry s Γ hx

theorem gfVote_processed_after_event_at_voteDuty
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} {i : Nat} {e : Event V} {u : GoldfishVote V} {s : Slot}
    (he : rho.events[i]? = some e) (hus : u.slot = s)
    (hprocessed : Object.processed
      (rho.stateBefore S (i + 1) w).st (Object.gfVote u) = true)
    (hearly : e.time < Protocol.view_freeze S.E s) :
    u ∈ beforeCutoff
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_vote
      (Protocol.view_freeze S.E s)
      ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) := by
  have hmem : u ∈ (rho.stateBefore S (i + 1) w).st.gf_votes s := by
    simp only [Object.processed, NamedReceipt.processed, decide_eq_true_eq,
      Protocol.Store.pool,
      List.mem_toFinset] at hprocessed
    rwa [hus] at hprocessed
  have hstamps := poolStamps_stateBefore S adm.toNamedScheduleWellFormed w (i + 1)
  obtain ⟨c, hc⟩ : ∃ c : Stamp,
      (rho.stateBefore S (i + 1) w).st.timestamp_vote u = some c :=
    Option.isSome_iff_exists.mp (hstamps.stamped s u hmem)
  have hclock : (rho.stateBefore S (i + 1) w).st.t ≤ e.time :=
    block_store_time_after_event_le S adm.toNamedScheduleWellFormed he w
  have hcFreeze : c < (Protocol.view_freeze S.E s : Stamp) :=
    lt_of_le_of_lt (hstamps.bounded u c hc)
      (WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hclock hearly))
  let Γ := Protocol.vote_time S.E (s + 1)
  let N := (rho.events.filter (fun x => decide (x.time < Γ))).length
  have hiN : i < N := by
    by_contra hnot
    have hNle : N ≤ i := Nat.le_of_not_gt hnot
    have hΓe : Γ ≤ e.time :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed (t := Γ)
        (j := i) (e := e) (by simpa [N] using hNle) he
    exact (not_le_of_gt
      (lt_trans hearly (view_freeze_lt_vote_time_succ S.E s))) hΓe
  have hcarry : PoolCarry (rho.stateBefore S (i + 1) w).st.core
      (rho.stateBefore S N w).st.core :=
    pool_carry S adm.toNamedScheduleWellFormed w N (Nat.succ_le_of_lt hiN)
  have hstore : Proofs.Optimistic.voteDutyStore S rho w (s + 1) =
      Proofs.Optimistic.voteStore S (rho.stateBefore S N w).st.core (s + 1) := by
    unfold Proofs.Optimistic.voteDutyStore Run.storeBeforeTime
    rw [congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed Γ) w)]
  rw [hstore]
  rw [beforeCutoff, Finset.mem_filter, Protocol.Store.pool, List.mem_toFinset]
  refine ⟨hcarry.mem s u hmem, ?_⟩
  simp only [Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, stampedBefore,
    hcarry.stamp u c hc, decide_eq_true_eq]
  exact hcFreeze

theorem relay_gf_vote_after_gst (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {u : GoldfishVote V} {t : Time} (hpost : S.E.t_GST ≤ t)
    (hacc : NamedRun.acceptsAt S rho i v (Object.gfVote u) t)
    (hunaccepted : NamedReceipt.processed
      (rho.stateBefore S (i + 1) w).st (Object.gfVote u) = false)
    (hhor : t + S.E.Δ ≤ rho.horizon) :
    ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
      ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t' := by
  have hmax : max t S.E.t_GST = t := max_eq_left hpost
  have h := adm.toNamedSynchrony.relay_gf_vote v hv i u t hacc w hw hunaccepted
    (by simpa only [hmax] using hhor) rfl
  simpa only [hmax] using h

theorem acceptsAt_carrier_before_vote_of_mem_voteDutyStore
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} {k : Slot} {B : Block V} (hBpos : 0 < B.slot)
    (hB : B ∈ (Proofs.Optimistic.voteDutyStore S rho w k).T) :
    ∃ (C : NamedBlock V) (i : Nat) (t : Time), C.erase = B ∧
      NamedRun.acceptsAt S rho i w (.block C) t ∧
      Protocol.proposal_time S.E B.slot ≤ t ∧
      t < Protocol.vote_time S.E k := by
  obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed (Protocol.vote_time S.E k)
  have hBn : B ∈ (rho.stateBefore S n w).st.core.T := by
    simpa [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.tickStore,
      Run.storeBeforeTime, hn] using hB
  obtain ⟨C, hCmem, hCerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n w hBn
  have hprocessed : NamedReceipt.processed
      (rho.stateBefore S n w).st (Object.block C) = true := by
    simpa only [Object.processed, NamedReceipt.processed, decide_eq_true_eq]
      using hCmem
  rcases acceptsAt_block_of_processed S rho w n C hprocessed with
    hgen | ⟨i, hin, t, hacc⟩
  · exfalso
    apply Nat.ne_of_gt hBpos
    rw [← hCerase, hgen]
    rfl
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    refine ⟨C, i, t, hCerase, hacc, ?_, ?_⟩
    · rw [← hCerase]
      exact Proofs.NamedSlotFreshness.proposal_time_le_of_acceptsAt_block S adm hacc
    · rw [← het]
      exact hbefore i e hin he

theorem targetPoolVoteAcceptedBeforeVote
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} {s : Slot} {u : GoldfishVote V}
    (hu : u ∈ (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) :
    ∃ (i : Nat) (t : Time), NamedRun.acceptsAt S rho i w (Object.gfVote u) t ∧
      u.slot = s ∧ Protocol.proposal_time S.E s ≤ t ∧
      t < Protocol.vote_time S.E (s + 1) := by
  let Γ := Protocol.vote_time S.E (s + 1)
  obtain ⟨n, hn, hbefore⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toNamedScheduleWellFormed Γ
  have huPool : u ∈ (NamedRun.stateBefore S rho n w).st.core.pool s := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn, Γ] using hu
  have huList : u ∈ (NamedRun.stateBefore S rho n w).st.core.gf_votes s := by
    simpa only [Protocol.Store.pool, List.mem_toFinset] using huPool
  have hus : u.slot = s :=
    (poolStamps_stateBefore S adm.toNamedScheduleWellFormed w n).slot s u huList
  have hprocessed : Object.processed (NamedRun.stateBefore S rho n w).st
      (Object.gfVote u) = true := by
    simp only [Object.processed, NamedReceipt.processed, decide_eq_true_eq]
    rw [hus]
    exact huPool
  obtain ⟨i, hin, t, hacc⟩ :=
    acceptsAt_gfVote_of_processed S rho w n u hprocessed
  obtain ⟨-, e, he, -, het⟩ := hacc.1
  have hit : t < Γ := by
    simpa only [het] using hbefore i e hin he
  have hlo : Protocol.proposal_time S.E s ≤ t := by
    rw [← hus]
    exact proposal_time_le_of_acceptsAt_gfVote S adm hacc
  exact ⟨i, t, hacc, hus, hlo, by simpa only [Γ] using hit⟩

theorem targetCarrierVote_settledInPool
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {B : Block V}
    (hB : B ∈ (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T)
    (hBslot : B.slot = s + 1) {u : GoldfishVote V}
    (hu : u ∈ B.gf_votes) (hus : u.slot = s) :
    u ∈ (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s ∨
      Protocol.equivocates
        ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s)
        u.val_index = true := by
  have hBpos : 0 < B.slot := by rw [hBslot]; exact Nat.zero_lt_succ s
  obtain ⟨C, i, t, hCerase, hacc, hlo, hhi⟩ :=
    acceptsAt_carrier_before_vote_of_mem_voteDutyStore S adm hBpos hB
  have huC : u ∈ C.erase.gf_votes := by rw [hCerase]; exact hu
  have hCslotB : C.erase.slot = s + 1 := by rw [hCerase]; exact hBslot
  obtain ⟨hhandle, hpreProcessed, hpostProcessed⟩ := hacc
  obtain ⟨hindex, e, he, hnode, htime⟩ := hhandle
  let Γ := Protocol.vote_time S.E (s + 1)
  let N := (rho.events.filter (fun x => decide (x.time < Γ))).length
  rcases hindex with ⟨t', htick, hem⟩ | ⟨t', hdeliver⟩
  · have heq : Event.tick w t' = e := Option.some.inj (htick.symm.trans he)
    have htt : t' = t := (congrArg Event.time heq).trans htime
    subst t'
    set pre := NamedRun.stateBefore S rho i w with hpredef
    obtain ⟨⟨hs0, htProp, hpropV⟩, hpropEq⟩ :=
      Proofs.HealingSurface.block_mem_on_tick_emit S w pre t hem
    set before := (NamedActionReads.confirmationReadFrom S pre t).st
      with hbeforedef
    let gc := NamedProfile.gradeContract
      (NamedActionReads.confirmationReadFrom S pre t).cache
    have hprop : Protocol.NamedActions.proposal_with gc .poolAndCarried
        S.E S.hc (S.node w) before = some C := by
      unfold Protocol.NamedDuties.propose_block_with at hpropEq
      cases hm : Protocol.NamedActions.proposal_with gc .poolAndCarried
          S.E S.hc (S.node w) before with
      | none => rw [hm] at hpropEq; simp at hpropEq
      | some C' => rw [hm] at hpropEq; exact hpropEq
    have hcslot : C.slot = before.core.s :=
      Proofs.Optimistic.proposal_with_slot gc .poolAndCarried
        S.E S.hc (S.node w) before hprop
    have hcgf : C.gf_votes = before.core.gf_votes (before.core.s - 1) :=
      Proofs.Optimistic.proposal_with_gf_votes gc .poolAndCarried
        S.E S.hc (S.node w) before hprop
    have hcslot' : C.slot = s + 1 :=
      (Proofs.NamedWire.erase_slot C).symm.trans hCslotB
    have hbeforeS : before.core.s = s + 1 := hcslot.symm.trans hcslot'
    have hu' : u ∈ C.gf_votes := by
      rw [← Proofs.NamedWire.erase_goldfish_votes]
      exact huC
    rw [hcgf, hbeforeS, Nat.add_sub_cancel] at hu'
    have huPre : u ∈ pre.st.core.gf_votes s := hu'
    have hiN : i < N := by
      by_contra hnot
      have hNle : N ≤ i := Nat.le_of_not_gt hnot
      have hΓe : Γ ≤ (Event.tick w t).time :=
        Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed (t := Γ)
          (j := i) (e := Event.tick w t) (by simpa [N] using hNle) htick
      exact (not_le_of_gt (by simpa only [Γ] using hhi)) hΓe
    have hcarry : PoolCarry pre.st.core (NamedRun.stateBefore S rho N w).st.core :=
      pool_carry S adm.toNamedScheduleWellFormed w N (Nat.le_of_lt hiN)
    have hstore : Proofs.Optimistic.voteDutyStore S rho w (s + 1) =
        Proofs.Optimistic.voteStore S (NamedRun.stateBefore S rho N w).st.core (s + 1) := by
      unfold Proofs.Optimistic.voteDutyStore Run.storeBeforeTime
      rw [congrArg NamedNodeState.st
        (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed Γ) w)]
    apply Or.inl
    rw [hstore]
    simpa only [Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
      Protocol.Store.pool, List.mem_toFinset] using hcarry.mem s u huPre
  · have heq : Event.deliver w (Object.block C) t' = e :=
      Option.some.inj (hdeliver.symm.trans he)
    have htt : t' = t := (congrArg Event.time heq).trans htime
    subst t'
    have hi : rho.events[i]? = some (Event.deliver w (Object.block C) t) := hdeliver
    set pre := (NamedRun.stateBefore S rho i w).st with hpredef
    have hstoreSlot : pre.core.s = s + 1 := by
      apply delivery_store_slot_before_freeze S adm
        (w := w) (i := i) (o := Object.block C) (s := s + 1) (t := t)
      · exact hw
      · exact hi
      · rw [← hBslot]
        exact hlo
      · exact lt_trans hhi (lt_trans
          (by rw [← Proofs.Optimistic.vote_time_add_delta]; exact Int.lt_add_of_pos_right _ S.E.Δ_pos)
          (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E (s + 1)))
    have hfresh : ¬ u.slot < pre.core.s - 1 := by
      rw [hus, hstoreSlot, Nat.add_sub_cancel]
      exact Nat.lt_irrefl s
    have hfuture : ¬ pre.core.s < u.slot := by
      rw [hus, hstoreSlot]
      exact Nat.not_lt.mpr (Nat.le_add_right s 1)
    have hclock : pre.core.t < Γ :=
      lt_of_le_of_lt
        (by simpa [pre, Event.time] using
          store_time_le_event_time S adm.toNamedScheduleWellFormed hi w)
        (by simpa only [Γ] using hhi)
    have hCpre : C ∉ pre.bodies := by
      simpa only [Object.processed, NamedReceipt.processed,
        decide_eq_false_iff_not] using hpreProcessed
    have hpost : (NamedRun.stateBefore S rho (i + 1) w).st =
        Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg pre C := by
      rw [Proofs.NamedReceiptCallsBase.delivery_result S rho hi]
      rfl
    have hCpost : C ∈
        (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg pre C).bodies := by
      rw [← hpost]
      simpa only [Object.processed, NamedReceipt.processed, decide_eq_true_eq]
        using hpostProcessed
    have hcommittee : u.val_index ∈ S.E.committee u.slot := by
      have hwire := adm.wire i w (Object.block C) t hi
      simp only [NamedReceipt.wellFormed, Bool.and_eq_true] at hwire
      have hcarried := hwire.2
      simp only [List.all_eq_true, decide_eq_true_eq] at hcarried
      exact hcarried u huC
    have hstamps : PoolStamps pre.core :=
      poolStamps_stateBefore S adm.toNamedScheduleWellFormed w i
    have hlocal := Proofs.Optimistic.block_carried_beforeCutoff_or_equivocates
      S pre C u Γ hstamps hCpre hCpost huC hcommittee hfresh hfuture hclock
    dsimp only at hlocal
    rw [hus] at hlocal
    rw [← hpost] at hlocal
    have hiN : i < N := by
      by_contra hnot
      have hNle : N ≤ i := Nat.le_of_not_gt hnot
      have hΓt : Γ ≤ t :=
        Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed (t := Γ)
          (j := i) (e := Event.deliver w (Object.block C) t)
          (by simpa [N] using hNle) hi
      exact (not_le_of_gt (by simpa only [Γ] using hhi)) hΓt
    have hcarry : PoolCarry (NamedRun.stateBefore S rho (i + 1) w).st.core
        (NamedRun.stateBefore S rho N w).st.core :=
      pool_carry S adm.toNamedScheduleWellFormed w N (Nat.succ_le_of_lt hiN)
    have hstore : Proofs.Optimistic.voteDutyStore S rho w (s + 1) =
        Proofs.Optimistic.voteStore S (NamedRun.stateBefore S rho N w).st.core (s + 1) := by
      unfold Proofs.Optimistic.voteDutyStore Run.storeBeforeTime
      rw [congrArg NamedNodeState.st
        (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed Γ) w)]
    rcases hlocal with hmem | hequiv
    · apply Or.inl
      have hfinal := beforeCutoff_subset_of_poolCarry hcarry s Γ hmem
      have hpool : u ∈ (NamedRun.stateBefore S rho N w).st.core.pool s :=
        (Finset.mem_filter.mp hfinal).1
      rw [hstore]
      simpa only [Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hpool
    · apply Or.inr
      apply equivocates_mono _ u.val_index hequiv
      intro x hx
      have hfinal := beforeCutoff_subset_of_poolCarry hcarry s Γ hx
      have hpool : x ∈ (NamedRun.stateBefore S rho N w).st.core.pool s :=
        (Finset.mem_filter.mp hfinal).1
      rw [hstore]
      simpa only [Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hpool

theorem find_voteDutyStore_of_source_find_and_mem
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {source : Protocol.Store V} {s : Slot} {w : V}
    (hw : w ∈ rho.honest) {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? source.T u.head = some H)
    (hHmem : H ∈ (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T) :
    Block.find? (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T u.head = some H := by
  obtain ⟨nw, hnw, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed (Protocol.vote_time S.E (s + 1))
  have htargetT : (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T =
      (rho.stateBefore S nw w).st.core.T := by
    simp only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime]
    show (NamedRun.stateBeforeTime S rho
      (Protocol.vote_time S.E (s + 1)) w).st.core.T = _
    rw [show NamedRun.stateBeforeTime S rho
      (Protocol.vote_time S.E (s + 1)) w =
        NamedRun.stateBefore S rho nw w from congrFun hnw w]
  have hHroot : H.root = u.head := by
    unfold Block.find? pickUnique? at hfind
    split at hfind
    · rename_i hex
      rw [Option.some_inj] at hfind
      subst hfind
      exact of_decide_eq_true (Finset.choose_property _ _ hex)
    · exact absurd hfind (by simp)
  rw [← hHroot]
  apply Proofs.Optimistic.find?_eq_some_of_unique hHmem
  intro Y hY hroot
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (rho.stateBefore S nw w).st :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho nw w).1.1.1
  have hrun : ∀ C ∈ (rho.stateBefore S nw w).st.bodies, RunBlock S rho C :=
    fun C hC => Proofs.Bridges.runBlock_of_stateBefore_mem S hw hC
  have hinj := Proofs.Bridges.rootInjectiveBelow_of_runBlocks S
    adm.toNamedRootCollisionFree hrun
  rw [← hcoh.1] at hinj
  have hYmem : Y ∈ (rho.stateBefore S nw w).st.core.T := by
    rw [← htargetT]
    exact hY
  have hHmem' : H ∈ (rho.stateBefore S nw w).st.core.T := by
    rw [← htargetT]
    exact hHmem
  exact hinj Y H ⟨Y, hYmem, Block.preceq_self Y⟩
    ⟨H, hHmem', Block.preceq_self H⟩ hroot

omit [Fintype V] in
private theorem weakct_recovery_admit_rows_bodies (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).bodies = st.bodies := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
      change (Protocol.NamedAdmission.admit_rows hc
        (Protocol.NamedAdmission.admit_row hc st row) rows).bodies = _
      rw [ih, NamedAdmission.admit_row_bodies]

private theorem weakct_recovery_core_new_body (S : Setup V)
    (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hnew : B.erase ∉ st.core.T)
    (hpost : B.erase ∈
      (Execution.NamedReceiptCalls.postCore S st B).core.T) :
    B ∈ (Execution.NamedReceiptCalls.postCore S st B).bodies := by
  unfold Execution.NamedReceiptCalls.postCore
    Protocol.NamedStore.process_block_core at hpost ⊢
  by_cases hp : B.parent ∉ st.bodies
  · simp only [hp] at hpost ⊢
    exact False.elim (hnew hpost)
  · rw [if_neg hp] at hpost ⊢
    let after := Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using S.E current B.erase
        (fun parentState => Protocol.named_transition S.E S.cfg parentState B))
      S.hc st.core B.erase
    change B.erase ∈ (Protocol.NamedStore.commitBlock st after B).core.T at hpost
    change B ∈ (Protocol.NamedStore.commitBlock st after B).bodies
    unfold Protocol.NamedStore.commitBlock at hpost ⊢
    split_ifs at hpost ⊢ with hcond
    · simp
    · have hafter : B.erase ∈ after.T := by simpa using hpost
      exact False.elim (hcond ⟨hnew, hafter⟩)

private theorem weakct_recovery_on_block_new_body (S : Setup V)
    (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hnew : B.erase ∉ st.core.T)
    (hpost : B.erase ∈
      (Execution.NamedReceiptCalls.postCore S st B).core.T) :
    B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies := by
  rw [show Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B =
      Protocol.NamedAdmission.admit_carried .alsoCarried S.hc st
        (Execution.NamedReceiptCalls.postCore S st B) B by rfl]
  unfold Protocol.NamedAdmission.admit_carried
  split_ifs
  · rw [weakct_recovery_admit_rows_bodies]
    exact weakct_recovery_core_new_body S st B hnew hpost
  · exact weakct_recovery_core_new_body S st B hnew hpost

private theorem weakct_core_goldfish_vote_with_fst_of_snd
    (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V)
    {u : GoldfishVote V}
    (h : (Protocol.goldfish_vote_with contract E hc nd st).2 = some u) :
    (Protocol.goldfish_vote_with contract E hc nd st).1 =
      Protocol.on_goldfish_vote st u := by
  simp only [Protocol.goldfish_vote_with] at h ⊢
  split_ifs at h ⊢ with hcommittee
  rw [← Option.some_inj.mp h]
  simp [Protocol.on_goldfish_vote_checked, hcommittee]


private theorem weakct_core_mem_pool_of_emits
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} {s : Slot} (hs : 0 < s) {u : GoldfishVote V}
    (hemit : NamedRun.emits S rho w (Object.gfVote u)
      (Protocol.vote_time S.E s))
    (hus : u.slot = s) (hval : u.val_index ∈ rho.honest) :
    ∃ i : Nat,
      rho.events[i]? = some (.tick w (Protocol.vote_time S.E s)) ∧
      u ∈ (NamedRun.stateBefore S rho (i + 1) w).st.gf_votes s ∧
      ∃ c : Stamp,
        (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote u = some c ∧
        c ≤ (Protocol.vote_time S.E s : Stamp) := by
  obtain ⟨i, hi, ho⟩ := hemit
  set t := Protocol.vote_time S.E s with htdef
  set n := NamedRun.stateBefore S rho i w with hndef
  obtain ⟨-, -, hduty, -, -⟩ := Proofs.Optimistic.gfVote_emitted_shape S w n t ho
  set gc := NamedProfile.gradeContract
    (NamedActionReads.confirmationReadFrom S n t).cache with hgcdef
  have hreadSteq : (NamedActionReads.confirmationReadFrom S n t).st =
      Protocol.NamedStore.setClock S.E n.st t := rfl
  set st₀ := Protocol.NamedStore.setClock S.E n.st t with hst₀def
  have hduty' :
      (Protocol.goldfish_vote_with gc S.E S.hc (S.node w) st₀.core).2 = some u := by
    rw [← hreadSteq]
    exact hduty
  have hfst := weakct_core_goldfish_vote_with_fst_of_snd
    gc S.E S.hc (S.node w) st₀.core hduty'
  have hslot₀ : st₀.core.s = s := by
    show S.E.slotOf t = s
    rw [htdef]
    exact Proofs.Optimistic.slotOf_vote_time S.E s
  have hclock₀ : st₀.core.t = t := rfl
  have hpoolEq : st₀.core.pool s = n.st.core.pool s := rfl
  have hclockle : n.st.core.t ≤ t := by
    simpa [Event.time] using store_time_le_event_time
      S adm.toNamedScheduleWellFormed hi w
  have hstamps₀ : PoolStamps st₀.core := by
    exact (poolStep_tickStore n.st.core t (S.E.slotOf t) hclockle
      (poolStamps_stateBefore S adm.toNamedScheduleWellFormed w i)).2
  have hfresh : ¬ u.slot < st₀.core.s - 1 := by
    rw [hslot₀, hus]
    exact Nat.not_lt.mpr (Nat.sub_le s 1)
  have hfuture : ¬ st₀.core.s < u.slot := by
    rw [hslot₀, hus]
    exact lt_irrefl s
  have hequiv : Protocol.equivocates
      (st₀.core.pool u.slot) u.val_index = false := by
    rw [hus, hpoolEq]
    exact Proofs.Optimistic.pool_no_honest_equivocation_of_core S adm w i s hval
  obtain ⟨hmem, c, hc, hle⟩ := mem_and_stamp_of_process
    st₀.core u hstamps₀ hfresh hfuture hequiv
  rw [hus] at hmem
  set s' := S.E.slotOf t with hs'def
  set proposed := Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
    (S.node w) st₀ with hproposeddef
  set proposalDue := 0 < s' ∧ t = Protocol.proposal_time S.E s' ∧
    S.E.proposer s' = (S.node w).val_index with hproposalDuedef
  set st₁ := if proposalDue then proposed.1 else st₀ with hst₁def
  set voted := Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc
    (S.node w) st₁ with hvoteddef
  set voteDue := 0 < s' ∧ t = Protocol.vote_time S.E s' with hvoteDuedef
  set st₂ := if voteDue then voted.1 else st₁ with hst₂def
  set st₃ := if 0 < s' ∧ t = Protocol.support_cutoff S.E s' then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st₂ (s' - 1)
    else st₂ with hst₃def
  have hs'eq : s' = s := by
    rw [hs'def, htdef]
    exact Proofs.Optimistic.slotOf_vote_time S.E s
  have hpne : ¬ proposalDue := by
    rw [hproposalDuedef]
    rintro ⟨-, hteq, -⟩
    exact Proofs.Optimistic.vote_time_ne_proposal_time S.E s'
      (by rw [← hteq, htdef, hs'eq])
  have hst₁eq : st₁ = st₀ := by rw [hst₁def, if_neg hpne]
  have hvd : voteDue := by
    rw [hvoteDuedef, hs'eq]
    exact ⟨hs, htdef⟩
  have hst₂eq : st₂.core = Protocol.on_goldfish_vote st₀.core u := by
    rw [hst₂def, if_pos hvd, hvoteddef, hst₁eq]
    exact hfst
  have hst₃fields :
      st₃.core.gf_votes = st₂.core.gf_votes ∧
      st₃.core.timestamp_vote = st₂.core.timestamp_vote := by
    rw [hst₃def]
    split_ifs <;> exact ⟨rfl, rfl⟩
  have htick₁eq :
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w)
        n.st n.record t).1 =
      if t = S.hc.a S.E.Δ (S.hc.round_of st₃.core.s) ∧
          (S.node w).awake (S.hc.round_of st₃.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node w)
          st₃ n.record).1
      else st₃ := by
    rw [Proofs.NamedTick.tick_computed_duties]
    dsimp only [st₃, st₂, voted, voteDue, st₁, proposed, proposalDue, s']
    split_ifs <;> rfl
  have hfinalfields :
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w)
        n.st n.record t).1.core.gf_votes = st₃.core.gf_votes ∧
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w)
        n.st n.record t).1.core.timestamp_vote = st₃.core.timestamp_vote := by
    rw [htick₁eq]
    split_ifs
    · obtain ⟨-, -, -, -, hgfv, htsv⟩ :=
        NamedAdmission.admit_row_fixed_fields S.hc st₃
          (Protocol.NamedActions.round_action_with gc S.E S.hc
            (S.node w) st₃.core.toHealing n.record).2
      exact ⟨hgfv, htsv⟩
    · exact ⟨rfl, rfl⟩
  have hstepFull : NamedRun.stateBefore S rho (i + 1) w =
      (NamedNode.tick S w n t).1 := Proofs.NamedRuntime.stateBefore_tick S rho hi
  have hgcstep : (NamedNode.tick S w n t).1.st =
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w)
        n.st n.record t).1 := rfl
  refine ⟨i, hi, ?_, c, ?_, ?_⟩
  · show u ∈ (NamedRun.stateBefore S rho (i + 1) w).st.core.gf_votes s
    rw [hstepFull, hgcstep, hfinalfields.1, hst₃fields.1, hst₂eq]
    exact hmem
  · show (NamedRun.stateBefore S rho (i + 1) w).st.core.timestamp_vote u = _
    rw [hstepFull, hgcstep, hfinalfields.2, hst₃fields.2, hst₂eq]
    exact hc
  · rw [← hclock₀]
    exact hle

private theorem weakct_actual_gfVote_settled_before_deadline
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {j : Nat} {w : V} {u : GoldfishVote V} {s : Slot} {t Gamma : Time}
    (hactual : NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t)
    (hus : u.slot = s) (hw : w ∈ rho.honest)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.view_freeze S.E s) (hdeadline : t < Gamma) :
    ∃ i : Nat, ∃ e : Event V, rho.events[i]? = some e ∧ e.time < Gamma ∧
      (u ∈ beforeCutoff
          (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote Gamma
          ((NamedRun.stateBefore S rho (i + 1) w).st.pool u.slot) ∨
        Protocol.equivocates
          (beforeCutoff
            (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote Gamma
            ((NamedRun.stateBefore S rho (i + 1) w).st.pool u.slot))
          u.val_index = true) := by
  obtain ⟨hindex, e, he, hnode, htime⟩ := hactual
  simp only [NamedRun.actualHandlesAtIndex, NamedRun.processesAtIndex] at hindex
  rcases hindex with (⟨t', htick, hem⟩ | ⟨t', hdeliver⟩) |
      ⟨B, j', before, hcall⟩
  · have heq : Event.tick w t' = e := Option.some.inj (htick.symm.trans he)
    have htt : t' = t := (congrArg Event.time heq).trans htime
    subst t'
    have hemit : NamedRun.emits S rho w (Object.gfVote u) t :=
      ⟨j, htick, hem⟩
    obtain ⟨hs', ht', hval, hus'⟩ := Proofs.Optimistic.emits_gfVote_shape S hemit
    have hslot : S.E.slotOf t = s := by rw [← hus', hus]
    have htVote : t = Protocol.vote_time S.E s := by
      simpa only [hslot] using ht'
    have hemitVote : NamedRun.emits S rho w (Object.gfVote u)
        (Protocol.vote_time S.E s) := by
      simpa only [htVote] using hemit
    have hs : 0 < s := by simpa only [hslot] using hs'
    obtain ⟨i, hi, hmem, c, hc, hle⟩ :=
      weakct_core_mem_pool_of_emits S adm (s := s) (u := u) hs hemitVote hus
        (by rw [hval]; exact hw)
    refine ⟨i, _, hi, ?_, ?_⟩
    · simpa only [Event.time, htVote] using hdeadline
    · rw [beforeCutoff, Finset.mem_filter]
      apply Or.inl
      refine ⟨?_, ?_⟩
      · simpa only [Protocol.NamedStore.pool, Protocol.Store.pool,
          List.mem_toFinset, hus] using hmem
      · cases hstamp :
            (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote u with
        | none => simp [stampedBefore, hstamp] at hc
        | some c' =>
          have hc' : c' < (Gamma : Stamp) := by
            have htime' : Protocol.vote_time S.E s < Gamma := by
              rw [← htVote]
              exact hdeadline
            have hcc : c' = c := Option.some.inj (hstamp.symm.trans hc)
            rw [hcc]
            exact lt_of_le_of_lt hle
              (WithBot.coe_lt_coe.mpr htime')
          simpa only [stampedBefore, hstamp, decide_eq_true_eq] using hc'
  · have heq : Event.deliver w (Object.gfVote u) t' = e :=
      Option.some.inj (hdeliver.symm.trans he)
    have htt : t' = t := (congrArg Event.time heq).trans htime
    subst t'
    have hslot : (NamedRun.stateBefore S rho j w).st.core.s = s := by
      show (NamedRun.stateBefore S rho j w).st.s = s
      exact delivery_store_slot_before_freeze S adm hw hdeliver hlo hhi
    have hcommittee : u.val_index ∈ S.E.committee u.slot := by
      have hwire := adm.wire j w (Object.gfVote u) t hdeliver
      simpa only [Object.wellFormed, NamedReceipt.wellFormed,
        Protocol.vote_well_formed, decide_eq_true_eq] using hwire
    have hstamps : Protocol.PoolStamps
        (NamedRun.stateBefore S rho j w).st.core :=
      Protocol.poolStamps_stateBefore S adm.toNamedScheduleWellFormed w j
    have hfresh : ¬ u.slot < (NamedRun.stateBefore S rho j w).st.core.s - 1 := by
      rw [hslot, hus]
      exact Nat.not_lt.mpr (Nat.sub_le s 1)
    have hfuture : ¬ (NamedRun.stateBefore S rho j w).st.core.s < u.slot := by
      rw [hslot, hus]
      exact Nat.lt_irrefl s
    have hclock : (NamedRun.stateBefore S rho j w).st.core.t < Gamma :=
      lt_of_le_of_lt
        (by
          show (NamedRun.stateBefore S rho j w).st.t ≤ t
          simpa [Event.time] using
            (Protocol.store_time_le_event_time S adm.toNamedScheduleWellFormed
              hdeliver w)) hdeadline
    have hlocal := Protocol.on_goldfish_vote_checked_beforeCutoff_or_equivocates
      S.E (NamedRun.stateBefore S rho j w).st.core u Gamma hcommittee hstamps
      hfresh hfuture hclock
    have hstep :
        (NamedRun.stateBefore S rho (j + 1) w).st.core =
          Protocol.on_goldfish_vote_checked S.E
            (NamedRun.stateBefore S rho j w).st.core u := by
      rw [Proofs.NamedRuntime.stateBefore_deliver S rho hdeliver]
      rfl
    refine ⟨j, _, hdeliver, ?_, ?_⟩
    · simpa only [Event.time] using hdeadline
    · change u ∈ beforeCutoff
          (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote Gamma
          ((NamedRun.stateBefore S rho (j + 1) w).st.core.pool u.slot) ∨
        Protocol.equivocates
          (beforeCutoff
            (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote Gamma
            ((NamedRun.stateBefore S rho (j + 1) w).st.core.pool u.slot))
          u.val_index = true
      rw [hstep]
      exact hlocal
  · obtain ⟨hblock, hnew, hcore, huindex⟩ := hcall
    have huB : u ∈ B.gf_votes := List.mem_of_getElem? huindex
    have huErase : u ∈ B.erase.gf_votes := by
      rwa [Proofs.NamedWire.erase_goldfish_votes]
    rcases hblock with
        ⟨t', hdeliver, hbefore⟩ | ⟨t', htick, hBemit, hbefore⟩
    · have heq : Event.deliver w (Object.block B) t' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      have hpreBodies : B ∉ before.bodies := by
        intro hB
        apply hnew
        have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j w).1.1.1
        have hB' : B ∈ (NamedRun.stateBefore S rho j w).st.bodies := by
          simpa [hbefore] using hB
        rw [hbefore, hcoh.1]
        exact Finset.mem_image_of_mem NamedBlock.erase hB'
      have hpostBodies := weakct_recovery_on_block_new_body S before B hnew hcore
      have hstamps : Protocol.PoolStamps before.core := by
        rw [hbefore]
        exact Protocol.poolStamps_stateBefore
          S adm.toNamedScheduleWellFormed w j
      have hslot : before.core.s = s := by
        rw [hbefore]
        exact delivery_store_slot_before_freeze S adm hw hdeliver hlo hhi
      have hfresh : ¬ u.slot < before.core.s - 1 := by
        rw [hus, hslot]
        exact Nat.not_lt.mpr (Nat.sub_le s 1)
      have hfuture : ¬ before.core.s < u.slot := by
        rw [hslot, hus]
        exact Nat.lt_irrefl s
      have hcommittee : u.val_index ∈ S.E.committee u.slot := by
        have hwire := adm.wire _ w (Object.block B) t hdeliver
        simp only [Object.wellFormed, NamedReceipt.wellFormed,
          Bool.and_eq_true] at hwire
        have hcommittee := hwire.2
        simp only [List.all_eq_true, decide_eq_true_eq] at hcommittee
        exact hcommittee u huErase
      have hclock : before.core.t < Gamma := by
        have hle : before.core.t ≤ t := by
          rw [hbefore]
          simpa [Event.time] using
            Protocol.store_time_le_event_time S adm.toNamedScheduleWellFormed
              hdeliver w
        exact lt_of_le_of_lt hle hdeadline
      have hlocal := Proofs.Optimistic.block_carried_before_deadline_or_equivocates
        S before B u Gamma hstamps hpreBodies hpostBodies huErase hcommittee
        hfresh hfuture hclock
      have hstate := Proofs.NamedReceiptCallsBase.delivery_result S rho hdeliver
      let final := Protocol.NamedAdmission.on_block_with
        .alsoCarried S.E S.hc S.cfg before B
      have hfinalEq : (NamedRun.stateBefore S rho (j + 1) w).st = final := by
        rw [hstate]
        simpa [final, hbefore, NamedReceipt.process]
      refine ⟨j, _, he, ?_, ?_⟩
      · simpa only [htime] using hdeadline
      · simpa only [final, hfinalEq] using hlocal
    · have heq : Event.tick w t' = e := Option.some.inj (htick.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      have hproposal := congrArg Prod.snd
        (Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hBemit)
      have hshape := Proofs.HealingSurface.block_mem_on_tick_emit S w
        (NamedRun.stateBefore S rho j w) t hBemit
      have hguard := hshape.1
      have hgf0 : B.gf_votes =
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S rho j w) t).st.core.gf_votes
            ((NamedActionReads.confirmationReadFrom S
              (NamedRun.stateBefore S rho j w) t).st.core.s - 1) := by
        unfold Protocol.NamedDuties.propose_block_with at hproposal
        split at hproposal
        · cases hproposal
        · rename_i B' hB'
          have hBB' : B' = B := Option.some.inj hproposal
          rw [← hBB']
          exact Proofs.Optimistic.proposal_with_gf_votes _ .poolAndCarried
            S.E S.hc (S.node w) _ hB'
      have hgf : B.gf_votes = before.core.gf_votes (before.core.s - 1) := by
        simpa [hbefore] using hgf0
      have hstamps : Protocol.PoolStamps before.core := by
        rw [hbefore]
        have hrawStamps := Protocol.poolStamps_stateBefore
          S adm.toNamedScheduleWellFormed w j
        have htle : (NamedRun.stateBefore S rho j w).st.core.t ≤ t := by
          simpa [Event.time] using
            Protocol.store_time_le_event_time S adm.toNamedScheduleWellFormed
              htick w
        exact (Protocol.poolStep_tickStore _ _ _ htle hrawStamps).2
      have huPool : u ∈ before.core.gf_votes (before.core.s - 1) := by
        rw [← hgf]
        exact List.mem_of_getElem? huindex
      have hslot : before.core.s = s + 1 := by
        have hslotTime : before.core.s = S.E.slotOf t := by
          rw [hbefore]
          rfl
        have hspos : 0 < before.core.s := by
          rw [hslotTime]
          exact hguard.1
        have hs' : s = before.core.s - 1 := by
          simpa only [hus] using hstamps.slot (before.core.s - 1) u huPool
        calc
          before.core.s = (before.core.s - 1) + 1 :=
            (Nat.sub_add_cancel (Nat.succ_le_of_lt hspos)).symm
          _ = s + 1 := by rw [← hs']
      have hcommittee : u.val_index ∈ S.E.committee u.slot := by
        have huPool' : u ∈
            (NamedRun.stateBefore S rho j w).st.core.gf_votes
              (before.core.s - 1) := by
          have hpoolEq : before.core.gf_votes =
              (NamedRun.stateBefore S rho j w).st.core.gf_votes := by
            rw [hbefore]
            rfl
          rw [← hpoolEq]
          exact huPool
        have hcommittee' := CommitteePools.stateBefore S rho w j
          (before.core.s - 1) u huPool'
        have hs' := hstamps.slot (before.core.s - 1) u huPool
        simpa only [hs'] using hcommittee'
      have hfresh : ¬ u.slot < before.core.s - 1 := by
        rw [hus, hslot]
        rw [Nat.add_sub_cancel]
        exact Nat.lt_irrefl s
      have hfuture : ¬ before.core.s < u.slot := by
        rw [hslot, hus]
        exact Nat.not_lt.mpr (Nat.le_add_right s 1)
      have hclock : before.core.t < Gamma := by
        rw [hbefore]
        simpa [Event.time] using hdeadline
      have hpostBodies := weakct_recovery_on_block_new_body S before B hnew hcore
      have hlocal := Proofs.Optimistic.block_carried_before_deadline_or_equivocates
        S before B u Gamma hstamps (by
          intro hB
          apply hnew
          have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j w).1.1.1
          have hB' : B ∈ (NamedRun.stateBefore S rho j w).st.bodies := by
            simpa [hbefore] using hB
          have hcoreB : B.erase ∈
              (NamedRun.stateBefore S rho j w).st.core.T := by
            rw [hcoh.1]
            exact Finset.mem_image_of_mem NamedBlock.erase hB'
          simpa [hbefore, Protocol.NamedStore.setClock] using hcoreB) hpostBodies huErase
        hcommittee hfresh hfuture hclock
      let pre := NamedRun.stateBefore S rho j w
      let gc := NamedProfile.gradeContract
        (NamedActionReads.confirmationReadFrom S pre t).cache
      have hfields := Proofs.Optimistic.tick_fields_from_proposal gc S (S.node w)
        pre.st pre.record t (by simpa only [S.node_val_index] using hguard)
      let final := Protocol.NamedAdmission.on_block_with
        .alsoCarried S.E S.hc S.cfg before B
      have hproposalStage :
          (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
            (S.node w) before).1 = final := by
        have hpair := congrArg Prod.fst
          (Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hBemit)
        simpa only [gc, pre, final, hbefore] using hpair
      have hstate : NamedRun.stateBefore S rho (j + 1) w =
          (NamedNode.tick S w pre t).1 := Proofs.NamedRuntime.stateBefore_tick S rho htick
      have hgcstep : (NamedNode.tick S w pre t).1.st =
          (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w)
            pre.st pre.record t).1 := rfl
      have hfinalFields :
          (NamedRun.stateBefore S rho (j + 1) w).st.core.gf_votes = final.core.gf_votes ∧
          (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote =
            final.core.timestamp_vote := by
        rw [hstate, hgcstep]
        have hguard' : 0 < S.E.slotOf t ∧
            t = Protocol.proposal_time S.E (S.E.slotOf t) ∧
            S.E.proposer (S.E.slotOf t) = (S.node w).val_index := by
          simpa only [S.node_val_index] using hguard
        dsimp only at hfields
        rw [if_pos hguard'] at hfields
        have hproposalStage' :
            (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
              (S.node w) (Protocol.NamedStore.setClock S.E pre.st t)).1 = final := by
          simpa only [pre, hbefore] using hproposalStage
        rw [hproposalStage'] at hfields
        exact hfields
      have hlocal' : u ∈ beforeCutoff final.core.timestamp_vote Gamma
          (final.core.pool u.slot) ∨
          Protocol.equivocates
            (beforeCutoff final.core.timestamp_vote Gamma (final.core.pool u.slot))
            u.val_index = true := by
        simpa only [final] using hlocal
      refine ⟨j, _, he, ?_, ?_⟩
      · simpa only [htime] using hdeadline
      · change u ∈ beforeCutoff
            (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote Gamma
            ((NamedRun.stateBefore S rho (j + 1) w).st.core.pool u.slot) ∨
          Protocol.equivocates
            (beforeCutoff
              (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote Gamma
              ((NamedRun.stateBefore S rho (j + 1) w).st.core.pool u.slot))
            u.val_index = true
        simp only [Protocol.NamedStore.pool, Protocol.Store.pool]
        rw [hfinalFields.1, hfinalFields.2]
        exact hlocal'

private theorem gfVote_processes_settled_at_voteDuty_after_gst
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest)
    {u : GoldfishVote V} {s : Slot} {t : Time} {j : Nat}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hproc : NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.view_freeze S.E s)
    (hhor : Protocol.view_freeze S.E s ≤ rho.horizon) :
    u ∈ beforeCutoff
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_vote
          (Protocol.view_freeze S.E s)
          ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) ∨
      Protocol.equivocates
        (beforeCutoff
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_vote
          (Protocol.view_freeze S.E s)
          ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s))
        u.val_index = true := by
  obtain ⟨i, e, hi, het, hlocal⟩ :=
    weakct_actual_gfVote_settled_before_deadline S adm hproc hus hw hlo hhi hhi
  let readTime := Protocol.vote_time S.E (s + 1)
  let N := (rho.events.filter (fun x => decide (x.time < readTime))).length
  have hiN : i < N := by
    by_contra hnot
    have hNle : N ≤ i := Nat.le_of_not_gt hnot
    have hreadE : readTime ≤ e.time :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        (t := readTime) (j := i) (e := e) (by simpa [N] using hNle) hi
    exact (not_le_of_gt
      (lt_trans het (view_freeze_lt_vote_time_succ S.E s))) hreadE
  have hcarry : PoolCarry (NamedRun.stateBefore S rho (i + 1) w).st.core
      (NamedRun.stateBefore S rho N w).st.core :=
    pool_carry S adm.toNamedScheduleWellFormed w N (Nat.succ_le_of_lt hiN)
  have hstore : Proofs.Optimistic.voteDutyStore S rho w (s + 1) =
      Proofs.Optimistic.voteStore S (NamedRun.stateBefore S rho N w).st.core (s + 1) := by
    unfold Proofs.Optimistic.voteDutyStore Run.storeBeforeTime
    rw [congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed readTime) w)]
  rw [hus] at hlocal
  rcases hlocal with hmem | hequiv
  · apply Or.inl
    rw [hstore]
    simpa only [Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      beforeCutoff_subset_of_poolCarry hcarry s
        (Protocol.view_freeze S.E s) hmem
  · apply Or.inr
    apply equivocates_mono _ u.val_index hequiv
    intro x hx
    rw [hstore]
    simpa only [Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      beforeCutoff_subset_of_poolCarry hcarry s
        (Protocol.view_freeze S.E s) hx

private theorem accepted_gfVote_forward_settled_at_voteDuty_after_gst
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {u : GoldfishVote V} {s : Slot} {t : Time}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hacc : NamedRun.acceptsAt S rho i v (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.support_cutoff S.E s)
    (hhor : Protocol.view_freeze S.E s ≤ rho.horizon) :
    u ∈ beforeCutoff
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_vote
          (Protocol.view_freeze S.E s)
          ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) ∨
      Protocol.equivocates
        (beforeCutoff
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_vote
          (Protocol.view_freeze S.E s)
          ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s))
        u.val_index = true := by
  by_cases halready : Object.processed
      (rho.stateBefore S (i + 1) w).st (Object.gfVote u) = true
  · obtain ⟨e, he, -, het⟩ := hacc.1.2
    apply Or.inl
    apply gfVote_processed_after_event_at_voteDuty S adm he hus halready
    simpa only [het] using
      lt_trans hhi (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s)
  · have hunaccepted : Object.processed
        (rho.stateBefore S (i + 1) w).st (Object.gfVote u) = false :=
      Bool.eq_false_of_not_eq_true halready
    have hrelayHor : t + S.E.Δ ≤ rho.horizon := by
      have hlt : t + S.E.Δ < Protocol.view_freeze S.E s := by
        calc
          t + S.E.Δ < Protocol.support_cutoff S.E s + S.E.Δ :=
            Int.add_lt_add_right hhi S.E.Δ
          _ = Protocol.view_freeze S.E s :=
            support_cutoff_add_delta_eq_view_freeze S.E s
      exact le_trans (le_of_lt hlt) hhor
    have hpostAcceptance : S.E.t_GST ≤ t := le_trans hpost hlo
    obtain ⟨t', hcausal, hdeadline, j', hproc⟩ :=
      relay_gf_vote_after_gst S adm hv hw hpostAcceptance hacc
        hunaccepted hrelayHor
    have hbeforeFreeze : t' < Protocol.view_freeze S.E s := by
      exact lt_trans hdeadline (by
        calc
          t + S.E.Δ < Protocol.support_cutoff S.E s + S.E.Δ :=
            Int.add_lt_add_right hhi S.E.Δ
          _ = Protocol.view_freeze S.E s :=
            support_cutoff_add_delta_eq_view_freeze S.E s)
    exact gfVote_processes_settled_at_voteDuty_after_gst
      S adm hw hpost hproc hus (le_trans hlo hcausal) hbeforeFreeze hhor

private theorem weakct_actual_gfVote_settled_at_confStore_after_gst
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {j : Nat} {w : V} {u : GoldfishVote V} {s : Slot} {t : Time}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hactual : NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t)
    (hus : u.slot = s) (hw : w ∈ rho.honest)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.confirmation_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    u ∈ confLate S.E (Proofs.Optimistic.confStore S rho w s) s ∨
      Protocol.equivocates
        (confLate S.E (Proofs.Optimistic.confStore S rho w s) s)
        u.val_index = true := by
  let Gamma := Protocol.confirmation_time S.E s
  have carry_to_conf :
      ∀ (i : Nat) (e : Event V),
        rho.events[i]? = some e → e.time < Gamma →
        (u ∈ beforeCutoff
            (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote Gamma
            ((NamedRun.stateBefore S rho (i + 1) w).st.pool u.slot) ∨
          Protocol.equivocates
            (beforeCutoff
              (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote Gamma
              ((NamedRun.stateBefore S rho (i + 1) w).st.pool u.slot))
            u.val_index = true) →
        u ∈ confLate S.E (Proofs.Optimistic.confStore S rho w s) s ∨
          Protocol.equivocates
            (confLate S.E (Proofs.Optimistic.confStore S rho w s) s)
            u.val_index = true := by
    intro i e hi hetime hlocal
    let N := (rho.events.filter (fun x => decide (x.time < Gamma))).length
    have hiN : i < N := by
      by_contra hnot
      have hNle : N ≤ i := Nat.le_of_not_gt hnot
      have hGammae : Gamma ≤ e.time :=
        Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
          (t := Gamma) (j := i) (e := e)
          (by simpa [N] using hNle) hi
      exact (not_le_of_gt hetime) hGammae
    have hcarry : PoolCarry
        (NamedRun.stateBefore S rho (i + 1) w).st.core
        (NamedRun.stateBefore S rho N w).st.core :=
      pool_carry S adm.toNamedScheduleWellFormed w N
        (Nat.succ_le_of_lt hiN)
    have hstore : Proofs.Optimistic.confStore S rho w s =
        Proofs.Optimistic.tickStore S (NamedRun.stateBefore S rho N w).st.core Gamma := by
      unfold Proofs.Optimistic.confStore Run.storeBeforeTime
      rw [congrArg NamedNodeState.st
        (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take
          S adm.toNamedScheduleWellFormed Gamma) w)]
    rw [hus] at hlocal
    rcases hlocal with hmem | hequiv
    · apply Or.inl
      rw [confLate, hstore, Proofs.Optimistic.tickStore]
      exact beforeCutoff_subset_of_poolCarry hcarry s Gamma hmem
    · apply Or.inr
      apply equivocates_mono _ u.val_index hequiv
      intro x hx
      rw [confLate, hstore, Proofs.Optimistic.tickStore]
      exact beforeCutoff_subset_of_poolCarry hcarry s Gamma hx
  by_cases hfreeze : t < Protocol.view_freeze S.E s
  · obtain ⟨i, e, hi, hetime, hlocal⟩ :=
      weakct_actual_gfVote_settled_before_deadline S adm hactual hus hw hlo
        hfreeze hhi
    exact carry_to_conf i e hi hetime hlocal
  · obtain ⟨hindex, e, he, hnode, htime⟩ := hactual
    simp only [NamedRun.actualHandlesAtIndex, NamedRun.processesAtIndex] at hindex
    rcases hindex with (⟨t', htick, hem⟩ | ⟨t', hdeliver⟩) |
        ⟨B, j', before, hcall⟩
    · have heq : Event.tick w t' = e := Option.some.inj (htick.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      have hemit : NamedRun.emits S rho w (Object.gfVote u) t :=
        ⟨j, htick, hem⟩
      obtain ⟨hs', ht', -, hus'⟩ := Proofs.Optimistic.emits_gfVote_shape S hemit
      have hslot : S.E.slotOf t = s := by rw [← hus', hus]
      have htVote : t = Protocol.vote_time S.E s := by
        simpa only [hslot] using ht'
      have hemitVote : NamedRun.emits S rho w (Object.gfVote u)
          (Protocol.vote_time S.E s) := by
        simpa only [htVote] using hemit
      have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E s :=
        le_trans hpost (le_of_lt (by
          unfold Protocol.vote_time
          exact Int.lt_add_of_pos_right _ S.E.Δ_pos))
      have hsupport : Protocol.support_cutoff S.E s ≤
          Protocol.confirmation_time S.E s :=
        support_cutoff_le_confirmation_time S.E s
      have hrecv := gfVote_in_cutoff_view_after_gst
        S adm hw (by simpa only [hslot] using hs') hpostVote hemitVote hus hw
        (Protocol.confirmation_time S.E s)
        (Protocol.confirmation_time S.E s)
        hsupport hsupport (le_trans hsupport hhor)
      apply Or.inl
      simpa only [confLate, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Protocol.NamedStore.pool, Protocol.Store.pool] using hrecv
    · have heq : Event.deliver w (Object.gfVote u) t' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      exact gfVote_delivery_settled_at_confStore S adm hw hdeliver hus hlo hhi
    · obtain ⟨hblock, hnew, hcore, huindex⟩ := hcall
      have huB : u ∈ B.gf_votes := List.mem_of_getElem? huindex
      have huErase : u ∈ B.erase.gf_votes := by
        rwa [Proofs.NamedWire.erase_goldfish_votes]
      rcases hblock with
          ⟨t', hdeliver, hbefore⟩ | ⟨t', htick, hBemit, hbefore⟩
      · have heq : Event.deliver w (Object.block B) t' = e :=
          Option.some.inj (hdeliver.symm.trans he)
        have htt : t' = t := (congrArg Event.time heq).trans htime
        subst t'
        have hpreBodies : B ∉ before.bodies := by
          intro hB
          apply hnew
          have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j w).1.1.1
          have hB' : B ∈ (NamedRun.stateBefore S rho j w).st.bodies := by
            simpa [hbefore] using hB
          have hcoreB : B.erase ∈
              (NamedRun.stateBefore S rho j w).st.core.T := by
            rw [hcoh.1]
            exact Finset.mem_image_of_mem NamedBlock.erase hB'
          simpa [hbefore, Protocol.NamedStore.setClock] using hcoreB
        have hpostBodies := weakct_recovery_on_block_new_body S before B hnew hcore
        have hstamps : Protocol.PoolStamps before.core := by
          rw [hbefore]
          exact Protocol.poolStamps_stateBefore
            S adm.toNamedScheduleWellFormed w j
        have hslot : before.core.s = s ∨ before.core.s = s + 1 := by
          rw [hbefore]
          exact delivery_store_slot_before_confirmation S adm hw hdeliver hlo hhi
        have hfresh : ¬ u.slot < before.core.s - 1 := by
          rcases hslot with hs | hs
          · rw [hus, hs]
            exact Nat.not_lt.mpr (Nat.sub_le s 1)
          · rw [hus, hs, Nat.add_sub_cancel]
            exact Nat.lt_irrefl s
        have hfuture : ¬ before.core.s < u.slot := by
          rcases hslot with hs | hs
          · rw [hus, hs]
            exact Nat.lt_irrefl s
          · rw [hus, hs]
            exact Nat.not_lt.mpr (Nat.le_add_right s 1)
        have hcommittee : u.val_index ∈ S.E.committee u.slot := by
          have hwire := adm.wire _ w (Object.block B) t hdeliver
          simp only [Object.wellFormed, NamedReceipt.wellFormed,
            Bool.and_eq_true] at hwire
          have hcarried := hwire.2
          simp only [List.all_eq_true, decide_eq_true_eq] at hcarried
          exact hcarried u huErase
        have hclock : before.core.t < Gamma := by
          have hle : before.core.t ≤ t := by
            rw [hbefore]
            simpa [Event.time] using
              Protocol.store_time_le_event_time S
                adm.toNamedScheduleWellFormed hdeliver w
          exact lt_of_le_of_lt hle hhi
        have hlocal := Proofs.Optimistic.block_carried_before_deadline_or_equivocates
          S before B u Gamma hstamps hpreBodies hpostBodies huErase hcommittee
          hfresh hfuture hclock
        have hstate := Proofs.NamedReceiptCallsBase.delivery_result S rho hdeliver
        let final := Protocol.NamedAdmission.on_block_with
          .alsoCarried S.E S.hc S.cfg before B
        have hfinalEq : (NamedRun.stateBefore S rho (j + 1) w).st = final := by
          rw [hstate]
          simpa [final, hbefore, NamedReceipt.process]
        have hlocal' : u ∈ beforeCutoff
            (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote Gamma
            ((NamedRun.stateBefore S rho (j + 1) w).st.pool u.slot) ∨
            Protocol.equivocates
              (beforeCutoff
                (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote Gamma
                ((NamedRun.stateBefore S rho (j + 1) w).st.pool u.slot))
              u.val_index = true := by
          simpa only [final, hfinalEq] using hlocal
        exact carry_to_conf j e he (by simpa only [htime] using hhi) hlocal'
      · have heq : Event.tick w t' = e :=
          Option.some.inj (htick.symm.trans he)
        have htt : t' = t := (congrArg Event.time heq).trans htime
        subst t'
        have hproposal := congrArg Prod.snd
          (Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hBemit)
        have hshape := Proofs.HealingSurface.block_mem_on_tick_emit S w
          (NamedRun.stateBefore S rho j w) t hBemit
        have hguard := hshape.1
        have hgf0 : B.gf_votes =
            (NamedActionReads.confirmationReadFrom S
              (NamedRun.stateBefore S rho j w) t).st.core.gf_votes
              ((NamedActionReads.confirmationReadFrom S
                (NamedRun.stateBefore S rho j w) t).st.core.s - 1) := by
          unfold Protocol.NamedDuties.propose_block_with at hproposal
          split at hproposal
          · cases hproposal
          · rename_i B' hB'
            have hBB' : B' = B := Option.some.inj hproposal
            rw [← hBB']
            exact Proofs.Optimistic.proposal_with_gf_votes _ .poolAndCarried
              S.E S.hc (S.node w) _ hB'
        have hgf : B.gf_votes = before.core.gf_votes (before.core.s - 1) := by
          simpa [hbefore] using hgf0
        have hstamps : Protocol.PoolStamps before.core := by
          rw [hbefore]
          have hrawStamps := Protocol.poolStamps_stateBefore
            S adm.toNamedScheduleWellFormed w j
          have htle : (NamedRun.stateBefore S rho j w).st.core.t ≤ t := by
            simpa [Event.time] using
              Protocol.store_time_le_event_time S
                adm.toNamedScheduleWellFormed htick w
          exact (Protocol.poolStep_tickStore _ _ _ htle hrawStamps).2
        have huPool : u ∈ before.core.gf_votes (before.core.s - 1) := by
          rw [← hgf]
          exact List.mem_of_getElem? huindex
        have hslot : before.core.s = s + 1 := by
          have hslotTime : before.core.s = S.E.slotOf t := by
            rw [hbefore]
            rfl
          have hspos : 0 < before.core.s := by
            rw [hslotTime]
            exact hguard.1
          have hs' : s = before.core.s - 1 := by
            simpa only [hus] using hstamps.slot (before.core.s - 1) u huPool
          calc
            before.core.s = (before.core.s - 1) + 1 :=
              (Nat.sub_add_cancel (Nat.succ_le_of_lt hspos)).symm
            _ = s + 1 := by rw [← hs']
        have hcommittee : u.val_index ∈ S.E.committee u.slot := by
          have huPool' : u ∈
              (NamedRun.stateBefore S rho j w).st.core.gf_votes
                (before.core.s - 1) := by
            have hpoolEq : before.core.gf_votes =
                (NamedRun.stateBefore S rho j w).st.core.gf_votes := by
              rw [hbefore]
              rfl
            rw [← hpoolEq]
            exact huPool
          have hcommittee' := CommitteePools.stateBefore S rho w j
            (before.core.s - 1) u huPool'
          have hs' := hstamps.slot (before.core.s - 1) u huPool
          simpa only [hs'] using hcommittee'
        have hfresh : ¬ u.slot < before.core.s - 1 := by
          rw [hus, hslot, Nat.add_sub_cancel]
          exact Nat.lt_irrefl s
        have hfuture : ¬ before.core.s < u.slot := by
          rw [hslot, hus]
          exact Nat.not_lt.mpr (Nat.le_add_right s 1)
        have hclock : before.core.t < Gamma := by
          rw [hbefore]
          simpa [Event.time] using hhi
        have hpostBodies := weakct_recovery_on_block_new_body S before B hnew hcore
        have hpreBodies : B ∉ before.bodies := by
          intro hB
          apply hnew
          have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j w).1.1.1
          have hB' : B ∈ (NamedRun.stateBefore S rho j w).st.bodies := by
            simpa [hbefore] using hB
          have hcoreB : B.erase ∈
              (NamedRun.stateBefore S rho j w).st.core.T := by
            rw [hcoh.1]
            exact Finset.mem_image_of_mem NamedBlock.erase hB'
          simpa [hbefore, Protocol.NamedStore.setClock] using hcoreB
        have hlocal := Proofs.Optimistic.block_carried_before_deadline_or_equivocates
          S before B u Gamma hstamps hpreBodies hpostBodies huErase hcommittee
          hfresh hfuture hclock
        let pre := NamedRun.stateBefore S rho j w
        let gc := NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S pre t).cache
        have hfields := Proofs.Optimistic.tick_fields_from_proposal gc S (S.node w)
          pre.st pre.record t (by simpa only [S.node_val_index] using hguard)
        let final := Protocol.NamedAdmission.on_block_with
          .alsoCarried S.E S.hc S.cfg before B
        have hproposalStage :
            (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
              (S.node w) before).1 = final := by
          have hpair := congrArg Prod.fst
            (Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hBemit)
          simpa only [gc, pre, final, hbefore] using hpair
        have hstate : NamedRun.stateBefore S rho (j + 1) w =
            (NamedNode.tick S w pre t).1 := Proofs.NamedRuntime.stateBefore_tick S rho htick
        have hgcstep : (NamedNode.tick S w pre t).1.st =
            (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w)
              pre.st pre.record t).1 := rfl
        have hfinalFields :
            (NamedRun.stateBefore S rho (j + 1) w).st.core.gf_votes = final.core.gf_votes ∧
            (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote =
              final.core.timestamp_vote := by
          rw [hstate, hgcstep]
          have hguard' : 0 < S.E.slotOf t ∧
              t = Protocol.proposal_time S.E (S.E.slotOf t) ∧
              S.E.proposer (S.E.slotOf t) = (S.node w).val_index := by
            simpa only [S.node_val_index] using hguard
          dsimp only at hfields
          rw [if_pos hguard'] at hfields
          have hproposalStage' :
              (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
                (S.node w) (Protocol.NamedStore.setClock S.E pre.st t)).1 = final := by
            simpa only [pre, hbefore] using hproposalStage
          rw [hproposalStage'] at hfields
          exact hfields
        have hlocal' : u ∈ beforeCutoff
            (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote Gamma
            ((NamedRun.stateBefore S rho (j + 1) w).st.pool u.slot) ∨
            Protocol.equivocates
              (beforeCutoff
                (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote Gamma
                ((NamedRun.stateBefore S rho (j + 1) w).st.pool u.slot))
              u.val_index = true := by
          change u ∈ beforeCutoff
              (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote Gamma
              ((NamedRun.stateBefore S rho (j + 1) w).st.core.pool u.slot) ∨
            Protocol.equivocates
              (beforeCutoff
                (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote Gamma
                ((NamedRun.stateBefore S rho (j + 1) w).st.core.pool u.slot))
              u.val_index = true
          simp only [Protocol.NamedStore.pool, Protocol.Store.pool]
          rw [hfinalFields.1, hfinalFields.2]
          simpa only [final] using hlocal
        exact carry_to_conf j e he (by simpa only [htime] using hhi) hlocal'

private theorem gfVote_processes_settled_at_confStore_after_gst
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest)
    {u : GoldfishVote V} {s : Slot} {t : Time}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    {j : Nat}
    (hproc : NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.confirmation_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    u ∈ confLate S.E (Proofs.Optimistic.confStore S rho w s) s ∨
      Protocol.equivocates
        (confLate S.E (Proofs.Optimistic.confStore S rho w s) s)
        u.val_index = true := by
  exact weakct_actual_gfVote_settled_at_confStore_after_gst S adm hpost hproc hus hw hlo hhi hhor

private theorem accepted_gfVote_backward_settled_at_confStore_after_gst
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {u : GoldfishVote V} {s : Slot} {t : Time}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hacc : NamedRun.acceptsAt S rho i w (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.vote_time S.E (s + 1))
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    u ∈ confLate S.E (Proofs.Optimistic.confStore S rho v s) s ∨
      Protocol.equivocates
        (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
        u.val_index = true := by
  by_cases halready : Object.processed
      (NamedRun.stateBefore S rho (i + 1) v).st (Object.gfVote u) = true
  · obtain ⟨e, he, -, het⟩ := hacc.1.2
    have hmem : u ∈ (NamedRun.stateBefore S rho (i + 1) v).st.gf_votes s := by
      simp only [Object.processed, NamedReceipt.processed, decide_eq_true_eq,
        Protocol.NamedStore.pool, Protocol.Store.pool, List.mem_toFinset] at halready
      rwa [hus] at halready
    have hstamps := Protocol.poolStamps_stateBefore
      S adm.toNamedScheduleWellFormed v (i + 1)
    obtain ⟨c, hc⟩ : ∃ c : Stamp,
        (NamedRun.stateBefore S rho (i + 1) v).st.timestamp_vote u = some c :=
      Option.isSome_iff_exists.mp (hstamps.stamped s u hmem)
    have hclock : (NamedRun.stateBefore S rho (i + 1) v).st.t ≤ e.time :=
      Protocol.block_store_time_after_event_le
        S adm.toNamedScheduleWellFormed he v
    have hvoteConf : Protocol.vote_time S.E (s + 1) <
        Protocol.confirmation_time S.E s := by
      rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos
    have hcConf : c < (Protocol.confirmation_time S.E s : Stamp) :=
      lt_of_le_of_lt (hstamps.bounded u c hc)
        (WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hclock (by
          simpa only [het] using lt_trans hhi hvoteConf)))
    let Gamma := Protocol.confirmation_time S.E s
    let N := (rho.events.filter (fun x => decide (x.time < Gamma))).length
    have hiN : i < N := by
      by_contra hnot
      have hNle : N ≤ i := Nat.le_of_not_gt hnot
      have hGammae : Gamma ≤ e.time :=
        Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed (t := Gamma)
          (j := i) (e := e) (by simpa only [N] using hNle) he
      rw [het] at hGammae
      exact (not_le_of_gt (lt_trans hhi hvoteConf)) hGammae
    have hcarry : PoolCarry
        (NamedRun.stateBefore S rho (i + 1) v).st.core
        (NamedRun.stateBefore S rho N v).st.core :=
      pool_carry S adm.toNamedScheduleWellFormed v N (Nat.succ_le_of_lt hiN)
    have hstore : Proofs.Optimistic.confStore S rho v s =
        Proofs.Optimistic.tickStore S (NamedRun.stateBefore S rho N v).st.core Gamma := by
      unfold Proofs.Optimistic.confStore Run.storeBeforeTime
      rw [congrArg NamedNodeState.st
        (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take
          S adm.toNamedScheduleWellFormed Gamma) v)]
    apply Or.inl
    rw [confLate, hstore, beforeCutoff, Finset.mem_filter, Protocol.Store.pool,
      List.mem_toFinset]
    refine ⟨hcarry.mem s u hmem, ?_⟩
    simp only [Proofs.Optimistic.tickStore, stampedBefore, hcarry.stamp u c hc,
      decide_eq_true_eq]
    exact hcConf
  · have hunaccepted : Object.processed
        (NamedRun.stateBefore S rho (i + 1) v).st (Object.gfVote u) = false :=
      Bool.eq_false_of_not_eq_true halready
    have hrelayHor : t + S.E.Δ ≤ rho.horizon := by
      have hlt : t + S.E.Δ < Protocol.confirmation_time S.E s := by
        rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
        exact Int.add_lt_add_right hhi S.E.Δ
      exact le_trans (le_of_lt hlt) hhor
    have hpostAcceptance : S.E.t_GST ≤ t := le_trans hpost hlo
    obtain ⟨t', hcausal, hdeadline, j', hproc⟩ :=
      relay_gf_vote_after_gst S adm hw hv hpostAcceptance hacc
        hunaccepted hrelayHor
    have hbeforeConf : t' < Protocol.confirmation_time S.E s :=
      lt_trans hdeadline (by
        rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
        exact Int.add_lt_add_right hhi S.E.Δ)
    exact gfVote_processes_settled_at_confStore_after_gst
      S adm hv hpost hproc hus (le_trans hlo hcausal) hbeforeConf hhor

private theorem targetPoolVote_settledAtSource_after_gst
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {u : GoldfishVote V}
    (hu : u ∈ (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) :
    u ∈ confLate S.E (Proofs.Optimistic.confStore S rho v s) s ∨
      Protocol.equivocates
        (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
        u.val_index = true := by
  obtain ⟨i, t, hacc, hus, hlo, hhi⟩ :=
    targetPoolVoteAcceptedBeforeVote S adm hu
  exact accepted_gfVote_backward_settled_at_confStore_after_gst
    S adm hv hw hpost hacc hus hlo hhi hhor

private theorem targetPoolEquivocates_settledAtSource_after_gst
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) {x : V}
    (hequiv : Protocol.equivocates
      ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) x = true) :
    Protocol.equivocates
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s) x = true := by
  by_cases hsource : Protocol.equivocates
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s) x = true
  · exact hsource
  rw [Protocol.equivocates, decide_eq_true_eq] at hequiv ⊢
  have hsub :
      Protocol.votes_by
          ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) x ⊆
        Protocol.votes_by
          (confLate S.E (Proofs.Optimistic.confStore S rho v s) s) x := by
    intro u hu
    rw [Protocol.votes_by, Finset.mem_filter] at hu ⊢
    refine ⟨?_, hu.2⟩
    rcases targetPoolVote_settledAtSource_after_gst
        S adm hv hw hpost hhor hu.1 with hmem | hequivSource
    · exact hmem
    · rw [hu.2] at hequivSource
      exact False.elim (hsource hequivSource)
  exact le_trans hequiv (Finset.card_le_card hsub)

private theorem targetRawVote_settledAtSource_after_gst
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    ∀ u ∈ Protocol.voter_view S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1),
      u ∈ confLate S.E (Proofs.Optimistic.confStore S rho v s) s ∨
        Protocol.equivocates
          (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
          u.val_index = true := by
  intro u hu
  rw [Protocol.voter_view, Finset.mem_union] at hu
  rcases hu with hreceipt | hcarried
  · rw [Nat.add_sub_cancel] at hreceipt
    obtain ⟨i, t, hacc, hus, hlo, hhi⟩ :=
      targetReceiptVotesAcceptedInWindow_of_admissible S adm hw s u hreceipt
    exact accepted_gfVote_backward_settled_at_confStore_after_gst
      S adm hv hw hpost hacc hus hlo
        (lt_trans hhi (view_freeze_lt_vote_time_succ S.E s)) hhor
  · rw [Finset.mem_biUnion] at hcarried
    obtain ⟨B, hB, huB⟩ := hcarried
    rw [Finset.mem_filter] at hB huB
    have hus : u.slot = s := by
      simpa only [Nat.add_sub_cancel] using huB.2
    have huList : u ∈ B.gf_votes := List.mem_toFinset.mp huB.1
    rcases targetCarrierVote_settledInPool
        S adm hw hB.1 hB.2 huList hus with hpool | hequiv
    · exact targetPoolVote_settledAtSource_after_gst
        S adm hv hw hpost hhor hpool
    · exact Or.inr
        (targetPoolEquivocates_settledAtSource_after_gst
          S adm hv hw hpost hhor hequiv)

private theorem weakct_finalized_preceq_at_event
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} {v : V} {B : Block V} {i : Nat} {e : Event V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).toHealing.toFG) B)
    (hi : rho.events[i]? = some e)
    (hlt : e.time < Protocol.view_freeze S.E s) :
    Block.Preceq (NamedRun.stateBefore S rho i v).st.core.F B := by
  let readTime := Protocol.vote_time S.E (s + 1)
  let n := (rho.events.filter (fun x => decide (x.time < readTime))).length
  have hiN : i < n := by
    by_contra hnot
    have hni : n ≤ i := Nat.le_of_not_gt hnot
    have hreadE : readTime ≤ e.time :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        (t := readTime) (j := i) (e := e)
        (by simpa [n] using hni) hi
    exact (not_le_of_gt (lt_trans hlt
      (view_freeze_lt_vote_time_succ S.E s))) hreadE
  let pre := (NamedRun.stateBeforeTime S rho readTime v).st
  have hmono : Block.Preceq
      (NamedRun.stateBefore S rho i v).st.core.F pre.core.F := by
    have hprefix := stateBefore_F_mono S rho v (Nat.le_of_lt hiN)
    have hstore : pre = (NamedRun.stateBefore S rho n v).st := by
      simpa only [pre] using congrArg NamedNodeState.st
        (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take
          S adm.toNamedScheduleWellFormed readTime) v)
    simpa only [hstore] using hprefix
  have hFJ : Block.Preceq pre.core.F pre.core.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho readTime v
  have hFroot : Block.Preceq pre.core.F
      (Protocol.get_fg_root pre.core.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F (st := pre.core.toHealing.toFG) hFJ
  have hroot' : Block.Preceq
      (Protocol.get_fg_root pre.core.toHealing.toFG) B := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, pre, readTime] using hroot
  exact Block.preceq_trans hmono (Block.preceq_trans hFroot hroot')

private theorem weakct_finalized_preceq_at_voteRead
    (S : Setup V) (rho : Run V) {s : Slot} {v : V} {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).toHealing.toFG) B) :
    Block.Preceq
      (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) v).st.core.F B := by
  let pre := (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) v).st
  have hFJ : Block.Preceq pre.core.F pre.core.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      S rho (Protocol.vote_time S.E (s + 1)) v
  have hFroot : Block.Preceq pre.core.F
      (Protocol.get_fg_root pre.core.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F (st := pre.core.toHealing.toFG) hFJ
  have hroot' : Block.Preceq
      (Protocol.get_fg_root pre.core.toHealing.toFG) B := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, pre] using hroot
  exact Block.preceq_trans hFroot hroot'

private theorem weakct_admittedBefore_of_accepted_after_support
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {B : NamedBlock V} {t : Time} {s : Slot}
    (hBpos : 0 < B.slot)
    (hacc : NamedRun.acceptsAt S rho i p (Object.block B) t)
    (htSupport : t < Protocol.support_cutoff S.E s)
    (hpostSupport : S.E.t_GST ≤ Protocol.support_cutoff S.E s)
    (hfreezeHor : Protocol.view_freeze S.E s ≤ rho.horizon)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B.erase) :
    AdmittedBefore S rho w B.erase (Protocol.view_freeze S.E s) := by
  have hsupportFreeze : Protocol.support_cutoff S.E s <
      Protocol.view_freeze S.E s :=
    Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s
  have hacceptCutoff : t < Protocol.view_freeze S.E s :=
    lt_trans htSupport hsupportFreeze
  have hmax : max t S.E.t_GST ≤ Protocol.support_cutoff S.E s :=
    max_le (le_of_lt htSupport) hpostSupport
  have hrelayCutoff : max t S.E.t_GST + S.E.Δ ≤
      Protocol.view_freeze S.E s := by
    calc
      max t S.E.t_GST + S.E.Δ ≤
          Protocol.support_cutoff S.E s + S.E.Δ :=
        by simpa only [add_comm] using add_le_add_right hmax S.E.Δ
      _ = Protocol.view_freeze S.E s :=
        support_cutoff_add_delta_eq_view_freeze S.E s
  have hrelayHorizon : max t S.E.t_GST + S.E.Δ ≤ rho.horizon :=
    le_trans hrelayCutoff hfreezeHor
  by_cases halready : NamedReceipt.processed
      (NamedRun.stateBefore S rho (i + 1) w).st (Object.block B) = true
  · rcases acceptsAt_block_of_processed S rho w (i + 1) B halready with
      hgen | ⟨j, hj, t', hacc'⟩
    · have hzero : B.slot = 0 := by rw [hgen]; rfl
      exact False.elim ((Nat.ne_of_gt hBpos) hzero)
    · obtain ⟨-, e', he', -, ht'⟩ := hacc'.1
      obtain ⟨-, e, he, -, ht⟩ := hacc.1
      have ht'le : t' ≤ t := by
        rw [← ht', ← ht]
        have hji : j ≤ i := Nat.le_of_lt_succ hj
        rcases hji.lt_or_eq with hlt | rfl
        · exact Proofs.Bridges.time_le_of_key_le
            (Proofs.Optimistic.key_le_of_index_lt S adm.toNamedScheduleWellFormed
              hlt he' he)
        · have heq : e' = e := Option.some.inj (he'.symm.trans he)
          rw [heq]
      exact ⟨B, rfl, j, t', hacc', lt_of_le_of_lt ht'le hacceptCutoff⟩
  · have halreadyFalse : NamedReceipt.processed
        (NamedRun.stateBefore S rho (i + 1) w).st (Object.block B) = false :=
      Bool.eq_false_of_not_eq_true halready
    have hguard := not_excludes_of_F_preceq_later_time S rho
      adm.toNamedScheduleWellFormed.sorted
      (hrelayCutoff.trans (view_freeze_lt_vote_time_succ S.E s).le)
      (weakct_finalized_preceq_at_voteRead S rho hroot)
    obtain ⟨t', htt', ht'hi, j, hproc⟩ :=
      adm.toNamedSynchrony.relay_block p hp i B t hacc w hw
        halreadyFalse hrelayHorizon hguard
    have ht'cutoff : t' < Protocol.view_freeze S.E s :=
      lt_of_lt_of_le ht'hi hrelayCutoff
    obtain ⟨e, he, -, heTime⟩ := hproc.2
    have hearly : e.time < Protocol.view_freeze S.E s := by
      simpa only [heTime] using ht'cutoff
    have hF : Block.Preceq
        (NamedRun.stateBefore S rho j w).st.core.F B.erase :=
      weakct_finalized_preceq_at_event S adm hroot
        (show rho.events[j]? = some e from he) hearly
    have hheld := NamedRelayGuards.handled_block_held_of_finalized_prefix
      S rho adm.toNamedScheduleWellFormed adm.toNamedDeliveryWellFormed
      adm.toNamedRootCollisionFree hacc hproc htt' hF
    by_cases hpreheld : B ∈ (NamedRun.stateBefore S rho j w).st.bodies
    · obtain hgen | ⟨k, hkj, ta, hacc'⟩ :=
        NamedOutageProvenance.held_block_origin S rho j w hpreheld
      · have hzero : B.slot = 0 := by rw [hgen]; rfl
        exact False.elim ((Nat.ne_of_gt hBpos) hzero)
      · obtain ⟨-, e', he', -, hta⟩ := hacc'.1
        have hta' : ta ≤ t' := by
          rw [← hta, ← heTime]
          have hkj' : k ≤ j := Nat.le_of_lt hkj
          rcases hkj'.lt_or_eq with hlt | rfl
          · exact Proofs.Bridges.time_le_of_key_le
              (Proofs.Optimistic.key_le_of_index_lt S adm.toNamedScheduleWellFormed
                hlt he' he)
          · have heq : e' = e := Option.some.inj (he'.symm.trans he)
            rw [heq]
        exact ⟨B, rfl, k, ta, hacc',
          lt_of_le_of_lt hta' ht'cutoff⟩
    · have hpreProcessed : NamedReceipt.processed
          (NamedRun.stateBefore S rho j w).st (Object.block B) = false := by
        simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hpreheld
      have hpostProcessed : NamedReceipt.processed
          (NamedRun.stateBefore S rho (j + 1) w).st (Object.block B) = true := by
        simpa only [NamedReceipt.processed, decide_eq_true_eq] using hheld
      have hacc' : NamedRun.acceptsAt S rho j w (Object.block B) t' :=
        ⟨hproc, hpreProcessed, hpostProcessed⟩
      exact ⟨B, rfl, j, t', hacc', ht'cutoff⟩

private theorem supportingTarget_visibleAtVoteDuty_after_gst
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B)
    {u : GoldfishVote V}
    (hu : u ∈ confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
    {H : Block V}
    (hfind : Block.find? (Proofs.Optimistic.confStore S rho v s).T u.head = some H)
    (hBH : Block.Preceq B H) :
    Block.find? (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T u.head = some H ∧
      stampedBefore
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_block
        (Protocol.view_freeze S.E s) H = true := by
  by_cases hgen : H = Block.genesis
  · subst H
    have hvisible := genesis_mem_and_stamp_storeBeforeTime S
      adm.toNamedScheduleWellFormed w (Protocol.vote_time S.E (s + 1))
      (Protocol.view_freeze S.E s)
    have hmem : Block.genesis ∈
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T := by
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hvisible.1
    refine ⟨find_voteDutyStore_of_source_find_and_mem
      S adm hw hfind hmem, ?_⟩
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hvisible.2
  · have hHsource : H ∈ (Proofs.Optimistic.confStore S rho v s).T :=
      Proofs.HealingLemmas.find?_mem hfind
    have hearly : u ∈ confEarly S.E (Proofs.Optimistic.confStore S rho v s) s :=
      (Finset.mem_filter.mp hu).1
    have hresolved : stampedBefore
        (Proofs.Optimistic.confStore S rho v s).tau
        (Protocol.support_cutoff S.E s) u = true := by
      rw [confEarly, beforeCutoff, Finset.mem_filter] at hearly
      exact hearly.2
    have hHstamp : stampedBefore
        (Proofs.Optimistic.confStore S rho v s).timestamp_block
        (Protocol.support_cutoff S.E s) H = true :=
      HonestWeightMajority.stampedBefore_block_of_resolution hfind hresolved
    have hHread : H ∈
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E s) v).st.core.T := by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Run.storeBeforeTime] using hHsource
    obtain ⟨C, hCread, hCErase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
        (Protocol.confirmation_time S.E s) v hHread
    have hCstampRead : stampedBefore
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E s) v).st.core.timestamp_block
        (Protocol.support_cutoff S.E s) C.erase = true := by
      have hHstampRead : stampedBefore
          (NamedRun.stateBeforeTime S rho
            (Protocol.confirmation_time S.E s) v).st.core.timestamp_block
          (Protocol.support_cutoff S.E s) H = true := by
        simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
          Run.storeBeforeTime] using hHstamp
      simpa only [hCErase] using hHstampRead
    have hCreadTime : C ∈
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E s) v).st.bodies := by
      simpa only [Run.storeBeforeTime] using hCread
    have hCsupport :=
      NamedPublicCutBody.body_mem_stateBeforeTime_of_public_stampedBefore S rho
        adm.toNamedScheduleWellFormed (publicTime_support_cutoff S s)
        hCreadTime hCstampRead
    obtain ⟨n, hn, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      adm.toNamedScheduleWellFormed.sorted (Protocol.support_cutoff S.E s)
    have hCsupportN : C ∈ (NamedRun.stateBefore S rho n v).st.bodies := by
      rw [← hn]
      exact hCsupport
    obtain hgenC | ⟨i, hi, t, hacc⟩ :=
      NamedOutageProvenance.held_block_origin S rho n v hCsupportN
    · exact False.elim (hgen (by rw [← hCErase, hgenC]; rfl))
    · obtain ⟨-, e, he, -, htime⟩ := hacc.1
      have htSupport : t < Protocol.support_cutoff S.E s := by
        simpa only [htime] using hbefore i e hi he
      have hCpos : 0 < C.slot := by
        rw [← Proofs.NamedWire.erase_slot C]
        exact Nat.zero_lt_of_lt
          (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
      have hBH' : Block.Preceq B C.erase := by
        simpa only [hCErase] using hBH
      have hrootC : Block.Preceq
          (Protocol.get_fg_root
            (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) C.erase :=
        Block.preceq_trans hroot hBH'
      have hpostSupport : S.E.t_GST ≤ Protocol.support_cutoff S.E s := by
        apply le_trans hpost
        unfold Protocol.proposal_time Protocol.support_cutoff
        exact le_add_of_nonneg_right
          (Int.mul_nonneg (by norm_num) (le_of_lt S.E.Δ_pos))
      have hfreezeHor : Protocol.view_freeze S.E s ≤ rho.horizon := by
        apply le_trans _ hhor
        exact le_of_lt (view_freeze_lt_confirmation_time S.E s)
      have hadmitC := weakct_admittedBefore_of_accepted_after_support
        S adm hv hw hCpos hacc htSupport hpostSupport hfreezeHor hrootC
      have hvisibleC := Protocol.admittedBefore_mem_and_stamp_at
        S adm.toNamedScheduleWellFormed hadmitC
          (le_of_lt (view_freeze_lt_vote_time_succ S.E s))
      have hmem : H ∈ (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T := by
        simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, hCErase] using hvisibleC.1
      refine ⟨find_voteDutyStore_of_source_find_and_mem
        S adm hw hfind hmem, ?_⟩
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, hCErase] using hvisibleC.2
    /-
    · have htSupport: t < Protocol.support_cutoff S.E s:=
        acceptsAt_block_lt_of_stamp_before
          S adm hv hacc (Nat.succ_le_of_lt hin)
            (publicTime_support_cutoff S s) hstampn
      have hHpos: 0 < H.slot:=
        Nat.zero_lt_of_lt (parent_slot_lt_of_acceptsAt_block S hacc)
      have hfreezeHor: Protocol.view_freeze S.E s ≤ rho.horizon:= by
        apply le_trans _ hhor
        exact le_of_lt (lt_trans
          (Int.lt_add_of_pos_right _ S.E.Δ_pos)
          (view_freeze_add_delta_lt_confirmation_time S.E s))
      have hpostCut: S.E.t_GST ≤ Protocol.support_cutoff S.E s:= by
        apply le_trans hpost
        unfold Protocol.proposal_time Protocol.support_cutoff
        exact le_add_of_nonneg_right
          (Int.mul_nonneg (by norm_num) (le_of_lt S.E.Δ_pos))
      have hadmit: AdmittedBefore S rho w H
          (Protocol.view_freeze S.E s):= by
        apply retired weak block-admission producer
          S adm hv hw hHpos hacc htSupport hpostCut
            (support_cutoff_add_delta_eq_view_freeze S.E s) hfreezeHor
        intro j t' hj _ hlt
        exact Block.preceq_trans
          (finalized_preceq_at_delivery_of_voteDutyRoot_preceq
            S adm hroot hj hlt) hBH
      have hvisible:= admittedBefore_mem_and_stamp_at S
        adm.toNamedScheduleWellFormed hadmit
          (le_of_lt (view_freeze_lt_vote_time_succ S.E s))
      have hmem: H ∈ (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T:= by
        simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore] using hvisible.1
      refine ⟨find_voteDutyStore_of_source_find_and_mem
        S adm hw hfind hmem, ?_⟩
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hvisible.2
    -/

theorem adoptionTransport_B_after_gst
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B) :
    AdoptionTransport
      (Proofs.Optimistic.confStore S rho v s).T
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T
      (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
      (Protocol.voter_view S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1))
      (Protocol.voter_support_view S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1)) B := by
  refine ⟨?_, targetRawVote_settledAtSource_after_gst
    S adm hv hw hpost hhor⟩
  intro u hu htargets
  obtain ⟨H, hfind, hslot, hBH⟩ := targets_under_iff.mp htargets
  obtain ⟨i, t, hacc, hus, hlo, hhi⟩ :=
    confirmationVotesAcceptedInWindow_of_admissible S adm hv s u hu
  have hfreezeHor : Protocol.view_freeze S.E s ≤ rho.horizon := by
    apply le_trans _ hhor
    exact le_of_lt (lt_trans
      (Int.lt_add_of_pos_right _ S.E.Δ_pos)
      (view_freeze_add_delta_lt_confirmation_time S.E s))
  have hsettled := accepted_gfVote_forward_settled_at_voteDuty_after_gst
    S adm hv hw hpost hacc hus hlo hhi hfreezeHor
  have hvisible := supportingTarget_visibleAtVoteDuty_after_gst
    S adm hv hw hpost hhor hroot hu hfind hBH
  rcases settled_before_freeze_in_voter_pair S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)) s
      hvisible.1 hvisible.2 hslot hsettled with hsupport | hequiv
  · exact Or.inl ⟨hsupport,
      targets_under_iff.mpr ⟨H, hvisible.1, hslot, hBH⟩⟩
  · exact Or.inr hequiv

omit [Fintype V] in
private theorem weakct_strict_filter_len_mono (rho : NamedRun V)
    {t t' : Time} (h : t ≤ t') :
    (rho.events.filter (fun e => decide (e.time < t))).length ≤
      (rho.events.filter (fun e => decide (e.time < t'))).length := by
  have hfun :
      (fun a : NamedEvent V => decide (a.time < t) && decide (a.time < t')) =
        fun a => decide (a.time < t) := by
    funext a
    by_cases hlt : a.time < t
    · simp only [hlt, decide_true, Bool.true_and, decide_eq_true_eq]
      exact hlt.trans_le h
    · simp only [hlt, decide_false, Bool.false_and]
  have hre : (rho.events.filter (fun e => decide (e.time < t'))).filter
      (fun e => decide (e.time < t)) =
        rho.events.filter (fun e => decide (e.time < t)) := by
    simp only [List.filter_filter, hfun]
  calc
    (rho.events.filter (fun e => decide (e.time < t))).length =
        ((rho.events.filter (fun e => decide (e.time < t'))).filter
          (fun e => decide (e.time < t))).length := by rw [hre]
    _ ≤ (rho.events.filter (fun e => decide (e.time < t'))).length :=
      List.length_filter_le _ _

private theorem weakct_stateBeforeTime_eq_take (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (t : Time) :
    NamedRun.stateBeforeTime S rho t = NamedRun.stateBefore S rho
      (rho.events.filter (fun e => decide (e.time < t))).length := by
  have hdown : ∀ e f : NamedEvent V, NamedEvent.key e ≤ NamedEvent.key f →
      decide (f.time < t) = true → decide (e.time < t) = true := by
    intro e f hk hf
    simp only [decide_eq_true_eq] at hf ⊢
    exact lt_of_le_of_lt (Proofs.Bridges.time_le_of_key_le hk) hf
  have hfilter := Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdown _ sch.sorted
  have hprefix : rho.events.filter (fun e => decide (e.time < t)) <+:
      rho.events := by
    rw [hfilter]
    exact List.takeWhile_prefix _
  have htake := List.prefix_iff_eq_take.mp hprefix
  unfold NamedRun.stateBeforeTime NamedRun.stateBefore
  exact congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init) htake


/-! ## Delivery-parametric confirmation transport -/

private theorem gfVote_processes_settled_at_voteDuty_without_gst
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest)
    {u : GoldfishVote V} {s : Slot} {t : Time} {j : Nat}
    (hproc : NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.view_freeze S.E s)
    (hhor : Protocol.view_freeze S.E s ≤ rho.horizon) :
    u ∈ beforeCutoff
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_vote
          (Protocol.view_freeze S.E s)
          ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) ∨
      Protocol.equivocates
        (beforeCutoff
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_vote
          (Protocol.view_freeze S.E s)
          ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s))
        u.val_index = true := by
  obtain ⟨i, e, hi, het, hlocal⟩ :=
    weakct_actual_gfVote_settled_before_deadline S adm hproc hus hw hlo hhi hhi
  let readTime := Protocol.vote_time S.E (s + 1)
  let N := (rho.events.filter (fun x => decide (x.time < readTime))).length
  have hiN : i < N := by
    by_contra hnot
    have hNle : N ≤ i := Nat.le_of_not_gt hnot
    have hreadE : readTime ≤ e.time :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        (t := readTime) (j := i) (e := e) (by simpa [N] using hNle) hi
    exact (not_le_of_gt
      (lt_trans het (view_freeze_lt_vote_time_succ S.E s))) hreadE
  have hcarry : PoolCarry (NamedRun.stateBefore S rho (i + 1) w).st.core
      (NamedRun.stateBefore S rho N w).st.core :=
    pool_carry S adm.toNamedScheduleWellFormed w N (Nat.succ_le_of_lt hiN)
  have hstore : Proofs.Optimistic.voteDutyStore S rho w (s + 1) =
      Proofs.Optimistic.voteStore S (NamedRun.stateBefore S rho N w).st.core (s + 1) := by
    unfold Proofs.Optimistic.voteDutyStore Run.storeBeforeTime
    rw [congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed readTime) w)]
  rw [hus] at hlocal
  rcases hlocal with hmem | hequiv
  · apply Or.inl
    rw [hstore]
    simpa only [Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      beforeCutoff_subset_of_poolCarry hcarry s
        (Protocol.view_freeze S.E s) hmem
  · apply Or.inr
    apply equivocates_mono _ u.val_index hequiv
    intro x hx
    rw [hstore]
    simpa only [Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      beforeCutoff_subset_of_poolCarry hcarry s
        (Protocol.view_freeze S.E s) hx

private theorem accepted_gfVote_forward_settled_at_voteDuty_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {u : GoldfishVote V} {s : Slot} {t : Time}
    (hcap : Protocol.view_freeze S.E s ≤ cap)
    (hacc : NamedRun.acceptsAt S rho i v (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.support_cutoff S.E s)
    (hhor : Protocol.view_freeze S.E s ≤ rho.horizon) :
    u ∈ beforeCutoff
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_vote
          (Protocol.view_freeze S.E s)
          ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) ∨
      Protocol.equivocates
        (beforeCutoff
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_vote
          (Protocol.view_freeze S.E s)
          ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s))
        u.val_index = true := by
  by_cases halready : Object.processed
      (rho.stateBefore S (i + 1) w).st (Object.gfVote u) = true
  · obtain ⟨e, he, -, het⟩ := hacc.1.2
    apply Or.inl
    apply gfVote_processed_after_event_at_voteDuty S adm he hus halready
    simpa only [het] using
      lt_trans hhi (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s)
  · have hunaccepted : Object.processed
        (rho.stateBefore S (i + 1) w).st (Object.gfVote u) = false :=
      Bool.eq_false_of_not_eq_true halready
    have hrelayCap : t + S.E.Δ ≤ cap := by
      apply (le_of_lt ?_).trans hcap
      calc
        t + S.E.Δ < Protocol.support_cutoff S.E s + S.E.Δ :=
          Int.add_lt_add_right hhi S.E.Δ
        _ = Protocol.view_freeze S.E s :=
          support_cutoff_add_delta_eq_view_freeze S.E s
    obtain ⟨t', hcausal, hdeadline, j', hproc⟩ :=
      hdelivery.relay_gf_vote v hv i u t hacc w hw
        hunaccepted hrelayCap rfl
    have hbeforeFreeze : t' < Protocol.view_freeze S.E s := by
      exact lt_trans hdeadline (by
        calc
          t + S.E.Δ < Protocol.support_cutoff S.E s + S.E.Δ :=
            Int.add_lt_add_right hhi S.E.Δ
          _ = Protocol.view_freeze S.E s :=
            support_cutoff_add_delta_eq_view_freeze S.E s)
    exact gfVote_processes_settled_at_voteDuty_without_gst
      S adm hw hproc hus (le_trans hlo hcausal) hbeforeFreeze hhor

private theorem weakct_actual_gfVote_settled_at_confStore_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {j : Nat} {w : V} {u : GoldfishVote V} {s : Slot} {t : Time}
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    (hactual : NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t)
    (hus : u.slot = s) (hw : w ∈ rho.honest)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.confirmation_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    u ∈ confLate S.E (Proofs.Optimistic.confStore S rho w s) s ∨
      Protocol.equivocates
        (confLate S.E (Proofs.Optimistic.confStore S rho w s) s)
        u.val_index = true := by
  let Gamma := Protocol.confirmation_time S.E s
  have carry_to_conf :
      ∀ (i : Nat) (e : Event V),
        rho.events[i]? = some e → e.time < Gamma →
        (u ∈ beforeCutoff
            (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote Gamma
            ((NamedRun.stateBefore S rho (i + 1) w).st.pool u.slot) ∨
          Protocol.equivocates
            (beforeCutoff
              (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote Gamma
              ((NamedRun.stateBefore S rho (i + 1) w).st.pool u.slot))
            u.val_index = true) →
        u ∈ confLate S.E (Proofs.Optimistic.confStore S rho w s) s ∨
          Protocol.equivocates
            (confLate S.E (Proofs.Optimistic.confStore S rho w s) s)
            u.val_index = true := by
    intro i e hi hetime hlocal
    let N := (rho.events.filter (fun x => decide (x.time < Gamma))).length
    have hiN : i < N := by
      by_contra hnot
      have hNle : N ≤ i := Nat.le_of_not_gt hnot
      have hGammae : Gamma ≤ e.time :=
        Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
          (t := Gamma) (j := i) (e := e)
          (by simpa [N] using hNle) hi
      exact (not_le_of_gt hetime) hGammae
    have hcarry : PoolCarry
        (NamedRun.stateBefore S rho (i + 1) w).st.core
        (NamedRun.stateBefore S rho N w).st.core :=
      pool_carry S adm.toNamedScheduleWellFormed w N
        (Nat.succ_le_of_lt hiN)
    have hstore : Proofs.Optimistic.confStore S rho w s =
        Proofs.Optimistic.tickStore S (NamedRun.stateBefore S rho N w).st.core Gamma := by
      unfold Proofs.Optimistic.confStore Run.storeBeforeTime
      rw [congrArg NamedNodeState.st
        (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take
          S adm.toNamedScheduleWellFormed Gamma) w)]
    rw [hus] at hlocal
    rcases hlocal with hmem | hequiv
    · apply Or.inl
      rw [confLate, hstore, Proofs.Optimistic.tickStore]
      exact beforeCutoff_subset_of_poolCarry hcarry s Gamma hmem
    · apply Or.inr
      apply equivocates_mono _ u.val_index hequiv
      intro x hx
      rw [confLate, hstore, Proofs.Optimistic.tickStore]
      exact beforeCutoff_subset_of_poolCarry hcarry s Gamma hx
  by_cases hfreeze : t < Protocol.view_freeze S.E s
  · obtain ⟨i, e, hi, hetime, hlocal⟩ :=
      weakct_actual_gfVote_settled_before_deadline S adm hactual hus hw hlo
        hfreeze hhi
    exact carry_to_conf i e hi hetime hlocal
  · obtain ⟨hindex, e, he, hnode, htime⟩ := hactual
    simp only [NamedRun.actualHandlesAtIndex, NamedRun.processesAtIndex] at hindex
    rcases hindex with (⟨t', htick, hem⟩ | ⟨t', hdeliver⟩) |
        ⟨B, j', before, hcall⟩
    · have heq : Event.tick w t' = e := Option.some.inj (htick.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      have hemit : NamedRun.emits S rho w (Object.gfVote u) t :=
        ⟨j, htick, hem⟩
      obtain ⟨hs', ht', -, hus'⟩ := Proofs.Optimistic.emits_gfVote_shape S hemit
      have hslot : S.E.slotOf t = s := by rw [← hus', hus]
      have htVote : t = Protocol.vote_time S.E s := by
        simpa only [hslot] using ht'
      have hemitVote : NamedRun.emits S rho w (Object.gfVote u)
          (Protocol.vote_time S.E s) := by
        simpa only [htVote] using hemit
      have hsupport : Protocol.support_cutoff S.E s ≤
          Protocol.confirmation_time S.E s :=
        support_cutoff_le_confirmation_time S.E s
      have hrecv := gfVote_in_cutoff_view_of_delivery
        S adm hdelivery hw (by simpa only [hslot] using hs') hemitVote hus hw
        (Protocol.confirmation_time S.E s)
        (Protocol.confirmation_time S.E s)
        hsupport hsupport (le_trans hsupport hcap)
      apply Or.inl
      simpa only [confLate, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Protocol.NamedStore.pool, Protocol.Store.pool] using hrecv
    · have heq : Event.deliver w (Object.gfVote u) t' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      exact gfVote_delivery_settled_at_confStore S adm hw hdeliver hus hlo hhi
    · obtain ⟨hblock, hnew, hcore, huindex⟩ := hcall
      have huB : u ∈ B.gf_votes := List.mem_of_getElem? huindex
      have huErase : u ∈ B.erase.gf_votes := by
        rwa [Proofs.NamedWire.erase_goldfish_votes]
      rcases hblock with
          ⟨t', hdeliver, hbefore⟩ | ⟨t', htick, hBemit, hbefore⟩
      · have heq : Event.deliver w (Object.block B) t' = e :=
          Option.some.inj (hdeliver.symm.trans he)
        have htt : t' = t := (congrArg Event.time heq).trans htime
        subst t'
        have hpreBodies : B ∉ before.bodies := by
          intro hB
          apply hnew
          have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j w).1.1.1
          have hB' : B ∈ (NamedRun.stateBefore S rho j w).st.bodies := by
            simpa [hbefore] using hB
          have hcoreB : B.erase ∈
              (NamedRun.stateBefore S rho j w).st.core.T := by
            rw [hcoh.1]
            exact Finset.mem_image_of_mem NamedBlock.erase hB'
          simpa [hbefore, Protocol.NamedStore.setClock] using hcoreB
        have hpostBodies := weakct_recovery_on_block_new_body S before B hnew hcore
        have hstamps : Protocol.PoolStamps before.core := by
          rw [hbefore]
          exact Protocol.poolStamps_stateBefore
            S adm.toNamedScheduleWellFormed w j
        have hslot : before.core.s = s ∨ before.core.s = s + 1 := by
          rw [hbefore]
          exact delivery_store_slot_before_confirmation S adm hw hdeliver hlo hhi
        have hfresh : ¬ u.slot < before.core.s - 1 := by
          rcases hslot with hs | hs
          · rw [hus, hs]
            exact Nat.not_lt.mpr (Nat.sub_le s 1)
          · rw [hus, hs, Nat.add_sub_cancel]
            exact Nat.lt_irrefl s
        have hfuture : ¬ before.core.s < u.slot := by
          rcases hslot with hs | hs
          · rw [hus, hs]
            exact Nat.lt_irrefl s
          · rw [hus, hs]
            exact Nat.not_lt.mpr (Nat.le_add_right s 1)
        have hcommittee : u.val_index ∈ S.E.committee u.slot := by
          have hwire := adm.wire _ w (Object.block B) t hdeliver
          simp only [Object.wellFormed, NamedReceipt.wellFormed,
            Bool.and_eq_true] at hwire
          have hcarried := hwire.2
          simp only [List.all_eq_true, decide_eq_true_eq] at hcarried
          exact hcarried u huErase
        have hclock : before.core.t < Gamma := by
          have hle : before.core.t ≤ t := by
            rw [hbefore]
            simpa [Event.time] using
              Protocol.store_time_le_event_time S
                adm.toNamedScheduleWellFormed hdeliver w
          exact lt_of_le_of_lt hle hhi
        have hlocal := Proofs.Optimistic.block_carried_before_deadline_or_equivocates
          S before B u Gamma hstamps hpreBodies hpostBodies huErase hcommittee
          hfresh hfuture hclock
        have hstate := Proofs.NamedReceiptCallsBase.delivery_result S rho hdeliver
        let final := Protocol.NamedAdmission.on_block_with
          .alsoCarried S.E S.hc S.cfg before B
        have hfinalEq : (NamedRun.stateBefore S rho (j + 1) w).st = final := by
          rw [hstate]
          simpa [final, hbefore, NamedReceipt.process]
        have hlocal' : u ∈ beforeCutoff
            (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote Gamma
            ((NamedRun.stateBefore S rho (j + 1) w).st.pool u.slot) ∨
            Protocol.equivocates
              (beforeCutoff
                (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote Gamma
                ((NamedRun.stateBefore S rho (j + 1) w).st.pool u.slot))
              u.val_index = true := by
          simpa only [final, hfinalEq] using hlocal
        exact carry_to_conf j e he (by simpa only [htime] using hhi) hlocal'
      · have heq : Event.tick w t' = e :=
          Option.some.inj (htick.symm.trans he)
        have htt : t' = t := (congrArg Event.time heq).trans htime
        subst t'
        have hproposal := congrArg Prod.snd
          (Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hBemit)
        have hshape := Proofs.HealingSurface.block_mem_on_tick_emit S w
          (NamedRun.stateBefore S rho j w) t hBemit
        have hguard := hshape.1
        have hgf0 : B.gf_votes =
            (NamedActionReads.confirmationReadFrom S
              (NamedRun.stateBefore S rho j w) t).st.core.gf_votes
              ((NamedActionReads.confirmationReadFrom S
                (NamedRun.stateBefore S rho j w) t).st.core.s - 1) := by
          unfold Protocol.NamedDuties.propose_block_with at hproposal
          split at hproposal
          · cases hproposal
          · rename_i B' hB'
            have hBB' : B' = B := Option.some.inj hproposal
            rw [← hBB']
            exact Proofs.Optimistic.proposal_with_gf_votes _ .poolAndCarried
              S.E S.hc (S.node w) _ hB'
        have hgf : B.gf_votes = before.core.gf_votes (before.core.s - 1) := by
          simpa [hbefore] using hgf0
        have hstamps : Protocol.PoolStamps before.core := by
          rw [hbefore]
          have hrawStamps := Protocol.poolStamps_stateBefore
            S adm.toNamedScheduleWellFormed w j
          have htle : (NamedRun.stateBefore S rho j w).st.core.t ≤ t := by
            simpa [Event.time] using
              Protocol.store_time_le_event_time S
                adm.toNamedScheduleWellFormed htick w
          exact (Protocol.poolStep_tickStore _ _ _ htle hrawStamps).2
        have huPool : u ∈ before.core.gf_votes (before.core.s - 1) := by
          rw [← hgf]
          exact List.mem_of_getElem? huindex
        have hslot : before.core.s = s + 1 := by
          have hslotTime : before.core.s = S.E.slotOf t := by
            rw [hbefore]
            rfl
          have hspos : 0 < before.core.s := by
            rw [hslotTime]
            exact hguard.1
          have hs' : s = before.core.s - 1 := by
            simpa only [hus] using hstamps.slot (before.core.s - 1) u huPool
          calc
            before.core.s = (before.core.s - 1) + 1 :=
              (Nat.sub_add_cancel (Nat.succ_le_of_lt hspos)).symm
            _ = s + 1 := by rw [← hs']
        have hcommittee : u.val_index ∈ S.E.committee u.slot := by
          have huPool' : u ∈
              (NamedRun.stateBefore S rho j w).st.core.gf_votes
                (before.core.s - 1) := by
            have hpoolEq : before.core.gf_votes =
                (NamedRun.stateBefore S rho j w).st.core.gf_votes := by
              rw [hbefore]
              rfl
            rw [← hpoolEq]
            exact huPool
          have hcommittee' := CommitteePools.stateBefore S rho w j
            (before.core.s - 1) u huPool'
          have hs' := hstamps.slot (before.core.s - 1) u huPool
          simpa only [hs'] using hcommittee'
        have hfresh : ¬ u.slot < before.core.s - 1 := by
          rw [hus, hslot, Nat.add_sub_cancel]
          exact Nat.lt_irrefl s
        have hfuture : ¬ before.core.s < u.slot := by
          rw [hslot, hus]
          exact Nat.not_lt.mpr (Nat.le_add_right s 1)
        have hclock : before.core.t < Gamma := by
          rw [hbefore]
          simpa [Event.time] using hhi
        have hpostBodies := weakct_recovery_on_block_new_body S before B hnew hcore
        have hpreBodies : B ∉ before.bodies := by
          intro hB
          apply hnew
          have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j w).1.1.1
          have hB' : B ∈ (NamedRun.stateBefore S rho j w).st.bodies := by
            simpa [hbefore] using hB
          have hcoreB : B.erase ∈
              (NamedRun.stateBefore S rho j w).st.core.T := by
            rw [hcoh.1]
            exact Finset.mem_image_of_mem NamedBlock.erase hB'
          simpa [hbefore, Protocol.NamedStore.setClock] using hcoreB
        have hlocal := Proofs.Optimistic.block_carried_before_deadline_or_equivocates
          S before B u Gamma hstamps hpreBodies hpostBodies huErase hcommittee
          hfresh hfuture hclock
        let pre := NamedRun.stateBefore S rho j w
        let gc := NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S pre t).cache
        have hfields := Proofs.Optimistic.tick_fields_from_proposal gc S (S.node w)
          pre.st pre.record t (by simpa only [S.node_val_index] using hguard)
        let final := Protocol.NamedAdmission.on_block_with
          .alsoCarried S.E S.hc S.cfg before B
        have hproposalStage :
            (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
              (S.node w) before).1 = final := by
          have hpair := congrArg Prod.fst
            (Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hBemit)
          simpa only [gc, pre, final, hbefore] using hpair
        have hstate : NamedRun.stateBefore S rho (j + 1) w =
            (NamedNode.tick S w pre t).1 := Proofs.NamedRuntime.stateBefore_tick S rho htick
        have hgcstep : (NamedNode.tick S w pre t).1.st =
            (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w)
              pre.st pre.record t).1 := rfl
        have hfinalFields :
            (NamedRun.stateBefore S rho (j + 1) w).st.core.gf_votes = final.core.gf_votes ∧
            (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote =
              final.core.timestamp_vote := by
          rw [hstate, hgcstep]
          have hguard' : 0 < S.E.slotOf t ∧
              t = Protocol.proposal_time S.E (S.E.slotOf t) ∧
              S.E.proposer (S.E.slotOf t) = (S.node w).val_index := by
            simpa only [S.node_val_index] using hguard
          dsimp only at hfields
          rw [if_pos hguard'] at hfields
          have hproposalStage' :
              (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
                (S.node w) (Protocol.NamedStore.setClock S.E pre.st t)).1 = final := by
            simpa only [pre, hbefore] using hproposalStage
          rw [hproposalStage'] at hfields
          exact hfields
        have hlocal' : u ∈ beforeCutoff
            (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote Gamma
            ((NamedRun.stateBefore S rho (j + 1) w).st.pool u.slot) ∨
            Protocol.equivocates
              (beforeCutoff
                (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote Gamma
                ((NamedRun.stateBefore S rho (j + 1) w).st.pool u.slot))
              u.val_index = true := by
          change u ∈ beforeCutoff
              (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote Gamma
              ((NamedRun.stateBefore S rho (j + 1) w).st.core.pool u.slot) ∨
            Protocol.equivocates
              (beforeCutoff
                (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote Gamma
                ((NamedRun.stateBefore S rho (j + 1) w).st.core.pool u.slot))
              u.val_index = true
          simp only [Protocol.NamedStore.pool, Protocol.Store.pool]
          rw [hfinalFields.1, hfinalFields.2]
          simpa only [final] using hlocal
        exact carry_to_conf j e he (by simpa only [htime] using hhi) hlocal'

private theorem gfVote_processes_settled_at_confStore_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {w : V} (hw : w ∈ rho.honest)
    {u : GoldfishVote V} {s : Slot} {t : Time}
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    {j : Nat}
    (hproc : NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.confirmation_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    u ∈ confLate S.E (Proofs.Optimistic.confStore S rho w s) s ∨
      Protocol.equivocates
        (confLate S.E (Proofs.Optimistic.confStore S rho w s) s)
        u.val_index = true := by
  exact weakct_actual_gfVote_settled_at_confStore_of_delivery S adm hdelivery hcap hproc hus hw hlo hhi hhor

private theorem accepted_gfVote_backward_settled_at_confStore_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {u : GoldfishVote V} {s : Slot} {t : Time}
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    (hacc : NamedRun.acceptsAt S rho i w (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.vote_time S.E (s + 1))
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    u ∈ confLate S.E (Proofs.Optimistic.confStore S rho v s) s ∨
      Protocol.equivocates
        (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
        u.val_index = true := by
  by_cases halready : Object.processed
      (NamedRun.stateBefore S rho (i + 1) v).st (Object.gfVote u) = true
  · obtain ⟨e, he, -, het⟩ := hacc.1.2
    have hmem : u ∈ (NamedRun.stateBefore S rho (i + 1) v).st.gf_votes s := by
      simp only [Object.processed, NamedReceipt.processed, decide_eq_true_eq,
        Protocol.NamedStore.pool, Protocol.Store.pool, List.mem_toFinset] at halready
      rwa [hus] at halready
    have hstamps := Protocol.poolStamps_stateBefore
      S adm.toNamedScheduleWellFormed v (i + 1)
    obtain ⟨c, hc⟩ : ∃ c : Stamp,
        (NamedRun.stateBefore S rho (i + 1) v).st.timestamp_vote u = some c :=
      Option.isSome_iff_exists.mp (hstamps.stamped s u hmem)
    have hclock : (NamedRun.stateBefore S rho (i + 1) v).st.t ≤ e.time :=
      Protocol.block_store_time_after_event_le
        S adm.toNamedScheduleWellFormed he v
    have hvoteConf : Protocol.vote_time S.E (s + 1) <
        Protocol.confirmation_time S.E s := by
      rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos
    have hcConf : c < (Protocol.confirmation_time S.E s : Stamp) :=
      lt_of_le_of_lt (hstamps.bounded u c hc)
        (WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hclock (by
          simpa only [het] using lt_trans hhi hvoteConf)))
    let Gamma := Protocol.confirmation_time S.E s
    let N := (rho.events.filter (fun x => decide (x.time < Gamma))).length
    have hiN : i < N := by
      by_contra hnot
      have hNle : N ≤ i := Nat.le_of_not_gt hnot
      have hGammae : Gamma ≤ e.time :=
        Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed (t := Gamma)
          (j := i) (e := e) (by simpa only [N] using hNle) he
      rw [het] at hGammae
      exact (not_le_of_gt (lt_trans hhi hvoteConf)) hGammae
    have hcarry : PoolCarry
        (NamedRun.stateBefore S rho (i + 1) v).st.core
        (NamedRun.stateBefore S rho N v).st.core :=
      pool_carry S adm.toNamedScheduleWellFormed v N (Nat.succ_le_of_lt hiN)
    have hstore : Proofs.Optimistic.confStore S rho v s =
        Proofs.Optimistic.tickStore S (NamedRun.stateBefore S rho N v).st.core Gamma := by
      unfold Proofs.Optimistic.confStore Run.storeBeforeTime
      rw [congrArg NamedNodeState.st
        (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take
          S adm.toNamedScheduleWellFormed Gamma) v)]
    apply Or.inl
    rw [confLate, hstore, beforeCutoff, Finset.mem_filter, Protocol.Store.pool,
      List.mem_toFinset]
    refine ⟨hcarry.mem s u hmem, ?_⟩
    simp only [Proofs.Optimistic.tickStore, stampedBefore, hcarry.stamp u c hc,
      decide_eq_true_eq]
    exact hcConf
  · have hunaccepted : Object.processed
        (NamedRun.stateBefore S rho (i + 1) v).st (Object.gfVote u) = false :=
      Bool.eq_false_of_not_eq_true halready
    have hrelayCap : t + S.E.Δ ≤ cap := by
      apply (le_of_lt ?_).trans hcap
      rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
      exact Int.add_lt_add_right hhi S.E.Δ
    obtain ⟨t', hcausal, hdeadline, j', hproc⟩ :=
      hdelivery.relay_gf_vote w hw i u t hacc v hv
        hunaccepted hrelayCap rfl
    have hbeforeConf : t' < Protocol.confirmation_time S.E s :=
      lt_trans hdeadline (by
        rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
        exact Int.add_lt_add_right hhi S.E.Δ)
    exact gfVote_processes_settled_at_confStore_of_delivery
      S adm hdelivery hv hcap hproc hus (le_trans hlo hcausal) hbeforeConf hhor

private theorem targetPoolVote_settledAtSource_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {s : Slot}
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {u : GoldfishVote V}
    (hu : u ∈ (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) :
    u ∈ confLate S.E (Proofs.Optimistic.confStore S rho v s) s ∨
      Protocol.equivocates
        (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
        u.val_index = true := by
  obtain ⟨i, t, hacc, hus, hlo, hhi⟩ :=
    targetPoolVoteAcceptedBeforeVote S adm hu
  exact accepted_gfVote_backward_settled_at_confStore_of_delivery
    S adm hdelivery hv hw hcap hacc hus hlo hhi hhor

private theorem targetPoolEquivocates_settledAtSource_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {s : Slot}
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) {x : V}
    (hequiv : Protocol.equivocates
      ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) x = true) :
    Protocol.equivocates
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s) x = true := by
  by_cases hsource : Protocol.equivocates
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s) x = true
  · exact hsource
  rw [Protocol.equivocates, decide_eq_true_eq] at hequiv ⊢
  have hsub :
      Protocol.votes_by
          ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) x ⊆
        Protocol.votes_by
          (confLate S.E (Proofs.Optimistic.confStore S rho v s) s) x := by
    intro u hu
    rw [Protocol.votes_by, Finset.mem_filter] at hu ⊢
    refine ⟨?_, hu.2⟩
    rcases targetPoolVote_settledAtSource_of_delivery
        S adm hdelivery hv hw hcap hhor hu.1 with hmem | hequivSource
    · exact hmem
    · rw [hu.2] at hequivSource
      exact False.elim (hsource hequivSource)
  exact le_trans hequiv (Finset.card_le_card hsub)

private theorem targetRawVote_settledAtSource_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {s : Slot}
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    ∀ u ∈ Protocol.voter_view S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1),
      u ∈ confLate S.E (Proofs.Optimistic.confStore S rho v s) s ∨
        Protocol.equivocates
          (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
          u.val_index = true := by
  intro u hu
  rw [Protocol.voter_view, Finset.mem_union] at hu
  rcases hu with hreceipt | hcarried
  · rw [Nat.add_sub_cancel] at hreceipt
    obtain ⟨i, t, hacc, hus, hlo, hhi⟩ :=
      targetReceiptVotesAcceptedInWindow_of_admissible S adm hw s u hreceipt
    exact accepted_gfVote_backward_settled_at_confStore_of_delivery
      S adm hdelivery hv hw hcap hacc hus hlo
        (lt_trans hhi (view_freeze_lt_vote_time_succ S.E s)) hhor
  · rw [Finset.mem_biUnion] at hcarried
    obtain ⟨B, hB, huB⟩ := hcarried
    rw [Finset.mem_filter] at hB huB
    have hus : u.slot = s := by
      simpa only [Nat.add_sub_cancel] using huB.2
    have huList : u ∈ B.gf_votes := List.mem_toFinset.mp huB.1
    rcases targetCarrierVote_settledInPool
        S adm hw hB.1 hB.2 huList hus with hpool | hequiv
    · exact targetPoolVote_settledAtSource_of_delivery
        S adm hdelivery hv hw hcap hhor hpool
    · exact Or.inr
        (targetPoolEquivocates_settledAtSource_of_delivery
          S adm hdelivery hv hw hcap hhor hequiv)

private theorem weakct_admittedBefore_of_accepted_after_support_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {B : NamedBlock V} {t : Time} {s : Slot}
    (hBpos : 0 < B.slot)
    (hacc : NamedRun.acceptsAt S rho i p (Object.block B) t)
    (htSupport : t < Protocol.support_cutoff S.E s)
    (hcap : Protocol.view_freeze S.E s ≤ cap)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B.erase) :
    AdmittedBefore S rho w B.erase (Protocol.view_freeze S.E s) := by
  have hsupportFreeze : Protocol.support_cutoff S.E s <
      Protocol.view_freeze S.E s :=
    Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s
  have hacceptCutoff : t < Protocol.view_freeze S.E s :=
    lt_trans htSupport hsupportFreeze
  have hrelayCutoff : t + S.E.Δ ≤
      Protocol.view_freeze S.E s := by
    calc
      t + S.E.Δ ≤ Protocol.support_cutoff S.E s + S.E.Δ :=
        Int.add_le_add_right (le_of_lt htSupport) S.E.Δ
      _ = Protocol.view_freeze S.E s :=
        support_cutoff_add_delta_eq_view_freeze S.E s
  have hrelayCap : t + S.E.Δ ≤ cap :=
    hrelayCutoff.trans hcap
  by_cases halready : NamedReceipt.processed
      (NamedRun.stateBefore S rho (i + 1) w).st (Object.block B) = true
  · rcases acceptsAt_block_of_processed S rho w (i + 1) B halready with
      hgen | ⟨j, hj, t', hacc'⟩
    · have hzero : B.slot = 0 := by rw [hgen]; rfl
      exact False.elim ((Nat.ne_of_gt hBpos) hzero)
    · obtain ⟨-, e', he', -, ht'⟩ := hacc'.1
      obtain ⟨-, e, he, -, ht⟩ := hacc.1
      have ht'le : t' ≤ t := by
        rw [← ht', ← ht]
        have hji : j ≤ i := Nat.le_of_lt_succ hj
        rcases hji.lt_or_eq with hlt | rfl
        · exact Proofs.Bridges.time_le_of_key_le
            (Proofs.Optimistic.key_le_of_index_lt S adm.toNamedScheduleWellFormed
              hlt he' he)
        · have heq : e' = e := Option.some.inj (he'.symm.trans he)
          rw [heq]
      exact ⟨B, rfl, j, t', hacc', lt_of_le_of_lt ht'le hacceptCutoff⟩
  · have halreadyFalse : NamedReceipt.processed
        (NamedRun.stateBefore S rho (i + 1) w).st (Object.block B) = false :=
      Bool.eq_false_of_not_eq_true halready
    have hguard := not_excludes_of_F_preceq_later_time S rho
      adm.toNamedScheduleWellFormed.sorted
      (hrelayCutoff.trans (view_freeze_lt_vote_time_succ S.E s).le)
      (weakct_finalized_preceq_at_voteRead S rho hroot)
    obtain ⟨t', htt', ht'hi, j, hproc⟩ :=
      hdelivery.relay_block p hp i B t hacc w hw
        halreadyFalse hrelayCap hguard
    have ht'cutoff : t' < Protocol.view_freeze S.E s :=
      lt_of_lt_of_le ht'hi hrelayCutoff
    obtain ⟨e, he, -, heTime⟩ := hproc.2
    have hearly : e.time < Protocol.view_freeze S.E s := by
      simpa only [heTime] using ht'cutoff
    have hF : Block.Preceq
        (NamedRun.stateBefore S rho j w).st.core.F B.erase :=
      weakct_finalized_preceq_at_event S adm hroot
        (show rho.events[j]? = some e from he) hearly
    have hheld := NamedRelayGuards.handled_block_held_of_finalized_prefix
      S rho adm.toNamedScheduleWellFormed adm.toNamedDeliveryWellFormed
      adm.toNamedRootCollisionFree hacc hproc htt' hF
    by_cases hpreheld : B ∈ (NamedRun.stateBefore S rho j w).st.bodies
    · obtain hgen | ⟨k, hkj, ta, hacc'⟩ :=
        NamedOutageProvenance.held_block_origin S rho j w hpreheld
      · have hzero : B.slot = 0 := by rw [hgen]; rfl
        exact False.elim ((Nat.ne_of_gt hBpos) hzero)
      · obtain ⟨-, e', he', -, hta⟩ := hacc'.1
        have hta' : ta ≤ t' := by
          rw [← hta, ← heTime]
          have hkj' : k ≤ j := Nat.le_of_lt hkj
          rcases hkj'.lt_or_eq with hlt | rfl
          · exact Proofs.Bridges.time_le_of_key_le
              (Proofs.Optimistic.key_le_of_index_lt S adm.toNamedScheduleWellFormed
                hlt he' he)
          · have heq : e' = e := Option.some.inj (he'.symm.trans he)
            rw [heq]
        exact ⟨B, rfl, k, ta, hacc',
          lt_of_le_of_lt hta' ht'cutoff⟩
    · have hpreProcessed : NamedReceipt.processed
          (NamedRun.stateBefore S rho j w).st (Object.block B) = false := by
        simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hpreheld
      have hpostProcessed : NamedReceipt.processed
          (NamedRun.stateBefore S rho (j + 1) w).st (Object.block B) = true := by
        simpa only [NamedReceipt.processed, decide_eq_true_eq] using hheld
      have hacc' : NamedRun.acceptsAt S rho j w (Object.block B) t' :=
        ⟨hproc, hpreProcessed, hpostProcessed⟩
      exact ⟨B, rfl, j, t', hacc', ht'cutoff⟩

private theorem supportingTarget_visibleAtVoteDuty_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {s : Slot}
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B)
    {u : GoldfishVote V}
    (hu : u ∈ confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
    {H : Block V}
    (hfind : Block.find? (Proofs.Optimistic.confStore S rho v s).T u.head = some H)
    (hBH : Block.Preceq B H) :
    Block.find? (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T u.head = some H ∧
      stampedBefore
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_block
        (Protocol.view_freeze S.E s) H = true := by
  by_cases hgen : H = Block.genesis
  · subst H
    have hvisible := genesis_mem_and_stamp_storeBeforeTime S
      adm.toNamedScheduleWellFormed w (Protocol.vote_time S.E (s + 1))
      (Protocol.view_freeze S.E s)
    have hmem : Block.genesis ∈
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T := by
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hvisible.1
    refine ⟨find_voteDutyStore_of_source_find_and_mem
      S adm hw hfind hmem, ?_⟩
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hvisible.2
  · have hHsource : H ∈ (Proofs.Optimistic.confStore S rho v s).T :=
      Proofs.HealingLemmas.find?_mem hfind
    have hearly : u ∈ confEarly S.E (Proofs.Optimistic.confStore S rho v s) s :=
      (Finset.mem_filter.mp hu).1
    have hresolved : stampedBefore
        (Proofs.Optimistic.confStore S rho v s).tau
        (Protocol.support_cutoff S.E s) u = true := by
      rw [confEarly, beforeCutoff, Finset.mem_filter] at hearly
      exact hearly.2
    have hHstamp : stampedBefore
        (Proofs.Optimistic.confStore S rho v s).timestamp_block
        (Protocol.support_cutoff S.E s) H = true :=
      HonestWeightMajority.stampedBefore_block_of_resolution hfind hresolved
    have hHread : H ∈
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E s) v).st.core.T := by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Run.storeBeforeTime] using hHsource
    obtain ⟨C, hCread, hCErase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
        (Protocol.confirmation_time S.E s) v hHread
    have hCstampRead : stampedBefore
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E s) v).st.core.timestamp_block
        (Protocol.support_cutoff S.E s) C.erase = true := by
      have hHstampRead : stampedBefore
          (NamedRun.stateBeforeTime S rho
            (Protocol.confirmation_time S.E s) v).st.core.timestamp_block
          (Protocol.support_cutoff S.E s) H = true := by
        simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
          Run.storeBeforeTime] using hHstamp
      simpa only [hCErase] using hHstampRead
    have hCreadTime : C ∈
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E s) v).st.bodies := by
      simpa only [Run.storeBeforeTime] using hCread
    have hCsupport :=
      NamedPublicCutBody.body_mem_stateBeforeTime_of_public_stampedBefore S rho
        adm.toNamedScheduleWellFormed (publicTime_support_cutoff S s)
        hCreadTime hCstampRead
    obtain ⟨n, hn, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      adm.toNamedScheduleWellFormed.sorted (Protocol.support_cutoff S.E s)
    have hCsupportN : C ∈ (NamedRun.stateBefore S rho n v).st.bodies := by
      rw [← hn]
      exact hCsupport
    obtain hgenC | ⟨i, hi, t, hacc⟩ :=
      NamedOutageProvenance.held_block_origin S rho n v hCsupportN
    · exact False.elim (hgen (by rw [← hCErase, hgenC]; rfl))
    · obtain ⟨-, e, he, -, htime⟩ := hacc.1
      have htSupport : t < Protocol.support_cutoff S.E s := by
        simpa only [htime] using hbefore i e hi he
      have hCpos : 0 < C.slot := by
        rw [← Proofs.NamedWire.erase_slot C]
        exact Nat.zero_lt_of_lt
          (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
      have hBH' : Block.Preceq B C.erase := by
        simpa only [hCErase] using hBH
      have hrootC : Block.Preceq
          (Protocol.get_fg_root
            (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) C.erase :=
        Block.preceq_trans hroot hBH'
      have hfreezeCap : Protocol.view_freeze S.E s ≤ cap :=
        (view_freeze_lt_confirmation_time S.E s).le.trans hcap
      have hadmitC := weakct_admittedBefore_of_accepted_after_support_of_delivery
        S adm hdelivery hv hw hCpos hacc htSupport hfreezeCap hrootC
      have hvisibleC := Protocol.admittedBefore_mem_and_stamp_at
        S adm.toNamedScheduleWellFormed hadmitC
          (le_of_lt (view_freeze_lt_vote_time_succ S.E s))
      have hmem : H ∈ (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T := by
        simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, hCErase] using hvisibleC.1
      refine ⟨find_voteDutyStore_of_source_find_and_mem
        S adm hw hfind hmem, ?_⟩
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, hCErase] using hvisibleC.2

theorem adoptionTransport_B_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {s : Slot}
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B) :
    AdoptionTransport
      (Proofs.Optimistic.confStore S rho v s).T
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T
      (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
      (Protocol.voter_view S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1))
      (Protocol.voter_support_view S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1)) B := by
  refine ⟨?_, targetRawVote_settledAtSource_of_delivery
    S adm hdelivery hv hw hcap hhor⟩
  intro u hu htargets
  obtain ⟨H, hfind, hslot, hBH⟩ := targets_under_iff.mp htargets
  obtain ⟨i, t, hacc, hus, hlo, hhi⟩ :=
    confirmationVotesAcceptedInWindow_of_admissible S adm hv s u hu
  have hfreezeHor : Protocol.view_freeze S.E s ≤ rho.horizon := by
    apply le_trans _ hhor
    exact le_of_lt (lt_trans
      (Int.lt_add_of_pos_right _ S.E.Δ_pos)
      (view_freeze_add_delta_lt_confirmation_time S.E s))
  have hsettled := accepted_gfVote_forward_settled_at_voteDuty_of_delivery
    S adm hdelivery hv hw
      ((view_freeze_lt_confirmation_time S.E s).le.trans hcap)
      hacc hus hlo hhi hfreezeHor
  have hvisible := supportingTarget_visibleAtVoteDuty_of_delivery
    S adm hdelivery hv hw hcap hroot hu hfind hBH
  rcases settled_before_freeze_in_voter_pair S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)) s
      hvisible.1 hvisible.2 hslot hsettled with hsupport | hequiv
  · exact Or.inl ⟨hsupport,
      targets_under_iff.mpr ⟨H, hvisible.1, hslot, hBH⟩⟩
  · exact Or.inr hequiv

#print axioms adoptionTransport_B_of_delivery

theorem voterProcessedTarget_of_genuineConfirmation_of_delivery
    (S : Setup V) {rho : Run V} {contract : Protocol.GradeContract V}
    (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {s : Slot}
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : Block V}
    (hgenuine : GenuineConfirmation (contract := contract) S.E S.hc
      (Proofs.Optimistic.confStore S rho v s) s B)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B) :
    B ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
  have hN := confNumerator S.E (Proofs.Optimistic.confStore S rho v s) s
  have hpositive : 0 <
      (Protocol.goldfishSupporters S.E (Proofs.Optimistic.confStore S rho v s).T
        (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
        (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s) s B).card := by
    have heligible := hgenuine.eligible
    rw [hN.score_eq_supporters] at heligible
    by_contra hnot
    have hzero :
        (Protocol.goldfishSupporters S.E (Proofs.Optimistic.confStore S rho v s).T
          (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
          (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s) s B).card = 0 :=
      Nat.eq_zero_of_not_pos hnot
    rw [hzero] at heligible
    simp at heligible
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpositive
  rw [mem_supporters_iff] at hu
  obtain ⟨-, u, huBy, -, htargets⟩ := hu
  rw [Protocol.votes_by, Finset.mem_filter] at huBy
  obtain ⟨H, hfind, hBHeadSlot, hBH⟩ := targets_under_iff.mp htargets
  have hvisible := supportingTarget_visibleAtVoteDuty_of_delivery
    S adm hdelivery hv hw hcap hroot huBy.1 hfind hBH
  let duty := Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  have hslot : duty.toHealing.s = s + 1 := by
    simpa only [duty, Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
  have hHmem : H ∈ duty.T :=
    Proofs.HealingLemmas.find?_mem hvisible.1
  let readTime := Protocol.vote_time S.E (s + 1)
  have hHread : H ∈
      (NamedRun.stateBeforeTime S rho readTime w).st.core.T := by
    simpa only [duty, readTime, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hHmem
  obtain ⟨C, hCread, hCErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho readTime w hHread
  have hCstampRead : stampedBefore
      (NamedRun.stateBeforeTime S rho readTime w).st.core.timestamp_block
      (Protocol.view_freeze S.E s) C.erase = true := by
    have hHstampRead : stampedBefore
        (NamedRun.stateBeforeTime S rho readTime w).st.core.timestamp_block
        (Protocol.view_freeze S.E s) H = true := by
      simpa only [duty, readTime, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hvisible.2
    simpa only [hCErase] using hHstampRead
  have hCfreeze :=
    NamedPublicCutBody.body_mem_stateBeforeTime_of_public_stampedBefore S rho
      adm.toNamedScheduleWellFormed (publicTime_view_freeze S s)
      hCread hCstampRead
  have hcohFreeze := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
    (Protocol.view_freeze S.E s) w).1.1.1
  have hHfreeze : H ∈
      (NamedRun.stateBeforeTime S rho (Protocol.view_freeze S.E s) w).st.core.T := by
    rw [hcohFreeze.1]
    exact Finset.mem_image.mpr ⟨C, hCfreeze, hCErase⟩
  have hBfreeze : B ∈
      (NamedRun.stateBeforeTime S rho (Protocol.view_freeze S.E s) w).st.core.T :=
    Proofs.Records.mem_of_preceq
      ((parentClosed_iff _).mp
        (Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
          (Protocol.view_freeze S.E s) w)).2 B H hHfreeze hBH
  obtain ⟨D, hDfreeze, hDErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.view_freeze S.E s) w hBfreeze
  have hDstampFreeze := NamedBlockStamp.held_body_stampedBefore_stateBeforeTime
    S rho adm.toNamedScheduleWellFormed w (Protocol.view_freeze S.E s) D hDfreeze
  let nFreeze :=
    (rho.events.filter (fun e => decide (e.time < Protocol.view_freeze S.E s))).length
  let nRead := (rho.events.filter (fun e => decide (e.time < readTime))).length
  have hFreezeEq : NamedRun.stateBeforeTime S rho (Protocol.view_freeze S.E s) =
      NamedRun.stateBefore S rho nFreeze := by
    simpa only [nFreeze] using
      weakct_stateBeforeTime_eq_take S rho adm.toNamedScheduleWellFormed
        (Protocol.view_freeze S.E s)
  have hReadEq : NamedRun.stateBeforeTime S rho readTime =
      NamedRun.stateBefore S rho nRead := by
    simpa only [nRead] using
      weakct_stateBeforeTime_eq_take S rho adm.toNamedScheduleWellFormed readTime
  have htimeOrder : Protocol.view_freeze S.E s ≤ readTime :=
    le_of_lt (view_freeze_lt_vote_time_succ S.E s)
  have hlen : nFreeze ≤ nRead := by
    simpa only [nFreeze, nRead] using
      weakct_strict_filter_len_mono rho htimeOrder
  have hDfreezeN : D ∈ (NamedRun.stateBefore S rho nFreeze w).st.bodies := by
    rw [← hFreezeEq]
    exact hDfreeze
  have hDreadN : D ∈ (NamedRun.stateBefore S rho nRead w).st.bodies :=
    NamedBodyRetention.stateBefore_bodies_mono S rho w hlen hDfreezeN
  have hDread : D ∈
      (NamedRun.stateBeforeTime S rho readTime w).st.bodies := by
    rw [hReadEq]
    exact hDreadN
  have hDstampFreezeN : stampedBefore
      (NamedRun.stateBefore S rho nFreeze w).st.core.timestamp_block
      (Protocol.view_freeze S.E s) D.erase := by
    simpa only [hFreezeEq] using hDstampFreeze
  have hDstampReadN : stampedBefore
      (NamedRun.stateBefore S rho nRead w).st.core.timestamp_block
      (Protocol.view_freeze S.E s) D.erase := by
    have hstampCarry := NamedBlockStamp.stateBefore_body_stamp_mono S rho w
      hlen hDfreezeN
    rw [stampedBefore_eq_occurrenceBefore] at hDstampFreezeN ⊢
    rw [hstampCarry.2]
    exact hDstampFreezeN
  have hDstampRead : stampedBefore
      (NamedRun.stateBeforeTime S rho readTime w).st.core.timestamp_block
      (Protocol.view_freeze S.E s) D.erase = true := by
    simpa only [hReadEq] using hDstampReadN
  have hBread : B ∈
      (NamedRun.stateBeforeTime S rho readTime w).st.core.T := by
    have hcohRead := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho readTime w).1.1.1
    rw [hcohRead.1]
    exact Finset.mem_image.mpr ⟨D, hDread, hDErase⟩
  have hBstamp : stampedBefore
      (NamedRun.stateBeforeTime S rho readTime w).st.core.timestamp_block
      (Protocol.view_freeze S.E s) B = true := by
    simpa only [hDErase] using hDstampRead
  simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
  rw [hslot, Nat.add_sub_cancel]
  exact ⟨by
    simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime, Protocol.Store.toHealing] using
      hBread,
    Or.inl (by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, Protocol.Store.toHealing] using
        hBstamp)⟩

#print axioms voterProcessedTarget_of_genuineConfirmation_of_delivery


#print axioms weakct_actual_gfVote_settled_before_deadline
#print axioms gfVote_processes_settled_at_voteDuty_after_gst
#print axioms accepted_gfVote_forward_settled_at_voteDuty_after_gst
#print axioms weakct_actual_gfVote_settled_at_confStore_after_gst
#print axioms targetPoolVote_settledAtSource_after_gst
#print axioms targetPoolEquivocates_settledAtSource_after_gst
#print axioms targetRawVote_settledAtSource_after_gst
#print axioms supportingTarget_visibleAtVoteDuty_after_gst
#print axioms adoptionTransport_B_after_gst
#print axioms weakct_finalized_preceq_at_event
#print axioms weakct_admittedBefore_of_accepted_after_support
#print axioms weakct_strict_filter_len_mono
#print axioms weakct_stateBeforeTime_eq_take

end WeakGoldfish
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
