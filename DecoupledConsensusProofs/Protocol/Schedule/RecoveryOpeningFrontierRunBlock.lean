module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryProposalConfirmationRead
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionConfirmationCore
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationMembership
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.AdoptionRun
public import DecoupledConsensusProofs.Protocol.Handlers.AdoptionConstructor
public import DecoupledConsensusProofs.Protocol.Handlers.AcceptanceTiming
public import DecoupledConsensusProofs.Protocol.Handlers.CommitteePools
public import DecoupledConsensusProofs.Objects.PostGSTSync
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityMonotoneCore
public import DecoupledConsensusProofs.Protocol.Grades.Grades
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationBound

@[expose] public section

/-!
# Run provenance for the opening confirmation frontier

Historical earlier source: the erased frontier existential was not
portable as written. The first declaration available in `75f32a9`; the named
frontier theorem is implemented below. the prior route reads an erased
reachable store and then treats the post-action confirmation store as the
pre-action tree.

earlier-vs-selection statement diff after the required  restatement:

earlier: (hforms: GradeFormsAt S rho q P)
selection: (hforms: NamedGradeFormsAt S rho q P)

This is the only textual binder change. The named `attestStore_fields` theorem
is now available, but it does not prove the missing confirmation-time chain.

First compiler error (verbatim):

DecoupledConsensusProofs/HealingSurface/RecoveryOpeningFrontierRunBlockRun.lean:35:15:
error(lean.unknownIdentifier): Unknown identifier `Proofs.Bridges.depReachable_stateBeforeTime`

earlier route (verbatim): `Proofs.Bridges.depReachable_stateBeforeTime`, followed by
`Proofs.Records.justifiedInTree_depReachable`,
`Proofs.Optimistic.confirmedInTree_depReachable`,
`Proofs.Optimistic.confirmedInTree_attestStore`, and
`Proofs.Optimistic.attestStore_fields`.

The named replacement for direct tree membership is
`Proofs.NamedStoreBridge.liveConfirmed_mem_stateBeforeTime`. The named
`attestStore_fields` field-preservation theorem available in `ad817fc`. The
named common-frontier route and its action-read compatibility producers are
implemented below. the prior route was `depReachable_stateBeforeTime` →
`confirmedInTree_attestStore` → `Proofs.Optimistic.attestStore_fields` → the frontier
producer.

Exact earlier goals:

theorem openingActionLiveConfirmed_mem_storeBeforeTime
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (v: V) (r: Round):
    (actionStoreAt S rho v r).live_confirmed ∈
      (rho.storeBeforeTime S v (S.a r)).T

theorem exists_openingConfirmationFrontier_runBlock_of_gradeFormsAt_after_gst
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q: Round} {P: Block V}
    (hforms: NamedGradeFormsAt S rho q P)
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hhor: Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hnonempty: rho.honest.Nonempty):
    ∃ C: Block V,
      Block.Preceq P C ∧
        (∀ v ∈ rho.honest,
          Block.Preceq (actionStoreAt S rho v q).live_confirmed C) ∧
        RunBlock S rho C ∧
        (C = P ∨ ∃ v ∈ rho.honest,
          C = (actionStoreAt S rho v q).live_confirmed)

The second goal also needs a named action-read compatibility producer. The
available named candidate, root, and anchor results require
`FinalityFilterRetainedAtRead`; `NamedGradeFormsAt` alone only gives the
earlier G2-domain read. No producer in this cone supplies that retention or
the pairwise live-confirmation compatibility from the public hypotheses.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem recovery_admit_rows_bodies (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).bodies = st.bodies := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
      change (Protocol.NamedAdmission.admit_rows hc
        (Protocol.NamedAdmission.admit_row hc st row) rows).bodies = _
      rw [ih, Proofs.NamedAdmission.admit_row_bodies]

private theorem recovery_core_new_body (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hnew : B.erase ∉ st.core.T)
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

private theorem recovery_on_block_new_body (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hnew : B.erase ∉ st.core.T)
    (hpost : B.erase ∈
      (Execution.NamedReceiptCalls.postCore S st B).core.T) :
    B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies := by
  rw [show Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B =
      Protocol.NamedAdmission.admit_carried .alsoCarried S.hc st
        (Execution.NamedReceiptCalls.postCore S st B) B by rfl]
  unfold Protocol.NamedAdmission.admit_carried
  split_ifs
  · rw [recovery_admit_rows_bodies]
    exact recovery_core_new_body S st B hnew hpost
  · exact recovery_core_new_body S st B hnew hpost

/-! ## Actual Goldfish-vote handling -/

private theorem actual_gfVote_settled_before_deadline
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {j : Nat} {w : V} {u : GoldfishVote V} {s : Slot} {t Gamma : Time}
    (hactual : NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t)
    (hs : 0 < s) (hus : u.slot = s) (hval : u.val_index ∈ rho.honest)
    (hw : w ∈ rho.honest) (hlo : Protocol.vote_time S.E s ≤ t)
    (hcut : t < Protocol.support_cutoff S.E s) (hdeadline : t < Gamma) :
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
    obtain ⟨hs', ht', -, hus'⟩ := Proofs.Optimistic.emits_gfVote_shape S hemit
    have hslot : S.E.slotOf t = s := by rw [← hus', hus]
    have htVote : t = Protocol.vote_time S.E s := by
      simpa only [hslot] using ht'
    have hemitVote : NamedRun.emits S rho w (Object.gfVote u)
        (Protocol.vote_time S.E s) := by
      simpa only [htVote] using hemit
    obtain ⟨i, hi, hmem, c, hc, hle⟩ :=
      Proofs.Optimistic.mem_pool_of_emits S adm hs hemitVote hus hval
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
    have hcommittee : u.val_index ∈ S.E.committee u.slot := by
      have hwire := adm.wire j w (Object.gfVote u) t hdeliver
      simpa only [Object.wellFormed, NamedReceipt.wellFormed,
        Protocol.vote_well_formed, decide_eq_true_eq] using hwire
    have hslot : (NamedRun.stateBefore S rho j w).st.s = s :=
      Proofs.Optimistic.delivery_store_slot S adm hw hdeliver hlo hcut
    have hfresh : ¬ u.slot < (NamedRun.stateBefore S rho j w).st.s - 1 := by
      rw [hslot, hus]
      exact Nat.not_lt.mpr (Nat.sub_le s 1)
    have hfuture : ¬ (NamedRun.stateBefore S rho j w).st.s < u.slot := by
      rw [hslot, hus]
      exact Nat.lt_irrefl s
    have hequiv := Proofs.Optimistic.pool_no_honest_equivocation S adm w j u.slot hval
    have hequiv' : ¬ Protocol.equivocates
        ((NamedRun.stateBefore S rho j w).st.pool u.slot) u.val_index = true := by
      intro hbad
      rw [hequiv] at hbad
      simp at hbad
    have hstamps : Protocol.PoolStamps
        (NamedRun.stateBefore S rho j w).st.core :=
      Protocol.poolStamps_stateBefore S adm.toNamedScheduleWellFormed w j
    have hstep :
        (NamedRun.stateBefore S rho (j + 1) w).st.core =
          Protocol.on_goldfish_vote
            (NamedRun.stateBefore S rho j w).st.core u := by
      rw [Proofs.NamedRuntime.stateBefore_deliver S rho hdeliver]
      show Protocol.on_goldfish_vote_checked S.E _ u = _
      unfold Protocol.on_goldfish_vote_checked
      rw [if_neg (not_not.mpr hcommittee)]
    have hsettled :
        u ∈ (NamedRun.stateBefore S rho (j + 1) w).st.gf_votes u.slot ∧
          ∃ c : Stamp,
            (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote u = some c ∧
              c ≤ ((NamedRun.stateBefore S rho j w).st.t : Stamp) := by
      by_cases hdup : u ∈ (NamedRun.stateBefore S rho j w).st.gf_votes u.slot
      · obtain ⟨hmem, c, hc, hle⟩ := Protocol.mem_and_stamp_of_process
          (NamedRun.stateBefore S rho j w).st.core u hstamps hfresh hfuture hequiv
        refine ⟨?_, ?_⟩
        · show u ∈ (NamedRun.stateBefore S rho (j + 1) w).st.core.gf_votes u.slot
          rw [hstep]
          exact hmem
        · exact ⟨c, by
            change (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote u = some c
            rw [hstep]
            exact hc, hle⟩
      · obtain ⟨hmem, hc⟩ := Proofs.Optimistic.mem_pool_of_delivery S rho hdeliver
          hcommittee hfresh hfuture hdup hequiv'
        refine ⟨hmem, ?_⟩
        exact ⟨_, hc, le_refl _⟩
    have hprele : (NamedRun.stateBefore S rho j w).st.t ≤ t := by
      simpa [Event.time] using
        Protocol.store_time_le_event_time S adm.toNamedScheduleWellFormed
          hdeliver w
    refine ⟨j, _, hdeliver, ?_, ?_⟩
    · simpa only [Event.time] using hdeadline
    · rw [beforeCutoff, Finset.mem_filter]
      apply Or.inl
      refine ⟨?_, ?_⟩
      · simpa only [Protocol.NamedStore.pool, Protocol.Store.pool,
          List.mem_toFinset, hus] using hsettled.1
      · obtain ⟨c, hc, hle⟩ := hsettled.2
        rw [stampedBefore, hc]
        simpa only [decide_eq_true_eq] using lt_of_le_of_lt hle
          (WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hprele hdeadline))
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
      have hpostBodies := recovery_on_block_new_body S before B hnew hcore
      have hstamps : Protocol.PoolStamps before.core := by
        rw [hbefore]
        exact Protocol.poolStamps_stateBefore
          S adm.toNamedScheduleWellFormed w j
      have hclock0 : Protocol.vote_time S.E s ≤ before.core.t := by
        rw [hbefore]
        refine Protocol.tick_le_store_time S adm.toNamedScheduleWellFormed
          hdeliver ?_ hlo
        exact adm.tick_total w hw _ (Proofs.Optimistic.publicTime_vote_time S s)
          (Proofs.Optimistic.vote_time_nonneg S.E s)
          (le_trans hlo (adm.in_horizon _ (List.mem_of_getElem? hdeliver)).2)
      have hclockUp : before.core.t ≤ t := by
        rw [hbefore]
        simpa [Event.time] using
          Protocol.store_time_le_event_time S adm.toNamedScheduleWellFormed
            hdeliver w
      have hslot : before.core.s = s := by
        have hsc := Proofs.NamedStoreBridge.slotOfClock_stateBefore S rho j w
        unfold Proofs.Optimistic.SlotOfClock at hsc
        have hsc' : before.core.s = S.E.slotOf before.core.t := by
          simpa [hbefore] using hsc
        rw [hsc']
        exact Proofs.Optimistic.slotOf_of_between S.E s hclock0
          (lt_of_le_of_lt hclockUp hcut)
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
      have hlocal := Proofs.Optimistic.block_carried_before_deadline_or_equivocates
        S before B u Gamma hstamps hpreBodies hpostBodies huErase hcommittee
        hfresh hfuture (lt_of_le_of_lt hclockUp hdeadline)
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
      have hgf' : B.gf_votes = before.core.gf_votes (before.core.s - 1) := by
        simpa [hbefore] using hgf0
      have hslot : before.core.s = s := by
        have hslot' := Proofs.Optimistic.slotOf_of_between S.E s hlo hcut
        simpa [hbefore, Protocol.NamedStore.setClock] using hslot'
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
        rw [← hgf']
        exact List.mem_of_getElem? huindex
      have huslot := hstamps.slot (before.core.s - 1) u huPool
      have hbad : s = s - 1 := by simpa [hus, hslot] using huslot
      have hltNat : s - 1 < s := Nat.sub_lt (Nat.zero_lt_of_lt hs) (by decide)
      exact False.elim ((Nat.ne_of_lt hltNat) hbad.symm)

private theorem actual_gfVote_settled_before_view_freeze
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
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
      ⟨B, jrow, before, hcall⟩
  · have heq : Event.tick w t' = e := Option.some.inj (htick.symm.trans he)
    have htt : t' = t := (congrArg Event.time heq).trans htime
    subst t'
    have hemit : NamedRun.emits S rho w (Object.gfVote u) t :=
      ⟨j, htick, hem⟩
    obtain ⟨hs', ht', hval, hus'⟩ := Proofs.Optimistic.emits_gfVote_shape S hemit
    have hslot : S.E.slotOf t = s := by rw [← hus', hus]
    have htVote : t = Protocol.vote_time S.E s := by
      simpa only [hslot] using ht'
    have hcut : t < Protocol.support_cutoff S.E s := by
      rw [htVote]
      rw [← Proofs.Optimistic.vote_time_add_delta]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos
    have hactual' : NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t := by
      exact ⟨Or.inl (Or.inl ⟨t, htick, hem⟩), ⟨e, he, hnode, htime⟩⟩
    exact actual_gfVote_settled_before_deadline S adm
      (s := S.E.slotOf t) hactual' hs' hus'
      (by rw [hval]; exact hw) hw (le_of_eq ht'.symm)
      (by simpa only [hslot] using hcut) hdeadline
  · have heq : Event.deliver w (Object.gfVote u) t' = e :=
      Option.some.inj (hdeliver.symm.trans he)
    have htt : t' = t := (congrArg Event.time heq).trans htime
    subst t'
    have hslot : (NamedRun.stateBefore S rho j w).st.core.s = s := by
      show (NamedRun.stateBefore S rho j w).st.s = s
      exact Protocol.delivery_store_slot_before_freeze S adm hw hdeliver hlo hhi
    have hcommittee : u.val_index ∈ S.E.committee u.slot := by
      have hwire := adm.wire j w (Object.gfVote u) t hdeliver
      simpa only [Object.wellFormed, NamedReceipt.wellFormed,
        Protocol.vote_well_formed, decide_eq_true_eq] using hwire
    have hstamps := Protocol.poolStamps_stateBefore
      S adm.toNamedScheduleWellFormed w j
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
            (Protocol.store_time_le_event_time S
              adm.toNamedScheduleWellFormed hdeliver w)) hdeadline
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
      have hpostBodies := recovery_on_block_new_body S before B hnew hcore
      have hstamps : Protocol.PoolStamps before.core := by
        rw [hbefore]
        exact Protocol.poolStamps_stateBefore
          S adm.toNamedScheduleWellFormed w j
      have hslot : before.core.s = s := by
        rw [hbefore]
        exact Protocol.delivery_store_slot_before_freeze S adm hw hdeliver hlo hhi
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
          have hslotTime : before.core.s = S.E.slotOf t := by
            rw [hbefore]
            rfl
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
      have hpostBodies := recovery_on_block_new_body S before B hnew hcore
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

#print axioms actual_gfVote_settled_before_deadline
#print axioms actual_gfVote_settled_before_view_freeze






#print axioms gfVote_in_cutoff_view_after_gst



private theorem gfVote_processes_settled_at_voteDuty_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
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
  obtain ⟨i, e, he, htime, hsettled⟩ :=
    actual_gfVote_settled_before_view_freeze S adm hproc
      hus hw hlo hhi hhi
  let Gamma := Protocol.vote_time S.E (s + 1)
  let N := (rho.events.filter (fun x => decide (x.time < Gamma))).length
  have hiN : i < N := by
    by_contra hnot
    have hNle : N ≤ i := Nat.le_of_not_gt hnot
    have hGammae : Gamma ≤ e.time :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        (t := Gamma) (j := i) (e := e)
        (by simpa [N] using hNle) he
    have hfreezeSucc : Protocol.view_freeze S.E s < Gamma := by
      simpa only [Gamma] using view_freeze_lt_vote_time_succ S.E s
    exact (not_le_of_gt (lt_trans htime hfreezeSucc)) hGammae
  have hcarry : Protocol.PoolCarry
      (NamedRun.stateBefore S rho (i + 1) w).st.core
      (NamedRun.stateBefore S rho N w).st.core :=
    Protocol.pool_carry S adm.toNamedScheduleWellFormed w N
      (Nat.succ_le_of_lt hiN)
  have hstore : Proofs.Optimistic.voteDutyStore S rho w (s + 1) =
      Proofs.Optimistic.voteStore S (NamedRun.stateBefore S rho N w).st.core (s + 1) := by
    unfold Proofs.Optimistic.voteDutyStore Run.storeBeforeTime
    rw [congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take
        S adm.toNamedScheduleWellFormed Gamma) w)]
  rw [hus] at hsettled
  rcases hsettled with hmem | hequiv
  · apply Or.inl
    rw [hstore]
    simpa only [Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      beforeCutoff_subset_of_poolCarry hcarry s (Protocol.view_freeze S.E s) hmem
  · apply Or.inr
    apply equivocates_mono _ u.val_index hequiv
    intro x hx
    rw [hstore]
    simpa only [Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      beforeCutoff_subset_of_poolCarry hcarry s (Protocol.view_freeze S.E s) hx

#print axioms gfVote_processes_settled_at_voteDuty_after_gst

private theorem accepted_gfVote_forward_settled_at_voteDuty_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
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
      (NamedRun.stateBefore S rho (i + 1) w).st (Object.gfVote u) = true
  · obtain ⟨e, he, -, het⟩ := hacc.1.2
    apply Or.inl
    apply gfVote_processed_after_event_at_voteDuty S adm he hus halready
    simpa only [het] using
      lt_trans hhi (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s)
  · have hunaccepted : Object.processed
        (NamedRun.stateBefore S rho (i + 1) w).st (Object.gfVote u) = false :=
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
    obtain ⟨t', hcausal, hdeadline, j, hproc⟩ :=
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

#print axioms accepted_gfVote_forward_settled_at_voteDuty_after_gst





private theorem confVote_transfer_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    ∀ u ∈ confVotes S.E (Proofs.Optimistic.confStore S rho v s) s,
      u ∈ confLate S.E (Proofs.Optimistic.confStore S rho w s) s ∨
        Protocol.equivocates
          (confLate S.E (Proofs.Optimistic.confStore S rho w s) s)
          u.val_index = true := by
  intro u hu
  obtain ⟨i, t, hacc, hus, hlo, hhi⟩ :=
    confirmationVotesAcceptedInWindow_of_admissible S adm hv s u hu
  have hfreezeHor : Protocol.view_freeze S.E s ≤ rho.horizon :=
    le_trans (le_of_lt (view_freeze_lt_confirmation_time S.E s)) hhor
  have hsettled := accepted_gfVote_forward_settled_at_voteDuty_after_gst
    S adm hv hw hpost hacc hus hlo hhi hfreezeHor
  have hsub := voteDutyFrozen_subset_confLate S
    adm.toNamedScheduleWellFormed w s
  rcases hsettled with hmem | hequiv
  · exact Or.inl (hsub hmem)
  · exact Or.inr (equivocates_mono hsub u.val_index hequiv)

omit [Fintype V] in
private theorem recovery_rootInjectiveBelow_mono
    {A B : Finset (Block V)} (hsub : A ⊆ B)
    (h : RootInjectiveBelow B) : RootInjectiveBelow A := by
  intro x y hx hy hroot
  refine h x y ?_ ?_ hroot
  · obtain ⟨C, hC, hxC⟩ := hx
    exact ⟨C, hsub hC, hxC⟩
  · obtain ⟨C, hC, hyC⟩ := hy
    exact ⟨C, hsub hC, hyC⟩

theorem opening_frontier_crossViews_confStore_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    CrossView
        (Proofs.Optimistic.confStore S rho v s).T
        (Proofs.Optimistic.confStore S rho w s).T
        (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
        (confLate S.E (Proofs.Optimistic.confStore S rho w s) s) ∧
      CrossView
        (Proofs.Optimistic.confStore S rho w s).T
        (Proofs.Optimistic.confStore S rho v s).T
        (confVotes S.E (Proofs.Optimistic.confStore S rho w s) s)
        (confLate S.E (Proofs.Optimistic.confStore S rho v s) s) := by
  refine ⟨?_, ?_⟩
  · apply CrossView.of_rootInjective
    · exact confVote_transfer_after_gst S adm hv hw hpost hhor
    · obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
        S adm.toNamedScheduleWellFormed (Protocol.confirmation_time S.E s)
      have hinj := Proofs.Bridges.rootInjectiveBelow_stateBefore_union S
        adm.toNamedRootCollisionFree hv hw n n
      have hstoreV : Proofs.Optimistic.confStore S rho v s =
          Proofs.Optimistic.tickStore S (rho.stateBefore S n v).st.core
            (Protocol.confirmation_time S.E s) := by
        unfold Proofs.Optimistic.confStore Run.storeBeforeTime
        rw [congrArg NamedNodeState.st (congrFun hn v)]
      have hstoreW : Proofs.Optimistic.confStore S rho w s =
          Proofs.Optimistic.tickStore S (rho.stateBefore S n w).st.core
            (Protocol.confirmation_time S.E s) := by
        unfold Proofs.Optimistic.confStore Run.storeBeforeTime
        rw [congrArg NamedNodeState.st (congrFun hn w)]
      have hveq : (Proofs.Optimistic.confStore S rho v s).T =
          (rho.stateBefore S n v).st.core.T := by
        rw [hstoreV]
        rfl
      have hweq : (Proofs.Optimistic.confStore S rho w s).T =
          (rho.stateBefore S n w).st.core.T := by
        rw [hstoreW]
        rfl
      rw [hveq, hweq]
      apply recovery_rootInjectiveBelow_mono _ hinj
      intro B hB
      rcases Finset.mem_union.mp hB with hB | hB
      · obtain ⟨D, hD, hDe⟩ :=
          Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hB
        exact Finset.mem_image.mpr ⟨D, Finset.mem_union_left _ hD, hDe⟩
      · obtain ⟨D, hD, hDe⟩ :=
          Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n w hB
        exact Finset.mem_image.mpr ⟨D, Finset.mem_union_right _ hD, hDe⟩
  · apply CrossView.of_rootInjective
    · exact confVote_transfer_after_gst S adm hw hv hpost hhor
    · obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
        S adm.toNamedScheduleWellFormed (Protocol.confirmation_time S.E s)
      have hinj := Proofs.Bridges.rootInjectiveBelow_stateBefore_union S
        adm.toNamedRootCollisionFree hw hv n n
      have hstoreV : Proofs.Optimistic.confStore S rho v s =
          Proofs.Optimistic.tickStore S (rho.stateBefore S n v).st.core
            (Protocol.confirmation_time S.E s) := by
        unfold Proofs.Optimistic.confStore Run.storeBeforeTime
        rw [congrArg NamedNodeState.st (congrFun hn v)]
      have hstoreW : Proofs.Optimistic.confStore S rho w s =
          Proofs.Optimistic.tickStore S (rho.stateBefore S n w).st.core
            (Protocol.confirmation_time S.E s) := by
        unfold Proofs.Optimistic.confStore Run.storeBeforeTime
        rw [congrArg NamedNodeState.st (congrFun hn w)]
      have hveq : (Proofs.Optimistic.confStore S rho v s).T =
          (rho.stateBefore S n v).st.core.T := by
        rw [hstoreV]
        rfl
      have hweq : (Proofs.Optimistic.confStore S rho w s).T =
          (rho.stateBefore S n w).st.core.T := by
        rw [hstoreW]
        rfl
      rw [hweq, hveq]
      apply recovery_rootInjectiveBelow_mono _ hinj
      intro B hB
      rcases Finset.mem_union.mp hB with hB | hB
      · obtain ⟨D, hD, hDe⟩ :=
          Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n w hB
        exact Finset.mem_image.mpr ⟨D, Finset.mem_union_left _ hD, hDe⟩
      · obtain ⟨D, hD, hDe⟩ :=
          Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hB
        exact Finset.mem_image.mpr ⟨D, Finset.mem_union_right _ hD, hDe⟩
end DecoupledConsensusModel.Protocol

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms Protocol.opening_frontier_crossViews_confStore_after_gst
end DecoupledConsensusModel.Proofs.HealingSurface

end
