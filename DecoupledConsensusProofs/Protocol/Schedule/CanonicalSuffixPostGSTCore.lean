module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.PostGSTSync
public import DecoupledConsensusProofs.Protocol.Grades.ProposalLifecycleCore
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ConePersistence
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore

@[expose] public section

/-!
# Post-GST vote visibility for the canonical suffix

These kernels use the actual vote duty as the synchrony source. They require
only that this source is after GST; no condition is imposed on the run prefix.

**Named-runtime proof.** The receiver-side interface
below reads `Proofs.Optimistic.voteDutyStore` only as a tree and a stamp map, which
 leaves verbatim, so it ports unchanged.

**Open (class d),.** Four kernels remain absent:
`canonicalSuffixConfRepresentation`,
`canonicalSuffixConfAnchorPreceqAfterGST`,
`CanonicalSuffixVoteStoreFacts.compatibleReach` and
`canonicalSuffixConeRecursCompatible`.

The four available vote-visibility kernels use the named Goldfish pool kernel and
the earlier counting route. The remaining declarations rest on these absent
producers: the confirmation anchor
`HonestWeightMajority.confAnchor_preceq_of_history`, left absent in
`Availability/EvaluationStoreRun.lean` (the grade-batch `sole` half, plus the
confirmation duty's own frozen-G1 contract anchor); the representation producer
at a post-GST read, whose full-participation form this chain rebuilds only at
GST zero (`Availability/EvaluationStoreRun.lean`'s
`honest_represented_stateBeforeTime`); the merged-view equivocation producer;
the  prepared vote-duty emission bridge; and the recovery adoption family
recorded as absent in `Availability/RecoveryHandoffCoreRun.lean`. Their
byte-exact earlier text
is archived  at
`the compatibility layer`.
Not guessed at; not available.
-/



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem canonicalSuffix_admit_rows_bodies (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).bodies = st.bodies := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
      change (Protocol.NamedAdmission.admit_rows hc
        (Protocol.NamedAdmission.admit_row hc st row) rows).bodies = _
      rw [ih, Proofs.NamedAdmission.admit_row_bodies]

private theorem canonicalSuffix_core_new_body (S : Setup V) (st : Protocol.NamedStore V)
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

private theorem canonicalSuffix_on_block_new_body (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hnew : B.erase ∉ st.core.T)
    (hpost : B.erase ∈
      (Execution.NamedReceiptCalls.postCore S st B).core.T) :
    B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies := by
  rw [show Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B =
      Protocol.NamedAdmission.admit_carried .alsoCarried S.hc st
        (Execution.NamedReceiptCalls.postCore S st B) B by rfl]
  unfold Protocol.NamedAdmission.admit_carried
  split_ifs
  · rw [canonicalSuffix_admit_rows_bodies]
    exact canonicalSuffix_core_new_body S st B hnew hpost
  · exact canonicalSuffix_core_new_body S st B hnew hpost

private theorem canonicalSuffix_propose_block_with_gf_votes
    (contract : Protocol.GradeContract V) (st : Protocol.NamedStore V)
    {E : Env V} {hc : Protocol.HealConfig} {cfg : Protocol.HeightConfig}
    {nd : Protocol.Node V} {B : NamedBlock V}
    (h : (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).2 = some B) :
    B.gf_votes = st.core.gf_votes (st.core.s - 1) := by
  unfold Protocol.NamedDuties.propose_block_with at h
  cases hm : Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st with
  | none => rw [hm] at h; simp at h
  | some B' =>
    rw [hm] at h
    have hBB' : B' = B := Option.some.inj h
    rw [← hBB']
    exact Proofs.Optimistic.proposal_with_gf_votes contract .poolAndCarried E hc nd st hm

theorem canonicalSuffixGfVotePooledBeforeFreeze_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {s : Slot} (hs : 0 < s)
    {u : GoldfishVote V}
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hemit : NamedRun.emits S rho v (Object.gfVote u)
      (Protocol.vote_time S.E s))
    (hus : u.slot = s) {w : V} (hw : w ∈ rho.honest)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon) :
    ∃ (j : Nat) (e : Event V), rho.events[j]? = some e ∧
      e.time < Protocol.support_cutoff S.E s ∧
      u ∈ (NamedRun.stateBefore S rho (j + 1) w).st.gf_votes s ∧
      ∃ c : Stamp,
        (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote u = some c ∧
          c < (Protocol.support_cutoff S.E s : Stamp) := by
  obtain ⟨-, -, hvalv, -⟩ := Proofs.Optimistic.emits_gfVote_shape S hemit
  have hval : u.val_index ∈ rho.honest := by rw [hvalv]; exact hv
  obtain ⟨t', hloRelay, hlt, hactual⟩ :=
    broadcast_after_gst S adm hv hw hpost hemit
      (by rw [Proofs.Optimistic.vote_time_add_delta]; exact hhor) rfl
  rw [Proofs.Optimistic.vote_time_add_delta] at hlt
  obtain ⟨j, hactual⟩ := hactual
  obtain ⟨hindex, e, he, hnode, htime⟩ := hactual
  rcases hindex with
      (⟨t'', htick, hem⟩ | ⟨t'', hdeliver⟩) |
        ⟨B, j', before, hcall⟩
  · have heq : Event.tick w t'' = e := Option.some.inj (htick.symm.trans he)
    have htt : t'' = t' := (congrArg Event.time heq).trans htime
    subst t''
    have hemit' : NamedRun.emits S rho w (Object.gfVote u) t' :=
      ⟨j, htick, hem⟩
    obtain ⟨hs', ht', -, hus'⟩ := Proofs.Optimistic.emits_gfVote_shape S hemit'
    have hslot : S.E.slotOf t' = s := by rw [← hus', hus]
    have ht'vote : t' = Protocol.vote_time S.E s := by
      simpa only [hslot] using ht'
    have hemitVote : NamedRun.emits S rho w (Object.gfVote u)
        (Protocol.vote_time S.E s) := by
      simpa only [ht'vote] using hemit'
    obtain ⟨i, hi, hmem, c, hc, hle⟩ :=
      Proofs.Optimistic.mem_pool_of_emits_core S adm hs hemitVote hus hval
    refine ⟨i, _, hi, ?_, hmem, c, hc, ?_⟩
    · simpa only [ht'vote] using hlt
    · refine lt_of_le_of_lt hle ?_
      rw [← Proofs.Optimistic.vote_time_add_delta]
      exact_mod_cast (show Protocol.vote_time S.E s <
        Protocol.vote_time S.E s + S.E.Δ from
        Int.lt_add_of_pos_right _ S.E.Δ_pos)
  · have heq : Event.deliver w (Object.gfVote u) t'' = e :=
      Option.some.inj (hdeliver.symm.trans he)
    have htt : t'' = t' := (congrArg Event.time heq).trans htime
    subst t''
    have hlo : Protocol.vote_time S.E s ≤ t' := hloRelay
    have hslot : (NamedRun.stateBefore S rho j w).st.core.s = s := by
      show (NamedRun.stateBefore S rho j w).st.s = s
      exact Proofs.Optimistic.delivery_store_slot_core S adm hw hdeliver hlo hlt
    have hcommittee : u.val_index ∈ S.E.committee u.slot := by
      have hwire := adm.wire j w (Object.gfVote u) t' hdeliver
      simpa only [Object.wellFormed, NamedReceipt.wellFormed,
        Protocol.vote_well_formed, decide_eq_true_eq] using hwire
    have hstamps := Protocol.poolStamps_stateBefore
      S adm.toNamedScheduleWellFormed w j
    have hfresh : ¬ u.slot <
        (NamedRun.stateBefore S rho j w).st.core.s - 1 := by
      rw [hslot, hus]
      exact Nat.not_lt.mpr (Nat.sub_le s 1)
    have hfuture : ¬ (NamedRun.stateBefore S rho j w).st.core.s < u.slot := by
      rw [hslot, hus]
      exact Nat.lt_irrefl s
    have hequiv := Proofs.Optimistic.pool_no_honest_equivocation_of_core S adm w j u.slot hval
    obtain ⟨hmem, c, hc, hle⟩ := Protocol.mem_and_stamp_of_process
      (NamedRun.stateBefore S rho j w).st.core u hstamps hfresh hfuture hequiv
    have hstep :
        (NamedRun.stateBefore S rho (j + 1) w).st.core =
          Protocol.on_goldfish_vote (NamedRun.stateBefore S rho j w).st.core u := by
      rw [Proofs.NamedRuntime.stateBefore_deliver S rho hdeliver]
      show Protocol.on_goldfish_vote_checked S.E _ u = _
      unfold Protocol.on_goldfish_vote_checked
      rw [if_neg (not_not.mpr hcommittee)]
    refine ⟨j, _, hdeliver, by simpa [Event.time] using hlt, ?_, c, ?_, ?_⟩
    · show u ∈ (NamedRun.stateBefore S rho (j + 1) w).st.core.gf_votes s
      rw [hstep]
      simpa only [hus] using hmem
    · show (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote u = some c
      rw [hstep]
      exact hc
    · have hup : (NamedRun.stateBefore S rho j w).st.core.t ≤ t' := by
        simpa [Event.time] using
          Protocol.store_time_le_event_time S adm.toNamedScheduleWellFormed hdeliver w
      exact lt_of_le_of_lt hle (WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hup hlt))
  · obtain ⟨hblock, hnew, hcore, huindex⟩ := hcall
    have huB : u ∈ B.gf_votes := List.mem_of_getElem? huindex
    have huErase : u ∈ B.erase.gf_votes := by
      rwa [Proofs.NamedWire.erase_goldfish_votes]
    rcases hblock with
        ⟨t'', hdeliver, hbefore⟩ | ⟨t'', htick, hBemit, hbefore⟩
    · have heq : Event.deliver w (Object.block B) t'' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have htt : t'' = t' := (congrArg Event.time heq).trans htime
      subst t''
      have hpreBodies : B ∉ before.bodies := by
        intro hB
        apply hnew
        have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j w).1.1.1
        have hB' : B ∈ (NamedRun.stateBefore S rho j w).st.bodies := by
          simpa [hbefore] using hB
        rw [hbefore, hcoh.1]
        exact Finset.mem_image_of_mem NamedBlock.erase hB'
      have hpostBodies := canonicalSuffix_on_block_new_body S before B hnew hcore
      have hstamps : Protocol.PoolStamps before.core := by
        rw [hbefore]
        exact Protocol.poolStamps_stateBefore S adm.toNamedScheduleWellFormed w j
      have hclock0 : Protocol.vote_time S.E s ≤ before.core.t := by
        rw [hbefore]
        refine Protocol.tick_le_store_time S adm.toNamedScheduleWellFormed hdeliver ?_
          hloRelay
        exact adm.tick_total w hw _ (Proofs.Optimistic.publicTime_vote_time S s)
          (Proofs.Optimistic.vote_time_nonneg S.E s)
          (le_trans hloRelay
            (adm.in_horizon _ (List.mem_of_getElem? hdeliver)).2)
      have hclockUp : before.core.t ≤ t' := by
        rw [hbefore]
        simpa [Event.time] using
          Protocol.store_time_le_event_time S adm.toNamedScheduleWellFormed hdeliver w
      have hslot : before.core.s = s := by
        have hsc := Proofs.NamedStoreBridge.slotOfClock_stateBefore S rho j w
        unfold Proofs.Optimistic.SlotOfClock at hsc
        have hsc' : before.core.s = S.E.slotOf before.core.t := by
          simpa [hbefore] using hsc
        rw [hsc']
        exact Proofs.Optimistic.slotOf_of_between S.E s hclock0
          (lt_of_le_of_lt hclockUp hlt)
      have hfresh : ¬ u.slot < before.core.s - 1 := by
        rw [hus, hslot]
        exact Nat.not_lt.mpr (Nat.sub_le s 1)
      have hfuture : ¬ before.core.s < u.slot := by
        rw [hslot, hus]
        exact Nat.lt_irrefl s
      have hcommittee : u.val_index ∈ S.E.committee u.slot := by
        have hwire := adm.wire _ w (Object.block B) t' hdeliver
        simp only [Object.wellFormed, NamedReceipt.wellFormed,
          Bool.and_eq_true] at hwire
        have hcarried := hwire.2
        simp only [List.all_eq_true, decide_eq_true_eq] at hcarried
        exact hcarried u huErase
      have hlocal := Proofs.Optimistic.block_carried_before_deadline_or_equivocates
        S before B u (Protocol.support_cutoff S.E s) hstamps hpreBodies hpostBodies
        huErase hcommittee hfresh hfuture (lt_of_le_of_lt hclockUp hlt)
      have hstate := Proofs.NamedReceiptCallsBase.delivery_result S rho hdeliver
      let final := Protocol.NamedAdmission.on_block_with
        .alsoCarried S.E S.hc S.cfg before B
      have hfinalEq : (NamedRun.stateBefore S rho (j + 1) w).st = final := by
        rw [hstate]
        simpa [final, hbefore, NamedReceipt.process]
      have hlocal' :
          u ∈ beforeCutoff final.core.timestamp_vote
              (Protocol.support_cutoff S.E s) (final.core.pool u.slot) ∨
            Protocol.equivocates
              (beforeCutoff final.core.timestamp_vote
                (Protocol.support_cutoff S.E s) (final.core.pool u.slot))
              u.val_index = true := by
        simpa only [final] using hlocal
      rcases hlocal' with hlocal | hequiv
      · rw [beforeCutoff, Finset.mem_filter] at hlocal
        have hpool := hlocal.1
        have hstamp := hlocal.2
        cases hc : final.core.timestamp_vote u with
        | none => simp [stampedBefore, hc] at hstamp
        | some c =>
          have hc' : c < (Protocol.support_cutoff S.E s : Stamp) := by
            simpa only [stampedBefore, hc, decide_eq_true_eq] using hstamp
          have hpool' : u ∈ final.core.gf_votes u.slot := by
            simpa only [Protocol.NamedStore.pool, Protocol.Store.pool,
              List.mem_toFinset] using hpool
          refine ⟨_, _, he, ?_, ?_, c, ?_, hc'⟩
          · simpa [htime] using hlt
          · rw [hfinalEq]
            simpa only [hus] using hpool'
          · rw [hfinalEq]
            exact hc
      · have hfull : Protocol.equivocates
            (final.core.pool u.slot)
            u.val_index = true :=
          equivocates_mono (by
            intro x hx
            exact (Finset.mem_filter.mp hx).1) u.val_index hequiv
        have hno := Proofs.Optimistic.pool_no_honest_equivocation_of_core S adm w (j + 1) s hval
        have hno' : Protocol.equivocates (final.core.pool u.slot) u.val_index = false := by
          simpa only [hfinalEq, hus] using hno
        rw [hno'] at hfull
        simp at hfull
    · have heq : Event.tick w t'' = e := Option.some.inj (htick.symm.trans he)
      have htt : t'' = t' := (congrArg Event.time heq).trans htime
      subst t''
      have hproposal := congrArg Prod.snd
        (Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hBemit)
      have hgf := canonicalSuffix_propose_block_with_gf_votes _ _ hproposal
      have hgf' : B.gf_votes = before.core.gf_votes (before.core.s - 1) := by
        simpa [hbefore] using hgf
      have hslot : before.core.s = s := by
        have hslot' := Proofs.Optimistic.slotOf_of_between S.E s hloRelay hlt
        simpa [hbefore, Protocol.NamedStore.setClock] using hslot'
      have hstamps : Protocol.PoolStamps before.core := by
        rw [hbefore]
        have hrawStamps := Protocol.poolStamps_stateBefore
          S adm.toNamedScheduleWellFormed w j
        have htle : (NamedRun.stateBefore S rho j w).st.core.t ≤ t' := by
          simpa [Event.time] using
            Protocol.store_time_le_event_time S adm.toNamedScheduleWellFormed htick w
        exact (Protocol.poolStep_tickStore _ _ _ htle hrawStamps).2
      have huPool : u ∈ before.core.gf_votes (before.core.s - 1) := by
        rw [← hgf']
        exact List.mem_of_getElem? huindex
      have huslot := hstamps.slot (before.core.s - 1) u huPool
      have hbad : s = s - 1 := by simpa [hus, hslot] using huslot
      have hltNat : s - 1 < s := Nat.sub_lt (Nat.zero_lt_of_lt hs) (by decide)
      exact False.elim ((Nat.ne_of_lt hltNat) hbad.symm)


/-- Exact receiver-side facts that make one next vote duty preserve a moving
suffix endpoint. -/
theorem canonicalSuffixGfVoteInCutoffView_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {s : Slot} (hs : 0 < s)
    {u : GoldfishVote V}
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hemit : NamedRun.emits S rho v (Object.gfVote u)
      (Protocol.vote_time S.E s))
    (hus : u.slot = s) {w : V} (hw : w ∈ rho.honest)
    (Gamma Gamma' : Time)
    (hGamma : Protocol.support_cutoff S.E s ≤ Gamma)
    (hGamma' : Protocol.support_cutoff S.E s ≤ Gamma')
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon) :
    u ∈ beforeCutoff (Run.storeBeforeTime S rho w Gamma).timestamp_vote Gamma'
      ((Run.storeBeforeTime S rho w Gamma).pool s) := by
  obtain ⟨j, e, hj, hjt, hmem, c, hc, hlt⟩ :=
    canonicalSuffixGfVotePooledBeforeFreeze_core S adm hv hs hpost hemit hus hw hhor
  have hjN : j <
      (rho.events.filter (fun x : Event V => decide (x.time < Gamma))).length := by
    by_contra hcon
    have h := Proofs.Optimistic.filter_false_of_index_ge
      S adm.toNamedScheduleWellFormed _
        (Proofs.Optimistic.downward_lt Gamma)
        (Nat.le_of_not_lt hcon) hj
    simp only [decide_eq_false_iff_not, not_lt] at h
    exact absurd (lt_of_lt_of_le hjt hGamma) (not_lt_of_ge h)
  have hcarry : Protocol.PoolCarry
      (NamedRun.stateBefore S rho (j + 1) w).st.core
      (NamedRun.stateBefore S rho
        (rho.events.filter (fun x : Event V => decide (x.time < Gamma))).length w).st.core :=
    Protocol.pool_carry S adm.toNamedScheduleWellFormed w
      (rho.events.filter (fun x : Event V => decide (x.time < Gamma))).length hjN
  have hstore : Run.storeBeforeTime S rho w Gamma =
      (NamedRun.stateBefore S rho
        (rho.events.filter (fun x : Event V => decide (x.time < Gamma))).length w).st := by
    change (NamedRun.stateBeforeTime S rho Gamma w).st = _
    rw [congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take
        S adm.toNamedScheduleWellFormed Gamma) w)]
  rw [hstore, beforeCutoff, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · simpa only [Protocol.Store.pool, List.mem_toFinset] using hcarry.mem s u hmem
  simp only [stampedBefore, hcarry.stamp u c hc, decide_eq_true_eq]
  exact lt_of_lt_of_le hlt (by exact_mod_cast hGamma')

/-- Exact receiver-side facts that make one next vote duty preserve a moving
suffix endpoint. -/
theorem canonicalSuffixGfVoteInCutoffView
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {s : Slot} (hs : 0 < s)
    {u : GoldfishVote V}
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hemit : NamedRun.emits S rho v (Object.gfVote u)
      (Protocol.vote_time S.E s))
    (hus : u.slot = s) {w : V} (hw : w ∈ rho.honest)
    (Gamma Gamma' : Time)
    (hGamma : Protocol.support_cutoff S.E s ≤ Gamma)
    (hGamma' : Protocol.support_cutoff S.E s ≤ Gamma')
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon) :
    u ∈ beforeCutoff (Run.storeBeforeTime S rho w Gamma).timestamp_vote Gamma'
      ((Run.storeBeforeTime S rho w Gamma).pool s) :=
  canonicalSuffixGfVoteInCutoffView_core S adm.toNamedAdmissibleCore hv hs hpost
    hemit hus hw Gamma Gamma' hGamma hGamma' hhor

/-- Every honest post-GST slot vote is in the exact confirmation numerator. -/
theorem canonicalSuffixHonestVoteCounted
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest)
    (u : GoldfishVote V) (hus : u.slot = s)
    (hval : u.val_index ∈ rho.honest)
    (hemit : rho.emits S u.val_index (Object.gfVote u)
      (Protocol.vote_time S.E s))
    (harr : Proofs.Optimistic.HeadArrivesBefore
      (Proofs.Optimistic.confStore S rho v s).T
      (Proofs.Optimistic.confStore S rho v s).timestamp_block
      (Protocol.support_cutoff S.E s) u) :
    u ∈ confVotes S.E (Proofs.Optimistic.confStore S rho v s) s := by
  have hle : Protocol.support_cutoff S.E s ≤
      Protocol.confirmation_time S.E s :=
    support_cutoff_le_confirmation_time S.E s
  obtain ⟨n, hn, -⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.confirmation_time S.E s)
  have hstore : rho.storeBeforeTime S v (Protocol.confirmation_time S.E s) =
      (rho.stateBefore S n v).st := by
    change (NamedRun.stateBeforeTime S rho
      (Protocol.confirmation_time S.E s) v).st =
      (NamedRun.stateBefore S rho n v).st
    exact congrArg (fun world => (world v).st) hn
  obtain ⟨H, hfind, hH⟩ := harr
  have hHmem : H ∈ (rho.storeBeforeTime S v
      (Protocol.confirmation_time S.E s)).T := by
    simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      (Proofs.HealingLemmas.find?_mem hfind)
  have hslot : H.slot ≤ u.slot :=
    Proofs.Optimistic.emitted_vote_head_slot_le_of_store_mem S adm.toNamedAdmissibleCore
      hval hv hemit hus hHmem (Proofs.HealingLemmas.find?_root hfind)
  have hrecv : u ∈ beforeCutoff
      (Proofs.Optimistic.confStore S rho v s).timestamp_vote
      (Protocol.support_cutoff S.E s)
      ((Proofs.Optimistic.confStore S rho v s).pool s) :=
    canonicalSuffixGfVoteInCutoffView S adm hval hs hpost hemit hus hv
      _ _ hle (le_refl _) (le_trans hle hhor)
  have hearly : u ∈ confEarly S.E (Proofs.Optimistic.confStore S rho v s) s :=
    Proofs.Optimistic.mem_tau_cutoff_of hrecv hfind hslot hH
  rw [confVotes, Finset.mem_filter]
  refine ⟨hearly, ?_⟩
  simp only [Protocol.no_second_vote_in, decide_eq_true_eq]
  intro x hx
  by_cases hxv : x.val_index = u.val_index
  · refine Or.inl ?_
    have hxpool : x ∈ (rho.stateBefore S n v).st.gf_votes s := by
      have h := (Finset.mem_filter.mp hx).1
      rw [Proofs.Optimistic.confStore, Protocol.Store.pool, List.mem_toFinset] at h
      rw [← hstore]
      exact h
    have hupool : u ∈ (rho.stateBefore S n v).st.gf_votes s := by
      have h := (Finset.mem_filter.mp hearly).1
      rw [Proofs.Optimistic.confStore, Protocol.Store.pool, List.mem_toFinset] at h
      rw [← hstore]
      exact h
    have hno := Proofs.Optimistic.pool_no_honest_equivocation S adm v n s hval
    rw [Protocol.equivocates, decide_eq_false_iff_not] at hno
    have hlt : (Protocol.votes_by
        ((NamedRun.stateBefore S rho n v).st.pool s) u.val_index).card < 2 :=
      Nat.lt_of_not_ge hno
    have hcard : (Protocol.votes_by
        ((NamedRun.stateBefore S rho n v).st.pool s) u.val_index).card ≤ 1 :=
      Nat.le_of_lt_succ (by simpa using hlt)
    have hxpool' : x ∈ (NamedRun.stateBefore S rho n v).st.pool s := by
      simpa only [Protocol.NamedStore.pool, Protocol.Store.pool,
        List.mem_toFinset] using hxpool
    have hupool' : u ∈ (NamedRun.stateBefore S rho n v).st.pool s := by
      simpa only [Protocol.NamedStore.pool, Protocol.Store.pool,
        List.mem_toFinset] using hupool
    have hxmem : x ∈ Protocol.votes_by
        ((NamedRun.stateBefore S rho n v).st.pool s) u.val_index := by
      rw [Protocol.votes_by, Finset.mem_filter]
      exact ⟨hxpool', hxv⟩
    have humem : u ∈ Protocol.votes_by
        ((NamedRun.stateBefore S rho n v).st.pool s) u.val_index := by
      rw [Protocol.votes_by, Finset.mem_filter]
      exact ⟨hupool', rfl⟩
    exact Finset.card_le_one.mp hcard x hxmem u humem
  · exact Or.inr hxv


/-- An honest post-GST vote is in a later honest node's merged support view
once its named head resolves there. -/
theorem canonicalSuffixHonestVoteMemVoterSupport_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    {x : V} (hx : x ∈ rho.honest) {u : GoldfishVote V}
    (hus : u.slot = s)
    (hemit : rho.emits S x (Object.gfVote u)
      (Protocol.vote_time S.E s))
    {w : V} (hw : w ∈ rho.honest) {Gamma : Time}
    (hGamma : Protocol.support_cutoff S.E s ≤ Gamma)
    {gst : Protocol.GoldfishStore V}
    (hgf : gst.gf_votes = (rho.storeBeforeTime S w Gamma).gf_votes)
    (hts : gst.timestamp_vote =
      (rho.storeBeforeTime S w Gamma).timestamp_vote)
    (hheads : ∀ H, Block.find? gst.T u.head = some H → H.slot ≤ u.slot)
    (harr : Proofs.Optimistic.HeadArrivesBefore gst.T gst.timestamp_block
      (Protocol.support_cutoff S.E s) u) :
    u ∈ Protocol.voter_support_view S.E gst (s + 1) := by
  have h := canonicalSuffixGfVoteInCutoffView_core
    S adm hx hs hpost hemit hus hw Gamma (Protocol.view_freeze S.E s)
      hGamma
      (le_of_lt (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s)) hhor
  have hpool : gst.pool s = (rho.storeBeforeTime S w Gamma).pool s := by
    simp only [Protocol.GoldfishStore.pool, Protocol.Store.pool, hgf]
  obtain ⟨H, hfind, hH⟩ := harr
  refine Proofs.Optimistic.mem_voter_support_view_of_pool S.E gst (s + 1) ?_
  rw [Nat.add_sub_cancel]
  refine Proofs.Optimistic.mem_tau_cutoff_of
    (Γ := Protocol.view_freeze S.E s) ?_ hfind
      (hheads H hfind)
      (occurrenceBefore_mono
        (le_of_lt (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s)) hH)
  rw [hts, hpool]
  exact h



private def canonicalVoteVisible
    (S : Setup V) (rho : Run V) (w : V) (n : Nat)
    (u : GoldfishVote V) : Prop :=
  (∃ k : Slot, u ∈ (NamedRun.stateBefore S rho n w).st.gf_votes k) ∨
    ∃ B ∈ (NamedRun.stateBefore S rho n w).st.core.T, u ∈ B.gf_votes

private theorem canonicalEmitsOfVoteVisible_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    (w : V) (n : Nat) {u : GoldfishVote V}
    (hu : canonicalVoteVisible S rho w n u)
    (hx : u.val_index ∈ rho.honest) :
    ∃ t : Time, NamedRun.emits S rho u.val_index (Object.gfVote u) t := by
  have hblock : ∀ B : NamedBlock V,
      B ∈ (NamedRun.stateBefore S rho n w).st.bodies →
      u ∈ B.gf_votes →
      ∃ t : Time, NamedRun.emits S rho u.val_index (Object.gfVote u) t := by
    intro B hB hmem
    rcases Proofs.Bridges.processes_block_of_mem_T S rho w n B hB with
      rfl | ⟨j, e, -, -, hproc⟩
    · exact absurd hmem (by simp [NamedBlock.gf_votes])
    · exact (adm.carried_gf w B e.time hproc u hmem hx).imp fun _ ht => ht.2
  rcases hu with ⟨k, hk⟩ | ⟨B, hB, hmem⟩
  · obtain ⟨j, e, -, -, hproc⟩ :=
      Protocol.processes_gfVote_of_mem_pool S rho w n k u hk
    rcases hproc with hbare | ⟨B, hprocB, hmem⟩
    · exact (adm.unforgeable w (Object.gfVote u) e.time hbare
        u.val_index hx rfl).imp fun _ ht => ht.2
    · exact (adm.carried_gf w B e.time hprocB u hmem hx).imp fun _ ht => ht.2
  · obtain ⟨B', hB', hB'eq⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n w hB
    have hmem' : u ∈ B'.gf_votes := by
      rw [← Proofs.NamedWire.erase_goldfish_votes, hB'eq]
      exact hmem
    exact hblock B' hB' hmem'


private theorem canonicalVoteVisibleUnique_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    (w : V) (n : Nat) {u₁ u₂ : GoldfishVote V}
    (h₁ : canonicalVoteVisible S rho w n u₁)
    (h₂ : canonicalVoteVisible S rho w n u₂)
    (hx : u₁.val_index ∈ rho.honest)
    (hval : u₂.val_index = u₁.val_index)
    (hslot : u₁.slot = u₂.slot) : u₁ = u₂ := by
  obtain ⟨t₁, he₁⟩ := canonicalEmitsOfVoteVisible_core S adm w n h₁ hx
  obtain ⟨t₂, he₂⟩ := canonicalEmitsOfVoteVisible_core S adm w n h₂ (by
    rw [hval]
    exact hx)
  rw [hval] at he₂
  exact Proofs.Optimistic.emits_gfVote_unique S adm.toNamedScheduleWellFormed he₁ he₂ hslot


private theorem canonicalVoterViewNoHonestEquivocation_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    (w : V) (n : Nat) (gst : Protocol.GoldfishStore V)
    (hgf : ∀ (k : Slot) (u : GoldfishVote V), u ∈ gst.gf_votes k →
      u ∈ (NamedRun.stateBefore S rho n w).st.gf_votes k)
    (hT : ∀ B ∈ gst.T, B ∈ (NamedRun.stateBefore S rho n w).st.core.T)
    {x : V} (hx : x ∈ rho.honest) (s : Slot) :
    Protocol.equivocates (Protocol.voter_view S.E gst s) x = false := by
  have hview : ∀ u ∈ Protocol.voter_view S.E gst s,
      canonicalVoteVisible S rho w n u ∧ u.slot = s - 1 := by
    intro u hu
    rw [Protocol.voter_view, Finset.mem_union] at hu
    rcases hu with hu | hu
    · rw [beforeCutoff, Finset.mem_filter, Protocol.GoldfishStore.pool,
        List.mem_toFinset] at hu
      have hmem := hgf (s - 1) u hu.1
      exact ⟨Or.inl ⟨s - 1, hmem⟩,
        (Protocol.poolStamps_stateBefore S
          adm.toNamedScheduleWellFormed w n).slot _ u hmem⟩
    · rw [Finset.mem_biUnion] at hu
      obtain ⟨B, hB, hmem⟩ := hu
      rw [Finset.mem_filter] at hB hmem
      have hBT : B ∈ (NamedRun.stateBefore S rho n w).st.core.T := hT B hB.1
      exact ⟨Or.inr ⟨B, hBT, List.mem_toFinset.mp hmem.1⟩, hmem.2⟩
  rw [Protocol.equivocates, decide_eq_false_iff_not, Nat.not_le]
  refine Nat.lt_succ_of_le (Finset.card_le_one.mpr ?_)
  intro u₁ hu₁ u₂ hu₂
  rw [Protocol.votes_by, Finset.mem_filter] at hu₁ hu₂
  obtain ⟨hv₁, hs₁⟩ := hview u₁ hu₁.1
  obtain ⟨hv₂, hs₂⟩ := hview u₂ hu₂.1
  exact canonicalVoteVisibleUnique_core S adm w n hv₁ hv₂
    (by rw [hu₁.2]; exact hx)
    (by rw [hu₂.2, hu₁.2]) (by rw [hs₁, hs₂])



/-- A post-GST named honest-vote cone gives the merged-view support package
used by the next vote duty. -/
theorem canonicalSuffixConeSupportVoterView_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    {tgt : Block V → Prop}
    (hnames : Proofs.HealingSurface.NamedHonestVotesCone S rho s tgt)
    {w : V} (hw : w ∈ rho.honest) {Gamma : Time}
    (hGamma : Protocol.support_cutoff S.E s ≤ Gamma)
    {gst : Protocol.GoldfishStore V}
    (hgf : gst.gf_votes = (rho.storeBeforeTime S w Gamma).gf_votes)
    (hts : gst.timestamp_vote =
      (rho.storeBeforeTime S w Gamma).timestamp_vote)
    (hT : gst.T = (rho.storeBeforeTime S w Gamma).T)
    (hres : Proofs.Optimistic.HeadsResolveIn S rho s gst.T gst.timestamp_block) :
    Proofs.Optimistic.ConeSupport S.E gst.T
      (Protocol.voter_view S.E gst (s + 1))
      (Protocol.voter_support_view S.E gst (s + 1))
      (Protocol.voter_view S.E gst (s + 1)) s rho.honest tgt := by
  obtain ⟨n, hn, -⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toNamedScheduleWellFormed Gamma
  have hstore : rho.storeBeforeTime S w Gamma =
      (rho.stateBefore S n w).st := by
    change (NamedRun.stateBeforeTime S rho Gamma w).st =
      (NamedRun.stateBefore S rho n w).st
    exact congrArg (fun world => (world w).st) hn
  refine Proofs.Optimistic.coneSupport_of_named_votes (hcom s) (subset_refl _)
    (Protocol.voter_support_view_subset S.E gst (s + 1) ?_) ?_ ?_
  · intro B hB
    refine Proofs.Optimistic.carried_support_subset_of_mem_T_core S adm w n ?_
    have hBstore : B ∈ (rho.storeBeforeTime S w Gamma).T := by
      rw [← hT]
      exact hB
    rw [hstore] at hBstore
    exact hBstore
  · intro y _ hyHonest
    refine canonicalVoterViewNoHonestEquivocation_core
      S adm w n gst ?_ ?_ hyHonest (s + 1)
    · intro k y' hy'
      rw [← hstore, ← hgf]
      exact hy'
    · intro B hB
      have hBstore : B ∈ (rho.storeBeforeTime S w Gamma).T := by
        rw [← hT]
        exact hB
      have hBcore : B ∈ (rho.storeBeforeTime S w Gamma).core.T := hBstore
      rw [hstore] at hBcore
      exact hBcore
  · intro y hyCommittee hyHonest
    obtain ⟨X, htgt, hrun, hemit⟩ := hnames y hyHonest hyCommittee
    have hhead : Proofs.Optimistic.HonestHead S rho s X.erase :=
      ⟨y, hyHonest, hyCommittee, ⟨X, rfl, hrun⟩, hemit⟩
    obtain ⟨hfind, hstamp⟩ := hres X.erase hhead
    have hheads : ∀ H, Block.find? gst.T X.erase.root = some H → H.slot ≤ s := by
      intro H hfindH
      have hHmem : H ∈ (rho.storeBeforeTime S w Gamma).T := by
        rw [← hT]
        exact Proofs.HealingLemmas.find?_mem hfindH
      exact Proofs.Optimistic.emitted_vote_head_slot_le_of_store_mem S adm
        hyHonest hw hemit rfl hHmem (Proofs.HealingLemmas.find?_root hfindH)
    exact ⟨X.erase, htgt, hheads X.erase hfind,
      canonicalSuffixHonestVoteMemVoterSupport_core
        S adm hs hpost hhor hyHonest rfl hemit hw hGamma hgf hts
          hheads
          ⟨X.erase, hfind, hstamp⟩,
      hfind⟩

theorem canonicalSuffixConeSupportVoterView
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    {tgt : Block V → Prop}
    (hnames : Proofs.HealingSurface.NamedHonestVotesCone S rho s tgt)
    {w : V} (hw : w ∈ rho.honest) {Gamma : Time}
    (hGamma : Protocol.support_cutoff S.E s ≤ Gamma)
    {gst : Protocol.GoldfishStore V}
    (hgf : gst.gf_votes = (rho.storeBeforeTime S w Gamma).gf_votes)
    (hts : gst.timestamp_vote =
      (rho.storeBeforeTime S w Gamma).timestamp_vote)
    (hT : gst.T = (rho.storeBeforeTime S w Gamma).T)
    (hres : Proofs.Optimistic.HeadsResolveIn S rho s gst.T gst.timestamp_block) :
    Proofs.Optimistic.ConeSupport S.E gst.T
      (Protocol.voter_view S.E gst (s + 1))
      (Protocol.voter_support_view S.E gst (s + 1))
      (Protocol.voter_view S.E gst (s + 1)) s rho.honest tgt :=
  canonicalSuffixConeSupportVoterView_core S adm.toNamedAdmissibleCore hcom hs
    hpost hhor hnames hw hGamma hgf hts hT hres



#print axioms canonicalSuffixGfVoteInCutoffView
#print axioms canonicalSuffixHonestVoteCounted
#print axioms canonicalSuffixConeSupportVoterView

end Protocol
end DecoupledConsensusModel

end
