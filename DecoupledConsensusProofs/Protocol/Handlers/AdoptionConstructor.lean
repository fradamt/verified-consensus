module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.StoreFinalityCore
public import DecoupledConsensusProofs.Protocol.Handlers.Blocks
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Objects.BlockVisibilityCore
public import DecoupledConsensusProofs.Protocol.Schedule.ProposalTransportCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.BlockEmission
public import DecoupledConsensusProofs.Protocol.Grades.CarrierAdmission
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistory
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroHeadResolution
public import DecoupledConsensusProofs.Execution.ReceiptCallsBase
public import DecoupledConsensusProofs.Protocol.Handlers.BlockStamp
public import DecoupledConsensusProofs.Protocol.Handlers.GoldfishVotePool
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates

@[expose] public section



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

namespace HonestWeightMajority

/-! ## Block receipt timing for B-specific support transport -/

omit [Fintype V] in
/-- A resolution-time bound includes the named block's receipt bound. -/
theorem stampedBefore_block_of_resolution
    {T : Finset (Block V)} {tb : TimestampMap (Block V)}
    {tv : TimestampMap (GoldfishVote V)} {Gamma : Time}
    {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? T u.head = some H)
    (hresolved : stampedBefore (Protocol.resolution_time T tb tv) Gamma u = true) :
    stampedBefore tb Gamma H = true := by
  simp only [stampedBefore_eq_occurrenceBefore, Protocol.resolution_time,
    hfind, Protocol.head_slot_le_of_resolution_time hfind hresolved,
    if_true] at hresolved ⊢
  cases hv : tv u with
  | none =>
      simp only [hv, occurrenceMax, occurrenceBefore] at hresolved
      simp at hresolved
  | some a =>
      cases hH : tb H with
      | none =>
          simp only [hv, hH, occurrenceMax, occurrenceBefore] at hresolved
          simp at hresolved
      | some b =>
          simp only [hv, hH, occurrenceMax, occurrenceBefore,
            decide_eq_true_eq] at hresolved ⊢
          exact lt_of_le_of_lt (le_max_right a b) hresolved


/-- If one `on_block` call newly inserts its argument, that block receives the
active store clock as its write-once block stamp. -/
theorem on_block_new_timestamp
    (E : Env V) (cfg : Protocol.HeightConfig)
    (st : Protocol.Store V) (B : Block V)
    (hpre : B ∉ st.T) (hpost : B ∈ (Protocol.on_block E cfg st B).T) :
    (Protocol.on_block E cfg st B).timestamp_block B = some (st.t : Stamp) := by
  by_cases hfirst : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
  · rw [show Protocol.on_block E cfg st B = st by
      simp only [Protocol.on_block, Protocol.on_block_using, if_pos hfirst]] at hpost
    exact False.elim (hpre hpost)
  by_cases hadmit : (!Block.preceq st.F B) = true
  · rw [show Protocol.on_block E cfg st B = st by
      simp only [Protocol.on_block, Protocol.on_block_using, if_neg hfirst,
        if_pos hadmit]] at hpost
    exact False.elim (hpre hpost)
  by_cases hprop : B.proposer? ≠ some (E.proposer B.slot)
  · rw [show Protocol.on_block E cfg st B = st by
      simp only [Protocol.on_block, Protocol.on_block_using, if_neg hfirst,
        if_neg hadmit, if_pos hprop]] at hpost
    exact False.elim (hpre hpost)
  by_cases hparent : ¬ B.parent.slot < B.slot
  · rw [show Protocol.on_block E cfg st B = st by
      simp only [Protocol.on_block, Protocol.on_block_using, if_neg hfirst,
        if_neg hadmit, if_neg hprop,
        if_pos hparent]] at hpost
    exact False.elim (hpre hpost)
  simp only [Protocol.on_block, Protocol.on_block_using, if_neg hfirst,
    if_neg hadmit, if_neg hprop,
    if_neg hparent, update_finality_timestamp_block,
    foldl_on_goldfish_vote_checked_timestamp_block]
  simp

/-- At a firing proposal tick, later same-tick duties preserve the block stamp
map produced by the proposal stage. -/
theorem on_tick_emit_proposal_timestamp_block
    (S : Setup V) (v : V) (n : NodeState V) (s : Slot) (hs : 0 < s)
    (hprop : S.E.proposer s = (S.node v).val_index) :
    let proposed := Protocol.NamedDuties.propose_block_with
      (NamedProfile.gradeContract
        (NamedActionReads.confirmationReadFrom S n
          (Protocol.proposal_time S.E s)).cache)
      S.E S.hc S.cfg (S.node v)
      (NamedActionReads.confirmationReadFrom S n
        (Protocol.proposal_time S.E s)).st
    let out := (on_tick_emit S v n (Protocol.proposal_time S.E s)).1
    out.st.core.timestamp_block = proposed.1.core.timestamp_block := by
  have hslot : S.E.slotOf (Protocol.proposal_time S.E s) = s :=
    Proofs.Optimistic.slotOf_proposal_time S.E s
  dsimp only
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick,
    Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps, hslot,
    NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
    Protocol.NamedStore.setClock,
    Proofs.Optimistic.proposal_time_ne_vote_time S.E s,
    Proofs.Optimistic.proposal_time_ne_support_cutoff S.E s, hprop, hs,
    and_false, and_true, if_false, if_true, Protocol.NamedDuties.attest_with,
    Protocol.NamedAdmission.admit_row]
  split
  · split <;> exact on_sg_vote_timestamp_block _ _ _
  · rfl

/-! ## Fresh-body write-once stamp, at the named admission pipeline

The named admission wraps the raw guard sequence (`process_block_core`) in a
`.bodies`-tracking commit and an F1 carried-row tail (`admit_carried`).
Neither the commit guard nor the row tail touches `.core.timestamp_block`
once a fresh body clears the raw guards, so the erased write-once fact
(`checked_new_block_stamp`, the named twin of `on_block_new_timestamp` above)
transports up to `Protocol.NamedAdmission.on_block_with`. These are private
verbatim copies of `NamedBlockStamp`'s own (private) chain, reproduced here
because that file exports only the run-level corollaries. -/

omit [Fintype V] in
private theorem rows_bodies (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).bodies = st.bodies := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
      change (Protocol.NamedAdmission.admit_rows hc
        (Protocol.NamedAdmission.admit_row hc st row) rows).bodies = _
      rw [ih, Proofs.NamedAdmission.admit_row_bodies]

omit [Fintype V] in
private theorem rows_block_stamp (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).core.timestamp_block =
      st.core.timestamp_block := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
      change (Protocol.NamedAdmission.admit_rows hc
        (Protocol.NamedAdmission.admit_row hc st row) rows).core.timestamp_block = _
      rw [ih]
      exact (Proofs.NamedAdmission.admit_row_fixed_fields hc st row).2.2.2.1

private theorem checked_new_block_stamp (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (B : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V)
    (hpre : B ∉ st.T)
    (hpost : B ∈ (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B buildState) hc st B).T) :
    (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B buildState)
      hc st B).timestamp_block B = some (st.t : Stamp) := by
  dsimp only [Protocol.on_block_checked_using] at hpost ⊢
  by_cases hvalid : Protocol.carried_attestations_admissible hc B = true
  · simp only [hvalid, if_true] at hpost ⊢
    by_cases hfirst : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
    · simp only [Protocol.on_block_using, if_pos hfirst] at hpost
      exact False.elim (hpre hpost)
    · by_cases hfinal : (!Block.preceq st.F B) = true
      · simp only [Protocol.on_block_using, if_neg hfirst, if_pos hfinal] at hpost
        exact False.elim (hpre hpost)
      · by_cases hproposer : B.proposer? ≠ some (E.proposer B.slot)
        · simp only [Protocol.on_block_using, if_neg hfirst, if_neg hfinal,
            if_pos hproposer] at hpost
          exact False.elim (hpre hpost)
        · by_cases hparent : ¬ B.parent.slot < B.slot
          · simp only [Protocol.on_block_using, if_neg hfirst, if_neg hfinal,
              if_neg hproposer, if_pos hparent] at hpost
            exact False.elim (hpre hpost)
          · simp only [Protocol.on_block_using, if_neg hfirst, if_neg hfinal,
              if_neg hproposer, if_neg hparent,
              update_finality_timestamp_block,
              foldl_on_goldfish_vote_checked_timestamp_block]
            simp
  · have hfalse : Protocol.carried_attestations_admissible hc B = false :=
      Bool.eq_false_of_not_eq_true hvalid
    simp only [hfalse, Bool.false_eq_true, if_false] at hpost
    exact False.elim (hpre hpost)

private theorem core_new_body_stamp (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hpre : B ∉ st.bodies)
    (hpost : B ∈ (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).bodies) :
    (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core.timestamp_block B.erase =
      some (st.core.t : Stamp) := by
  unfold Protocol.NamedStore.process_block_core at hpost ⊢
  by_cases hp : B.parent ∉ st.bodies
  · simp only [hp] at hpost
    exact False.elim (hpre hpost)
  · rw [if_neg hp] at hpost ⊢
    let after := Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using S.E current B.erase
        (fun parentState => Protocol.named_transition S.E S.cfg parentState B))
      S.hc st.core B.erase
    change B ∈ (Protocol.NamedStore.commitBlock st after B).bodies at hpost
    change (Protocol.NamedStore.commitBlock st after B).core.timestamp_block B.erase = _
    by_cases hfresh : B.erase ∉ st.core.T ∧ B.erase ∈ after.T
    · unfold Protocol.NamedStore.commitBlock
      rw [if_pos hfresh]
      exact checked_new_block_stamp S.E S.hc st.core B.erase _ hfresh.1 hfresh.2
    · unfold Protocol.NamedStore.commitBlock at hpost ⊢
      rw [if_neg hfresh] at hpost
      exact False.elim (hpre hpost)

/-- A fresh named body admitted through the full named block handler receives
the store clock as its write-once block stamp. Named twin of
`on_block_new_timestamp`. -/
private theorem block_new_body_stamp (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hpre : B ∉ st.bodies)
    (hpost : B ∈
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies) :
    (Protocol.NamedAdmission.on_block_with
      .alsoCarried S.E S.hc S.cfg st B).core.timestamp_block B.erase =
        some (st.core.t : Stamp) := by
  let core := Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B
  have hcore : B ∈ core.bodies := by
    unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried at hpost
    split_ifs at hpost
    · simpa only [rows_bodies] using hpost
    · exact hpost
  have hs := core_new_body_stamp S st B hpre hcore
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · simpa only [rows_block_stamp] using hs
  · exact hs

/-- The engine's proposal duty's own slot, from its `Option`-valued output.
Private companion to `Proofs.Optimistic.proposal_with_slot`, unwrapping
`propose_block_with`'s one fixed `.poolAndCarried` call. -/
private theorem propose_block_with_slot {contract : Protocol.GradeContract V}
    {E : Env V} {hc : Protocol.HealConfig} {cfg : Protocol.HeightConfig}
    {nd : Protocol.Node V} {st : Protocol.NamedStore V} {B : NamedBlock V}
    (h : (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).2 = some B) :
    B.slot = st.core.s := by
  unfold Protocol.NamedDuties.propose_block_with at h
  cases hm : Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st with
  | none => rw [hm] at h; simp at h
  | some B' =>
    rw [hm] at h
    have hBB' : B' = B := Option.some.inj h
    rw [← hBB']
    exact Proofs.Optimistic.proposal_with_slot contract .poolAndCarried E hc nd st hm

/-- The engine's proposal duty's own carried votes, from its `Option`-valued
output. Private companion to `Proofs.Optimistic.proposal_with_gf_votes`. -/
private theorem propose_block_with_gf_votes {contract : Protocol.GradeContract V}
    {E : Env V} {hc : Protocol.HealConfig} {cfg : Protocol.HeightConfig}
    {nd : Protocol.Node V} {st : Protocol.NamedStore V} {B : NamedBlock V}
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

/-- At a firing proposal tick, later same-tick duties preserve the retained
bodies produced by the proposal stage. -/
private theorem tick_bodies_proposal
    (S : Setup V) (v : V) (n : NodeState V) (s : Slot) (hs : 0 < s)
    (hprop : S.E.proposer s = (S.node v).val_index) :
    (on_tick_emit S v n (Protocol.proposal_time S.E s)).1.st.bodies =
      (Protocol.NamedDuties.propose_block_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S n
            (Protocol.proposal_time S.E s)).cache)
        S.E S.hc S.cfg (S.node v)
        (NamedActionReads.confirmationReadFrom S n
          (Protocol.proposal_time S.E s)).st).1.bodies := by
  have hslot : S.E.slotOf (Protocol.proposal_time S.E s) = s :=
    Proofs.Optimistic.slotOf_proposal_time S.E s
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick,
    Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps, hslot,
    NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
    Protocol.NamedStore.setClock,
    Proofs.Optimistic.proposal_time_ne_vote_time S.E s,
    Proofs.Optimistic.proposal_time_ne_support_cutoff S.E s, hprop, hs,
    and_false, and_true, if_false, if_true, Protocol.NamedDuties.attest_with,
    Protocol.NamedAdmission.admit_row]
  split
  · split <;> rfl
  · rfl

/-- If an accepted block keeps a block stamp below a later public cutoff, its
accepting event is strictly before that cutoff. This is the block analogue of
`acceptsAt_gfVote_lt_of_stamp_before`. -/
theorem acceptsAt_block_lt_of_stamp_before_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {i n : Nat}
    {B : NamedBlock V} {t Gamma : Time}
    (hacc : NamedRun.acceptsAt S rho i v (Object.block B) t)
    (hin : i + 1 ≤ n) (hpub : PublicTime S Gamma)
    (hstamp : stampedBefore
      (rho.stateBefore S n v).st.core.timestamp_block Gamma B.erase = true) :
    t < Gamma := by
  have hstamp' : stampedBefore
      (NamedRun.stateBefore S rho n v).st.core.timestamp_block Gamma B.erase = true := hstamp
  obtain ⟨hhandle, hpreProcessed, hpostProcessed⟩ := hacc
  obtain ⟨hindex, e, he, hnode, htime⟩ := hhandle
  simp only [NamedRun.actualHandlesAtIndex, NamedRun.processesAtIndex] at hindex
  have hBpre : B ∉ (NamedRun.stateBefore S rho i v).st.bodies := by
    simpa only [Object.processed, NamedReceipt.processed, decide_eq_false_iff_not]
      using hpreProcessed
  have hBpostFull : B ∈ (NamedRun.stateBefore S rho (i + 1) v).st.bodies := by
    simpa only [Object.processed, NamedReceipt.processed, decide_eq_true_eq]
      using hpostProcessed
  obtain ⟨-, hcarryStamp⟩ :=
    Proofs.NamedBlockStamp.stateBefore_body_stamp_mono S rho v hin hBpostFull
  rcases hindex with ⟨t', htick, hem⟩ | ⟨t', hdeliver⟩
  · have heq : Event.tick v t' = e := Option.some.inj (htick.symm.trans he)
    have htt : t' = t := (congrArg Event.time heq).trans htime
    subst t'
    obtain ⟨⟨hs0, htProp, hpropV⟩, -⟩ :=
      Proofs.HealingSurface.block_mem_on_tick_emit S v (NamedRun.stateBefore S rho i v) t hem
    have hpropIdx : S.E.proposer (S.E.slotOf t) = (S.node v).val_index := by
      rw [hpropV, S.node_val_index]
    have hcallEq := Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hem
    have hbodiesEq := tick_bodies_proposal S v (NamedRun.stateBefore S rho i v)
      (S.E.slotOf t) hs0 hpropIdx
    have hstampEq := on_tick_emit_proposal_timestamp_block S v
      (NamedRun.stateBefore S rho i v) (S.E.slotOf t) hs0 hpropIdx
    rw [← htProp] at hbodiesEq hstampEq
    have hcacheEq : NamedProfile.gradeContract
        (NamedActionReads.confirmationReadFrom S (NamedRun.stateBefore S rho i v) t).cache =
        DecoupledConsensusModel.Protocol.frameContract
          (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc
            (NamedRun.stateBefore S rho i v).st.core.toHealing t
            (NamedRun.stateBefore S rho i v).cache) := rfl
    have hstoreEq : (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S rho i v) t).st =
        Protocol.NamedStore.setClock S.E (NamedRun.stateBefore S rho i v).st t := rfl
    rw [hcacheEq, hstoreEq, hcallEq] at hbodiesEq hstampEq
    dsimp only at hbodiesEq hstampEq
    have hstateEq : (NamedRun.stateBefore S rho (i + 1) v).st =
        (on_tick_emit S v (NamedRun.stateBefore S rho i v) t).1.st := by
      rw [Proofs.NamedRuntime.stateBefore_tick S rho htick]
    have hBpostStage :
        B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg
          (Protocol.NamedStore.setClock S.E (NamedRun.stateBefore S rho i v).st t) B).bodies := by
      rw [← hbodiesEq, ← hstateEq]
      exact hBpostFull
    have hBpreStage :
        B ∉ (Protocol.NamedStore.setClock S.E (NamedRun.stateBefore S rho i v).st t).bodies := by
      simpa only [Protocol.NamedStore.setClock] using hBpre
    have hnewStamp := block_new_body_stamp S
      (Protocol.NamedStore.setClock S.E (NamedRun.stateBefore S rho i v).st t)
      B hBpreStage hBpostStage
    have hclockEq :
        (Protocol.NamedStore.setClock S.E (NamedRun.stateBefore S rho i v).st t).core.t = t :=
      rfl
    rw [hclockEq] at hnewStamp
    have hfinalStamp : (NamedRun.stateBefore S rho (i + 1) v).st.core.timestamp_block B.erase =
        some (t : Stamp) := by
      rw [hstateEq, hstampEq]
      exact hnewStamp
    simp only [stampedBefore, hcarryStamp, hfinalStamp, decide_eq_true_eq] at hstamp'
    exact WithBot.coe_lt_coe.mp hstamp'
  · have heq : Event.deliver v (Object.block B) t' = e :=
      Option.some.inj (hdeliver.symm.trans he)
    have htt : t' = t := (congrArg Event.time heq).trans htime
    subst t'
    have hi : rho.events[i]? = some (Event.deliver v (Object.block B) t) := hdeliver
    have hstate : (NamedRun.stateBefore S rho (i + 1) v).st =
        NamedReceipt.process S (NamedRun.stateBefore S rho i v).st (Object.block B) :=
      Proofs.NamedReceiptCallsBase.delivery_result S rho hi
    have hBpost' : B ∈
        (NamedReceipt.process S (NamedRun.stateBefore S rho i v).st (Object.block B)).bodies := by
      rw [← hstate]
      exact hBpostFull
    have hnewStamp := block_new_body_stamp S
      (NamedRun.stateBefore S rho i v).st B hBpre hBpost'
    have hfinalStamp : (NamedRun.stateBefore S rho (i + 1) v).st.core.timestamp_block B.erase =
        some ((NamedRun.stateBefore S rho i v).st.core.t : Stamp) := by
      rw [hstate]
      exact hnewStamp
    have hclock : (NamedRun.stateBefore S rho i v).st.core.t < Gamma := by
      simp only [stampedBefore, hcarryStamp, hfinalStamp, decide_eq_true_eq] at hstamp'
      exact WithBot.coe_lt_coe.mp hstamp'
    exact processed_lt_of_store_time_lt S adm.toNamedScheduleWellFormed
      hv hi hpub hclock

theorem acceptsAt_block_lt_of_stamp_before
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {i n : Nat}
    {B : NamedBlock V} {t Gamma : Time}
    (hacc : NamedRun.acceptsAt S rho i v (Object.block B) t)
    (hin : i + 1 ≤ n) (hpub : PublicTime S Gamma)
    (hstamp : stampedBefore
      (rho.stateBefore S n v).st.core.timestamp_block Gamma B.erase = true) :
    t < Gamma :=
  acceptsAt_block_lt_of_stamp_before_core S adm.toNamedAdmissibleCore hv hacc hin
    hpub hstamp

theorem find_voteDutyStore_of_source_find_and_mem
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {source : Protocol.Store V} {s : Slot} {w : V}
    (hw : w ∈ rho.honest) {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? source.T u.head = some H)
    (hHmem : H ∈ (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T) :
    Block.find? (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T u.head = some H := by
  obtain ⟨nw, hnw, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (Protocol.vote_time S.E (s + 1))
  have htargetT : (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T =
      (rho.stateBefore S nw w).st.core.T := by
    show (NamedRun.stateBeforeTime S rho
      (Protocol.vote_time S.E (s + 1)) w).st.core.T = _
    rw [show NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w =
      NamedRun.stateBefore S rho nw w from congrFun hnw w]
  have hHroot : H.root = u.head := by
    unfold Block.find? pickUnique? at hfind
    split at hfind
    · rename_i hex
      rw [Option.some_inj] at hfind
      subst hfind
      exact of_decide_eq_true (Finset.choose_property _ _ hex)
    · exact absurd hfind (by simp)
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (rho.stateBefore S nw w).st :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho nw w).1.1.1
  have hrun : ∀ C ∈ (rho.stateBefore S nw w).st.bodies, RunBlock S rho C :=
    fun C hC => Proofs.Bridges.runBlock_of_stateBefore_mem S hw hC
  have hinj := Proofs.Bridges.rootInjectiveBelow_of_runBlocks S
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree hrun
  rw [← hcoh.1] at hinj
  rw [← hHroot]
  apply Proofs.Optimistic.find?_eq_some_of_unique hHmem
  intro Y hY hroot
  have hYmem : Y ∈ (rho.stateBefore S nw w).st.core.T := by
    rw [← htargetT]
    exact hY
  have hHmem' : H ∈ (rho.stateBefore S nw w).st.core.T := by
    rw [← htargetT]
    exact hHmem
  exact hinj Y H ⟨Y, hYmem, Block.preceq_self Y⟩
    ⟨H, hHmem', Block.preceq_self H⟩ hroot

/-! ## The next vote duty's canonical anchor and candidate tree -/



/-! ## Target-pool vote settlement -/

/-- Every stored target-pool vote has an acceptance event strictly before the
next vote duty. -/
theorem targetPoolVoteAcceptedBeforeVote
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} {s : Slot} {u : GoldfishVote V}
    (hu : u ∈ (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) :
    ∃ (i : Nat) (t : Time), NamedRun.acceptsAt S rho i w (Object.gfVote u) t ∧
      u.slot = s ∧ Protocol.proposal_time S.E s ≤ t ∧
      t < Protocol.vote_time S.E (s + 1) := by
  let Γ := Protocol.vote_time S.E (s + 1)
  obtain ⟨n, hn, hbefore⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed Γ
  have huPool : u ∈ (NamedRun.stateBefore S rho n w).st.core.pool s := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn, Γ] using hu
  have huList : u ∈ (NamedRun.stateBefore S rho n w).st.core.gf_votes s := by
    simpa only [Protocol.Store.pool, List.mem_toFinset] using huPool
  have hus : u.slot = s :=
    (poolStamps_stateBefore S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w n).slot
      s u huList
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




/-- Processing a slot-`(s+1)` carrier before the target vote duty settles each
carried slot-`s` vote in the target pool. The exact vote can be absent only when
the checked two-vote cap already detects its validator as equivocating.

The proposal-tick branch needs no network premise: a proposal copies its
carried votes from the proposer's existing slot-`s` pool
(`Proofs.Optimistic.proposal_with_gf_votes`, via `propose_block_with_gf_votes`). The
delivery branch reduces to `Proofs.Optimistic.block_carried_beforeCutoff_or_equivocates`
(`NamedGoldfishVotePool.lean`), the named twin of
`Protocol.on_block_carried_beforeCutoff_or_equivocates` earlier's own proof
used. -/
theorem targetCarrierVote_settledInPool
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
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
    set before := (NamedActionReads.confirmationReadFrom S pre t).st with hbeforedef
    have hcslot : C.slot = before.core.s := propose_block_with_slot hpropEq
    have hcgf : C.gf_votes = before.core.gf_votes (before.core.s - 1) :=
      propose_block_with_gf_votes hpropEq
    have hcslot' : C.slot = s + 1 := (Proofs.NamedWire.erase_slot C).symm.trans hCslotB
    have hbeforeS : before.core.s = s + 1 := hcslot.symm.trans hcslot'
    have hu' : u ∈ C.gf_votes := by rw [← Proofs.NamedWire.erase_goldfish_votes]; exact huC
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
      apply Protocol.delivery_store_slot_before_freeze S adm
        (w := w) (i := i) (o := Object.block C) (s := s + 1) (t := t)
      · exact hw
      · exact hi
      · rw [← hBslot]
        exact hlo
      · exact lt_trans hhi (lt_trans
          (by
            rw [← Proofs.Optimistic.vote_time_add_delta]
            exact Int.lt_add_of_pos_right _ S.E.Δ_pos)
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
      simpa only [Object.processed, NamedReceipt.processed, decide_eq_false_iff_not]
        using hpreProcessed
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
    have hstamps : Protocol.PoolStamps pre.core :=
      poolStamps_stateBefore S adm.toNamedScheduleWellFormed w i
    have hlocal := Proofs.Optimistic.block_carried_beforeCutoff_or_equivocates S pre C u Γ
      hstamps hCpre hCpost huC hcommittee hfresh hfuture hclock
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





/-! ## Canonical vote-duty candidate -/






#print axioms stampedBefore_block_of_resolution
#print axioms on_tick_emit_proposal_timestamp_block
#print axioms find_voteDutyStore_of_source_find_and_mem

end HonestWeightMajority

end Protocol
end DecoupledConsensusModel

end
