module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainSupporter
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The next slot entry state, obligation by obligation

`MovingChainSupporterRun` closes the one protocol step the slot fold was
missing: the slot-`c` confirmation the window absorbs is visible at the
slot-`(c+1)` vote read, so the slot-`(c+1)` vote cone sits above the WINDOW
endpoint and not merely above the entry endpoint.

This module turns that into the three forward obligations of the NEXT entry
state. All three are read at instants after the next slot's proposal cursor,
so all three are proved from the pre-entry half of that state, which the window
step produces before the record exists.

* `confOutcome_atPrev` at the pre-entry state certifies every honest
  confirmation of the previous slot: it is genuine and lands above `Prev`.
  This is the same statement `MovingChainFoldRun` proves for a full entry
  state, restated on the half of the record its proof actually reads.
* `genuineConfirmation_preceq_voteDutyHead` composes that with the supporter
  visibility and the capture lemma: an absorbed confirmation is at or below
  every honest vote head of the following slot.
* The two `confCompatible` suppliers are the Byzantine and honest readings of
  the last step. With a Byzantine proposer the endpoint does not move and
  `Prev ⪯ D` is already compatibility; with an honest proposer the transfer
  makes the vote head the proposal, so `D ⪯ proposal`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 0. Schedule separations

`MovingChainFoldRun` keeps its normalised instants private, so the one
separation this module needs is restated here. Every duty instant is
`(4 * slot + offset) * Δ`, and round actions are the `+6` instants. -/



private theorem int_le_add_two' {x d : Int} (hd : 0 < d) :
    x ≤ x + 2 * d := by omega

private theorem int_add_le_add_two' {x d : Int} (hd : 0 < d) :
    x + d ≤ x + 2 * d := by omega

/-- `t_{s+1} + Δ ≤ t_s + 6Δ`: the next slot's vote read precedes this slot's
confirmation evaluation. -/
private theorem voteTimeSucc_le_confirmationTime' (E : Env V) (s : Slot) :
    Protocol.vote_time E (s + 1) ≤ Protocol.confirmation_time E s := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ]
  simp only [Protocol.vote_time, Protocol.support_cutoff]
  exact int_add_le_add_two' E.Δ_pos

/-- `t_{s+1} ≤ t_s + 6Δ`: the next slot's proposal precedes this slot's
confirmation evaluation. -/
private theorem proposalTimeSucc_le_confirmationTime' (E : Env V) (s : Slot) :
    Protocol.proposal_time E (s + 1) ≤ Protocol.confirmation_time E s := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ]
  simp only [Protocol.proposal_time, Protocol.support_cutoff]
  exact int_le_add_two' E.Δ_pos

private theorem proposal_time_normal' (E : Env V) (s : Slot) :
    Protocol.proposal_time E s = (4 * (s : Time) + 0) * E.Δ := by
  unfold Protocol.proposal_time Env.t slotStart
  ring



private theorem view_freeze_normal' (E : Env V) (s : Slot) :
    Protocol.view_freeze E s = (4 * (s : Time) + 3) * E.Δ := by
  unfold Protocol.view_freeze Env.t slotStart
  ring

private theorem view_freeze_lt_proposal_time_succ' (E : Env V) (s : Slot) :
    Protocol.view_freeze E s < Protocol.proposal_time E (s + 1) := by
  rw [view_freeze_normal', proposal_time_normal']
  refine Int.mul_lt_mul_of_pos_right ?_ E.Δ_pos
  have hcast : ((s + 1 : Nat) : Int) = (s : Int) + 1 := by push_cast; ring
  rw [hcast]
  omega

private theorem proposal_time_le_view_freeze' (E : Env V) (s : Slot) :
    Protocol.proposal_time E s ≤ Protocol.view_freeze E s := by
  rw [proposal_time_normal', view_freeze_normal']
  exact Int.mul_le_mul_of_nonneg_right (by omega) (le_of_lt E.Δ_pos)

private theorem proposal_time_lt_succ' (E : Env V) (s : Slot) :
    Protocol.proposal_time E s < Protocol.proposal_time E (s + 1) :=
  lt_of_le_of_lt (proposal_time_le_view_freeze' E s)
    (view_freeze_lt_proposal_time_succ' E s)

omit [DecidableEq V] [Fintype V] in
private theorem inclusive_le_strict_of_lt'
    (rho : Run V) {t0 t1 : Time} (hlt : t0 < t1) :
    inclusiveEventIndex rho t0 ≤ strictEventIndex rho t1 := by
  unfold inclusiveEventIndex strictEventIndex
  exact (List.monotone_filter_right rho.events (fun e he => by
    simp only [decide_eq_true_eq] at he ⊢
    exact lt_of_le_of_lt he hlt)).length_le


omit [DecidableEq V] [Fintype V] in
/-- An event index is determined by its event. -/
private theorem eventIndex_unique'
    {rho : Run V} (hnodup : rho.events.Nodup) {i j : Nat} {e : Event V}
    (hi : rho.events[i]? = some e) (hj : rho.events[j]? = some e) :
    i = j := by
  obtain ⟨hiLen, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjLen, hje⟩ := List.getElem?_eq_some_iff.mp hj
  have hfin : (⟨i, hiLen⟩ : Fin rho.events.length) = ⟨j, hjLen⟩ :=
    (List.nodup_iff_injective_getElem.mp hnodup) (by simp only [hie, hje])
  simpa using congrArg Fin.val hfin

/-- An event at or after the inclusive cursor of `t0` happens strictly after
`t0`. -/
private theorem eventTime_gt_of_inclusive_le'
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {t0 : Time} {j : Nat} {e : Event V}
    (hj : inclusiveEventIndex rho t0 ≤ j)
    (hget : rho.events[j]? = some e) :
    t0 < e.time := by
  have hfalse := Proofs.Optimistic.filter_false_of_index_ge S sch _
    (Proofs.Optimistic.downward_le t0)
    (by simpa only [inclusiveEventIndex] using hj) hget
  simpa only [decide_eq_false_iff_not, not_le] using hfalse



/-! ## 1. Certifying the previous slot's confirmations at the pre-entry state -/


/-
/-- Every honest slot-`c` confirmation selection is genuine and lands above the
previous endpoint of the slot-`(c+1)` window.

This is `MovingSlotEntryState.confOutcome_atPrev` on the pre-entry half of the
record; the proof reads nothing else, and the next entry state has that half
before it has its obligations. -/
theorem MovingSlotPreEntry.confOutcome_atPrev
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End: Block V}
    (hentry: MovingSlotPreEntry S rho t1 M0 (c + 1) Prev End)
    (hc: 0 < c)
    {r: Round}
    (hround: S.hc.round_of (c + 1) = r + 1)
    (ht1: t1 ≤ S.a r)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor: Protocol.confirmation_time S.E c ≤ rho.horizon)
    {w: V} (hw: w ∈ rho.honest):
    GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc (Proofs.Optimistic.confStore S rho w c) c
        (movingSlotConfirmationOutput S rho c w) ∧
      Block.Preceq Prev (movingSlotConfirmationOutput S rho c w):= by
  obtain ⟨EndAt, hhistory, hprev, _hEnd⟩:= hentry.prevEndpoint
  set k:= strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) with hk
  have hpre: MovingFrontierChainState S rho t1 M0
      (strictEventIndex rho t1) k EndAt:=
    hhistory.prefix (strictEventIndex_mono rho hentry.startTime)
      (strictEventIndex_le_inclusiveEventIndex rho _)
  have hvotes: Proofs.Optimistic.HonestVotesCone S rho c
      (fun X => Block.Preceq (EndAt k) X):= by
    rw [hprev]
    simpa only [Nat.add_sub_cancel] using hentry.prevVotes
  let pre:= rho.storeBeforeTime S w (Protocol.confirmation_time S.E c)
  have hrootRaw: Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) (EndAt k):=
    hpre.confRoot_preceq_endpointAtCursor S adm hfb (Nat.le_refl k) hw
      hentry.startTime
  have hband: pre.h_max - 1 ≤ (derived_state S.E S.cfg (EndAt k)).h:=
    hpre.confFrontier_sub_one_le_endpointAtCursor S adm hfb
      (Nat.le_refl k) hw
  have hroot: Block.Preceq
      (confRoot (Proofs.Optimistic.confStore S rho w c)) (EndAt k):= by
    simpa only [confRoot, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      pre, Run.storeBeforeTime] using hrootRaw
  have hresolve:= headsResolveIn_confStore_of_postHealingCone
    S adm hw hpostVote
      ((support_cutoff_le_confirmation_time S.E c).trans hslotHor)
      hroot hvotes
  have hpositive: 0 < ((S.E.committee c) ∩ rho.honest).card:= by
    have hcc:= hcom c
    omega
  obtain ⟨x, hx⟩:= Finset.card_pos.mp hpositive
  obtain ⟨X, hEndX, hXrun, hXemit⟩:=
    hvotes x (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hx).1
  have hXmem: X ∈ (Proofs.Optimistic.confStore S rho w c).T:=
    Proofs.HealingLemmas.find?_mem
      ((hresolve X ⟨x, (Finset.mem_inter.mp hx).2,
        (Finset.mem_inter.mp hx).1, hXrun, hXemit⟩).1)
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node w) pre:= by
    simpa only [pre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (Protocol.confirmation_time S.E c) w)
  have hpc: ParentClosed pre:=
    parentClosed_depReachable S.E S.hc S.cfg (S.node w) pre hdep
  have hmem: EndAt k ∈ pre.T:= by
    apply Proofs.Records.mem_of_preceq ((parentClosed_iff pre).mp hpc).2 (EndAt k) X
    · simpa only [pre, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hXmem
    · exact hEndX
  have hFJ: Block.Preceq pre.F pre.J:=
    finalizedPrecedesJustifiedInvariant S.E S.hc S.cfg (S.node w) pre
      (Proofs.Bridges.reachableStore_of_depReachableStore
        S.E S.hc S.cfg (S.node w) hdep)
  have hagree: DerivedStateAgrees S.E S.cfg pre:=
    derivedStateAgrees_depReachable S.E S.hc S.cfg (S.node w) pre hdep
  have hbandStore: pre.h_max - 1 ≤ (pre.σ (EndAt k)).h:= by
    rw [hagree (EndAt k) hmem]
    exact hband
  have hFEnd: Block.Preceq pre.F (EndAt k):=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st:= pre.toHealing.toFG) hFJ)
      hrootRaw
  have hcandidate: EndAt k ∈ confTree (Proofs.Optimistic.confStore S rho w c):= by
    have hfull: EndAt k ∈ Protocol.get_filtered_block_tree
        pre.toHealing.toFG:= by
      simpa only [Protocol.get_filtered_block_tree] using
        mem_get_filtered_block_tree_from_of_selfViable pre.toHealing.toFG
          pre.T hmem hFEnd hrootRaw hbandStore
    simpa only [confTree, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      pre, Run.storeBeforeTime] using hfull
  have hread: S.hc.Γ_0 S.E.Δ (r + 1) ≤ Protocol.confirmation_time S.E c:=
    Γ_0_le_confirmation_time_of_round_succ S hround
  have hbeforeConf: S.a r < Protocol.confirmation_time S.E c:=
    (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos).trans_le
      ((action_add_delta_le_next_Γ_neg1 S r).trans
        ((le_of_lt (Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1))).trans hread))
  have hactionHor: S.a r ≤ rho.horizon:=
    (le_of_lt (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos)).trans
      ((action_add_delta_le_next_Γ_neg1 S r).trans hcut)
  have hupper:= hpre.previousActionCarriersPreceqAtRead S adm ht1 hactionHor
    (action_time_lt_proposal_of_lt_confirmation' S hbeforeConf)
    (Nat.le_refl k)
  have hanchorRaw:= readAnchor_preceq_of_previousActionCeiling
    S adm hfb hpostAction hcut hread hw
    (by simpa only [pre] using hmem) hrootRaw hupper
  have hanchor: Block.Preceq
      (confAnchor S.E S.hc (Proofs.Optimistic.confStore S rho w c)) (EndAt k):= by
    rw [confAnchor]
    have hroundSt: S.hc.round_of
        (Proofs.Optimistic.confStore S rho w c).s = r + 1:= by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Proofs.Optimistic.slotOf_confirmation_time] using hround
    rw [hroundSt]
    simpa only [pre, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore]
      using hanchorRaw
  have hout:= genuineConfirmationAndPreceq_of_postHealingCone
    S adm hcom hc hpostVote hslotHor hw hvotes hroot hanchor hcandidate
  rw [hprev] at hout
  simpa only [movingSlotConfirmationOutput] using hout
-/


/-! ## 2. The absorbed confirmation reaches the next slot's vote head -/


/-
/-- **Every honest slot-`c` genuine confirmation is at or below every honest
slot-`(c+1)` vote head.**

The confirmation is evaluated at `t_{c+1} + 2Δ`, one instant AFTER the
slot-`(c+1)` vote read at `t_{c+1} + Δ`, so store monotonicity cannot make it
visible there. Its own honest slot-`c` supporter can: the supporter's head was
processed before its slot-`c` vote and is admitted at every honest node before
`t_c + 2Δ`, the processed tree is ancestor-closed, and the confirmation is an
ancestor of that head. With the confirmation visible, above `Prev`, below the
read anchor's chain and inside the local frontier band, the capture lemma
applies. -/
theorem MovingSlotPreEntry.genuineConfirmation_preceq_voteDutyHead
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End: Block V}
    (hentry: MovingSlotPreEntry S rho t1 M0 (c + 1) Prev End)
    (hc: 0 < c)
    {r: Round}
    (hround: S.hc.round_of (c + 1) = r + 1)
    (ht1: t1 ≤ S.a r)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hpostProp: S.E.t_GST ≤ Protocol.proposal_time S.E c)
    (hslotHor: Protocol.confirmation_time S.E c ≤ rho.horizon)
    {v: V} (hv: v ∈ rho.honest) {D: Block V}
    (hgenuine: GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc
      (Proofs.Optimistic.confStore S rho v c) c D)
    {w: V} (hw: w ∈ rho.honest):
    Block.Preceq D (voteDutyHead S rho w (c + 1)):= by
  have hprevVotes: Proofs.Optimistic.HonestVotesCone S rho c
      (fun X => Block.Preceq Prev X):= by
    simpa only [Nat.add_sub_cancel] using hentry.prevVotes
  have hDout: movingSlotConfirmationOutput S rho c v = D:= hgenuine.selected
  have hPrevD: Block.Preceq Prev D:= by
    have hout:= (hentry.confOutcome_atPrev S adm hcom hfb hc hround ht1
      hpostAction hcut hpostVote hslotHor hv).2
    rwa [hDout] at hout
  have hvoteHorC: Protocol.vote_time S.E c ≤ rho.horizon:=
    (voteTime_le_confirmationTime' S.E c).trans hslotHor
  have hresolve:= headsResolveIn_confStore_of_postHealingCone
    S adm hv hpostVote
      ((support_cutoff_le_confirmation_time S.E c).trans hslotHor)
      (hentry.confRoot_preceq_prev S adm hfb hv)
      hprevVotes
  obtain ⟨x, hx, hxc, hDx⟩:= genuineConfirmation_exists_honestSupporter
    S adm hcom hc hpostVote hslotHor hv hresolve hgenuine
  have hhead:= honestHead_voteDutyHead S adm hc hvoteHorC hx hxc
  have hrootVoteRaw:=
    hentry.voteRoot_preceq_prev S adm hfb hw
  have hrootVote: Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG) Prev:= by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hrootVoteRaw
  have havailable:= honestHeadsAvailableBefore_of_postHealingCone_atVoteDuty
    S adm hw hpostVote
      ((support_cutoff_le_confirmation_time S.E c).trans hslotHor)
      hrootVote hprevVotes
  have hprocessed:= voterProcessed_of_availableBefore_of_honestHead
    S adm havailable hhead hDx
  let pre:= rho.storeBeforeTime S w (Protocol.vote_time S.E (c + 1))
  have hDpre: D ∈ pre.T:= by
    have hdata:= hprocessed
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    simpa only [pre, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hdata.1
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node w) pre:= by
    simpa only [pre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (Protocol.vote_time S.E (c + 1)) w)
  have hagree: DerivedStateAgrees S.E S.cfg pre:=
    derivedStateAgrees_depReachable S.E S.hc S.cfg (S.node w) pre hdep
  have hband: (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).h_max - 1 ≤
      ((Proofs.Optimistic.voteDutyStore S rho w (c + 1)).σ D).h:= by
    have hbandPre: pre.h_max - 1 ≤ (pre.σ D).h:= by
      rw [hagree D hDpre]
      exact (hentry.voteFrontier_sub_one_le_prevHeight S adm hfb hw).trans
        (Protocol.derived_h_mono S.E S.cfg hPrevD)
    simpa only [pre, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hbandPre
  exact genuineConfirmation_preceq_nextVoteDutyHead_of_endpointBand
    S adm hv hw hpostProp hslotHor hgenuine hPrevD
    (hentry.voteAnchor_preceq_prev S adm hcom hfb hround ht1 hpostAction
      hcut hpostVote hslotHor hw)
    hprocessed hband
-/

/-! ## 3. The `confCompatible` obligation of the next entry state -/


/-
/-- `confCompatible` in a Byzantine-proposer slot, where the endpoint does not
move: the previous slot's genuine confirmations are already above `Prev`, and
that is compatibility. -/
theorem MovingSlotPreEntry.confCompatible_byzantine
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End: Block V}
    (hentry: MovingSlotPreEntry S rho t1 M0 (c + 1) Prev End)
    (hc: 0 < c)
    {r: Round}
    (hround: S.hc.round_of (c + 1) = r + 1)
    (ht1: t1 ≤ S.a r)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor: Protocol.confirmation_time S.E c ≤ rho.horizon):
    ∀ u ∈ rho.honest, ∀ D: Block V,
      GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc (Proofs.Optimistic.confStore S rho u c) c D →
        Block.compatible D Prev = true:= by
  intro u hu D hgenuine
  have hDout: movingSlotConfirmationOutput S rho c u = D:= hgenuine.selected
  have hPrevD: Block.Preceq Prev D:= by
    have hout:= (hentry.confOutcome_atPrev S adm hcom hfb hc hround ht1
      hpostAction hcut hpostVote hslotHor hu).2
    rwa [hDout] at hout
  exact Block.compatible_of_preceq_common (Block.preceq_self D) hPrevD
-/


/-
/-- `confCompatible` in an honest-proposer slot: the transfer makes every
honest vote head the slot proposal, and the previous slot's genuine
confirmations are at or below every honest vote head. -/
theorem MovingSlotPreEntry.confCompatible_honest
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End: Block V}
    (hentry: MovingSlotPreEntry S rho t1 M0 (c + 1) Prev End)
    (hc: 0 < c)
    {r: Round}
    (hround: S.hc.round_of (c + 1) = r + 1)
    (ht1: t1 ≤ S.a r)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hpostProp: S.E.t_GST ≤ Protocol.proposal_time S.E c)
    (hslotHor: Protocol.confirmation_time S.E c ≤ rho.horizon)
    (hheadEq: ∀ u ∈ rho.honest, voteDutyHead S rho u (c + 1) = End)
    {w: V} (hw: w ∈ rho.honest):
    ∀ u ∈ rho.honest, ∀ D: Block V,
      GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc (Proofs.Optimistic.confStore S rho u c) c D →
        Block.compatible D End = true:= by
  intro u hu D hgenuine
  have hDhead:= hentry.genuineConfirmation_preceq_voteDutyHead
    S adm hcom hfb hc hround ht1 hpostAction hcut hpostVote hpostProp
    hslotHor hu hgenuine hw
  rw [hheadEq w hw] at hDhead
  exact Block.compatible_of_preceq_common hDhead (Block.preceq_self End)
-/

/-! ## 4. Read-time root-side geometry

`MovingChainStateRun` proves the endpoint's activity and the activity of the
whole root-to-endpoint path at an EXACT event index, with the local frontier
bounded by the honest frontier up to that index. A slot window reads at an
instant strictly after the cursor its endpoint was fixed at, so that route is
not available: the local frontier at the read may already have risen. What is
available there is the crossing-row band of the moving history, which is what
these two forms take as input instead. -/

/-- A block at the local frontier band, below the selected root's chain and
processed, is active at the read. -/
theorem storeBeforeTime_mem_filtered_of_band
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t : Time} {v : V} {A : NamedBlock V}
    (hmem : A ∈ (rho.storeBeforeTime S v t).bodies)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v t).toHealing.toFG) A.erase)
    (hband : (rho.storeBeforeTime S v t).core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg A).h) :
    A.erase ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S v t).toHealing.toFG := by
  let st := (rho.storeBeforeTime S v t).core
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (rho.storeBeforeTime S v t) :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).1.1.1
  have hmemCore : A.erase ∈ st.T := by
    have htree := hcoh.1
    rw [htree]
    exact Finset.mem_image.mpr ⟨A, hmem, rfl⟩
  have hFJ : Block.Preceq st.F st.J := by
    simpa only [st, Run.storeBeforeTime] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho t v
  have hfloor : st.h_max - 1 ≤ (st.σ A.erase).h := by
    have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho t v A hmem
    have hview' : st.σ A.erase = Protocol.derive_named S.E S.cfg A := by
      simpa only [st, Run.storeBeforeTime] using hview
    rw [hview']
    simpa only [st, Run.storeBeforeTime] using hband
  have hFA : Block.Preceq st.F A.erase :=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st := st.toHealing.toFG) hFJ)
      (by simpa only [st, Run.storeBeforeTime] using hroot)
  simpa only [Protocol.get_filtered_block_tree] using
    mem_get_filtered_block_tree_from_of_selfViable st.toHealing.toFG st.T
      hmemCore hFA
      (by simpa only [st, Run.storeBeforeTime] using hroot) hfloor

/-- Every block between the selected root and a band block is active at the
read. The band block is the viability witness for the whole path. -/
theorem storeBeforeTime_path_mem_filtered_of_band
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t : Time} {v : V} {A D : NamedBlock V}
    (hmem : A ∈ (rho.storeBeforeTime S v t).bodies)
    (hband : (rho.storeBeforeTime S v t).core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg A).h)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v t).toHealing.toFG) D.erase)
    (hDA : Block.Preceq D.erase A.erase) :
    D.erase ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S v t).toHealing.toFG := by
  let st := (rho.storeBeforeTime S v t).core
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (rho.storeBeforeTime S v t) :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).1.1.1
  have hmemCore : A.erase ∈ st.T := by
    rw [hcoh.1]
    exact Finset.mem_image.mpr ⟨A, hmem, rfl⟩
  have hpc : ParentClosed st := by
    simpa only [st, Run.storeBeforeTime] using
      Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho t v
  have hDmem : D.erase ∈ st.T := by
    apply Proofs.Records.mem_of_preceq ((parentClosed_iff st).mp hpc).2 D.erase A.erase
    · exact hmemCore
    · exact hDA
  have hFJ : Block.Preceq st.F st.J := by
    simpa only [st, Run.storeBeforeTime] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho t v
  have hFD : Block.Preceq st.F D.erase :=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st := st.toHealing.toFG) hFJ)
      (by simpa only [st, Run.storeBeforeTime] using hroot)
  have hfloor : st.h_max - 1 ≤ (st.σ A.erase).h := by
    have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho t v A hmem
    have hview' : st.σ A.erase = Protocol.derive_named S.E S.cfg A := by
      simpa only [st, Run.storeBeforeTime] using hview
    rw [hview']
    simpa only [st, Run.storeBeforeTime] using hband
  have hV : D.erase ∈ Protocol.V_tree st.toHealing.toFG := by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
    exact ⟨⟨hDmem, hFD⟩, A.erase,
      hmemCore, hDA, hfloor⟩
  exact Proofs.Records.mem_filtered_of_mem_V_tree hV
    (by simpa only [st, Run.storeBeforeTime] using hroot)

/-! ## 5. The primed Goldfish inputs at the pre-entry state -/


/-
/-- The primed Goldfish vote input at the slot-`(c+1)` vote read, with the
previous endpoint as pivot.

Every clause is a fact about the previous endpoint at that read: the selected
root is below it, it is inside the frozen processed view because the slot-`c`
cone made every honest head available, its whole root-side path is active
because it sits at the local frontier band, and the read anchor is below it. -/
theorem MovingSlotPreEntry.voteInputs
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End: Block V}
    (hentry: MovingSlotPreEntry S rho t1 M0 (c + 1) Prev End)
    {r: Round}
    (hround: S.hc.round_of (c + 1) = r + 1)
    (ht1: t1 ≤ S.a r)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor: Protocol.confirmation_time S.E c ≤ rho.horizon)
    {w: V} (hw: w ∈ rho.honest):
    GoldfishConeVoteInputs' S rho c Prev w:= by
  have hprevVotes: Proofs.Optimistic.HonestVotesCone S rho c
      (fun X => Block.Preceq Prev X):= by
    simpa only [Nat.add_sub_cancel] using hentry.prevVotes
  have hrootRaw:= hentry.voteRoot_preceq_prev S adm hfb hw
  have hroot: Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG) Prev:= by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hrootRaw
  have havailable:= honestHeadsAvailableBefore_of_postHealingCone_atVoteDuty
    S adm hw hpostVote
      ((support_cutoff_le_confirmation_time S.E c).trans hslotHor)
      hroot hprevVotes
  have hprocessed:= Protocol.voterProcessedConeEndpoint_of_availableBefore
    S adm hcom havailable hprevVotes
  have hbandRaw:= hentry.voteFrontier_sub_one_le_prevHeight S adm hfb hw
  have hmemRaw: Prev ∈
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (c + 1))).T:= by
    have hdata:= hprocessed
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hdata.1
  have hfilteredRaw:= storeBeforeTime_mem_filtered_of_band S adm hmemRaw
    hrootRaw hbandRaw
  refine voteInputs_of_rootSideWithPath S adm hw hprocessed ?_ (Or.inl
    ⟨hroot, ?_, ?_⟩) ?_
  · have hmaxRaw: (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (c + 1))).h_max ≤
        (derived_state S.E S.cfg Prev).h + 1:=
      Nat.sub_le_iff_le_add.mp hbandRaw
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hmaxRaw
  · simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hfilteredRaw
  · intro D hrootD hDPrev
    have hrootDRaw: Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S w
            (Protocol.vote_time S.E (c + 1))).toHealing.toFG) D:= by
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hrootD
    have hpathRaw:= storeBeforeTime_path_mem_filtered_of_band S adm
      hmemRaw hbandRaw hrootDRaw hDPrev
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hpathRaw
  · exact Block.compatible_of_preceq_common
      (hentry.voteAnchor_preceq_prev S adm hcom hfb hround ht1 hpostAction
        hcut hpostVote hslotHor hw)
      (Block.preceq_self Prev)
-/


/-
/-- The slot-`(c+1)` vote cone above the previous endpoint.

In a Byzantine-proposer slot the endpoint does not move, so this is the `votes`
obligation of the next entry state. -/
theorem MovingSlotPreEntry.votesCone_prev
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End: Block V}
    (hentry: MovingSlotPreEntry S rho t1 M0 (c + 1) Prev End)
    (hc: 0 < c)
    {r: Round}
    (hround: S.hc.round_of (c + 1) = r + 1)
    (ht1: t1 ≤ S.a r)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor: Protocol.confirmation_time S.E c ≤ rho.horizon):
    Proofs.Optimistic.HonestVotesCone S rho (c + 1)
      (fun X => Block.Preceq Prev X):= by
  have hprevVotes: Proofs.Optimistic.HonestVotesCone S rho c
      (fun X => Block.Preceq Prev X):= by
    simpa only [Nat.add_sub_cancel] using hentry.prevVotes
  have hstep: ∀ u ∈ rho.honest,
      Block.Preceq Prev (voteDutyHead S rho u (c + 1)):= by
    intro u hu
    exact goldfishCone_step' S adm hcom hc hpostVote hslotHor hprevVotes hu
      (hentry.voteInputs S adm hcom hfb hround ht1 hpostAction hcut
        hpostVote hslotHor hu)
  intro u hu huc
  obtain ⟨hrun, hemit⟩:= voteDutyHead_runBlock_and_emits S adm
    (Nat.succ_pos c)
    ((voteTimeSucc_le_confirmationTime' S.E c).trans hslotHor) hu huc
  exact ⟨voteDutyHead S rho u (c + 1), hstep u hu, hrun, hemit⟩
-/

/-! ## 6. The slot step with a Byzantine next proposer

The endpoint does not move across the next proposal, so the next entry state
repeats the window endpoint in both slots. All three obligations come from the
pre-entry half of that state, which the window fold produces first. -/


/-
/-- The pre-entry half of the next slot's entry state, Byzantine proposer. -/
theorem MovingSlotEntryState.nextPreEntry_byzantine
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End Next: Block V}
    (hentry: MovingSlotEntryState S rho t1 M0 (c + 1) Prev End)
    (hc: 0 < c)
    {r: Round}
    (hround: S.hc.round_of (c + 1) = r + 1)
    (ht1: t1 ≤ S.a r)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hpostProp: S.E.t_GST ≤ Protocol.proposal_time S.E c)
    (hslotHor: Protocol.confirmation_time S.E c ≤ rho.horizon)
    (hfrontier: MovingSlotFrontierAt S rho c End Next)
    (hfacts: MovingSlotWindowFacts S rho (c + 1) End Next)
    (hbyz: S.E.proposer (c + 2) ∉ rho.honest)
    {v: V} (hv: v ∈ rho.honest)
    (hhorSC: Protocol.support_cutoff S.E (c + 1) ≤ rho.horizon):
    MovingSlotPreEntry S rho t1 M0 (c + 2) Next Next:= by
  obtain ⟨EndAt, hhistory, _hprev, hEndAt⟩:= hentry.prevEndpoint
  have hrunE: RunBlock S rho End:= hentry.endpointRun
  have hrunN: RunBlock S rho Next:=
    hfrontier.runBlock S adm hrunE
  obtain ⟨End', _hlow', hhigh', hstate'⟩:=
    hhistory.through_slotWindow_byzantineProposer S adm (Nat.succ_pos c)
      hEndAt hrunE hrunN hfacts hbyz hv hhorSC
  have hfreezeStrict:
      inclusiveEventIndex rho (Protocol.view_freeze S.E (c + 1)) ≤
        strictEventIndex rho (Protocol.proposal_time S.E (c + 1 + 1)):=
    inclusive_le_strict_of_lt' rho
      (view_freeze_lt_proposal_time_succ' S.E (c + 1))
  have hcone:= hentry.windowVotesCone S adm hcom hfb hc hround ht1
    hpostAction hcut hpostVote hpostProp hslotHor hfrontier
  exact
    { startTime:= hentry.startTime.trans
        (le_of_lt (proposal_time_lt_succ' S.E (c + 1)))
      prevEndpoint:= ⟨End', hstate', hhigh' _ hfreezeStrict,
        hhigh' _ (hfreezeStrict.trans
          (strictEventIndex_le_inclusiveEventIndex rho _))⟩
      prevVotes:= hcone }
-/

/-! ## 7. Per-slot schedule data, and the Byzantine step

The window lemmas all take the same block of schedule and horizon facts about
one slot. Bundling them keeps the step and the iteration readable; the bundle
is internal to the fold and is not part of the finality hand-off. -/

/-- The schedule and horizon data one slot window consumes. -/
structure MovingSlotWindowData
    (S : Setup V) (rho : Run V) (t1 : Time) (M0 : Height) (c : Slot) :
    Prop where
  pos : 0 < c
  round : ∃ r : Round, S.hc.round_of (c + 1) = r + 1 ∧ t1 ≤ S.a r ∧
    S.E.t_GST ≤ S.a r ∧ S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon
  postVote : S.E.t_GST ≤ Protocol.vote_time S.E c
  postProp : S.E.t_GST ≤ Protocol.proposal_time S.E c
  slotHor : Protocol.confirmation_time S.E c ≤ rho.horizon

/-- The N-history pre-entry half used while building the next N entry. -/
structure MovingSlotPreEntryN
    (S : Setup V) (rho : Run V) (t1 : Time) (M0 : Height)
    (s : Slot) (Prev End : Block V) : Prop where
  startTime : t1 ≤ Protocol.proposal_time S.E s
  prevEndpoint : ∃ EndAt : Nat → Block V,
    MovingFrontierChainStateN S rho t1 M0 (strictEventIndex rho t1)
        (inclusiveEventIndex rho (Protocol.proposal_time S.E s)) EndAt ∧
      EndAt (strictEventIndex rho (Protocol.proposal_time S.E s)) = Prev ∧
      EndAt (inclusiveEventIndex rho (Protocol.proposal_time S.E s)) = End
  prevVotes : NamedHonestVotesCone S rho (s - 1)
    (fun X => Block.Preceq Prev X)


/-- The confirmation outcome at the previous endpoint, for the named
pre-entry half. Same proof as the entry-state form, through the shared core
`movingSlotPreEntryN_confOutcome_atPrev_core` (the corresponding branch). -/
theorem MovingSlotPreEntryN.confOutcome_atPrev
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End)
    (hc : 0 < c)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (ht1 : t1 ≤ S.a r)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) :
    GenuineConfirmationWith
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho w c).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho w c) c
        (movingSlotConfirmationOutput S rho c w) ∧
      Block.Preceq Prev (movingSlotConfirmationOutput S rho c w) :=
  movingSlotPreEntryN_confOutcome_atPrev_core S adm hcom hfb
    hentry.startTime hentry.prevEndpoint hentry.prevVotes hc hround ht1
    hpostAction hcut hpostVote hslotHor hw

#print axioms MovingSlotPreEntryN.confOutcome_atPrev

/-- `confCompatible` in a Byzantine-proposer slot, for the named pre-entry
half: the previous slot's genuine confirmations are already above `Prev`, and
that is compatibility. This is the `hconf` input of
`MovingSlotEntryStateN.step_byzantineProposer_named`. -/
theorem MovingSlotPreEntryN.confCompatible_byzantine
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End)
    (hc : 0 < c)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (ht1 : t1 ≤ S.a r)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon) :
    ∀ u ∈ rho.honest, ∀ D : Block V,
      GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho u c).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho u c) c D →
        Block.compatible D Prev = true := by
  intro u hu D hgenuine
  have hDout : movingSlotConfirmationOutput S rho c u = D := hgenuine.selected
  have hPrevD : Block.Preceq Prev D := by
    have hout := (hentry.confOutcome_atPrev S adm hcom hfb hc hround ht1
      hpostAction hcut hpostVote hslotHor hu).2
    rwa [hDout] at hout
  exact Block.compatible_of_preceq_common (Block.preceq_self D) hPrevD

#print axioms MovingSlotPreEntryN.confCompatible_byzantine

/-- The pre-entry half of the next N entry, with a Byzantine proposer. -/
theorem MovingSlotEntryStateN.nextPreEntry_byzantine
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End Next : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hc : 0 < c)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (ht1 : t1 ≤ S.a r)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hpostProp : S.E.t_GST ≤ Protocol.proposal_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    (hfrontier : MovingSlotFrontierAt S rho c End Next)
    (hfacts : NamedMovingSlotWindowFacts S rho (c + 1) End Next)
    (hbyz : S.E.proposer (c + 2) ∉ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hhorSC : Protocol.support_cutoff S.E (c + 1) ≤ rho.horizon) :
    MovingSlotPreEntryN S rho t1 M0 (c + 2) Next Next := by
  obtain ⟨EndAt, hhistory, _hprev, hEndAt⟩ := hentry.prevEndpoint
  have hrunE : ∃ E : NamedBlock V, E.erase = End ∧ RunBlock S rho E := by
    rw [← hEndAt]
    exact hhistory.endpointRun _ hhistory.start_le (Nat.le_refl _)
  have hrunN : ∃ N : NamedBlock V, N.erase = Next ∧ RunBlock S rho N :=
    hfrontier.runBlock S adm hrunE
  obtain ⟨End', _hlow', hhigh', hstate'⟩ :=
    hhistory.through_slotWindow_byzantineProposer_named S adm
      (Nat.succ_pos c) hEndAt hrunE hrunN hfacts hbyz hv hhorSC
  have hfreezeStrict :
      inclusiveEventIndex rho (Protocol.view_freeze S.E (c + 1)) ≤
        strictEventIndex rho (Protocol.proposal_time S.E (c + 1 + 1)) :=
    inclusive_le_strict_of_lt' rho
      (view_freeze_lt_proposal_time_succ' S.E (c + 1))
  have hcone := hentry.windowVotesCone S adm hcom hfb hc hround ht1
    hpostAction hcut hpostVote hpostProp hslotHor hfrontier
  exact
    { startTime := hentry.startTime.trans
        (le_of_lt (proposal_time_lt_succ' S.E (c + 1)))
      prevEndpoint := ⟨End', hstate', hhigh' _ hfreezeStrict,
        hhigh' _ (hfreezeStrict.trans
          (strictEventIndex_le_inclusiveEventIndex rho _))⟩
      prevVotes := hcone }

#print axioms MovingSlotEntryStateN.nextPreEntry_byzantine


/-
/-- **The slot step with a Byzantine next proposer.**

The window endpoint carries over unchanged, and the next entry state's three
obligations are discharged from its own pre-entry half: the slot-`(c+2)` cone
by one regime-free Goldfish step above the endpoint, the head equality
vacuously, and the compatibility of the slot-`(c+1)` confirmations because
those are certified above the endpoint. -/
theorem MovingSlotEntryState.stepByzantine
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End Next: Block V}
    (hentry: MovingSlotEntryState S rho t1 M0 (c + 1) Prev End)
    (hdata: MovingSlotWindowData S rho t1 M0 c)
    (hdata': MovingSlotWindowData S rho t1 M0 (c + 1))
    (hfrontier: MovingSlotFrontierAt S rho c End Next)
    (hfacts: MovingSlotWindowFacts S rho (c + 1) End Next)
    (hbyz: S.E.proposer (c + 2) ∉ rho.honest)
    {v: V} (hv: v ∈ rho.honest):
    MovingSlotEntryState S rho t1 M0 (c + 2) Next Next:= by
  obtain ⟨r, hround, ht1, hpostAction, hcut⟩:= hdata.round
  obtain ⟨r', hround', ht1', hpostAction', hcut'⟩:= hdata'.round
  have hhorSC: Protocol.support_cutoff S.E (c + 1) ≤ rho.horizon:=
    (support_cutoff_le_confirmation_time S.E (c + 1)).trans hdata'.slotHor
  have hrunN: RunBlock S rho Next:=
    hfrontier.runBlock S adm hentry.endpointRun
  have hcone:= hentry.windowVotesCone S adm hcom hfb hdata.pos hround ht1
    hpostAction hcut hdata.postVote hdata.postProp hdata.slotHor
    hfrontier
  have hnext:= hentry.nextPreEntry_byzantine S adm hcom hfb hdata.pos hround
    ht1 hpostAction hcut hdata.postVote hdata.postProp hdata.slotHor
    hfrontier hfacts hbyz hv hhorSC
  exact hentry.step_byzantineProposer S adm (Nat.succ_pos c) hrunN hfacts
    hbyz hv hhorSC hcone
    (hnext.votesCone_prev S adm hcom hfb hdata'.pos hround' ht1' hpostAction'
      hcut' hdata'.postVote hdata'.slotHor)
    (hnext.confCompatible_byzantine S adm hcom hfb hdata'.pos hround' ht1'
      hpostAction' hcut' hdata'.postVote hdata'.slotHor)
-/

/-! ## 8. The honest slot step

The transfer producer of `MovingChainTransferRun` is keyed on the exact
proposal EVENT, not on the proposal cursor: it identifies the proposer's own
duty store with the run's state at that event. The window fold's public output
exposes only the cursor values, so the history through the proposal event is
rebuilt here — vote phase, confirmation phase, then the constant tail up to the
proposer's tick, where the endpoint is still the window endpoint. -/


/-- The N moving history through the honest next-proposal event. -/
theorem MovingSlotEntryStateN.historyAtHonestProposalEvent
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End Next : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hfrontier : MovingSlotFrontierAt S rho c End Next)
    (hfacts : NamedMovingSlotWindowFacts S rho (c + 1) End Next)
    (hprop : S.E.proposer (c + 1 + 1) ∈ rho.honest)
    (hhorProp : Protocol.proposal_time S.E (c + 1 + 1) ≤ rho.horizon)
    (hhorSC : Protocol.support_cutoff S.E (c + 1) ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    ∃ (p : Nat) (EndAt : Nat → Block V),
      rho.events[p]? = some
        (Event.tick (S.E.proposer (c + 1 + 1))
          (Protocol.proposal_time S.E (c + 1 + 1))) ∧
      strictEventIndex rho (Protocol.proposal_time S.E (c + 1 + 1)) ≤ p ∧
      EndAt p = Next ∧
      MovingFrontierChainStateN S rho t1 M0
        (strictEventIndex rho t1) p EndAt := by
  obtain ⟨EndAt0, hhistory, _hprev, hEndAt⟩ := hentry.prevEndpoint
  have hrunE : ∃ E : NamedBlock V, E.erase = End ∧ RunBlock S rho E := by
    rw [← hEndAt]
    exact hhistory.endpointRun _ hhistory.start_le (Nat.le_refl _)
  have hrunN : ∃ N : NamedBlock V, N.erase = Next ∧ RunBlock S rho N :=
    hfrontier.runBlock S adm hrunE
  obtain ⟨End1, _hlow1, hval1, hstate1⟩ :=
    through_slotWindowPrefix_named S adm (Nat.succ_pos c) hhistory hEndAt
      hrunE hrunN hfacts hv hhorSC
  set cf := inclusiveEventIndex rho (Protocol.view_freeze S.E (c + 1)) with hcf
  set sn := strictEventIndex rho
    (Protocol.proposal_time S.E (c + 1 + 1)) with hsn
  set cn := inclusiveEventIndex rho
    (Protocol.proposal_time S.E (c + 1 + 1)) with hcn
  obtain ⟨B, hB⟩ := proposedBlockAt_isSome S rho (c + 1 + 1)
  obtain ⟨_hBslot, hpemit⟩ := Proofs.Optimistic.proposalTick S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (c + 1 + 1)
      (Nat.succ_pos _) hprop hhorProp hB
  obtain ⟨p, hpevent, _hpblock⟩ := hpemit
  have hcfsn : cf ≤ sn :=
    inclusive_le_strict_of_lt' rho
      (view_freeze_lt_proposal_time_succ' S.E (c + 1))
  have hsnp : sn ≤ p := by
    by_contra hnot
    have htrue := Proofs.Optimistic.filter_true_of_index_lt
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed _
      (Proofs.Optimistic.downward_lt (Protocol.proposal_time S.E (c + 1 + 1)))
      (by simpa only [strictEventIndex] using Nat.lt_of_not_ge hnot) hpevent
    simp only [decide_eq_true_eq, Event.time] at htrue
    exact lt_irrefl _ htrue
  have hcfp : cf ≤ p := hcfsn.trans hsnp
  have hpcn : p < cn := by
    by_contra hnot
    have hgt := eventTime_gt_of_inclusive_le' S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Nat.le_of_not_gt hnot) hpevent
    simp only [Event.time] at hgt
    exact lt_irrefl _ hgt
  have hpUnique : ∀ (j : Nat) (u : V), u ∈ rho.honest →
      rho.events[j]? = some
        (Event.tick u (Protocol.proposal_time S.E (c + 1 + 1))) →
      S.E.proposer (c + 1 + 1) = (S.node u).val_index → j = p := by
    intro j u _hu hev heq
    rw [S.node_val_index u] at heq
    subst heq
    exact eventIndex_unique' adm.nodup hev hpevent
  obtain ⟨End2, hlow2, hhigh2, hstate2⟩ :=
    hstate1.through_constantEndpoint_named_public S
      (by rw [hval1]; exact Block.preceq_self _) hrunN hcfp (by
      intro j hj hjp
      refine movingSlotWindowTail_eventFacts_named_public S adm
        (Block.preceq_self Next) ?_ hj (hjp.trans hpcn)
      intro u hu hev heq
      exact absurd (hpUnique j u hu hev heq) (Nat.ne_of_lt hjp))
  have hEnd2p : End2 p = Next := by
    rcases Nat.eq_or_lt_of_le hcfp with heq | hlt
    · rw [← heq, hlow2 _ (Nat.le_refl _), hval1]
    · exact hhigh2 p hlt
  exact ⟨p, End2, hpevent, hsnp, hEnd2p, hstate2⟩


/-- The pre-entry half of the next N entry, with an honest proposer. -/
theorem MovingSlotEntryStateN.nextPreEntry_honest
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End Next : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hdata : MovingSlotWindowData S rho t1 M0 c)
    (hdata' : MovingSlotWindowData S rho t1 M0 (c + 1))
    (hfrontier : MovingSlotFrontierAt S rho c End Next)
    (hfacts : NamedMovingSlotWindowFacts S rho (c + 1) End Next)
    (hprop : S.E.proposer (c + 1 + 1) ∈ rho.honest)
    (hparent : Block.Preceq Next (proposedParent S rho (c + 1 + 1)))
    {v : V} (hv : v ∈ rho.honest) :
    ∃ P : NamedBlock V, proposedBlockAt S rho (c + 1 + 1) = some P ∧
      MovingSlotPreEntryN S rho t1 M0 (c + 1 + 1) Next P.erase := by
  obtain ⟨r, hround, ht1, hpostAction, hcut⟩ := hdata.round
  have hhorSC : Protocol.support_cutoff S.E (c + 1) ≤ rho.horizon :=
    (support_cutoff_le_confirmation_time S.E (c + 1)).trans hdata'.slotHor
  have hhorProp : Protocol.proposal_time S.E (c + 1 + 1) ≤ rho.horizon :=
    (proposalTimeSucc_le_confirmationTime' S.E (c + 1)).trans hdata'.slotHor
  obtain ⟨EndAt, hhistory, _hprev, hEndAt⟩ := hentry.prevEndpoint
  have hrunE : ∃ E : NamedBlock V, E.erase = End ∧ RunBlock S rho E := by
    rw [← hEndAt]
    exact hhistory.endpointRun _ hhistory.start_le (Nat.le_refl _)
  have hrunN : ∃ N : NamedBlock V, N.erase = Next ∧ RunBlock S rho N :=
    hfrontier.runBlock S adm hrunE
  obtain ⟨P, hP, End', _hlow', hstrict', hincl', hstate'⟩ :=
    hhistory.through_slotWindow_honestProposer_named S adm
      (Nat.succ_pos c) hEndAt hrunE hrunN hfacts hprop hhorProp hparent hv hhorSC
  have hcone := hentry.windowVotesCone S adm hcom hfb hdata.pos hround ht1
    hpostAction hcut hdata.postVote hdata.postProp hdata.slotHor hfrontier
  refine ⟨P, hP, ?_⟩
  exact
    { startTime := hentry.startTime.trans
        (le_of_lt (proposal_time_lt_succ' S.E (c + 1)))
      prevEndpoint := ⟨End', hstate', hstrict', hincl'⟩
      prevVotes := hcone }

#print axioms MovingSlotEntryStateN.nextPreEntry_honest


/-
/-- The pre-entry half of the next slot's entry state, honest proposer. -/
theorem MovingSlotEntryState.nextPreEntry_honest
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End Next: Block V}
    (hentry: MovingSlotEntryState S rho t1 M0 (c + 1) Prev End)
    (hdata: MovingSlotWindowData S rho t1 M0 c)
    (hdata': MovingSlotWindowData S rho t1 M0 (c + 1))
    (hfrontier: MovingSlotFrontierAt S rho c End Next)
    (hfacts: MovingSlotWindowFacts S rho (c + 1) End Next)
    (hprop: S.E.proposer (c + 1 + 1) ∈ rho.honest)
    (hparent: Block.Preceq Next (proposedParent S rho (c + 1 + 1)))
    {v: V} (hv: v ∈ rho.honest):
    MovingSlotPreEntry S rho t1 M0 (c + 1 + 1) Next
      (proposedBlock S rho (c + 1 + 1)):= by
  obtain ⟨r, hround, ht1, hpostAction, hcut⟩:= hdata.round
  have hhorSC: Protocol.support_cutoff S.E (c + 1) ≤ rho.horizon:=
    (support_cutoff_le_confirmation_time S.E (c + 1)).trans hdata'.slotHor
  have hhorProp: Protocol.proposal_time S.E (c + 1 + 1) ≤ rho.horizon:=
    (proposalTimeSucc_le_confirmationTime' S.E (c + 1)).trans hdata'.slotHor
  obtain ⟨EndAt, hhistory, _hprev, hEndAt⟩:= hentry.prevEndpoint
  have hrunE: RunBlock S rho End:= hentry.endpointRun
  have hrunN: RunBlock S rho Next:= hfrontier.runBlock S adm hrunE
  obtain ⟨End', _hlow', hstrict', hincl', hstate'⟩:=
    hhistory.through_slotWindow_honestProposer S adm (Nat.succ_pos c)
      hEndAt hrunE hrunN hfacts hprop hhorProp hparent hv hhorSC
  exact
    { startTime:= hentry.startTime.trans
        (le_of_lt (proposal_time_lt_succ' S.E (c + 1)))
      prevEndpoint:= ⟨End', hstate', hstrict', hincl'⟩
      prevVotes:= hentry.windowVotesCone S adm hcom hfb hdata.pos hround ht1
        hpostAction hcut hdata.postVote hdata.postProp hdata.slotHor
        hfrontier }
-/


/-
/-- **The head equality of the honest slot step.**

Every honest slot-`(c+2)` vote duty returns the new proposal exactly: the
proposal walk transfers over the window endpoint. The vote input is the
pre-entry's own; the two viability bands are the moving history's crossing-row
bands at the proposer read and at the voter read. -/
theorem MovingSlotEntryState.headTransfer_honest
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End Next: Block V}
    (hentry: MovingSlotEntryState S rho t1 M0 (c + 1) Prev End)
    (hdata: MovingSlotWindowData S rho t1 M0 c)
    (hdata': MovingSlotWindowData S rho t1 M0 (c + 1))
    (hfrontier: MovingSlotFrontierAt S rho c End Next)
    (hfacts: MovingSlotWindowFacts S rho (c + 1) End Next)
    (hprop: S.E.proposer (c + 1 + 1) ∈ rho.honest)
    (hparent: Block.Preceq Next (proposedParent S rho (c + 1 + 1)))
    {v: V} (hv: v ∈ rho.honest)
    {w: V} (hw: w ∈ rho.honest):
    Protocol.ProposalWalkTransferred S rho (c + 1 + 1)
      (proposedBlock S rho (c + 1 + 1))
      (proposedParent S rho (c + 1 + 1)) w:= by
  obtain ⟨r, hround, ht1, hpostAction, hcut⟩:= hdata.round
  obtain ⟨r', hround', ht1', hpostAction', hcut'⟩:= hdata'.round
  have hhorSC: Protocol.support_cutoff S.E (c + 1) ≤ rho.horizon:=
    (support_cutoff_le_confirmation_time S.E (c + 1)).trans hdata'.slotHor
  have hhorProp: Protocol.proposal_time S.E (c + 1 + 1) ≤ rho.horizon:=
    (proposalTimeSucc_le_confirmationTime' S.E (c + 1)).trans hdata'.slotHor
  have hvoteHor: Protocol.vote_time S.E (c + 1 + 1) ≤ rho.horizon:=
    (voteTimeSucc_le_confirmationTime' S.E (c + 1)).trans hdata'.slotHor
  have hcone:= hentry.windowVotesCone S adm hcom hfb hdata.pos hround ht1
    hpostAction hcut hdata.postVote hdata.postProp hdata.slotHor
    hfrontier
  have hnext:= hentry.nextPreEntry_honest S adm hcom hfb hdata hdata'
    hfrontier hfacts hprop hparent hv
  have hinputs:= hnext.voteInputs S adm hcom hfb hround' ht1' hpostAction'
    hcut' hdata'.postVote hdata'.slotHor hw
  obtain ⟨p, End2, hpevent, _hsnp, hEnd2p, hstate2⟩:=
    hentry.historyAtHonestProposalEvent S adm hfrontier hfacts hprop
      hhorProp hhorSC hv
  rw [← hEnd2p] at hparent hcone hinputs
  have hcore:= hstate2.frozenProposalSuffixCoreInputs_of_proposalEvent
    S adm hcom hfb hround' ht1' hpostAction' hcut' hdata'.postVote
    hdata'.slotHor hcone hprop hpevent hparent
    (hentry.startTime.trans (le_of_lt (proposal_time_lt_succ' S.E (c + 1))))
    hw
  exact hstate2.proposalWalkTransferred_of_sourceFloor S adm hcom hfb
    (Nat.succ_pos c) hdata'.postProp hdata'.slotHor hprop hpevent hw
    hvoteHor hparent hcone hinputs hcore
-/


/-
/-- **The slot step with an honest next proposer.**

The window endpoint becomes the next state's `Prev` and the new proposal
becomes its endpoint. The three obligations: the slot-`(c+2)` cone is the
proposal itself because the walk transfers, the head equality IS that transfer,
and the slot-`(c+1)` confirmations are below every honest slot-`(c+2)` head,
hence below the proposal. -/
theorem MovingSlotEntryState.stepHonest
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End Next: Block V}
    (hentry: MovingSlotEntryState S rho t1 M0 (c + 1) Prev End)
    (hdata: MovingSlotWindowData S rho t1 M0 c)
    (hdata': MovingSlotWindowData S rho t1 M0 (c + 1))
    (hfrontier: MovingSlotFrontierAt S rho c End Next)
    (hfacts: MovingSlotWindowFacts S rho (c + 1) End Next)
    (hprop: S.E.proposer (c + 1 + 1) ∈ rho.honest)
    (hparent: Block.Preceq Next (proposedParent S rho (c + 1 + 1)))
    {v: V} (hv: v ∈ rho.honest):
    MovingSlotEntryState S rho t1 M0 (c + 1 + 1) Next
      (proposedBlock S rho (c + 1 + 1)):= by
  obtain ⟨r, hround, ht1, hpostAction, hcut⟩:= hdata.round
  obtain ⟨r', hround', ht1', hpostAction', hcut'⟩:= hdata'.round
  have hhorSC: Protocol.support_cutoff S.E (c + 1) ≤ rho.horizon:=
    (support_cutoff_le_confirmation_time S.E (c + 1)).trans hdata'.slotHor
  have hhorProp: Protocol.proposal_time S.E (c + 1 + 1) ≤ rho.horizon:=
    (proposalTimeSucc_le_confirmationTime' S.E (c + 1)).trans hdata'.slotHor
  have hvoteHor: Protocol.vote_time S.E (c + 1 + 1) ≤ rho.horizon:=
    (voteTimeSucc_le_confirmationTime' S.E (c + 1)).trans hdata'.slotHor
  have hrunN: RunBlock S rho Next:=
    hfrontier.runBlock S adm hentry.endpointRun
  have hcone:= hentry.windowVotesCone S adm hcom hfb hdata.pos hround ht1
    hpostAction hcut hdata.postVote hdata.postProp hdata.slotHor
    hfrontier
  have htransfer: ∀ u ∈ rho.honest,
      Protocol.ProposalWalkTransferred S rho (c + 1 + 1)
        (proposedBlock S rho (c + 1 + 1))
        (proposedParent S rho (c + 1 + 1)) u:= fun u hu =>
    hentry.headTransfer_honest S adm hcom hfb hdata hdata' hfrontier hfacts
      hprop hparent hv hu
  have hheadEq: ∀ u ∈ rho.honest,
      voteDutyHead S rho u (c + 1 + 1) = proposedBlock S rho (c + 1 + 1):=
    fun u hu => voteDutyHead_eq_proposedBlock_of_transferred S (htransfer u hu)
  have hvotes: Proofs.Optimistic.HonestVotesCone S rho (c + 1 + 1)
      (fun X => Block.Preceq (proposedBlock S rho (c + 1 + 1)) X):= by
    intro u hu huc
    obtain ⟨hrun, hemit⟩:=
      voteDutyHead_runBlock_and_emits S adm (Nat.succ_pos (c + 1)) hvoteHor
        hu huc
    exact ⟨voteDutyHead S rho u (c + 1 + 1),
      by rw [hheadEq u hu]; exact Block.preceq_self _, hrun, hemit⟩
  have hnext:= hentry.nextPreEntry_honest S adm hcom hfb hdata hdata'
    hfrontier hfacts hprop hparent hv
  exact hentry.step_honestProposer S adm (Nat.succ_pos c) hrunN hfacts hprop
    hhorProp hhorSC hparent hv hcone hvotes htransfer
    (hnext.confCompatible_honest S adm hcom hfb hdata'.pos hround' ht1'
      hpostAction' hcut' hdata'.postVote hdata'.postProp hdata'.slotHor
      hheadEq hv)
-/


-- these over the ERASED `MovingSlotPreEntry`; they do not transfer, because the
-- pre-entry's history is `MovingFrontierChainStateN` and the two frontier-chain
-- states differ in `genuineConfirmations`, `anchors` and `oldRows`, all on the

-- cursor reads they go through DO exist on the N state
-- (`MovingChainSlotStepRun.lean:621-676`), so each is u's proof over the N
-- history.

/-- The confirmation read's FG root is at or below the previous endpoint, for
the named pre-entry half. -/
theorem MovingSlotPreEntryN.confRoot_preceq_prev
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End)
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq (confRoot (Proofs.Optimistic.confStore S rho w c)) Prev := by
  exact movingSlotPreEntryN_confRoot_preceq_prev_core S adm hfb
    hentry.startTime hentry.prevEndpoint hw


/-- The next slot's vote read has its FG root at or below the previous
endpoint, for the named pre-entry half. -/
theorem MovingSlotPreEntryN.voteRoot_preceq_prev
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End)
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E (c + 1))).toHealing.toFG) Prev := by
  exact movingSlotPreEntryN_voteRoot_preceq_prev_core S adm hfb
    hentry.startTime hentry.prevEndpoint hw


/-- The previous endpoint has a named run witness, for the named pre-entry
half. -/
theorem MovingSlotPreEntryN.prevRunAt
    (S : Setup V) {rho : Run V}
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End) :
    ∃ E : NamedBlock V, E.erase = Prev ∧ RunBlock S rho E := by
  exact movingSlotPreEntryN_prevRunAt_core S hentry.startTime
    hentry.prevEndpoint


/-- The next slot's vote read is within one height of the previous endpoint's
NAMED derivation, for the named pre-entry half. -/
theorem MovingSlotPreEntryN.voteFrontier_sub_one_le_prevHeight_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End)
    {w : V} (hw : w ∈ rho.honest)
    {E : NamedBlock V} (hE : E.erase = Prev) (hErun : RunBlock S rho E) :
    (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (c + 1))).core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h := by
  exact movingSlotPreEntryN_voteFrontier_sub_one_le_prevHeight_named_core
    S adm hfb hentry.startTime hentry.prevEndpoint hw hE hErun



/-- The same band on the reader's own chain-state map, for a reader that holds
The previous endpoint. This is where  bites: the erased route converted
`derived_state` to `σ` through the retired `derivedStateAgrees_depReachable`,
and this one identifies `σ` with `derive_named` at the endpoint's retained
body instead. -/
theorem MovingSlotPreEntryN.voteFrontier_sub_one_le_prevHeightSigma
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End)
    {w : V} (hw : w ∈ rho.honest)
    (hmem : Prev ∈
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (c + 1))).core.T) :
    (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (c + 1))).core.h_max - 1 ≤
      ((rho.storeBeforeTime S w
        (Protocol.vote_time S.E (c + 1))).core.σ Prev).h := by
  exact movingSlotPreEntryN_voteFrontier_sub_one_le_prevHeightSigma_core
    S adm hfb hentry.startTime hentry.prevEndpoint hw hmem




private theorem w4u_vote_time_normal (E : Env V) (s : Slot) :
    Protocol.vote_time E s = (4 * (s : Time) + 1) * E.Δ := by
  unfold Protocol.vote_time Env.t slotStart
  ring

private theorem w4u_support_cutoff_normal (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s = (4 * (s : Time) + 2) * E.Δ := by
  unfold Protocol.support_cutoff Env.t slotStart
  ring

private theorem w4u_support_cutoff_le_vote_time_succ (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≤ Protocol.vote_time E (s + 1) := by
  rw [w4u_support_cutoff_normal, w4u_vote_time_normal]
  refine Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt E.Δ_pos)
  push_cast
  omega

/-- The selected FG root is at or below the prepared vote anchor: either the
anchor IS that root, or it is an active prefix inside the filtered tree. -/
private theorem w4u_fgRoot_preceq_voterAnchorAt
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.toHealing.toFG)
      (voterAnchorAt S rho v s) := by
  rcases voterAnchorAt_cases S rho v s with hfg | ⟨root, A, _hframe, hactive,
    hanchor⟩
  · rw [hfg]
    exact Block.preceq_self _
  · rw [hanchor]
    exact Proofs.Records.preceq_get_fg_root_of_mem_filtered
      (Proofs.NamedProposalParent.activePrefix_mem _ root A hactive)

/-- The prepared slot-`(c+1)` vote anchor is on the previous endpoint's
chain. -/
theorem MovingSlotPreEntryN.voterAnchorAt_preceq_prev
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (ht1 : t1 ≤ S.a r)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq (voterAnchorAt S rho w (c + 1)) Prev :=
  movingSlotPreEntryN_voterAnchorAt_preceq_prev_core S adm hfb
    hentry.startTime hentry.prevEndpoint hround ht1 hpostAction hcut hslotHor hw

/-- The primed Goldfish vote inputs at the named pre-entry. -/
theorem MovingSlotPreEntryN.voteInputs
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (ht1 : t1 ≤ S.a r)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) :
    GoldfishConeVoteInputs' S rho c Prev w := by
  have hprevVotes : NamedHonestVotesCone S rho c
      (fun X => Block.Preceq Prev X) := by
    simpa only [Nat.add_sub_cancel] using hentry.prevVotes
  have hrootRaw := hentry.voteRoot_preceq_prev S adm hfb hw
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG) Prev := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hrootRaw
  have hcutHor : Protocol.support_cutoff S.E c ≤ rho.horizon :=
    (support_cutoff_le_confirmation_time S.E c).trans hslotHor
  have havailable := honestHeadsAvailableBefore_of_namedPostHealingCone
    S adm hw hpostVote hcutHor hroot hprevVotes
  have hpositive : 0 < ((S.E.committee c) ∩ rho.honest).card := by
    have hcc := hcom c
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  obtain ⟨X, hPrevX, hXrun, hXemit⟩ :=
    hprevVotes x (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hx).1
  have hhead : Proofs.Optimistic.HonestHead S rho c X.erase :=
    ⟨x, (Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hx).1,
      ⟨X, rfl, hXrun⟩, hXemit⟩
  have hprocessed := voterProcessed_of_availableBefore_of_honestHead
    S adm havailable hhead (Block.preceq_self X.erase)
  obtain ⟨E, hE, hErun⟩ := hentry.prevRunAt S
  have hbandE := hentry.voteFrontier_sub_one_le_prevHeight_named S adm hfb hw
    hE hErun
  have hnamedEX : NamedBlock.Preceq E X :=
    namedPreceq_of_runBlock_erase_preceq adm hErun hXrun
      (by rw [hE]; exact hPrevX)
  have hbandX : (rho.storeBeforeTime S w
      (Protocol.vote_time S.E (c + 1))).core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg X).h :=
    hbandE.trans (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hnamedEX)
  have hmax : (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).h_max ≤
      (Protocol.derive_named S.E S.cfg X).h + 1 := by
    have hle := Nat.sub_le_iff_le_add.mp hbandX
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hle
  have hmemT : Prev ∈ (rho.storeBeforeTime S w
      (Protocol.vote_time S.E (c + 1))).T :=
    mem_storeBeforeTime_of_cone S adm hcom havailable
      (w4u_support_cutoff_le_vote_time_succ S.E c) hprevVotes
  have hbodies : E ∈ (rho.storeBeforeTime S w
      (Protocol.vote_time S.E (c + 1))).bodies :=
    mem_bodies_of_mem_T S adm hw hErun (by rw [hE]; exact hmemT)
  have hfilteredRaw := storeBeforeTime_mem_filtered_of_band S adm hbodies
    (by rw [hE]; exact hrootRaw) hbandE
  have hfiltered : Prev ∈ Protocol.get_filtered_block_tree
      (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG := by
    rw [← hE]
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hfilteredRaw
  have hanchorP := hentry.voterAnchorAt_preceq_prev S adm hfb hround ht1
    hpostAction hcut hslotHor hw
  refine ⟨Or.inl ⟨?_, ?_, ?_⟩,
    Block.compatible_of_preceq_common hanchorP (Block.preceq_self Prev)⟩
  · simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hroot
  · exact namedAncestorCandidate_of_processedDescendant_and_hMax_core
      S adm.toNamedAdmissibleCore hw hprocessed hXrun hPrevX hfiltered hmax
  · intro D hAD _hAne hDPrev _hDne
    have hrootDRaw : Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S w
            (Protocol.vote_time S.E (c + 1))).toHealing.toFG) D := by
      refine Block.preceq_trans ?_ hAD
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime] using
        w4u_fgRoot_preceq_voterAnchorAt S rho w (c + 1)
    have hpc : ParentClosed (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (c + 1))).core := by
      simpa only [Run.storeBeforeTime] using
        Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
          (Protocol.vote_time S.E (c + 1)) w
    have hDmemT : D ∈ (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (c + 1))).core.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2 D Prev hmemT hDPrev
    obtain ⟨Dn, hDnerase, hDnrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        adm.toNamedScheduleWellFormed hw (Protocol.vote_time S.E (c + 1))
        (by simpa only [Run.storeBeforeTime] using hDmemT)
    have hDfilteredRaw := storeBeforeTime_path_mem_filtered_of_band S adm
      hbodies hbandE (by rw [hDnerase]; exact hrootDRaw)
      (by rw [hDnerase, hE]; exact hDPrev)
    have hDfiltered : D ∈ Protocol.get_filtered_block_tree
        (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG := by
      rw [← hDnerase]
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hDfilteredRaw
    exact namedAncestorCandidate_of_processedDescendant_and_hMax_core
      S adm.toNamedAdmissibleCore hw hprocessed hXrun
      (Block.preceq_trans hDPrev hPrevX) hDfiltered hmax

#print axioms MovingSlotPreEntryN.voterAnchorAt_preceq_prev
#print axioms MovingSlotPreEntryN.voteInputs



/-- **The slot-`(c+1)` vote cone above the previous endpoint.**

In a Byzantine-proposer slot the endpoint does not move, so at the pre-entry of
slot `c + 2` this IS the slot-`(c+2)` cone above the window endpoint that
`MovingSlotEntryStateN.step_byzantineProposer_named` takes as `hvotes` (branches
w4-u,  item 1). -/
theorem MovingSlotPreEntryN.votesCone_prev
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End)
    (hc : 0 < c)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (ht1 : t1 ≤ S.a r)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon) :
    NamedHonestVotesCone S rho (c + 1)
      (fun X => Block.Preceq Prev X) := by
  have hprevVotes : NamedHonestVotesCone S rho c
      (fun X => Block.Preceq Prev X) := by
    simpa only [Nat.add_sub_cancel] using hentry.prevVotes
  have hvoteHorSucc : Protocol.vote_time S.E (c + 1) ≤ rho.horizon :=
    (voteTimeSucc_le_confirmationTime' S.E c).trans hslotHor
  have hstep : ∀ u ∈ rho.honest,
      Block.Preceq Prev (voteDutyHead S rho u (c + 1)) := by
    intro u hu
    exact goldfishCone_step' S adm hcom hc hpostVote
      hslotHor hprevVotes hu
      (hentry.voteInputs S adm hcom hfb hround ht1 hpostAction hcut hpostVote
        hslotHor hu)
  intro u hu huc
  obtain ⟨X, hXerase, hXrun, hXemit⟩ := voteDutyHead_runBlock_and_emits S adm
    (Nat.succ_pos c) hvoteHorSucc hu huc
  exact ⟨X, by simpa only [hXerase] using hstep u hu, hXrun, hXemit⟩

#print axioms MovingSlotPreEntryN.votesCone_prev


/-- `confCompatible` in an honest-proposer slot, for the named pre-entry half:
the transfer makes every honest vote head the slot proposal, and the previous
slot's genuine confirmations are at or below every honest vote head. This is
the `hconf` input of `MovingSlotEntryStateN.step_honestProposer_named`.

The head fact is taken as a pin: its own producer is the named twin of
`MovingSlotPreEntry.genuineConfirmation_preceq_voteDutyHead` (parked above),
which needs the four pre-entry reads of `MovingChainSupporterRun` restated over
`MovingSlotPreEntryN`. Those four are not derivable from the erased ones:
`MovingFrontierChainStateN` differs from `MovingFrontierChainState` in exactly
`genuineConfirmations`, `anchors` and `oldRows`, all three on the prepared
contract rather than `GradeContract.current`, so there is no conversion
either way. -/
theorem MovingSlotPreEntryN.confCompatible_honest
    (S : Setup V) {rho : Run V}
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End)
    (hheadEq : ∀ u ∈ rho.honest, voteDutyHead S rho u (c + 1) = End)
    {w : V} (hw : w ∈ rho.honest)
    (_of_genuineConfirmation_preceq_voteDutyHead :
      ∀ u ∈ rho.honest, ∀ D : Block V,
        GenuineConfirmationWith
            (NamedProfile.gradeContract
              (Internal.NamedRecoveryRead.confirmationInputRead S rho u c).cache)
            S.E S.hc (Proofs.Optimistic.confStore S rho u c) c D →
          Block.Preceq D (voteDutyHead S rho w (c + 1))) :
    ∀ u ∈ rho.honest, ∀ D : Block V,
      GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho u c).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho u c) c D →
        Block.compatible D End = true := by
  intro u hu D hgenuine
  have _hentry := hentry
  have hDhead := _of_genuineConfirmation_preceq_voteDutyHead u hu D hgenuine
  rw [hheadEq w hw] at hDhead
  exact Block.compatible_of_preceq_common hDhead (Block.preceq_self End)

#print axioms MovingSlotPreEntryN.confCompatible_honest

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
