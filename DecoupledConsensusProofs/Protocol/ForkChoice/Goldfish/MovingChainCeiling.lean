module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.MovingChainBase
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.MovingChainTransfer

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The window facts with the carrier ceiling supplied

`MovingSlotEntryState.windowFacts` reads the previous round's SG carrier
ceiling out of the moving history, which needs the history to start at or
before that round's action. With the history starting at the healing
boundary's own action `a_q`, that holds only for slots whose round is `q + 1`
or later — for `R = 2` the fold's own base slot, but for `R > 2` not for the
slots that still lie inside round `q`.

Those slots are not out of reach: the ceiling is an ordinary hypothesis of
`readAnchor_preceq_of_previousActionCeiling`, and the boundary's own lifecycle
records carries it — `SGProposalLifecyclePacket.actionTargetParent` puts every
honest round-`(q-1)` carrier below the opening proposal's parent, hence below
the block the fold starts from. This module is the same three reads with that
ceiling passed in instead of read out.

Nothing else changes: same cursor, same bands, same anchors.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem Γ_0_le_proposal_time_of_round_eq''
    (S : Setup V) {r : Round} {s : Slot}
    (hround : S.hc.round_of s = r) :
    S.hc.Γ_0 S.E.Δ r ≤ Protocol.proposal_time S.E s := by
  have hopen : S.hc.opening_slot r ≤ s := by
    unfold Protocol.HealConfig.round_of at hround
    unfold Protocol.HealConfig.opening_slot
    rw [← hround]
    exact Nat.div_mul_le_self s S.hc.R
  rw [Protocol.Γ_0_eq_proposal_time]
  exact Protocol.proposal_time_mono S.E hopen

/-! ## Named ceiling reads

These are additive twins of the erased ceiling producers below. They keep
the same binders and replace only the absolute vote anchor and the default
confirmation contract with their prepared named forms. -/




/-- Every N entry state is an N pre-entry state. -/
theorem MovingSlotEntryStateN.toPreN
    {S : Setup V} {rho : Run V} {t1 : Time} {M0 : Height}
    {s : Slot} {Prev End : Block V}
    (h : MovingSlotEntryStateN S rho t1 M0 s Prev End) :
    MovingSlotPreEntryN S rho t1 M0 s Prev End where
  startTime := h.startTime
  prevEndpoint := h.prevEndpoint
  prevVotes := h.prevVotes

/-- The slot-`c` confirmation output is genuine and is above `Prev` for an N
pre-entry state when the previous-round carrier ceiling is supplied. -/
theorem MovingSlotPreEntryN.confOutcome_atPrev_of_ceiling_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End)
    (hc : 0 < c)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) :
    GenuineConfirmationWith
        (NamedProfile.gradeContract (confirmationInputRead S rho w c).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho w c) c
        (movingSlotConfirmationOutput S rho c w) ∧
      Block.Preceq Prev (movingSlotConfirmationOutput S rho c w) := by
  obtain ⟨EndAt, hhistory, hprev, _hEnd⟩ := hentry.prevEndpoint
  set k := strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) with hk
  have hpre : MovingFrontierChainStateN S rho t1 M0
      (strictEventIndex rho t1) k EndAt :=
    hhistory.prefix (strictEventIndex_mono rho hentry.startTime)
      (strictEventIndex_le_inclusiveEventIndex rho _)
  have hvotes : NamedHonestVotesCone S rho c
      (fun X => Block.Preceq (EndAt k) X) := by
    rw [hprev]
    simpa only [Nat.add_sub_cancel] using hentry.prevVotes
  obtain ⟨E0, hE0, hE0run⟩ :=
    hpre.endpointRun k hpre.start_le (Nat.le_refl k)
  have hrootRaw : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w
          (Protocol.confirmation_time S.E c)).core.toHealing.toFG) E0.erase :=
    hpre.confRoot_preceq_endpointAtCursor_named S adm hfb
      (Nat.le_refl k) hw hentry.startTime hE0 hE0run
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (confirmationInputRead S rho w c).st.core.toHealing.toFG) E0.erase := by
    simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime] using hrootRaw
  have hresolve := Protocol.headsResolveIn_confStore_of_postHealingCone
    S adm hw hpostVote
      ((support_cutoff_le_confirmation_time S.E c).trans hslotHor)
      (by simpa only [confRoot,
        Proofs.Optimistic.confStore_eq_confirmationInputRead, hE0] using hroot) hvotes
  have hpositive : 0 < ((S.E.committee c) ∩ rho.honest).card := by
    have hcc := hcom c
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  obtain ⟨X, hEndX, hXrun, hXemit⟩ :=
    hvotes x (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hx).1
  have hXmem : X.erase ∈
      (Proofs.Optimistic.confStore S rho w c).T :=
    Proofs.HealingLemmas.find?_mem
      ((hresolve X.erase ⟨x, (Finset.mem_inter.mp hx).2,
        (Finset.mem_inter.mp hx).1, ⟨X, rfl, hXrun⟩, hXemit⟩).1)
  have hpc : ParentClosed (Proofs.Optimistic.confStore S rho w c) := by
    simpa only [confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      NamedRun.stateBeforeTime] using
      Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
        (Protocol.confirmation_time S.E c) w
  have hmem : E0.erase ∈ (Proofs.Optimistic.confStore S rho w c).T := by
    apply Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
      E0.erase X.erase hXmem
    simpa only [hE0] using hEndX
  have hFJ : Block.Preceq
      (Proofs.Optimistic.confStore S rho w c).F
      (Proofs.Optimistic.confStore S rho w c).J := by
    simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead,
      confirmationInputRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      NamedRun.stateBeforeTime] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (Protocol.confirmation_time S.E c) w
  have hrootConf : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.confStore S rho w c).toHealing.toFG) E0.erase := by
    simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead] using hroot
  have hrootEndAt : Block.Preceq
      (Protocol.get_fg_root
        (confirmationInputRead S rho w c).st.core.toHealing.toFG)
      (EndAt k) := by
    simpa only [hE0] using hroot
  have hFEnd : Block.Preceq
      (Proofs.Optimistic.confStore S rho w c).F E0.erase :=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F
        (st := (Proofs.Optimistic.confStore S rho w c).toHealing.toFG) hFJ)
      hrootConf
  obtain ⟨K, hKbody, hKErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.confirmation_time S.E c) w
      (by simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead,
        confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Run.storeBeforeTime] using hmem)
  have hKrun : RunBlock S rho K := by
    obtain ⟨n, hn, _⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.confirmation_time S.E c)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i := n)
    simpa only [Run.storeBeforeTime, hn] using hKbody
  have hKEnd : K.erase = EndAt k := hKErase.trans hE0
  have hband :
      (rho.storeBeforeTime S w
        (Protocol.confirmation_time S.E c)).core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg K).h := by
    exact hpre.confFrontier_sub_one_le_endpointAtCursor_named S adm hfb
      (Nat.le_refl k) hw hKEnd hKrun
  have hsigma :
      (Proofs.Optimistic.confStore S rho w c).σ E0.erase =
        Protocol.derive_named S.E S.cfg K := by
    rw [← hKErase]
    simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead,
      confirmationInputRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      NamedRun.stateBeforeTime] using
      Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
        (Protocol.confirmation_time S.E c) w K hKbody
  have hbandStore : (Proofs.Optimistic.confStore S rho w c).h_max - 1 ≤
      ((Proofs.Optimistic.confStore S rho w c).σ E0.erase).h := by
    rw [hsigma]
    exact hband
  have hfull : E0.erase ∈
      Protocol.get_filtered_block_tree
        (Proofs.Optimistic.confStore S rho w c).toHealing.toFG :=
    mem_get_filtered_block_tree_from_of_selfViable
      (Proofs.Optimistic.confStore S rho w c).toHealing.toFG
      (Proofs.Optimistic.confStore S rho w c).T hmem hFEnd hrootConf hbandStore
  have hcandidate : K.erase ∈
      confTree (confirmationInputRead S rho w c).st.core := by
    simpa only [hKErase, confTree, Protocol.get_filtered_block_tree,
      Proofs.Optimistic.confStore_eq_confirmationInputRead] using hfull
  have hread : S.hc.Γ_0 S.E.Δ (r + 1) ≤
      Protocol.confirmation_time S.E c := by
    rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E c]
    calc
      S.hc.Γ_0 S.E.Δ (r + 1) ≤
          Protocol.proposal_time S.E (c + 1) :=
        Γ_0_le_proposal_time_of_round_eq'' S hround
      _ ≤ Protocol.vote_time S.E (c + 1) :=
        (Protocol.proposal_time_lt_vote_time S.E (c + 1)).le
      _ ≤ Protocol.vote_time S.E (c + 1) + S.E.Δ :=
        Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  have hupperK : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) (EndAt k) := by
    rw [hprev]
    exact hupper
  have hanchor : Block.Preceq
      (confirmationAnchorAt S rho w c) E0.erase := by
    exact confirmationAnchorAt_preceq_of_previousCarriers S adm hfb hround
      hpostAction hcut hslotHor
      (by simpa only [hE0] using hupperK) hw
      (by simpa only [hE0] using hrootEndAt)
  have hKPrev : K.erase = Prev := hKEnd.trans hprev
  have hout := genuineConfirmationAndPreceq_of_postHealingCone
    S adm hcom hc hpostVote hslotHor hw (B := K)
    (by simpa only [hKEnd] using hvotes)
    (by simpa only [hKErase] using hroot)
    (by simpa only [hKErase] using hanchor) hcandidate
  simpa only [movingSlotConfirmationOutput, hKPrev] using hout


/-- The same at an N entry state. -/
theorem MovingSlotEntryStateN.confOutcome_atPrev_of_ceiling_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hc : 0 < c)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) :
    GenuineConfirmationWith
        (NamedProfile.gradeContract (confirmationInputRead S rho w c).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho w c) c
        (movingSlotConfirmationOutput S rho c w) ∧
      Block.Preceq Prev (movingSlotConfirmationOutput S rho c w) :=
  hentry.toPreN.confOutcome_atPrev_of_ceiling_named S adm hcom hfb hc hround
    hupper hpostAction hcut hpostVote hslotHor hw


/-- The next-slot vote anchor is below the ceiling endpoint for an N entry
state. -/
theorem MovingSlotEntryStateN.windowVoteAnchor_of_ceiling_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {Next : Block V} (hNext : Block.Preceq End Next) :
    ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (c + 1)) Next = true := by
  intro w hw
  obtain ⟨EndAt, hhistory, hprev, _hEnd⟩ := hentry.prevEndpoint
  set k := strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) with hk
  have hpre : MovingFrontierChainStateN S rho t1 M0
      (strictEventIndex rho t1) k EndAt :=
    hhistory.prefix (strictEventIndex_mono rho hentry.startTime)
      (strictEventIndex_le_inclusiveEventIndex rho _)
  obtain ⟨E0, hE0, hE0run⟩ :=
    hpre.endpointRun k hpre.start_le (Nat.le_refl k)
  have hrootRaw : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E (c + 1))).core.toHealing.toFG) E0.erase :=
    hpre.voteRoot_preceq_endpointAtCursor_named S adm hfb
      (Nat.le_refl k) hw hentry.startTime hE0 hE0run
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG)
      E0.erase := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hrootRaw
  have hvoteHor : Protocol.vote_time S.E (c + 1) ≤ rho.horizon := by
    have htime : Protocol.vote_time S.E (c + 1) ≤
        Protocol.confirmation_time S.E c := by
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E c]
      exact le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
    exact htime.trans hslotHor
  have hupperK : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) E0.erase := by
    intro u hu
    simpa only [hE0, hprev] using hupper u hu
  have hanchor : Block.Preceq
      (voterAnchorAt S rho w (c + 1)) E0.erase :=
    voterAnchorAt_preceq_of_previousCarriers S adm hfb hround
      hpostAction hcut hvoteHor hupperK hw hroot
  have hanchorNext : Block.Preceq
      (voterAnchorAt S rho w (c + 1)) Next := by
    refine Block.preceq_trans hanchor ?_
    exact Block.preceq_trans
      (by simpa only [hE0, hprev] using hentry.prevLe) hNext
  exact Block.compatible_of_preceq_common hanchorNext
    (Block.preceq_self Next)



/-
/-- **The confirmation certification, with the ceiling supplied.** -/
theorem MovingSlotPreEntry.confOutcome_atPrev_of_ceiling
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End: Block V}
    (hentry: MovingSlotPreEntry S rho t1 M0 (c + 1) Prev End)
    (hc: 0 < c)
    {r: Round}
    (hround: S.hc.round_of (c + 1) = r + 1)
    (hupper: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev)
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
  have hupperK: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) (EndAt k):= by
    rw [hprev]
    exact hupper
  have hanchorRaw:= readAnchor_preceq_of_previousActionCeiling
    S adm hfb hpostAction hcut hread hw
    (by simpa only [pre] using hmem) hrootRaw hupperK
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

/-- **The vote anchor, with the ceiling supplied.** -/
theorem MovingSlotEntryState.windowVoteAnchor_of_ceiling
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End: Block V}
    (hentry: MovingSlotEntryState S rho t1 M0 (c + 1) Prev End)
    {r: Round}
    (hround: S.hc.round_of (c + 1) = r + 1)
    (hupper: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor: Protocol.confirmation_time S.E c ≤ rho.horizon)
    {Next: Block V} (hNext: Block.Preceq End Next):
    ∀ w ∈ rho.honest,
      Block.compatible (Proofs.Optimistic.healAnchor S.E S.hc
        (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing) Next = true:= by
  intro w hw
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
  have hrootRaw: Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E (c + 1))).toHealing.toFG) (EndAt k):=
    hpre.voteRoot_preceq_endpointAtCursor S adm hfb (Nat.le_refl k) hw
      hentry.startTime
  have hroot: Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG)
      (EndAt k):= by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hrootRaw
  have havailable:= honestHeadsAvailableBefore_of_postHealingCone_atVoteDuty
    S adm hw hpostVote
      ((support_cutoff_le_confirmation_time S.E c).trans hslotHor)
      hroot hvotes
  have hprocessed:= Protocol.voterProcessedConeEndpoint_of_availableBefore
    S adm hcom havailable hvotes
  have hmem: EndAt k ∈
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (c + 1))).T:= by
    have hdata:= hprocessed
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hdata.1
  have hread: S.hc.Γ_0 S.E.Δ (r + 1) ≤
      Protocol.vote_time S.E (c + 1):=
    Γ_0_le_vote_time_of_round_eq S hround
  have hupperK: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) (EndAt k):= by
    rw [hprev]
    exact hupper
  have hanchorRaw:= readAnchor_preceq_of_previousActionCeiling
    S adm hfb hpostAction hcut hread hw hmem hrootRaw hupperK
  have hslotEq:
      (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.s = c + 1:= by
    simpa only [Protocol.Store.toHealing] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (c + 1)
  have hanchor: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing) (EndAt k):= by
    rw [Proofs.Optimistic.healAnchor_eq_get_sg_root, hslotEq, hround]
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hanchorRaw
  refine Block.compatible_of_preceq_common ?_ (Block.preceq_self Next)
  refine Block.preceq_trans hanchor ?_
  rw [hprev]
  exact Block.preceq_trans hentry.prevLe hNext
-/

/-! ## The window facts, with the ceiling supplied
The schedule bundle of `MovingChainSlotStepRun` asks the history to reach back
to the previous round's action. This one asks for the ceiling that reach-back
was only ever produces. -/

/-- The timing a slot window needs at its confirmation instant when that
instant is also a Section 7 action, with the previous round's carrier ceiling
supplied rather than read from the history. -/
def MovingSlotActionCeiling
    (S : Setup V) (rho : Run V) (c : Slot) (Prev : Block V) : Prop :=
  ∀ q : Round, S.a q = Protocol.confirmation_time S.E c →
    0 < q ∧ S.E.t_GST ≤ S.a (q - 1) ∧
      S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon ∧
      ∀ u ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho u (q - 1)) Prev


/-
/-- **`windowFacts` with the carrier ceiling supplied.**

Same statement as `MovingSlotEntryState.windowFacts`, with `t1 ≤ S.a r`
replaced by the ceiling itself at both the vote read and the confirmation read,
and with the action-instant branch taking its ceiling from the caller too. -/
theorem MovingSlotEntryState.windowFacts_of_ceiling
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End: Block V}
    (hentry: MovingSlotEntryState S rho t1 M0 (c + 1) Prev End)
    (hc: 0 < c)
    {r: Round}
    (hround: S.hc.round_of (c + 1) = r + 1)
    (hupper: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hpostProp: S.E.t_GST ≤ Protocol.proposal_time S.E c)
    (hslotHor: Protocol.confirmation_time S.E c ≤ rho.horizon)
    (htiming: MovingSlotActionCeiling S rho c Prev):
    ∃ Next: Block V,
      MovingSlotFrontierAt S rho c End Next ∧
        MovingSlotWindowFacts S rho (c + 1) End Next:= by
  obtain ⟨Next, hfrontier⟩:=
    hentry.existsWindowFrontier S adm hpostProp hslotHor
  have hprevNext: Block.Preceq Prev Next:=
    Block.preceq_trans hentry.prevLe hfrontier.oldPreceq
  refine ⟨Next, hfrontier, ?_⟩
  refine movingSlotWindowFacts_of_readInputs S adm hfb
    hfrontier.oldPreceq
    (by simpa only [Nat.add_sub_cancel] using hslotHor)
    hentry.headEq ?_ ?_ ?_
  · intro w hw
    exact hentry.windowVoteAnchor_of_ceiling S adm hcom hfb hround hupper
      hpostAction hcut hpostVote hslotHor (Block.preceq_self End) w hw
  · simp only [Nat.add_sub_cancel]
    intro w hw
    have hgenuine:= (hentry.toPre.confOutcome_atPrev_of_ceiling S adm hcom
      hfb hc hround hupper hpostAction hcut hpostVote hslotHor hw).1
    exact ⟨hgenuine, hfrontier.genuinePreceq w hw _ hgenuine⟩
  · intro q hq
    rw [Nat.add_sub_cancel] at hq
    obtain ⟨hq0, hpost, hcutq, hceil⟩:= htiming q hq
    exact ⟨hq0, hpost, hcutq, fun u hu =>
      Block.preceq_trans (hceil u hu) hprevNext⟩

/-- **The honest proposal parent, with the ceiling supplied.** -/
theorem MovingFrontierChainState.endpoint_preceq_proposedParent_of_ceiling
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 k: Nat} {EndAt: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 k EndAt)
    {c: Slot} (hc: 0 < c)
    {r: Round}
    (hround: S.hc.round_of (c + 1) = r + 1)
    (hupper: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) (EndAt k))
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hcutHor: Protocol.support_cutoff S.E c ≤ rho.horizon)
    (hcursor: strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) ≤ k)
    (hprop: S.E.proposer (c + 1) ∈ rho.honest)
    (hvotes: Proofs.Optimistic.HonestVotesCone S rho c
      (fun X => Block.Preceq (EndAt k) X))
    (hstart: t1 ≤ Protocol.proposal_time S.E (c + 1)):
    Block.Preceq (EndAt k) (proposedParent S rho (c + 1)):= by
  let duty:= proposerDutyStore S rho (c + 1)
  let raw:= (Protocol.proposer_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s).toFinset
  let support:=
    (Protocol.proposer_support_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s).toFinset
  have hdutySlot: duty.s = c + 1:= by
    simp only [duty, proposerDutyStore, Proofs.Optimistic.tickStore,
      Proofs.Optimistic.slotOf_proposal_time]
  have hsep: ∀ q: Round,
      S.a q < Protocol.proposal_time S.E (c + 1) →
      S.a q < Protocol.proposal_time S.E (c + 1):= fun _ hq => hq
  have hrootRaw:= h.readRoot_preceq_endpointAtCursor S adm hfb hsep hcursor
    hprop hstart
  have hbandRaw:= h.readFrontier_sub_one_le_endpointAtCursor S adm hfb hsep
    hcursor hprop
  have hroot: Block.Preceq
      (Protocol.get_fg_root duty.toHealing.toFG) (EndAt k):= by
    simpa only [duty, proposerDutyStore, Proofs.Optimistic.tickStore] using hrootRaw
  have havailable:= honestHeadsAvailableBefore_of_postHealingCone_at
    S adm hprop hpostVote hcutHor
      (support_cutoff_le_proposal_time_succ S.E c) hrootRaw hvotes
  have hmemRaw: EndAt k ∈ (rho.storeBeforeTime S (S.E.proposer (c + 1))
      (Protocol.proposal_time S.E (c + 1))).T:=
    proposerStore_mem_of_cone S adm hcom havailable hvotes
  have hresolve:= headsResolveIn_proposerDutyStore_of_postHealingCone
    S adm hpostVote hcutHor hprop hroot hvotes
  have hcone0:= coneSupport_proposerDutyStore_after_gst
    S adm hcom hc hpostVote hcutHor hvotes hprop hresolve
  have hcone: Proofs.Optimistic.ConeSupport S.E duty.T raw support raw c
      rho.honest (fun X => Block.Preceq (EndAt k) X):= by
    simpa only [duty, raw, support, hdutySlot] using hcone0
  have hvalid0:= proposerDutyStore_proposer_view_valid S adm (c + 1)
  have hvalid: Protocol.VoteSetValid S.E c raw:= by
    simpa only [duty, raw, hdutySlot, Nat.add_sub_cancel] using hvalid0
  have hread: S.hc.Γ_0 S.E.Δ (r + 1) ≤ Protocol.proposal_time S.E (c + 1):=
    Γ_0_le_proposal_time_of_round_eq'' S hround
  have hanchorRaw:= readAnchor_preceq_of_previousActionCeiling
    S adm hfb hpostAction hcut hread hprop hmemRaw hrootRaw hupper
  have hslotEq: duty.toHealing.s = c + 1:= by
    simpa only [Protocol.Store.toHealing] using hdutySlot
  have hanchor: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc duty.toHealing) (EndAt k):= by
    rw [Proofs.Optimistic.healAnchor_eq_get_sg_root, hslotEq, hround]
    simpa only [duty, proposerDutyStore, Proofs.Optimistic.tickStore] using hanchorRaw
  have hpath: ∀ C: Block V,
      Block.Preceq (Proofs.Optimistic.healAnchor S.E S.hc duty.toHealing) C →
      C ≠ Proofs.Optimistic.healAnchor S.E S.hc duty.toHealing →
      Block.Preceq C (EndAt k) →
      C ∈ Protocol.get_filtered_block_tree duty.toHealing.toFG:= by
    intro C hAC _ hCEnd
    have hrootC: Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S (S.E.proposer (c + 1))
            (Protocol.proposal_time S.E (c + 1))).toHealing.toFG) C:= by
      have hrootAnchor:= StoreFinality.get_fg_root_preceq_get_sg_root
        S.E S.hc duty
      have hstep: Block.Preceq
          (Protocol.get_fg_root duty.toHealing.toFG) C:=
        Block.preceq_trans hrootAnchor
          (by simpa only [Proofs.Optimistic.healAnchor_eq_get_sg_root] using hAC)
      simpa only [duty, proposerDutyStore, Proofs.Optimistic.tickStore] using hstep
    have hpathRaw:= storeBeforeTime_path_mem_filtered_of_band S adm
      hmemRaw hbandRaw hrootC hCEnd
    simpa only [duty, proposerDutyStore, Proofs.Optimistic.tickStore] using hpathRaw
  have hhead:= Proofs.Optimistic.heal_get_head_preceq S.E S.hc duty.toHealing
    raw support c rho.honest hcone hvalid hanchor hpath
  simpa only [proposedParent, Protocol.get_head, duty, raw, support,
    hdutySlot, Nat.add_sub_cancel] using hhead

/-! ## The vote read, with the ceiling supplied

The two remaining ceiling users, so a fold whose history starts after the
previous round's action can still read its own vote duty. -/

theorem MovingSlotPreEntry.voteAnchor_preceq_prev_of_ceiling
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End: Block V}
    (hentry: MovingSlotPreEntry S rho t1 M0 (c + 1) Prev End)
    {r: Round}
    (hround: S.hc.round_of (c + 1) = r + 1)
    (hupper: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor: Protocol.confirmation_time S.E c ≤ rho.horizon)
    {w: V} (hw: w ∈ rho.honest):
    Block.Preceq (Proofs.Optimistic.healAnchor S.E S.hc
      (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing) Prev:= by
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
  have hrootRaw: Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E (c + 1))).toHealing.toFG) (EndAt k):=
    hpre.voteRoot_preceq_endpointAtCursor S adm hfb (Nat.le_refl k) hw
      hentry.startTime
  have hroot: Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG)
      (EndAt k):= by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hrootRaw
  have havailable:= honestHeadsAvailableBefore_of_postHealingCone_atVoteDuty
    S adm hw hpostVote
      ((support_cutoff_le_confirmation_time S.E c).trans hslotHor)
      hroot hvotes
  have hprocessed:= Protocol.voterProcessedConeEndpoint_of_availableBefore
    S adm hcom havailable hvotes
  have hmem: EndAt k ∈
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (c + 1))).T:= by
    have hdata:= hprocessed
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hdata.1
  have hread: S.hc.Γ_0 S.E.Δ (r + 1) ≤ Protocol.vote_time S.E (c + 1):=
    Γ_0_le_vote_time_of_round_eq S hround
  have hupperK: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) (EndAt k):= by
    rw [hprev]
    exact hupper
  have hanchorRaw:= readAnchor_preceq_of_previousActionCeiling
    S adm hfb hpostAction hcut hread hw hmem hrootRaw hupperK
  have hslotEq:
      (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.s = c + 1:= by
    simpa only [Protocol.Store.toHealing] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (c + 1)
  rw [← hprev, Proofs.Optimistic.healAnchor_eq_get_sg_root, hslotEq, hround]
  simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
    Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hanchorRaw

/-- **The primed Goldfish vote input, with the ceiling supplied.** -/
theorem MovingSlotPreEntry.voteInputs_of_ceiling
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End: Block V}
    (hentry: MovingSlotPreEntry S rho t1 M0 (c + 1) Prev End)
    {r: Round}
    (hround: S.hc.round_of (c + 1) = r + 1)
    (hupper: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev)
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
      (hentry.voteAnchor_preceq_prev_of_ceiling S adm hcom hfb hround hupper
        hpostAction hcut hpostVote hslotHor hw)
      (Block.preceq_self Prev)

/-! ## The proposal read, with the ceiling supplied

(The private root helper of is restated first.) -/

-/


theorem MovingFrontierChainStateN.voteInputsAtVote_of_proposalEvent_of_ceiling_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {r : Round} {s : Slot}
    (hround : S.hc.round_of (s + 1) = r + 1)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) (End i))
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hslotHor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq (End i) X))
    (hevent : rho.events[i]? = some
      (Event.tick (S.E.proposer (s + 1))
        (Protocol.proposal_time S.E (s + 1))))
    {w : V} (hw : w ∈ rho.honest)
    (hstart : t1 ≤ Protocol.vote_time S.E (s + 1)) :
    GoldfishConeVoteInputs' S rho s (End i) w ∧
      End i ∈ voterCandidateTreeAt S rho w (s + 1) ∧
      Block.Preceq (voterAnchorAt S rho w (s + 1)) (End i) := by
  exact MovingFrontierChainStateN.voteInputsAtVote_of_proposalEvent_named_of_ceiling
    S adm hcom hfb h hround hupper hpostAction hcut hpostVote hslotHor hvotes
      hevent hw hstart

#print axioms MovingFrontierChainStateN.voteInputsAtVote_of_proposalEvent_of_ceiling_named

theorem MovingFrontierChainStateN.proposalAnchor_preceq_endpointAtProposal_of_ceiling_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {r : Round} {s : Slot}
    (hround : S.hc.round_of s = r + 1)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) (End i))
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hevent : rho.events[i]? = some
      (Event.tick (S.E.proposer s) (Protocol.proposal_time S.E s)))
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    (hendParent : Block.Preceq (End i) (proposedParent S rho s))
    {E : NamedBlock V} (hE : E.erase = End i) (hErun : RunBlock S rho E) :
    Block.Preceq
      (Internal.PhaseGrades.nodeAnchor S (proposerReadAt S rho s)
        (S.hc.round_of (proposerReadAt S rho s).st.core.s)) (End i) := by
  have hrootState := h.root_preceq_endpointAtProposal_beforeVote
    S adm hfb hevent hevent
      (by simpa only [Event.time] using
        (Protocol.proposal_time_lt_vote_time S.E s))
      hprop h.start_le hE hErun
  have hstate := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hevent
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (proposerReadAt S rho s).st.core.toHealing.toFG) (End i) := by
    rw [hstate] at hrootState
    simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hrootState
  exact proposalAnchorAt_preceq_of_previousCarriers_named
    S adm hfb hround hpostAction hcut hhor hupper hprop hroot

#print axioms MovingFrontierChainStateN.proposalAnchor_preceq_endpointAtProposal_of_ceiling_named



private theorem confirmation_time_normal_c (E : Env V) (s : Slot) :
    Protocol.confirmation_time E s = (4 * (s : Time) + 6) * E.Δ := by
  unfold Protocol.confirmation_time Env.t slotStart
  ring

private theorem vote_time_normal_c (E : Env V) (s : Slot) :
    Protocol.vote_time E s = (4 * (s : Time) + 1) * E.Δ := by
  unfold Protocol.vote_time Env.t slotStart
  ring


private theorem voteTimeSucc_le_confirmationTime_c (E : Env V) (s : Slot) :
    Protocol.vote_time E (s + 1) ≤ Protocol.confirmation_time E s := by
  rw [vote_time_normal_c, confirmation_time_normal_c]
  refine Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt E.Δ_pos)
  push_cast
  omega

/-! ## The rest of the pre-entry reads, with the ceiling supplied

The capture, both compatibility readings and the vote-cone step, so a whole
slot-entry state can be built inside the boundary round. -/




/-! ## The slot data with the ceiling, and the entry state from it -/

/-- The schedule and horizon data one slot window consumes, with the previous
round's carrier ceiling in place of the history reach-back. -/
structure MovingSlotWindowDataC
    (S : Setup V) (rho : Run V) (M0 : Height) (c : Slot) (Prev : Block V) :
    Prop where
  pos : 0 < c
  round : ∃ r : Round, S.hc.round_of (c + 1) = r + 1 ∧
    S.E.t_GST ≤ S.a r ∧ S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon ∧
    ∀ u ∈ rho.honest, Block.Preceq (actionSGBlockAt S rho u r) Prev
  postVote : S.E.t_GST ≤ Protocol.vote_time S.E c
  postProp : S.E.t_GST ≤ Protocol.proposal_time S.E c
  slotHor : Protocol.confirmation_time S.E c ≤ rho.horizon


/-
/-- **A pre-entry state with its head equality is an entry state**, with the
ceiling supplied. `MovingChainBaseRun`'s `toEntry` reads the ceiling out of the
history; this one takes it, so it applies inside the boundary round. -/
theorem MovingSlotPreEntry.toEntry_of_ceiling
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End: Block V}
    (hpre: MovingSlotPreEntry S rho t1 M0 (c + 1) Prev End)
    (hdata: MovingSlotWindowDataC S rho M0 c Prev)
    (hslotHorSucc: Protocol.confirmation_time S.E (c + 1) ≤ rho.horizon)
    (hheadEq: S.E.proposer (c + 1) ∈ rho.honest → ∀ w ∈ rho.honest,
      voteDutyHead S rho w (c + 1) = End)
    (hbyz: S.E.proposer (c + 1) ∉ rho.honest → End = Prev):
    MovingSlotEntryState S rho t1 M0 (c + 1) Prev End:= by
  obtain ⟨r, hround, hpostAction, hcut, hupper⟩:= hdata.round
  have hvoteHor: Protocol.vote_time S.E (c + 1) ≤ rho.horizon:=
    (voteTime_le_confirmationTime_c S.E (c + 1)).trans hslotHorSucc
  have hvotes: Proofs.Optimistic.HonestVotesCone S rho (c + 1)
      (fun X => Block.Preceq End X):= by
    by_cases hprop: S.E.proposer (c + 1) ∈ rho.honest
    · intro u hu huc
      obtain ⟨hrun, hemit⟩:=
        voteDutyHead_runBlock_and_emits S adm (Nat.succ_pos c) hvoteHor hu huc
      exact ⟨voteDutyHead S rho u (c + 1),
        by rw [hheadEq hprop u hu]; exact Block.preceq_self _, hrun, hemit⟩
    · have hcone:= hpre.votesCone_prev_of_ceiling S adm hcom hfb hdata.pos
        hround hupper hpostAction hcut hdata.postVote hdata.slotHor
      rw [hbyz hprop]
      exact hcone
  refine
    { startTime:= hpre.startTime
      prevEndpoint:= hpre.prevEndpoint
      prevVotes:= hpre.prevVotes
      votes:= hvotes
      headEq:= hheadEq
      confCompatible:= ?_ }
  by_cases hprop: S.E.proposer (c + 1) ∈ rho.honest
  · obtain ⟨v, hv⟩:= honest_nonempty_of_honestCommittees hcom
    exact hpre.confCompatible_honest_of_ceiling S adm hcom hfb hdata.pos
      hround hupper hpostAction hcut hdata.postVote hdata.postProp
      hdata.slotHor (hheadEq hprop) hv
  · have hcompat:= hpre.confCompatible_byzantine_of_ceiling S adm hcom hfb
      hdata.pos hround hupper hpostAction hcut hdata.postVote
      hdata.slotHor
    rw [hbyz hprop]
    exact hcompat

/-! ## The window vote cone, with the ceiling supplied -/

theorem MovingSlotEntryState.windowVotesCone_of_ceiling
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End: Block V}
    (hentry: MovingSlotEntryState S rho t1 M0 (c + 1) Prev End)
    (hc: 0 < c)
    {r: Round}
    (hround: S.hc.round_of (c + 1) = r + 1)
    (hupper: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hpostProp: S.E.t_GST ≤ Protocol.proposal_time S.E c)
    (hslotHor: Protocol.confirmation_time S.E c ≤ rho.horizon)
    {Next: Block V}
    (hfrontier: MovingSlotFrontierAt S rho c End Next):
    Proofs.Optimistic.HonestVotesCone S rho (c + 1)
      (fun X => Block.Preceq Next X):= by
  rcases hfrontier.source with rfl | ⟨v, hv, hgenuine⟩
  · exact hentry.votes
  have hprevVotes: Proofs.Optimistic.HonestVotesCone S rho c
      (fun X => Block.Preceq Prev X):= by
    simpa only [Nat.add_sub_cancel] using hentry.prevVotes
  have hvoteHorC: Protocol.vote_time S.E c ≤ rho.horizon:=
    (voteTime_le_confirmationTime_c S.E c).trans hslotHor
  have hvoteHorSucc: Protocol.vote_time S.E (c + 1) ≤ rho.horizon:=
    (voteTimeSucc_le_confirmationTime_c S.E c).trans hslotHor
  have hresolve:= headsResolveIn_confStore_of_postHealingCone
    S adm hv hpostVote
      ((support_cutoff_le_confirmation_time S.E c).trans hslotHor)
      (hentry.toPre.confRoot_preceq_prev S adm hfb hv)
      hprevVotes
  obtain ⟨x, hx, hxc, hDx⟩:= genuineConfirmation_exists_honestSupporter
    S adm hcom hc hpostVote hslotHor hv hresolve hgenuine
  have hhead:= honestHead_voteDutyHead S adm hc hvoteHorC hx hxc
  intro w hw hwc
  have hrootVoteRaw:=
    hentry.toPre.voteRoot_preceq_prev S adm hfb hw
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
  have hNextPre: Next ∈ pre.T:= by
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
  have hPrevNext: Block.Preceq Prev Next:=
    Block.preceq_trans hentry.prevLe hfrontier.oldPreceq
  have hband: (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).h_max - 1 ≤
      ((Proofs.Optimistic.voteDutyStore S rho w (c + 1)).σ Next).h:= by
    have hbandPre: pre.h_max - 1 ≤ (pre.σ Next).h:= by
      rw [hagree Next hNextPre]
      exact (hentry.toPre.voteFrontier_sub_one_le_prevHeight S adm hfb hw).trans
        (Protocol.derived_h_mono S.E S.cfg hPrevNext)
    simpa only [pre, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hbandPre
  have hanchorEnd: Block.Preceq (Proofs.Optimistic.healAnchor S.E S.hc
      (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing) End:=
    Block.preceq_trans
      (hentry.toPre.voteAnchor_preceq_prev_of_ceiling S adm hcom hfb hround hupper hpostAction
        hcut hpostVote hslotHor hw)
      hentry.prevLe
  have hcapture:= genuineConfirmation_preceq_nextVoteDutyHead_of_endpointBand
    S adm hv hw hpostProp hslotHor hgenuine hfrontier.oldPreceq hanchorEnd
    hprocessed hband
  obtain ⟨hrun, hemit⟩:=
    voteDutyHead_runBlock_and_emits S adm (Nat.succ_pos c) hvoteHorSucc hw hwc
  exact ⟨voteDutyHead S rho w (c + 1), hcapture, hrun, hemit⟩
-/

/-- **The slot-`(c+1)` named vote cone above a ceiling window endpoint.**

This is the N-history twin of the ceiling cone. The supplied carrier ceiling
replaces the history reach-back used for the vote anchor; the confirmation and
vote-read parts use the prepared named contract. -/
theorem MovingSlotEntryStateN.windowVotesCone_of_ceiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hc : 0 < c)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hpostProp : S.E.t_GST ≤ Protocol.proposal_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {Next : Block V}
    (hfrontier : MovingSlotFrontierAt S rho c End Next) :
    NamedHonestVotesCone S rho (c + 1)
      (fun X => Block.Preceq Next X) := by
  rcases hfrontier.source with rfl | ⟨v, hv, hgenuine⟩
  · exact hentry.votes
  obtain ⟨EndAt, hhistory, hprev, _hEnd⟩ := hentry.prevEndpoint
  set k := strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) with hk
  have hpre : MovingFrontierChainStateN S rho t1 M0
      (strictEventIndex rho t1) k EndAt :=
    hhistory.prefix (strictEventIndex_mono rho hentry.startTime)
      (strictEventIndex_le_inclusiveEventIndex rho _)
  obtain ⟨E0, hE0, hE0run⟩ :=
    hpre.endpointRun k hpre.start_le (Nat.le_refl k)
  have hprevVotes : NamedHonestVotesCone S rho c
      (fun X => Block.Preceq (EndAt k) X) := by
    rw [hprev]
    simpa only [Nat.add_sub_cancel] using hentry.prevVotes
  have hPrevNext : Block.Preceq Prev Next :=
    Block.preceq_trans hentry.prevLe hfrontier.oldPreceq
  intro w hw hwcommittee
  have hrootRaw : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E (c + 1))).core.toHealing.toFG) E0.erase :=
    hpre.voteRoot_preceq_endpointAtCursor_named S adm hfb
      (Nat.le_refl k) hw hentry.startTime hE0 hE0run
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG)
      E0.erase := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hrootRaw
  have hrootNext : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG) Next := by
    exact Block.preceq_trans hroot (by
      simpa only [hE0, hprev] using hPrevNext)
  have hgenuine' : GenuineConfirmation (contract :=
      NamedProfile.gradeContract (confirmationInputRead S rho v c).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v c) c Next := by
    exact ⟨hgenuine.selected, hgenuine.genuine⟩
  have hprocessedOld :=
    Protocol.voterProcessedTarget_of_genuineConfirmation_after_gst
      S adm hv hw hpostProp hslotHor hgenuine' hrootNext
  have hprocessed : Next ∈
      Protocol.voter_processed_block_tree S.E
        (voteDutyRead S rho w (c + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore
        (voteDutyRead S rho w (c + 1)).st.core.s := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hprocessedOld
  have htime : Protocol.vote_time S.E (c + 1) ≤
      Protocol.confirmation_time S.E c :=
    voteTimeSucc_le_confirmationTime_c S.E c
  have hmax := storeBeforeTime_hMax_mono S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w htime
  have hconfBand := hpre.confFrontier_sub_one_le_endpointAtCursor_named
    S adm hfb (c := c) (Nat.le_refl k) hw hE0 hE0run
  have hendpointMono : ∀ {a b : Nat},
      strictEventIndex rho t1 ≤ a → a ≤ b → b ≤ k →
      Block.Preceq (EndAt a) (EndAt b) := by
    intro a b ha hab hb
    induction hab with
    | refl => exact Block.preceq_self _
    | @step b hab ih =>
        exact Block.preceq_trans (ih (Nat.le_trans (Nat.le_succ b) hb))
          (hpre.endpointMono b (ha.trans hab) (Nat.lt_of_succ_le hb))
  have hNextCore : Next ∈
      (voteDutyRead S rho w (c + 1)).st.core.T := by
    have hdata := hprocessed
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    simpa only [Protocol.Store.toHealing] using hdata.1
  have hNextPre : Next ∈
      (rho.stateBeforeTime S (Protocol.vote_time S.E (c + 1)) w).st.core.T := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hNextCore
  obtain ⟨N, hNbody, hNerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.vote_time S.E (c + 1)) w hNextPre
  have hNrun : RunBlock S rho N := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.vote_time S.E (c + 1))
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
    simpa only [Run.storeBeforeTime, hn] using hNbody
  have hE0N : NamedBlock.Preceq E0 N :=
    Protocol.namedPreceq_of_runBlock_erase_preceq adm hE0run hNrun (by
      simpa only [hE0, hprev, hNerase] using hPrevNext)
  have hsigma :
      (voteDutyRead S rho w (c + 1)).st.core.σ Next =
        Protocol.derive_named S.E S.cfg N := by
    rw [← hNerase]
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
        (Protocol.vote_time S.E (c + 1)) w N hNbody
  have hband :
      (voteDutyRead S rho w (c + 1)).st.core.h_max - 1 ≤
        ((voteDutyRead S rho w (c + 1)).st.core.σ Next).h := by
    rw [hsigma]
    have hmaxSub :
        (voteDutyRead S rho w (c + 1)).st.core.h_max - 1 ≤
          (rho.storeBeforeTime S w
            (Protocol.confirmation_time S.E c)).core.h_max - 1 := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Run.storeBeforeTime] using Nat.sub_le_sub_right hmax 1
    exact hmaxSub.trans (hconfBand.trans
      (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hE0N))
  have hanchor : Block.Preceq
      (voterAnchorAt S rho w (c + 1)) E0.erase := by
    have hvoteHor : Protocol.vote_time S.E (c + 1) ≤ rho.horizon :=
      htime.trans hslotHor
    have hupperE0 : ∀ u ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho u r) E0.erase := by
      intro u hu
      simpa only [hE0, hprev] using hupper u hu
    exact voterAnchorAt_preceq_of_previousCarriers S adm hfb hround
      hpostAction hcut hvoteHor hupperE0 hw hroot
  have hanchorEnd : Block.Preceq
      (voterAnchorAt S rho w (c + 1)) End :=
    Block.preceq_trans hanchor (by
      simpa only [hE0, hprev] using hentry.prevLe)
  have hbandN :
      (voteDutyRead S rho w (c + 1)).st.core.h_max - 1 ≤
        ((voteDutyRead S rho w (c + 1)).st.core.σ N.erase).h := by
    simpa only [← hNerase] using hband
  have hcapture := genuineConfirmation_preceq_nextVoteDutyHead_of_endpointBand
    S adm hv hw hpostProp hslotHor (B := N)
    (by simpa only [← hNerase] using hgenuine)
    (by simpa only [← hNerase] using hfrontier.oldPreceq)
      hanchorEnd (by simpa only [← hNerase] using hprocessed) hbandN
  obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
    voteDutyHead_runBlock_and_emits S adm (Nat.succ_pos c)
      (htime.trans hslotHor) hw hwcommittee
  have hcapture' : Block.Preceq Next (voteDutyHead S rho w (c + 1)) := by
    simpa only [voteDutyHead, hNerase] using hcapture
  exact ⟨X, by simpa only [hXerase] using hcapture', hXrun, hXemit⟩

#print axioms MovingSlotEntryStateN.windowVotesCone_of_ceiling

private theorem proposal_time_normal_c (E : Env V) (s : Slot) :
    Protocol.proposal_time E s = (4 * (s : Time) + 0) * E.Δ := by
  unfold Protocol.proposal_time Env.t slotStart
  ring

private theorem view_freeze_normal_c (E : Env V) (s : Slot) :
    Protocol.view_freeze E s = (4 * (s : Time) + 3) * E.Δ := by
  unfold Protocol.view_freeze Env.t slotStart
  ring

private theorem view_freeze_lt_proposal_time_succ_c (E : Env V) (s : Slot) :
    Protocol.view_freeze E s < Protocol.proposal_time E (s + 1) := by
  rw [view_freeze_normal_c, proposal_time_normal_c]
  refine Int.mul_lt_mul_of_pos_right ?_ E.Δ_pos
  push_cast
  omega

private theorem proposal_time_lt_succ_c (E : Env V) (s : Slot) :
    Protocol.proposal_time E s < Protocol.proposal_time E (s + 1) := by
  rw [proposal_time_normal_c, proposal_time_normal_c]
  refine Int.mul_lt_mul_of_pos_right ?_ E.Δ_pos
  push_cast
  omega

private theorem proposalTimeSucc_le_confirmationTime_c (E : Env V) (s : Slot) :
    Protocol.proposal_time E (s + 1) ≤ Protocol.confirmation_time E s := by
  rw [proposal_time_normal_c, confirmation_time_normal_c]
  refine Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt E.Δ_pos)
  push_cast
  omega

omit [DecidableEq V] [Fintype V] in
private theorem inclusive_le_strict_of_lt_c
    (rho : Run V) {t0 t1 : Time} (hlt : t0 < t1) :
    inclusiveEventIndex rho t0 ≤ strictEventIndex rho t1 := by
  unfold inclusiveEventIndex strictEventIndex
  exact (List.monotone_filter_right rho.events (fun e he => by
    simp only [decide_eq_true_eq] at he ⊢
    exact lt_of_le_of_lt he hlt)).length_le

/-! ## The slot step, with the ceiling supplied

With these the fold crosses the slots inside the boundary round, where the
history cannot reach back to the previous round's action. -/




private theorem nat_not_succ_succ_le_c (c : Nat) : ¬ (c + 1 + 1 ≤ c + 1) := by
  omega

private theorem nat_le_of_lt_succ_c {d c : Nat} (h : d < c + 1 + 1) :
    d ≤ c + 1 := by omega

private theorem nat_not_add_two_le_succ_c (d : Nat) : ¬ (d + 2 ≤ d + 1) := by
  omega

private theorem nat_eq_of_succ_le_succ_of_lt_succ_c {d c : Nat}
    (hge : c + 1 ≤ d + 1) (hlt : d + 1 < c + 1 + 1) : d = c :=
  Nat.le_antisymm (Nat.le_of_succ_le_succ (Nat.le_of_lt_succ hlt))
    (Nat.le_of_succ_le_succ hge)

/-- The ceiling data weakens along the endpoint chain. -/
theorem MovingSlotWindowDataC.mono
    {S : Setup V} {rho : Run V} {M0 : Height} {c : Slot} {A B : Block V}
    (h : MovingSlotWindowDataC S rho M0 c A) (hAB : Block.Preceq A B) :
    MovingSlotWindowDataC S rho M0 c B where
  pos := h.pos
  round := by
    obtain ⟨r, hround, hpost, hcut, hupper⟩ := h.round
    exact ⟨r, hround, hpost, hcut,
      fun u hu => Block.preceq_trans (hupper u hu) hAB⟩
  postVote := h.postVote
  postProp := h.postProp
  slotHor := h.slotHor

/-! ## The fold step, with the ceiling supplied

One slot of the fold inside the boundary round. The ordinary
 takes over from the next round on, where the history
reaches its own ceiling. -/




/-! Assemble the named window facts from an N entry and an explicit carrier
ceiling. -/
theorem MovingSlotEntryStateN.windowFacts_of_ceiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hc : 0 < c)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hpostProp : S.E.t_GST ≤ Protocol.proposal_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    (htiming : MovingSlotActionCeiling S rho c Prev) :
    ∃ Next : Block V,
      MovingSlotFrontierAt S rho c End Next ∧
        NamedMovingSlotWindowFacts S rho (c + 1) End Next := by
  obtain ⟨Next, hfrontier⟩ :=
    movingSlot_existsFrontier S adm hpostProp hslotHor (by
      intro w hw D hD
      simpa only [Nat.add_sub_cancel] using hentry.confCompatible w hw D hD)
  have hprevNext : Block.Preceq Prev Next :=
    Block.preceq_trans hentry.prevLe hfrontier.oldPreceq
  refine ⟨Next, hfrontier, ?_⟩
  refine movingSlotWindowFacts_of_readInputs S adm hfb
    hfrontier.oldPreceq
    (by simpa only [Nat.add_sub_cancel] using hslotHor)
    hentry.headEq ?_ ?_ ?_
  · intro w hw
    exact hentry.windowVoteAnchor_of_ceiling_named S adm hcom hfb hround hupper
      hpostAction hcut hpostVote hslotHor (Block.preceq_self End) w hw
  · simp only [Nat.add_sub_cancel]
    intro w hw
    have hgenuine := hentry.confOutcome_atPrev_of_ceiling_named S adm hcom hfb
      hc hround hupper hpostAction hcut hpostVote hslotHor hw
    exact ⟨hgenuine.1, hfrontier.genuinePreceq w hw _ hgenuine.1⟩
  · intro q hq
    rw [Nat.add_sub_cancel] at hq
    obtain ⟨hq0, hpost, hcutq, hceil⟩ := htiming q hq
    exact ⟨hq0, hpost, hcutq, fun u hu =>
      Block.preceq_trans (hceil u hu) hprevNext⟩

#print axioms MovingSlotEntryStateN.windowFacts_of_ceiling





/-- Every honest slot-`c` named confirmation is compatible with the endpoint
the next slot enters with, when that endpoint is the previous one (the
Byzantine-proposer case), with the carrier ceiling supplied. -/
theorem MovingSlotPreEntryN.confCompatible_byzantine_of_ceiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End)
    (hc : 0 < c)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon) :
    ∀ u ∈ rho.honest, ∀ D : Block V,
      GenuineConfirmationWith
          (NamedProfile.gradeContract (confirmationInputRead S rho u c).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho u c) c D →
        Block.compatible D Prev = true := by
  intro u hu D hgenuine
  have hDout : movingSlotConfirmationOutput S rho c u = D := hgenuine.selected
  have hPrevD : Block.Preceq Prev D := by
    have hout := (hentry.confOutcome_atPrev_of_ceiling_named S adm hcom hfb hc
      hround hupper hpostAction hcut hpostVote hslotHor hu).2
    rwa [hDout] at hout
  exact Block.compatible_of_preceq_common (Block.preceq_self D) hPrevD

#print axioms MovingSlotPreEntryN.confCompatible_byzantine_of_ceiling

/-! ## The Byzantine pre-entry of the next slot, with the ceiling supplied

The N twin of `MovingSlotEntryState.nextPreEntry_byzantine_of_ceiling`
(retained above). It is the live N `nextPreEntry_byzantine` with the history
reach-back `t1 ≤ S.a r` replaced by the supplied carrier ceiling: the only use
of the reach-back there is the window vote cone, which
`MovingSlotEntryStateN.windowVotesCone_of_ceiling` supplies from the ceiling. -/
theorem MovingSlotEntryStateN.nextPreEntry_byzantine_of_ceiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End Next : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hc : 0 < c)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev)
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
    inclusive_le_strict_of_lt_c rho
      (view_freeze_lt_proposal_time_succ_c S.E (c + 1))
  have hcone := hentry.windowVotesCone_of_ceiling S adm hcom hfb hc hround
    hupper hpostAction hcut hpostVote hpostProp hslotHor hfrontier
  exact
    { startTime := hentry.startTime.trans
        (le_of_lt (proposal_time_lt_succ_c S.E (c + 1)))
      prevEndpoint := ⟨End', hstate', hhigh' _ hfreezeStrict,
        hhigh' _ (hfreezeStrict.trans
          (strictEventIndex_le_inclusiveEventIndex rho _))⟩
      prevVotes := hcone }

#print axioms MovingSlotEntryStateN.nextPreEntry_byzantine_of_ceiling

/-- The N honest pre-entry of the next slot, with the carrier ceiling supplied.

Same relation to the live N `nextPreEntry_honest` as the Byzantine twin above:
the history reach-back is replaced by the supplied ceiling, which is all the
window vote cone needed it for. -/
theorem MovingSlotEntryStateN.nextPreEntry_honest_of_ceiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End Next : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hdata : MovingSlotWindowDataC S rho M0 c Prev)
    (hdata' : MovingSlotWindowDataC S rho M0 (c + 1) Next)
    (hfrontier : MovingSlotFrontierAt S rho c End Next)
    (hfacts : NamedMovingSlotWindowFacts S rho (c + 1) End Next)
    (hprop : S.E.proposer (c + 1 + 1) ∈ rho.honest)
    (hparent : Block.Preceq Next (proposedParent S rho (c + 1 + 1)))
    {v : V} (hv : v ∈ rho.honest) :
    ∃ P : NamedBlock V, proposedBlockAt S rho (c + 1 + 1) = some P ∧
      MovingSlotPreEntryN S rho t1 M0 (c + 1 + 1) Next P.erase := by
  obtain ⟨r, hround, hpostAction, hcut, hupper⟩ := hdata.round
  have hhorSC : Protocol.support_cutoff S.E (c + 1) ≤ rho.horizon :=
    (support_cutoff_le_confirmation_time S.E (c + 1)).trans hdata'.slotHor
  have hhorProp : Protocol.proposal_time S.E (c + 1 + 1) ≤ rho.horizon :=
    (proposalTimeSucc_le_confirmationTime_c S.E (c + 1)).trans hdata'.slotHor
  obtain ⟨EndAt, hhistory, _hprev, hEndAt⟩ := hentry.prevEndpoint
  have hrunE : ∃ E : NamedBlock V, E.erase = End ∧ RunBlock S rho E := by
    rw [← hEndAt]
    exact hhistory.endpointRun _ hhistory.start_le (Nat.le_refl _)
  have hrunN : ∃ N : NamedBlock V, N.erase = Next ∧ RunBlock S rho N :=
    hfrontier.runBlock S adm hrunE
  obtain ⟨P, hP, End', _hlow', hstrict', hincl', hstate'⟩ :=
    hhistory.through_slotWindow_honestProposer_named S adm
      (Nat.succ_pos c) hEndAt hrunE hrunN hfacts hprop hhorProp hparent hv
      hhorSC
  have hcone := hentry.windowVotesCone_of_ceiling S adm hcom hfb hdata.pos
    hround hupper hpostAction hcut hdata.postVote hdata.postProp hdata.slotHor
    hfrontier
  refine ⟨P, hP, ?_⟩
  exact
    { startTime := hentry.startTime.trans
        (le_of_lt (proposal_time_lt_succ_c S.E (c + 1)))
      prevEndpoint := ⟨End', hstate', hstrict', hincl'⟩
      prevVotes := hcone }

#print axioms MovingSlotEntryStateN.nextPreEntry_honest_of_ceiling

/-! ## The fold step inside the boundary round, over the three N step pins

`MovingSlotFoldAt.step_of_ceiling` (earlier's erased route, retained above) crosses
one slot of the fold with the previous round's carrier ceiling supplied. Its
named twin needs three producers that this module cannot yet build: the honest
parent read, and the honest and Byzantine entry steps, all with the ceiling
supplied and all over the N history. Each of the three rests on the named
pre-entry vote read of `MovingChainSupporterRun`, which is still parked.

The step itself does not: every other input is live here. It is therefore
stated over the three producers as hypotheses, with EXACTLY the statement each
will have once available, so closing it is one application. -/
theorem MovingSlotFoldAtN.step_of_ceiling_of_pins
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {s0 c : Slot} {F : Slot → Block V}
    {End : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 (c + 1) F End)
    (hdata : MovingSlotWindowDataC S rho M0 c (F (c + 1)))
    (htiming : MovingSlotActionCeiling S rho c (F (c + 1)))
    (hdata' : MovingSlotWindowDataC S rho M0 (c + 1) (F (c + 1)))
    {v : V} (hv : v ∈ rho.honest)
    (hpinParent : ∀ Nxt : Block V,
      MovingSlotFrontierAt S rho c End Nxt →
      NamedMovingSlotWindowFacts S rho (c + 1) End Nxt →
      MovingSlotWindowDataC S rho M0 (c + 1) Nxt →
      S.E.proposer (c + 1 + 1) ∈ rho.honest →
      Block.Preceq Nxt (proposedParent S rho (c + 1 + 1)))
    (hpinHonest : ∀ Nxt : Block V,
      MovingSlotFrontierAt S rho c End Nxt →
      NamedMovingSlotWindowFacts S rho (c + 1) End Nxt →
      MovingSlotWindowDataC S rho M0 (c + 1) Nxt →
      S.E.proposer (c + 1 + 1) ∈ rho.honest →
      Block.Preceq Nxt (proposedParent S rho (c + 1 + 1)) →
      ∃ P : NamedBlock V, proposedBlockAt S rho (c + 1 + 1) = some P ∧
        MovingSlotEntryStateN S rho t1 M0 (c + 1 + 1) Nxt P.erase)
    (hpinByzantine : ∀ Nxt : Block V,
      MovingSlotFrontierAt S rho c End Nxt →
      NamedMovingSlotWindowFacts S rho (c + 1) End Nxt →
      MovingSlotWindowDataC S rho M0 (c + 1) Nxt →
      S.E.proposer (c + 1 + 1) ∉ rho.honest →
      MovingSlotEntryStateN S rho t1 M0 (c + 1 + 1) Nxt Nxt) :
    ∃ (F' : Slot → Block V) (End' : Block V),
      MovingSlotFoldAtN S rho t1 M0 s0 (c + 1 + 1) F' End' ∧
        ∀ d : Slot, d ≤ c + 1 → F' d = F d := by
  classical
  obtain ⟨r, hround, hpostAction, hcut, hupper⟩ := hdata.round
  obtain ⟨Next, hfrontier, hfacts⟩ :=
    hfold.entry.windowFacts_of_ceiling S adm hcom hfb hdata.pos hround hupper
      hpostAction hcut hdata.postVote hdata.postProp hdata.slotHor htiming
  refine ⟨fun d => if d ≤ c + 1 then F d else Next, ?_⟩
  have hlow : ∀ d : Slot, d ≤ c + 1 →
      (if d ≤ c + 1 then F d else Next) = F d := fun _ hd => if_pos hd
  have hhigh : (if c + 1 + 1 ≤ c + 1 then F (c + 1 + 1) else Next) = Next :=
    if_neg (nat_not_succ_succ_le_c c)
  have hendNext : Block.Preceq End Next := hfrontier.oldPreceq
  have hprevNext : Block.Preceq (F (c + 1)) Next :=
    Block.preceq_trans hfold.entry.prevLe hendNext
  have hdataNext : MovingSlotWindowDataC S rho M0 (c + 1) Next :=
    hdata'.mono hprevNext
  have hmono : ∀ d e : Slot, s0 ≤ d → d ≤ e → e ≤ c + 1 + 1 →
      Block.Preceq (if d ≤ c + 1 then F d else Next)
        (if e ≤ c + 1 then F e else Next) := by
    intro d e hd hde he
    by_cases hec : e ≤ c + 1
    · rw [hlow d (hde.trans hec), hlow e hec]
      exact hfold.mono d e hd hde hec
    · rw [if_neg hec]
      by_cases hdle : d ≤ c + 1
      · rw [hlow d hdle]
        exact Block.preceq_trans (hfold.mono d (c + 1) hd hdle (Nat.le_refl _))
          hprevNext
      · rw [if_neg hdle]
        exact Block.preceq_self Next
  have habsorbed : ∀ d : Slot, s0 ≤ d → d < c + 1 + 1 →
      S.E.proposer d ∈ rho.honest →
      ∃ P : NamedBlock V, proposedBlockAt S rho d = some P ∧
        Block.Preceq P.erase
          (if d + 1 ≤ c + 1 then F (d + 1) else Next) := by
    intro d hd hdlt hdprop
    rcases Nat.lt_or_ge d (c + 1) with hlt | hge
    · rw [hlow (d + 1) (Nat.succ_le_of_lt hlt)]
      exact hfold.absorbed d hd hlt hdprop
    · have hdeq : d = c + 1 := Nat.le_antisymm (nat_le_of_lt_succ_c hdlt) hge
      subst hdeq
      obtain ⟨P, hP, hEnd⟩ := hfold.endpointProposal hdprop
      rw [hhigh]
      exact ⟨P, hP, hEnd ▸ hendNext⟩
  have hconfAbsorbed : ∀ d : Slot, s0 ≤ d → d + 1 < c + 1 + 1 →
      ∀ u ∈ rho.honest,
        GenuineConfirmationWith
            (NamedProfile.gradeContract (confirmationInputRead S rho u d).cache)
            S.E S.hc (Proofs.Optimistic.confStore S rho u d) d
            (movingSlotConfirmationOutput S rho d u) ∧
          Block.Preceq (movingSlotConfirmationOutput S rho d u)
            (if d + 2 ≤ c + 1 then F (d + 2) else Next) := by
    intro d hd hdlt u hu
    rcases Nat.lt_or_ge (d + 1) (c + 1) with hlt | hge
    · rw [hlow (d + 2) (Nat.succ_le_of_lt hlt)]
      exact hfold.confAbsorbed d hd hlt u hu
    · have hdeq : d = c := nat_eq_of_succ_le_succ_of_lt_succ_c hge hdlt
      subst hdeq
      have hout := hfold.entry.confOutcome_atPrev_of_ceiling_named S adm hcom
        hfb hdata.pos hround hupper hpostAction hcut hdata.postVote
        hdata.slotHor hu
      refine ⟨hout.1, ?_⟩
      rw [if_neg (nat_not_add_two_le_succ_c d)]
      exact hfrontier.genuinePreceq u hu _ hout.1
  have hconfAbove : ∀ d : Slot, s0 ≤ d → d + 1 < c + 1 + 1 →
      ∀ u ∈ rho.honest,
        Block.Preceq (if d + 1 ≤ c + 1 then F (d + 1) else Next)
          (movingSlotConfirmationOutput S rho d u) := by
    intro d hd hdlt u hu
    rcases Nat.lt_or_ge (d + 1) (c + 1) with hlt | hge
    · rw [hlow (d + 1) (le_of_lt hlt)]
      exact hfold.confAbove d hd hlt u hu
    · have hdeq : d = c := nat_eq_of_succ_le_succ_of_lt_succ_c hge hdlt
      subst hdeq
      rw [hlow (d + 1) (Nat.le_refl _)]
      exact (hfold.entry.confOutcome_atPrev_of_ceiling_named S adm hcom hfb
        hdata.pos hround hupper hpostAction hcut hdata.postVote hdata.slotHor
        hu).2
  have hcone := hfold.entry.windowVotesCone_of_ceiling S adm hcom hfb
    hdata.pos hround hupper hpostAction hcut hdata.postVote hdata.postProp
    hdata.slotHor hfrontier
  have hwindowCone : ∀ d : Slot, s0 ≤ d → d < c + 1 + 1 →
      NamedHonestVotesCone S rho d
        (fun X => Block.Preceq
          (if d + 1 ≤ c + 1 then F (d + 1) else Next) X) := by
    intro d hd hdlt
    rcases Nat.lt_or_ge d (c + 1) with hlt | hge
    · rw [hlow (d + 1) (Nat.succ_le_of_lt hlt)]
      exact hfold.windowCone d hd hlt
    · have hdeq : d = c + 1 := Nat.le_antisymm (nat_le_of_lt_succ_c hdlt) hge
      subst hdeq
      rw [if_neg (nat_not_succ_succ_le_c c)]
      exact hcone
  have hhistoryAt : ∀ E' : Block V,
      MovingSlotEntryStateN S rho t1 M0 (c + 1 + 1) Next E' →
      ∀ d : Slot, s0 ≤ d → d ≤ c + 1 + 1 →
        ∃ EndAt : Nat → Block V,
          MovingFrontierChainStateN S rho t1 M0 (strictEventIndex rho t1)
              (strictEventIndex rho (Protocol.proposal_time S.E d)) EndAt ∧
            EndAt (strictEventIndex rho (Protocol.proposal_time S.E d)) =
              (if d ≤ c + 1 then F d else Next) := by
    intro E' hentry' d hd hdle
    rcases Nat.lt_or_ge d (c + 1 + 1) with hlt | hge
    · obtain ⟨EndAt, hstate, hval⟩ :=
        hfold.historyAt d hd (nat_le_of_lt_succ_c hlt)
      refine ⟨EndAt, hstate, ?_⟩
      rw [hlow d (nat_le_of_lt_succ_c hlt)]
      exact hval
    · have hdeq : d = c + 1 + 1 := Nat.le_antisymm hdle hge
      subst hdeq
      obtain ⟨EndAt, hhistory, hprev, _hEnd⟩ := hentry'.prevEndpoint
      refine ⟨EndAt, hhistory.prefix
        (strictEventIndex_mono rho hentry'.startTime)
        (strictEventIndex_le_inclusiveEventIndex rho _), ?_⟩
      rw [hhigh]
      exact hprev
  by_cases hprop : S.E.proposer (c + 1 + 1) ∈ rho.honest
  · have hparent := hpinParent Next hfrontier hfacts hdataNext hprop
    obtain ⟨P, hP, hentry'⟩ :=
      hpinHonest Next hfrontier hfacts hdataNext hprop hparent
    refine ⟨P.erase, ?_, hlow⟩
    exact
      { base := hfold.base.trans (Nat.le_succ _)
        entry := by rw [hhigh]; exact hentry'
        endpointProposal := fun _ => ⟨P, hP, rfl⟩
        mono := hmono
        parent := by
          intro d hd hdle hdprop
          rcases Nat.lt_or_ge d (c + 1 + 1) with hlt | hge
          · rw [hlow d (nat_le_of_lt_succ_c hlt)]
            exact hfold.parent d hd (nat_le_of_lt_succ_c hlt) hdprop
          · have hdeq : d = c + 1 + 1 := Nat.le_antisymm hdle hge
            subst hdeq
            rw [hhigh]
            exact hparent
        absorbed := habsorbed
        confAbsorbed := hconfAbsorbed
        confAbove := hconfAbove
        windowCone := hwindowCone
        historyAt := hhistoryAt _ hentry' }
  · have hentry' := hpinByzantine Next hfrontier hfacts hdataNext hprop
    refine ⟨Next, ?_, hlow⟩
    exact
      { base := hfold.base.trans (Nat.le_succ _)
        entry := by rw [hhigh]; exact hentry'
        endpointProposal := fun hp => absurd hp hprop
        mono := hmono
        parent := by
          intro d hd hdle hdprop
          rcases Nat.lt_or_ge d (c + 1 + 1) with hlt | hge
          · rw [hlow d (nat_le_of_lt_succ_c hlt)]
            exact hfold.parent d hd (nat_le_of_lt_succ_c hlt) hdprop
          · have hdeq : d = c + 1 + 1 := Nat.le_antisymm hdle hge
            subst hdeq
            exact absurd hdprop hprop
        absorbed := habsorbed
        confAbsorbed := hconfAbsorbed
        confAbove := hconfAbove
        windowCone := hwindowCone
        historyAt := hhistoryAt _ hentry' }

#print axioms MovingSlotFoldAtN.step_of_ceiling_of_pins

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
