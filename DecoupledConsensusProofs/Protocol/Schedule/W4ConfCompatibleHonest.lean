module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainNextEntry
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGoldfishCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeilingStep
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.CarrierInteriorInputs

@[expose] public section

/-!
# W4 branches b: the honest `confCompatible` of the named pre-entry, pin-free

`MovingSlotPreEntryN.confCompatible_honest` (`MovingChainNextEntryRun`) takes
one pin, the named twin of
`MovingSlotPreEntry.genuineConfirmation_preceq_voteDutyHead`. This leaf proves
that twin and closes the pin.

It is a SEPARATE leaf on purpose. The twin needs three modules that
`MovingChainNextEntryRun` does not import — `WeakGoldfishConeRun` for the
available-heads producer, `SeedCeilingStepRun` for the named witness of a
prepared genuine confirmation, and `CarrierInteriorInputsRun` for σ-height
monotonicity — and adding those imports IN PLACE breaks declarations that
already compile in that module (name resolution changes: `activePrefix_mem`
becomes unknown and `MovingSlotPreEntryN.voteRoot_preceq_prev` open items resolving
as a projection). `check-cycle.py` and `check-below.py` do not see that, since
it is neither a cycle nor a red import.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem w4b_vote_time_normal (E : Env V) (s : Slot) :
    Protocol.vote_time E s = (4 * (s : Time) + 1) * E.Δ := by
  unfold Protocol.vote_time Env.t slotStart
  ring

private theorem w4b_support_cutoff_normal (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s = (4 * (s : Time) + 2) * E.Δ := by
  unfold Protocol.support_cutoff Env.t slotStart
  ring

private theorem w4b_support_cutoff_le_vote_time_succ (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≤ Protocol.vote_time E (s + 1) := by
  rw [w4b_support_cutoff_normal, w4b_vote_time_normal]
  refine Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt E.Δ_pos)
  push_cast
  linarith


/-- Copy of the corresponding branch's private `w4_mem_of_cone`
(`MovingChainSupporterRun.lean`): it is `private` there, and its packaged form
`storeBeforeTime_mem_stamp_of_cone` sits in `MovingChainBatchRun`, above the
pre-entry modules. -/
private theorem w4b_mem_of_cone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {c : Slot} {P : Block V} {w : V} {Gamma : Time}
    (havailable : HonestHeadsAvailableBefore S rho c w
      (Protocol.support_cutoff S.E c))
    (hcut : Protocol.support_cutoff S.E c ≤ Gamma)
    (hvotes : NamedHonestVotesCone S rho c (fun X => Block.Preceq P X)) :
    P ∈ (rho.storeBeforeTime S w Gamma).T := by
  have hpositive : 0 < ((S.E.committee c) ∩ rho.honest).card := by
    have hcc := hcom c
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  have hxCommittee : x ∈ S.E.committee c := (Finset.mem_inter.mp hx).1
  have hxHonest : x ∈ rho.honest := (Finset.mem_inter.mp hx).2
  obtain ⟨X, hPX, hXrun, hXemit⟩ := hvotes x hxHonest hxCommittee
  rcases havailable X.erase
      ⟨x, hxHonest, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩ with
    hXgen | hXadmit
  · have hPgen : P = Block.genesis :=
      Block.preceq_antisymm (hXgen ▸ hPX) (Protocol.preceq_genesis P)
    rw [hPgen]
    exact (genesis_mem_and_stamp_storeBeforeTime S
      adm.toNamedScheduleWellFormed w Gamma
      (Protocol.support_cutoff S.E c)).1
  · exact (Proofs.Optimistic.admittedBefore_ancestor_mem_and_stamp_at
      S adm hXadmit hPX hcut).1

private theorem w4b_voteTime_le_confirmationTime (E : Env V) (s : Slot) :
    Protocol.vote_time E s ≤ Protocol.confirmation_time E s := by
  unfold Protocol.vote_time Protocol.confirmation_time
  have h : E.Δ ≤ 6 * E.Δ := by linarith [E.Δ_pos]
  linarith

/-- **Every honest slot-`c` genuine confirmation is at or below every honest
slot-`(c+1)` vote head**, for the named pre-entry half. -/
theorem MovingSlotPreEntryN.genuineConfirmation_preceq_voteDutyHead
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
    (hpostProp : S.E.t_GST ≤ Protocol.proposal_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {D : Block V}
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v c).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v c) c D)
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq D (voteDutyHead S rho w (c + 1)) := by
  have hprevVotes : NamedHonestVotesCone S rho c
      (fun X => Block.Preceq Prev X) := by
    simpa only [Nat.add_sub_cancel] using hentry.prevVotes
  have hDout : movingSlotConfirmationOutput S rho c v = D := hgenuine.selected
  have hPrevD : Block.Preceq Prev D := by
    have hout := (hentry.confOutcome_atPrev S adm hcom hfb hc hround ht1
      hpostAction hcut hpostVote hslotHor hv).2
    rwa [hDout] at hout
  have hvoteHorC : Protocol.vote_time S.E c ≤ rho.horizon :=
    (w4b_voteTime_le_confirmationTime S.E c).trans hslotHor
  have hcutHor : Protocol.support_cutoff S.E c ≤ rho.horizon :=
    (support_cutoff_le_confirmation_time S.E c).trans hslotHor
  have hresolve := headsResolveIn_confStore_of_postHealingCone
    S adm hv hpostVote hcutHor
      (hentry.confRoot_preceq_prev S adm hfb hv) hprevVotes
  obtain ⟨x, hx, hxc, hDx⟩ := genuineConfirmation_exists_honestSupporter_with
    S adm hcom _ hc hpostVote hslotHor hv hresolve hgenuine
  have hhead := honestHead_voteDutyHead S adm hc hvoteHorC hx hxc
  have hrootVoteRaw := hentry.voteRoot_preceq_prev S adm hfb hw
  have hrootVote : Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (c + 1)).st.core.toHealing.toFG) Prev := by
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      Run.storeBeforeTime] using hrootVoteRaw
  have havailable := WeakGoldfish.honestHeadsAvailableBefore_of_postHealingCone_atVoteDuty
    S adm.toNamedAdmissibleCore hw hpostVote hcutHor hrootVote hprevVotes
  have hprocessed := voterProcessed_of_availableBefore_of_honestHead
    S adm havailable hhead hDx
  obtain ⟨Dn, hDn, _hDnRun⟩ :=
    genuineConfirmation_runBlock_step S adm hv hgenuine
  have hmemPrev : Prev ∈
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (c + 1))).core.T :=
    w4b_mem_of_cone S adm hcom havailable
      (w4b_support_cutoff_le_vote_time_succ S.E c) hprevVotes
  have hmemD : D ∈
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (c + 1))).core.T := by
    have hdata := hprocessed
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hdata.1
  have hbandRaw :
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (c + 1))).core.h_max - 1 ≤
        ((rho.storeBeforeTime S w
          (Protocol.vote_time S.E (c + 1))).core.σ D).h :=
    (hentry.voteFrontier_sub_one_le_prevHeightSigma S adm hfb hw hmemPrev).trans
      (interior_sigma_height_mono S rho w
        (Protocol.vote_time S.E (c + 1)) hmemPrev hmemD hPrevD)
  have hband : (Internal.NamedRecoveryRead.voteDutyRead S rho w
        (c + 1)).st.core.h_max - 1 ≤
      ((Internal.NamedRecoveryRead.voteDutyRead S rho w
        (c + 1)).st.core.σ Dn.erase).h := by
    rw [hDn]
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      Run.storeBeforeTime] using hbandRaw
  have hanchorEnd : Block.Preceq (voterAnchorAt S rho w (c + 1)) Prev :=
    hentry.voterAnchorAt_preceq_prev S adm hfb hround ht1 hpostAction hcut
      hslotHor hw
  have hprocessed' : Dn.erase ∈ Protocol.voter_processed_block_tree S.E
      (Internal.NamedRecoveryRead.voteDutyRead S rho w
        (c + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore
      (Internal.NamedRecoveryRead.voteDutyRead S rho w (c + 1)).st.core.s := by
    rw [hDn]
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
      Run.storeBeforeTime] using hprocessed
  have hgenuineN : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v c).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v c) c Dn.erase := by
    rw [hDn]; exact hgenuine
  have hEndB : Block.Preceq Prev Dn.erase := by rw [hDn]; exact hPrevD
  have hfinal := genuineConfirmation_preceq_nextVoteDutyHead_of_endpointBand
    S adm hv hw hpostProp hslotHor hgenuineN hEndB hanchorEnd hprocessed' hband
  rw [hDn] at hfinal
  simpa only [voterHeadAt] using hfinal

#print axioms MovingSlotPreEntryN.genuineConfirmation_preceq_voteDutyHead

/-- **`confCompatible` in an honest-proposer slot, pin-free.**

`MovingSlotPreEntryN.confCompatible_honest` (`MovingChainNextEntryRun`) with
its head pin discharged. This is the `hconf` input of
`MovingSlotEntryStateN.step_honestProposer_named`, and, instantiated at the
entered slot, it is the fourth conjunct of `MovingSlotAdoptionSupply`
(`MovingChainIterateRun`). -/
theorem MovingSlotPreEntryN.confCompatible_honest_closed
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
    (hpostProp : S.E.t_GST ≤ Protocol.proposal_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    (hheadEq : ∀ u ∈ rho.honest, voteDutyHead S rho u (c + 1) = End)
    {w : V} (hw : w ∈ rho.honest) :
    ∀ u ∈ rho.honest, ∀ D : Block V,
      GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho u c).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho u c) c D →
        Block.compatible D End = true :=
  MovingSlotPreEntryN.confCompatible_honest S hentry hheadEq hw
    (fun _u hu _D hgenuine =>
      hentry.genuineConfirmation_preceq_voteDutyHead S adm hcom hfb hc hround
        ht1 hpostAction hcut hpostVote hpostProp hslotHor hu hgenuine hw)

#print axioms MovingSlotPreEntryN.confCompatible_honest_closed

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
