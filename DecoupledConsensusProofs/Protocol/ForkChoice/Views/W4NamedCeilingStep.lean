module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.W4NamedFoldSupplies
public import DecoupledConsensusProofs.Protocol.Schedule.W4CarryBranch2

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The named ceiling fold step

This leaf closes the ceiling fold step over the named state. The two entry
branches use the dedicated ceiling vote-input, vote-cone, and confirmation
compatibility producers. The ordinary entered-slot record is not used here;
the ceiling branch keeps its own `MovingSlotWindowDataC` records.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem w4ncs_proposedParent_preceq_proposedBlockAt
    (S : Setup V) (rho : Run V) (s : Slot) {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P) :
    Block.Preceq (proposedParent S rho s) P.erase := by
  obtain ⟨p, hp, hparent⟩ := proposedBlockAt_parent S rho s hP
  rw [← hparent]
  cases P with
  | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hp
  | node parent slot root votes support rows proposer =>
      simp only [NamedBlock.parent?, Option.some.injEq] at hp
      subst hp
      apply Protocol.preceq_of_parent?
      rfl

private theorem w4ncs_vote_time_succ_le_confirmation_time
    (E : Env V) (s : Slot) :
    Protocol.vote_time E (s + 1) ≤ Protocol.confirmation_time E s := by
  rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time E s]
  exact Int.le_add_of_nonneg_right E.Δ_pos.le

private theorem w4ncs_frontier_unique
    {S : Setup V} {rho : Run V} {s : Slot} {End A B : Block V}
    (hA : MovingSlotFrontierAt S rho s End A)
    (hB : MovingSlotFrontierAt S rho s End B) : A = B :=
  Option.some.inj (hA.selected.symm.trans hB.selected)

/-- The mixed-region adoption supply. The left record is a ceiling record and
the entered record is ordinary; the two are supplied independently. -/
theorem w4MovingSlotAdoptionSupplyAt_of_mixedFoldStep
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {t1 : Time} {M0 : Height} {s0 c : Slot} {F : Slot → Block V}
    {End : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 (c + 1) F End)
    (hdata : MovingSlotWindowDataC S rho M0 c (F (c + 1)))
    (htiming : MovingSlotActionCeiling S rho c (F (c + 1)))
    (hdata' : MovingSlotWindowData S rho t1 M0 (c + 1))
    {v : V} (hv : v ∈ rho.honest)
    (hdeadline : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ c + 1 + 1)
    (hvoteHor : Protocol.vote_time S.E (c + 1 + 1) ≤ rho.horizon) :
    MovingSlotAdoptionSupplyAt S rho c End := by
  obtain ⟨r, hround, hpostAction, hcut, hupper⟩ := hdata.round
  obtain ⟨Next0, hfrontier0, hfacts0⟩ :=
    hfold.entry.windowFacts_of_ceiling S adm hcom hfb hdata.pos hround hupper
      hpostAction hcut hdata.postVote hdata.postProp hdata.slotHor htiming
  have hfacts : ∀ Next : Block V,
      MovingSlotFrontierAt S rho c End Next →
      NamedMovingSlotWindowFacts S rho (c + 1) End Next := by
    intro Next hfrontier
    rw [w4ncs_frontier_unique hfrontier hfrontier0]
    exact hfacts0
  refine movingSlotAdoptionSupplyAt_of_generalSlot S adm hcom hfb hrec hdelay
    hpost hfold.entry hdata hdata' hfacts hv hdeadline hvoteHor ?_
  intro Next hfrontier hprop P hP
  have hparent := movingSlotAdoptionParent_of_ordinary S adm hcom hfb
    hfold.entry hdata htiming hdata' hv Next hfrontier hprop P hP
  obtain ⟨P0, hP0, hpre⟩ :=
    hfold.entry.nextPreEntry_honest_mixed_named S adm hcom hfb hdata hdata'
      hfrontier (hfacts Next hfrontier) hprop hparent hv
  have hP0eq : P0 = P := proposedBlockAt_unique S rho
    (c + 1 + 1) hP0 hP
  subst P0
  have hheadEq : ∀ w ∈ rho.honest,
      voteDutyHead S rho w (c + 1 + 1) = P.erase :=
    honestProposal_voterHeadAt_eq_after_SG_healing_named_slot
      S adm hcom hfb hrec hdelay hpost hdeadline hvoteHor hprop hP
  obtain ⟨r', hround', ht1', hpostAction', hcut'⟩ := hdata'.round
  obtain ⟨w0, hw0⟩ := honest_nonempty_of_honestCommittees hcom
  have hconf := hpre.confCompatible_honest_closed S adm hcom hfb
    (Nat.zero_lt_succ c) hround' ht1' hpostAction' hcut'
    hdata'.postVote hdata'.postProp hdata'.slotHor hheadEq hw0
  exact hconf

#print axioms w4MovingSlotAdoptionSupplyAt_of_mixedFoldStep

/-- A ceiling pre-entry still places each genuine previous confirmation below
the next honest vote head. This is the prepared-contract twin of the
ceiling-side read used by the fold entry. -/
theorem MovingSlotPreEntryN.genuineConfirmation_preceq_voteDutyHead_of_ceiling_named
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
    (hpostProp : S.E.t_GST ≤ Protocol.proposal_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {D : Block V}
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (confirmationInputRead S rho v c).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v c) c D)
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq D (voteDutyHead S rho w (c + 1)) := by
  have hprevVotes : NamedHonestVotesCone S rho c
      (fun X => Block.Preceq Prev X) := by
    simpa only [Nat.add_sub_cancel] using hentry.prevVotes
  have hDout : movingSlotConfirmationOutput S rho c v = D :=
    hgenuine.selected
  have hPrevD : Block.Preceq Prev D := by
    have hout := hentry.confOutcome_atPrev_of_ceiling_named S adm hcom hfb
      hc hround hupper hpostAction hcut hpostVote hslotHor hv
    rw [hDout] at hout
    exact hout.2
  have hvoteHorC : Protocol.vote_time S.E c ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E c).trans hslotHor
  have hcutHor : Protocol.support_cutoff S.E c ≤ rho.horizon :=
    (Protocol.support_cutoff_le_confirmation_time S.E c).trans hslotHor
  have hresolve := headsResolveIn_confStore_of_postHealingCone
    S adm hv hpostVote hcutHor
      (hentry.confRoot_preceq_prev S adm hfb hv) hprevVotes
  obtain ⟨x, hx, hxc, hDx⟩ := genuineConfirmation_exists_honestSupporter_with
    S adm hcom _ hc hpostVote hslotHor hv hresolve hgenuine
  have hhead := honestHead_voteDutyHead S adm hc hvoteHorC hx hxc
  have hrootVoteRaw := hentry.voteRoot_preceq_prev S adm hfb hw
  have hrootVote : Block.Preceq
      (Protocol.get_fg_root
        ((Internal.NamedRecoveryRead.voteDutyRead S rho w (c + 1)).st.core.toHealing.toFG))
      Prev := by
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      Run.storeBeforeTime] using hrootVoteRaw
  have havailable :=
    WeakGoldfish.honestHeadsAvailableBefore_of_postHealingCone_atVoteDuty
      S adm.toNamedAdmissibleCore hw hpostVote hcutHor hrootVote hprevVotes
  have hprocessed := voterProcessed_of_availableBefore_of_honestHead
    S adm havailable hhead hDx
  obtain ⟨Dn, hDn, hDnrun⟩ :=
    genuineConfirmation_runBlock_step S adm hv hgenuine
  have hmemPrev : Prev ∈
      (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (c + 1))).core.T :=
    mem_storeBeforeTime_of_cone S adm hcom havailable
      (Proofs.Optimistic.support_cutoff_le_vote_time_succ S.E c) hprevVotes
  have hmemD : D ∈
      (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (c + 1))).core.T := by
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
  have hband :
      (Internal.NamedRecoveryRead.voteDutyRead S rho w (c + 1)).st.core.h_max - 1 ≤
        ((Internal.NamedRecoveryRead.voteDutyRead S rho w (c + 1)).st.core.σ
          Dn.erase).h := by
    rw [hDn]
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      Run.storeBeforeTime] using hbandRaw
  have hanchorEnd : Block.Preceq
      (voterAnchorAt S rho w (c + 1)) Prev :=
    w4cx_movingSlotPreEntryN_voterAnchorAt_preceq_prev_of_ceiling
      S adm hcom hfb hentry hround hupper hpostAction hcut hpostVote
      hcutHor (by
        exact (w4ncs_vote_time_succ_le_confirmation_time S.E c).trans
          hslotHor) hw
  have hprocessed' : Dn.erase ∈
      Protocol.voter_processed_block_tree S.E
        ((Internal.NamedRecoveryRead.voteDutyRead S rho w (c + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore)
        ((Internal.NamedRecoveryRead.voteDutyRead S rho w (c + 1)).st.core.s) := by
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
    rw [hDn]
    exact hgenuine
  have hEndB : Block.Preceq Prev Dn.erase := by
    rw [hDn]
    exact hPrevD
  have hfinal := genuineConfirmation_preceq_nextVoteDutyHead_of_endpointBand
    S adm hv hw hpostProp hslotHor hgenuineN hEndB hanchorEnd hprocessed' hband
  rw [hDn] at hfinal
  simpa only [voterHeadAt] using hfinal

#print axioms MovingSlotPreEntryN.genuineConfirmation_preceq_voteDutyHead_of_ceiling_named

/-- Close one ceiling fold step, including both proposer-status entry arms. -/
theorem w4MovingSlotFoldAtN_step_of_ceiling_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {t1 : Time} {M0 : Height} {s0 c : Slot} {F : Slot → Block V}
    {End : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 (c + 1) F End)
    (hdata : MovingSlotWindowDataC S rho M0 c (F (c + 1)))
    (htiming : MovingSlotActionCeiling S rho c (F (c + 1)))
    (hdata' : MovingSlotWindowDataC S rho M0 (c + 1) (F (c + 1)))
    {v : V} (hv : v ∈ rho.honest)
    (hdeadline : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ c + 1 + 1) :
    ∃ (F' : Slot → Block V) (End' : Block V),
      MovingSlotFoldAtN S rho t1 M0 s0 (c + 1 + 1) F' End' ∧
        ∀ d : Slot, d ≤ c + 1 → F' d = F d := by
  apply MovingSlotFoldAtN.step_of_ceiling_of_stepPins S adm hcom hfb
    hfold hdata htiming hdata' hv
  · intro Next hfrontier hfacts hdataNext hprop
    intro hparent
    obtain ⟨r', hround', hpostAction', hcut', hupper'⟩ := hdataNext.round
    obtain ⟨P, hP, hpre⟩ :=
      hfold.entry.nextPreEntry_honest_of_ceiling S adm hcom hfb
        hdata hdataNext hfrontier hfacts hprop hparent hv
    have hvoteHor : Protocol.vote_time S.E (c + 1 + 1) ≤ rho.horizon :=
      (w4ncs_vote_time_succ_le_confirmation_time S.E (c + 1)).trans
        hdataNext.slotHor
    have hheadEq : ∀ w ∈ rho.honest,
        voterHeadAt S rho w (c + 1 + 1) = P.erase :=
      honestProposal_voterHeadAt_eq_after_SG_healing_named_slot
        S adm hcom hfb hrec hdelay hpost hdeadline hvoteHor hprop hP
    have hvotes : NamedHonestVotesCone S rho (c + 1 + 1)
        (fun X => Block.Preceq P.erase X) :=
      honestProposal_slotVoteCone_after_SG_healing_named
        S adm hcom hfb hrec hdelay hpost hdeadline hvoteHor hprop hP
    have hNextP : Block.Preceq Next P.erase :=
      Block.preceq_trans hparent
        (w4ncs_proposedParent_preceq_proposedBlockAt S rho
          (c + 1 + 1) hP)
    have hconf : ∀ w ∈ rho.honest, ∀ D : Block V,
        GenuineConfirmationWith
          (NamedProfile.gradeContract
            (confirmationInputRead S rho w (c + 1)).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho w (c + 1)) (c + 1) D →
        Block.compatible D P.erase = true := by
      intro w hw D hD
      have hDhead :=
        MovingSlotPreEntryN.genuineConfirmation_preceq_voteDutyHead_of_ceiling_named
          S adm hcom hfb (hentry := hpre) (Nat.zero_lt_succ c)
          hround' hupper' hpostAction' hcut' hdataNext.postVote
          hdataNext.postProp hdataNext.slotHor (v := w) hw hD (w := w) hw
      have hDhead' : Block.Preceq D
          (voterHeadAt S rho w (c + 1 + 1)) := by
        simpa only [voteDutyHead] using hDhead
      rw [hheadEq w hw] at hDhead'
      exact Block.compatible_of_preceq_common hDhead'
        (Block.preceq_self P.erase)
    have hvotesNext : NamedHonestVotesCone S rho (c + 1 + 1)
        (fun X => Block.Preceq Next X) := by
      intro w hw hcommittee
      obtain ⟨X, hX, hXrun, hXemit⟩ := hvotes w hw hcommittee
      exact ⟨X,
        Block.preceq_trans
          (show Block.preceq Next P.erase = true from hNextP)
          (show Block.preceq P.erase X.erase = true from hX),
        hXrun, hXemit⟩
    have hentry := hpre.toEntryN_of_voteHorizon S adm hvoteHor
      (fun _ => fun w hw => by
        simpa only [voteDutyHead] using hheadEq w hw)
      (fun hbyz' => (hbyz' hprop).elim) hvotesNext hconf
    exact ⟨P, hP, hentry⟩
  · intro Next hfrontier hfacts hdataNext hbyz
    obtain ⟨r, hround, hpostAction, hcut, hupper⟩ := hdata.round
    obtain ⟨r', hround', hpostAction', hcut', hupper'⟩ := hdataNext.round
    have hpre := hfold.entry.nextPreEntry_byzantine_of_ceiling S adm
      hcom hfb hdata.pos hround hupper hpostAction hcut hdata.postVote
      hdata.postProp hdata.slotHor hfrontier hfacts hbyz hv
      ((support_cutoff_le_confirmation_time S.E (c + 1)).trans
        hdataNext.slotHor)
    have hvoteHor : Protocol.vote_time S.E (c + 1 + 1) ≤ rho.horizon :=
      (w4ncs_vote_time_succ_le_confirmation_time S.E (c + 1)).trans
        hdataNext.slotHor
    have hvotes := hpre.votesCone_prev_of_ceiling S adm hcom hfb
      (Nat.zero_lt_succ c) hround' hupper' hpostAction' hcut'
      hdataNext.postVote hdataNext.slotHor
    have hconf := hpre.confCompatible_byzantine_of_ceiling S adm hcom hfb
      (Nat.zero_lt_succ c) hround' hupper' hpostAction' hcut'
      hdataNext.postVote hdataNext.slotHor
    have hentry := hpre.toEntryN_of_voteHorizon S adm hvoteHor
      (fun hprop' => (hbyz hprop').elim)
      (fun _ => rfl) hvotes hconf
    exact hentry

#print axioms w4MovingSlotFoldAtN_step_of_ceiling_named

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
