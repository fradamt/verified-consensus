module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.W4NamedExecution

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Fold-only opening head for the named finality execution

This leaf ports earlier
`MovingChainExecutionRun.openingProposalPreceqActionHead_of_handoff` to the
prepared named action head. The selected root and the named height band come
from the staged `MovingSlotFoldAtN` history itself. No carrier record,
canonical regime round, or later-stage height-band premise is used.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Copy of earlier's private slot-separation helper
`MovingChainExecutionRun.vote_lt_proposal_succ_le`. -/
private theorem w4fh_vote_lt_proposal_succ_le
    (E : Env V) {a b : Slot}
    (h : Protocol.vote_time E a < Protocol.proposal_time E b) :
    a + 1 ≤ b := by
  apply Nat.succ_le_of_lt
  by_contra hnot
  have hba : b ≤ a := Nat.le_of_not_gt hnot
  exact (not_le_of_gt h)
    ((Protocol.proposal_time_mono E hba).trans
      (Protocol.proposal_time_lt_vote_time E a).le)

/-- Copy of the private round-separation helper in
`MovingChainRoundReadRun`. -/
private theorem w4fh_action_time_lt_openingProposal
    (S : Setup V) {p r : Round} (hlt : S.a p < S.a r) :
    S.a p < Protocol.proposal_time S.E (S.hc.opening_slot r) := by
  have hpr : p < r := (action_strictMono S).lt_iff_lt.mp hlt
  exact (Protocol.action_lt_proposal_time_two_after S p).trans_le
    (Protocol.proposal_time_mono S.E
      (openingSlot_add_two_le_openingSlot_of_lt S hpr))

/-- Copy of earlier's private opening-slot arithmetic helper. -/
private theorem w4fh_round_of_opening_add_three_le_succ
    (hc : Protocol.HealConfig) (q : Round) :
    hc.round_of (hc.opening_slot q + 3) ≤ q + 1 := by
  have hRpos : 0 < hc.R := lt_of_lt_of_le Nat.zero_lt_two hc.R_ge_two
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  rw [show q * hc.R + 3 = 3 + hc.R * q by ring,
    Nat.add_mul_div_left _ _ hRpos]
  have hdiv : 3 / hc.R ≤ 1 := by
    have hlt : 3 / hc.R < 2 := by
      rw [Nat.div_lt_iff_lt_mul hRpos]
      exact lt_of_lt_of_le (by decide : 3 < 4)
        (by simpa only [Nat.mul_comm] using
          Nat.mul_le_mul_left 2 hc.R_ge_two)
    exact Nat.le_of_lt_succ hlt
  simpa only [Nat.add_comm] using Nat.add_le_add_left hdiv q

/-- Copy of earlier's private predecessor arithmetic helper. -/
private theorem w4fh_nat_pred_le_of_pos_le_succ {a b : Nat}
    (ha : 0 < a) (h : a ≤ b + 1) : a - 1 ≤ b :=
  Nat.lt_succ_iff.mp ((Nat.sub_lt ha (by decide : 0 < 1)).trans_le h)

/-- Copy of the private named-entry endpoint order in
`MovingChainIterateRun`. -/
private theorem w4fh_movingSlotEntryStateN_prevLe
    {S : Setup V} {rho : Run V} {t1 : Time} {M0 : Height}
    {s : Slot} {Prev End : Block V}
    (h : MovingSlotEntryStateN S rho t1 M0 s Prev End) :
    Block.Preceq Prev End := by
  obtain ⟨EndAt, hhistory, hprev, hEnd⟩ := h.prevEndpoint
  rw [← hprev, ← hEnd]
  have hmono : ∀ {j k : Nat},
      strictEventIndex rho t1 ≤ j → j ≤ k →
      k ≤ inclusiveEventIndex rho (Protocol.proposal_time S.E s) →
      Block.Preceq (EndAt j) (EndAt k) := by
    intro j k hj hjk hk
    induction hjk with
    | refl => exact Block.preceq_self _
    | @step k hjk ih =>
        exact Block.preceq_trans (ih (Nat.le_trans (Nat.le_succ k) hk))
          (hhistory.endpointMono k (hj.trans hjk) (Nat.lt_of_succ_le hk))
  exact hmono (strictEventIndex_mono rho h.startTime)
    (strictEventIndex_le_inclusiveEventIndex rho _) (Nat.le_refl _)

/-- The existing global pin, restricted to the selected handoff round. -/
def W4NamedExecOpeningHeadAtPinFor
    (S : Setup V) (rho : Run V) (q : Round) : Prop :=
  ∀ {r : Round},
    0 < S.hc.opening_slot r →
    healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r) →
    S.E.proposer (S.hc.opening_slot r) ∈ rho.honest →
    S.a r ≤ rho.horizon →
    ∀ B : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some B →
      ∀ v ∈ rho.honest,
        Block.Preceq B.erase (actionHeadAt S rho v r)

/-- The fixed-round head field from the first three staged execution fields
and the staged named fold. -/
theorem w4NamedExecOpeningHeadAtPinFor_of_fold
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {q : Round} {D : NamedBlock V} {M0 : Height}
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon)
    (hduty : ∀ s : Slot, 0 < s →
      healingBoundaryTime S q < Protocol.proposal_time S.E s →
      S.E.proposer s ∈ rho.honest →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ B : NamedBlock V, proposedBlockAt S rho s = some B →
        Protocol.CanonicalProposalDutyAt S rho s B)
    (hfoldAt : ∀ {s : Slot}, S.hc.opening_slot q + 3 ≤ s →
      Protocol.confirmation_time S.E (s - 1) ≤ rho.horizon →
      ∃ F : Slot → Block V, ∃ End : Block V,
        MovingSlotFoldAtN S rho
          (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
          (S.hc.opening_slot q + 3) s F End ∧
        F (S.hc.opening_slot q + 3) = D.erase) :
    W4NamedExecOpeningHeadAtPinFor S rho q := by
  intro r hslot hafter hprop hhor B hB v hv
  let s := S.hc.opening_slot r
  have hs : 0 < s := by simpa only [s] using hslot
  have hafter' : healingBoundaryTime S q < Protocol.proposal_time S.E s := by
    simpa only [s] using hafter
  have hprop' : S.E.proposer s ∈ rho.honest := by
    simpa only [s] using hprop
  have hconfHor : Protocol.confirmation_time S.E s ≤ rho.horizon := by
    simpa only [s, Setup.a, Protocol.a_eq_confirmation_time] using hhor
  have hduty' := hduty s hs hafter' hprop' hconfHor B hB
  have hsBase : S.hc.opening_slot q + 3 ≤ s := by
    apply w4fh_vote_lt_proposal_succ_le S.E
    simpa only [healingBoundaryTime] using hafter'
  obtain ⟨F, End, hfold, _hbaseEq⟩ := hfoldAt
    (s := s + 1) (hsBase.trans (Nat.le_succ s)) (by
      simpa only [Nat.add_sub_cancel] using hconfHor)
  have hproposalHor : Protocol.proposal_time S.E s ≤ rho.horizon :=
    (le_of_lt (Protocol.proposal_time_lt_vote_time S.E s)).trans
      ((Protocol.vote_time_le_confirmation_time S.E s).trans hconfHor)
  have hBRun : RunBlock S rho B :=
    proposedBlock_runBlock S adm hs hprop' hproposalHor hB
  have hendpointToB : Block.Preceq (F s) B.erase :=
    Block.preceq_trans
      (hfold.parent s hsBase (Nat.le_succ s) hprop')
      (proposedParent_preceq_proposedBlockAt S rho s hB)
  obtain ⟨EndAt, hstate, hval⟩ :=
    hfold.historyAt s hsBase (Nat.le_succ s)
  obtain ⟨E, hE, hErun⟩ :=
    hstate.endpointRun _ hstate.start_le (Nat.le_refl _)
  have hEF : E.erase = F s := hE.trans hval
  have hEB : Block.Preceq E.erase B.erase := by
    rw [hEF]
    exact hendpointToB
  have hEnamedB : NamedBlock.Preceq E B :=
    Protocol.namedPreceq_of_runBlock_erase_preceq
      adm hErun hBRun hEB
  have hcut : S.a r = Protocol.support_cutoff S.E (s + 1) := by
    simpa only [s] using Protocol.a_eq_support_cutoff_succ S.hc S.E r
  have hstartAction :
      Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) ≤ S.a r := by
    rw [hcut]
    exact Proofs.Optimistic.support_cutoff_mono S.E
      ((Nat.le_succ (S.hc.opening_slot q + 2)).trans
        (hsBase.trans (Nat.le_succ s)))
  have hsep : ∀ p : Round, S.a p < S.a r →
      S.a p < Protocol.proposal_time S.E s := by
    intro p hp
    simpa only [s] using w4fh_action_time_lt_openingProposal S hp
  have hrootE : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v (S.a r)).core.toHealing.toFG) E.erase :=
    hstate.readRoot_preceq_endpointAtCursor_named S adm hbelow hsep
      (Nat.le_refl _) hv hstartAction hE hErun
  have hrootB : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v (S.a r)).core.toHealing.toFG) B.erase :=
    Block.preceq_trans hrootE hEB
  have hbandE :
      (rho.storeBeforeTime S v (S.a r)).core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg E).h :=
    hstate.readFrontier_sub_one_le_endpointAtCursor_named S adm hbelow hsep
      (Nat.le_refl _) hv hE hErun
  have hbandB :
      (rho.storeBeforeTime S v (S.a r)).core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg B).h :=
    hbandE.trans
      (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hEnamedB)
  have hconeB : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B.erase X) := by
    intro x hx hxc
    obtain ⟨X, hXB, hXrun, hXemit⟩ := hduty'.votes x hx hxc
    refine ⟨X, ?_, hXrun, hXemit⟩
    rw [hXB]
    exact Block.preceq_self B.erase
  have hR0q : S.hc.round_of (S.hc.opening_slot q + 3) - 1 ≤ q :=
    w4fh_nat_pred_le_of_pos_le_succ hbaseTiming.1
      (w4fh_round_of_opening_add_three_le_succ S.hc q)
  have hpostAtBase : S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q + 2) :=
    hbaseTiming.2.1.trans
      (((action_strictMono S).monotone hR0q).trans
        (Protocol.action_lt_proposal_time_two_after S q).le)
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E s :=
    hpostAtBase.trans
      ((Protocol.proposal_time_mono S.E
        ((Nat.le_succ (S.hc.opening_slot q + 2)).trans hsBase)).trans
          (le_of_lt (Protocol.proposal_time_lt_vote_time S.E s)))
  have hcutS : Protocol.support_cutoff S.E s ≤ S.a r := by
    rw [hcut]
    exact Proofs.Optimistic.support_cutoff_mono S.E (Nat.le_succ s)
  have hcutSHor : Protocol.support_cutoff S.E s ≤ rho.horizon :=
    hcutS.trans hhor
  have havailable := honestHeadsAvailableBefore_of_postHealingCone_at
    S adm.toNamedAdmissibleCore hv hpost hcutSHor hcutS hrootB hconeB
  have hmemT : B.erase ∈ (rho.storeBeforeTime S v (S.a r)).core.T :=
    mem_storeBeforeTime_of_cone S adm hcom havailable hcutS hconeB
  have hmem : B ∈ (rho.storeBeforeTime S v (S.a r)).bodies :=
    mem_bodies_of_mem_T S adm hv hBRun hmemT
  have hcandidateRaw : B.erase ∈
      Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S v (S.a r)).core.toHealing.toFG :=
    storeBeforeTime_mem_filtered_of_band S adm hmem hrootB hbandB
  have hcandidate : B.erase ∈
      Protocol.get_filtered_block_tree
        (actionStoreAt S rho v r).toHealing.toFG := by
    rw [actionStoreAt_filteredTree_eq_storeBeforeTime S rho v r]
    exact hcandidateRaw
  have hBEnd : Block.Preceq B.erase End :=
    Block.preceq_trans
      (by
        obtain ⟨B', hB', hpre⟩ :=
          hfold.absorbed s hsBase (Nat.lt_succ_self s) hprop'
        have hBB' : B' = B := proposedBlockAt_unique S rho s hB' hB
        simpa only [hBB'] using hpre)
      (w4fh_movingSlotEntryStateN_prevLe hfold.entry)
  have hnextCone : NamedHonestVotesCone S rho (s + 1)
      (fun X => Block.Preceq B.erase X) := by
    intro x hx hxc
    obtain ⟨X, hEndX, hXrun, hXemit⟩ := hfold.entry.votes x hx hxc
    exact ⟨X, Block.preceq_trans hBEnd hEndX, hXrun, hXemit⟩
  have hpostNext : S.E.t_GST ≤ Protocol.vote_time S.E (s + 1) :=
    hpost.trans (Protocol.vote_time_mono_slots S.E (Nat.le_succ s))
  have hcutHor : Protocol.support_cutoff S.E (s + 1) ≤ rho.horizon := by
    rw [← hcut]
    exact hhor
  have hrootAction : Block.Preceq
      (Protocol.get_fg_root
        (actionStoreAt S rho v r).toHealing.toFG) B.erase := by
    rw [actionStoreAt_fgRoot_eq_storeBeforeTime S rho v r]
    exact hrootB
  have hresolve := WeakAction.headsResolveIn_actionStore_of_postHealingCone
    S adm hv hpostNext hcutHor hcut hrootAction hnextCone
  have hconeAction := WeakAction.coneSupport_actionStoreAt S
    adm.toNamedAdmissibleCore hcom (Nat.succ_pos s) hpostNext hcutHor
    hnextCone hv hcut hresolve
  have hroundConf : S.hc.round_of
      (confirmationInputRead S rho v s).st.core.s = r := by
    simpa only [s, confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Proofs.HealingSurface.opening_confirmation_time_eq_action,
      Protocol.NamedStore.setClock] using Proofs.HealingLemmas.round_of_slotOf_a S r
  have hconfAnchor : namedConfirmationAnchor S
      (confirmationInputRead S rho v s) =
      PhaseGrades.nodeAnchor S (confirmationInputRead S rho v s) r := by
    simp only [namedConfirmationAnchor, PhaseGrades.nodeAnchor,
      PhaseGrades.nodeRead, Protocol.get_sg_root_with, hroundConf]
  have hnode : PhaseGrades.nodeAnchor S (actionReadAt S rho v r) r =
      PhaseGrades.nodeAnchor S (confirmationInputRead S rho v s) r := rfl
  have hanchorNode : Block.Preceq
      (PhaseGrades.nodeAnchor S (actionReadAt S rho v r) r) B.erase := by
    rw [hnode, ← hconfAnchor]
    exact hduty'.anchor v hv
  have hroundAction : S.hc.round_of
      (actionStoreAt S rho v r).toHealing.s = r := by
    simpa only [Protocol.Store.toHealing] using actionStoreAt_round S rho v r
  have hanchor : Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
        S.E S.hc (actionStoreAt S rho v r).toHealing
        (S.hc.round_of (actionStoreAt S rho v r).toHealing.s)) B.erase := by
    rw [hroundAction]
    simpa only [PhaseGrades.nodeAnchor, PhaseGrades.nodeRead, actionReadAt]
      using hanchorNode
  have hpath := WeakAction.actionPath_to_ancestor_of_candidate S
    adm.toNamedAdmissibleCore hcandidate (Block.preceq_self B.erase)
  exact WeakAction.protectedBlock_preceq_actionHead_of_cone_compatible S
    adm.toNamedAdmissibleCore hcut hconeAction
    (Block.compatible_of_preceq_common hanchor (Block.preceq_self B.erase))
    (fun _ => hpath)

#print axioms w4NamedExecOpeningHeadAtPinFor_of_fold




/-- The prepared execution record from the stage-2 records. This additive
twin avoids the global head-pin interface: it constructs the selected
round's head field directly from the records's named fold. -/
theorem canonicalSuffixExecutionPrepared_named_of_prefix_and_fold
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {q : Round} {D : NamedBlock V} {M0 : Height}
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon)
    (hprefix :
      CanonicalSuffixFrom S rho (healingBoundaryTime S q) ∧
      Nonempty (CanonicalSuffixActionHistory S rho q) ∧
      (∀ s : Slot, 0 < s →
        healingBoundaryTime S q < Protocol.proposal_time S.E s →
        S.E.proposer s ∈ rho.honest →
        Protocol.confirmation_time S.E s ≤ rho.horizon →
        ∀ B : NamedBlock V, proposedBlockAt S rho s = some B →
          Protocol.CanonicalProposalDutyAt S rho s B) ∧
      (∀ {s : Slot}, S.hc.opening_slot q + 3 ≤ s →
        Protocol.confirmation_time S.E (s - 1) ≤ rho.horizon →
        ∃ F : Slot → Block V, ∃ End : Block V,
          MovingSlotFoldAtN S rho
            (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
            (S.hc.opening_slot q + 3) s F End ∧
          F (S.hc.opening_slot q + 3) = D.erase)) :
    CanonicalSuffixExecutionPrepared S rho q := by
  have hhead : W4NamedExecOpeningHeadAtPinFor S rho q := by
    exact w4NamedExecOpeningHeadAtPinFor_of_fold S adm hcom hbelow
      hbaseTiming hprefix.2.2.1 hprefix.2.2.2
  exact
    { canonicalSuffixFrom := hprefix.1
      actionHistory := hprefix.2.1
      duty := hprefix.2.2.1
      openingProposalPreceqActionHeadAt := hhead }

#print axioms canonicalSuffixExecutionPrepared_named_of_prefix_and_fold

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
