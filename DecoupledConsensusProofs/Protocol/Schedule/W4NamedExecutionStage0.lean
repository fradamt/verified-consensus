module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.W4NamedFoldStage0

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The staged named execution records from stage-0 data

This leaf closes the selected complete state and returns the four stage-2
execution fields: suffix, action history, canonical proposal duty, and the
named fold at every slot. The prepared action-head field is deliberately
left to the fold-only head leaf.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem w4nes_vote_lt_proposal_succ_le
    (E : Env V) {a b : Slot}
    (h : Protocol.vote_time E a < Protocol.proposal_time E b) :
    a + 1 ≤ b := by
  apply Nat.succ_le_of_lt
  by_contra hnot
  have hba : b ≤ a := Nat.le_of_not_gt hnot
  exact (not_le_of_gt h)
    ((Protocol.proposal_time_mono E hba).trans
      (Protocol.proposal_time_lt_vote_time E a).le)

private theorem w4nes_round_of_opening_add_three_le_succ
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

private theorem w4nes_nat_pred_le_of_pos_le_succ {a b : Nat}
    (ha : 0 < a) (h : a ≤ b + 1) : a - 1 ≤ b :=
  Nat.lt_succ_iff.mp ((Nat.sub_lt ha (by decide : 0 < 1)).trans_le h)

private theorem w4nes_vote_time_le_support_cutoff (E : Env V) (s : Slot) :
    Protocol.vote_time E s ≤ Protocol.support_cutoff E s := by
  rw [← Proofs.Optimistic.vote_time_add_delta]
  exact Int.le_add_of_nonneg_right E.Δ_pos.le

private theorem w4nes_confirmation_time_mono
    (E : Env V) {a b : Slot} (hab : a ≤ b) :
    Protocol.confirmation_time E a ≤ Protocol.confirmation_time E b :=
  Int.add_le_add_right (Protocol.proposal_time_mono E hab) _

private theorem w4nes_proposedParent_preceq_proposedBlockAt
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


private theorem w4nes_proposal_succ_le_confirmation (E : Env V) (s : Slot) :
    Protocol.proposal_time E (s + 1) ≤ Protocol.confirmation_time E s := by
  exact (Protocol.proposal_time_lt_vote_time E (s + 1)).le.trans
    (by
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time E s]
      exact Int.le_add_of_nonneg_right E.Δ_pos.le)

private theorem w4nes_postGST_at_selected
    (S : Setup V) {rho : Run V}
    {rGST gap q : Round}
    (hcom : HonestCommittees S rho.honest)
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon)
    (hqLate : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q) :
    ∀ s : Slot,
      healingBoundaryTime S q < Protocol.proposal_time S.E s →
      S.E.t_GST ≤ Protocol.vote_time S.E s := by
  let o := S.hc.opening_slot q
  have hR0pos : 0 < S.hc.round_of (o + 3) := by
    simpa only [o] using hbaseTiming.1
  have hR0q : S.hc.round_of (o + 3) - 1 ≤ q := by
    exact w4nes_nat_pred_le_of_pos_le_succ hR0pos
      (w4nes_round_of_opening_add_three_le_succ S.hc q)
  have hpostAtBase : S.E.t_GST ≤
      Protocol.proposal_time S.E (o + 2) := by
    exact hbaseTiming.2.1.trans
      (((action_strictMono S).monotone hR0q).trans
        (Protocol.action_lt_proposal_time_two_after S q).le)
  intro s hafter
  have hsBase : o + 3 ≤ s := by
    apply w4nes_vote_lt_proposal_succ_le S.E
    simpa only [healingBoundaryTime, o] using hafter
  have hpostProposal : S.E.t_GST ≤ Protocol.proposal_time S.E s :=
    hpostAtBase.trans
      (Protocol.proposal_time_mono S.E
        ((Nat.le_add_right (o + 2) 1).trans hsBase))
  exact hpostProposal.trans
    (Protocol.proposal_time_lt_vote_time S.E s).le

private theorem w4nes_honestVoteReads_of_fold
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {rGST gap q : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    (hqLate : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q)
    {D : NamedBlock V} {M0 : Height}
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon)
    (hcarrierBase : ∀ r : Round,
      S.hc.round_of (S.hc.opening_slot q + 3) = r + 1 →
      ∀ u ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho u r) D.erase)
    (hcarrierQ : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u q) D.erase)
    {s : Slot} {F : Slot → Block V} {End Next : Block V} {P : NamedBlock V}
    (hfold : MovingSlotFoldAtN S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
      (S.hc.opening_slot q + 3) s F End)
    (hsBase : S.hc.opening_slot q + 3 ≤ s)
    (hbaseEq : F (S.hc.opening_slot q + 3) = D.erase)
    (hfrontier : MovingSlotFrontierAt S rho (s - 1) End Next)
    (hfacts : NamedMovingSlotWindowFacts S rho s End Next)
    (hcone : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq Next X))
    (hcutS : Protocol.support_cutoff S.E s ≤ rho.horizon)
    (hproposalS : Protocol.proposal_time S.E (s + 1) ≤ rho.horizon)
    (hvoteS : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hprop : S.E.proposer (s + 1) ∈ rho.honest)
    (hP : proposedBlockAt S rho (s + 1) = some P) :
    (∀ w ∈ rho.honest, voteDutyHead S rho w (s + 1) = P.erase) ∧
      (∀ w ∈ rho.honest,
        Block.compatible (voterAnchorAt S rho w (s + 1)) P.erase = true) := by
  obtain ⟨EndAt0, hstate0, hprev0, hEnd0⟩ := hfold.entry.prevEndpoint
  have hrunEnd : ∃ E : NamedBlock V, E.erase = End ∧ RunBlock S rho E := by
    obtain ⟨E0, hE0, hE0run⟩ := hstate0.endpointRun _ hstate0.start_le
      (Nat.le_refl _)
    refine ⟨E0, ?_, hE0run⟩
    exact hE0.trans hEnd0
  have hrunNext : ∃ E : NamedBlock V, E.erase = Next ∧ RunBlock S rho E :=
    hfrontier.runBlock S adm hrunEnd
  have hDNext : Block.Preceq D.erase Next := by
    have hDPrev : Block.Preceq D.erase (F s) := by
      rw [← hbaseEq]
      exact hfold.mono _ _ (Nat.le_refl _) hsBase (Nat.le_refl _)
    exact Block.preceq_trans hDPrev
      (Block.preceq_trans hfold.entry.prevLe hfrontier.oldPreceq)
  obtain ⟨v, hv⟩ := honest_nonempty_of_honestCommittees hcom
  have hparent := hfold.nextParent_hybrid S adm hcom hfb
    hbaseTiming.1 hbaseTiming.2.1 hcarrierBase hcarrierQ
    hsBase hbaseEq hfrontier hfacts hcone hcutS hproposalS hprop hv
  obtain ⟨P0, hP0, EndAt, _hlow, hstrict, hincl, hstate⟩ :=
    MovingFrontierChainStateN.through_slotWindow_honestProposer_named
      S adm (Nat.lt_of_lt_of_le (Nat.succ_pos _) hsBase) hstate0 hEnd0
      hrunEnd hrunNext hfacts hprop hproposalS hparent hv
      hcutS
  have hP0eq : P0 = P := proposedBlockAt_unique S rho (s + 1) hP0 hP
  subst P0
  have hstart : Protocol.support_cutoff S.E
      (S.hc.opening_slot q + 2) ≤ Protocol.proposal_time S.E (s + 1) := by
    exact (Protocol.support_cutoff_lt_proposal_time_succ S.E
      (S.hc.opening_slot q + 2)).le.trans
      (Protocol.proposal_time_mono S.E
        (hsBase.trans (Nat.le_succ s)))
  have hpre : MovingSlotPreEntryN S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
      (s + 1) Next P.erase :=
    { startTime := hstart
      prevEndpoint := ⟨EndAt, hstate, hstrict, hincl⟩
      prevVotes := by simpa only [Nat.add_sub_cancel] using hcone }
  obtain ⟨r, hround, hpostAction, hcut, hmode⟩ :=
    w4_proposalSchedule_hybrid S hbaseTiming.1 hbaseTiming.2.1
      hcarrierBase hcarrierQ hDNext (hsBase.trans (Nat.le_succ s))
      hproposalS
  have hafterS : healingBoundaryTime S q <
      Protocol.proposal_time S.E s := by
    have hbaseAfter : healingBoundaryTime S q <
        Protocol.proposal_time S.E (S.hc.opening_slot q + 3) := by
      exact (w4nes_vote_time_le_support_cutoff S.E
        (S.hc.opening_slot q + 2)).trans_lt
        (Protocol.support_cutoff_lt_proposal_time_succ S.E
          (S.hc.opening_slot q + 2))
    exact hbaseAfter.trans_le
      (Protocol.proposal_time_mono S.E hsBase)
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E s :=
    w4nes_postGST_at_selected S hcom hbaseTiming hqLate s hafterS
  have hhead : ∀ w ∈ rho.honest,
      voteDutyHead S rho w (s + 1) = P.erase := by
    have hdeadlineSlot : S.hc.opening_slot
        (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ s + 1 := by
      have hd : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ q :=
        (Nat.le_succ _).trans hqLate
      have hqslot : S.hc.opening_slot q ≤ s :=
        (Nat.le_add_right (S.hc.opening_slot q) 3).trans hsBase
      exact (Nat.mul_le_mul_right S.hc.R hd).trans
        (hqslot.trans (Nat.le_add_right s 1))
    exact honestProposal_voterHeadAt_eq_after_SG_healing_named_slot
      S adm hcom hfb hrec hdelay hpost (s := s) (P := P)
      hdeadlineSlot hvoteS hprop hP
  have hanchor : ∀ w ∈ rho.honest,
      Block.Preceq (voterAnchorAt S rho w (s + 1)) Next := by
    intro w hw
    rcases hmode with ht1 | hupper
    · exact w4cx_movingSlotPreEntryN_voterAnchorAt_preceq_prev_of_voteHorizon
        S adm hfb hpre.startTime hpre.prevEndpoint hround ht1 hpostAction
        hcut hvoteS hw
    · exact w4cx_movingSlotPreEntryN_voterAnchorAt_preceq_prev_of_ceiling
        S adm hcom hfb hpre hround hupper hpostAction hcut hpostVote hcutS
        hvoteS hw
  have hparentP : Block.Preceq Next P.erase := Block.preceq_trans hparent
    (w4nes_proposedParent_preceq_proposedBlockAt S rho (s + 1) hP)
  refine ⟨hhead, ?_⟩
  intro w hw
  exact Block.compatible_of_preceq_common
    (Block.preceq_trans (hanchor w hw) hparentP) (Block.preceq_self P.erase)


/-- The four-part named execution records from stage-0 data. -/
theorem w4NamedExecutionPrefix_of_stage0
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {rGST gap q : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    (hqLate : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q)
    {D : NamedBlock V} {carrier : V} {M0 : Height}
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    (hboundary : W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 D)
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon) :
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
        F (S.hc.opening_slot q + 3) = D.erase) := by
  have hcarrierBase := hboundary.carrierCeiling
  have hcarrierQPin := w4CarrierCeilingAtQPin_of_prepared S adm hfb
  have hcarrierAtQ := hcarrierQPin q D carrier hhandoff hbaseTiming hcarrierBase
  have hfoldAt : ∀ {s : Slot}, S.hc.opening_slot q + 3 ≤ s →
      Protocol.confirmation_time S.E (s - 1) ≤ rho.horizon →
      ∃ F : Slot → Block V, ∃ End : Block V,
        MovingSlotFoldAtN S rho
          (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
          (S.hc.opening_slot q + 3) s F End ∧
        F (S.hc.opening_slot q + 3) = D.erase := by
    intro s hs hhor
    exact w4NamedFoldAtEverySlotFrom_stage0 S adm hcom hfb hrec hdelay
      hpost hqLate hhandoff hboundary hbaseTiming hs hhor
  have hpostGST := w4nes_postGST_at_selected S hcom hbaseTiming hqLate
  have hdeadlineHor : healingBoundaryTime S q ≤ rho.horizon := by
    have hconfMono := w4nes_confirmation_time_mono S.E
      (show S.hc.opening_slot q + 2 ≤ S.hc.opening_slot q + 3 by
        exact Nat.le_succ _)
    simpa only [healingBoundaryTime] using
      (Protocol.vote_time_le_confirmation_time S.E
        (S.hc.opening_slot q + 2)).trans
        (hconfMono.trans hbaseTiming.2.2)
  obtain ⟨nB, hstart, hlast⟩ :=
    exists_lastCanonicalSuffixStart S adm hcom hdeadlineHor
  obtain ⟨EndAt, hcompleteState⟩ := by
    have hbyz : W4ByzantineVoteAnchorPin S rho := by
      change w4cx_ByzantineVoteAnchorPin S rho
      exact w4cx_byzantineVoteAnchorPin_of_preentry S adm hcom hfb
    have hproposalBaseSuccHor : Protocol.proposal_time S.E
        (S.hc.opening_slot q + 3 + 1) ≤ rho.horizon :=
      (w4nes_proposal_succ_le_confirmation S.E
        (S.hc.opening_slot q + 3)).trans hbaseTiming.2.2
    have hbaseSuccZ := Protocol.slot_le_slotOf_of_proposal_time_le S.E
      hproposalBaseSuccHor
    have hhorNonneg := (Proofs.Optimistic.proposal_time_nonneg S.E
      (S.hc.opening_slot q + 3 + 1)).trans hproposalBaseSuccHor
    have hproposalZ := Protocol.proposal_time_slotOf_le S.E hhorNonneg
    have hnextFuture : rho.horizon <
        Protocol.proposal_time S.E (S.E.slotOf rho.horizon + 1) := by
      exact lt_of_not_ge (fun h => by
        have hs := Protocol.slot_le_slotOf_of_proposal_time_le S.E h
        exact Nat.not_succ_le_self _ hs)
    by_cases hcutZ : Protocol.support_cutoff S.E
        (S.E.slotOf rho.horizon) ≤ rho.horizon
    · exact w4CompleteStateN_of_foldN_at_lastSlot S adm hcom hfb hbaseTiming
        hcarrierBase hcarrierAtQ
        (Nat.le_trans (Nat.le_succ _) hbaseSuccZ) hcutZ hnextFuture hfoldAt
    · have hhonestReads : ∀ {s : Slot} {F : Slot → Block V}
          {End Next : Block V} {P : NamedBlock V},
          MovingSlotFoldAtN S rho
            (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
            (S.hc.opening_slot q + 3) s F End →
          S.hc.opening_slot q + 3 ≤ s →
          F (S.hc.opening_slot q + 3) = D.erase →
          MovingSlotFrontierAt S rho (s - 1) End Next →
          NamedMovingSlotWindowFacts S rho s End Next →
          NamedHonestVotesCone S rho s (fun X => Block.Preceq Next X) →
          Protocol.support_cutoff S.E s ≤ rho.horizon →
          Protocol.proposal_time S.E (s + 1) ≤ rho.horizon →
          Protocol.vote_time S.E (s + 1) ≤ rho.horizon →
          S.E.proposer (s + 1) ∈ rho.honest →
          proposedBlockAt S rho (s + 1) = some P →
          (∀ w ∈ rho.honest, voteDutyHead S rho w (s + 1) = P.erase) ∧
            (∀ w ∈ rho.honest,
              Block.compatible (voterAnchorAt S rho w (s + 1)) P.erase = true) := by
        intro s F End Next P hfold hsBase hbaseEq hfrontier hfacts hcone hcutS
          hproposalS hvoteS hprop hP
        exact w4nes_honestVoteReads_of_fold S adm hcom hfb hrec hdelay hpost
          hqLate hbaseTiming hcarrierBase hcarrierAtQ hfold hsBase hbaseEq
          hfrontier hfacts hcone hcutS hproposalS hvoteS hprop hP
      exact w4CompleteStateN_of_foldN_at_cutoffPastHorizon S adm hcom hfb
        hbaseTiming hcarrierBase hcarrierAtQ hbaseSuccZ hproposalZ
        (lt_of_not_ge hcutZ) hnextFuture hfoldAt hhonestReads hbyz
  have hnBM := lastSuffixStart_le_movingStart S adm hstart
  obtain ⟨hsuffix, haction⟩ :=
    canonicalSuffixAndActionHistory_of_completeN
      S adm hcompleteState hstart hlast hnBM
  refine ⟨hsuffix, haction, ?_, hfoldAt⟩
  intro s hs hafter hprop hhor B hB
  exact canonicalProposalDutyAt_of_adoption S adm hcom hfb hrec hdelay hpost
    hqLate hpostGST hs hafter hprop hhor hB

#print axioms w4NamedExecutionPrefix_of_stage0

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
