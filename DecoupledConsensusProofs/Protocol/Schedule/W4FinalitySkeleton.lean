module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Head.W4D3PreparedFinality
public import DecoupledConsensusProofs.Execution.W4UniformDeadline
public import DecoupledConsensusProofs.Execution.W4FKChainAdvanceFold
public import DecoupledConsensusProofs.Protocol.Schedule.W4CarrierFinalityScoped
public import DecoupledConsensusProofs.Protocol.Schedule.W4NamedBoundaryPublic

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# W4 finality end-to-end skeleton

This leaf composes the two public finality fields through the prepared D3
route. The residual record keeps only selected-run and selected-round inputs
that do not yet have a producer. The handoff selection, uniform deadline,
later-read cap, prepared anchor, non-lostness, height progress, processed
finality advance, density, regime, and final projections are discharged here.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.Optimistic Proofs.HealingLemmas
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem w4fs_confirmation_time_mono
    (E : Env V) {s t : Slot} (h : s ≤ t) :
    Protocol.confirmation_time E s ≤ Protocol.confirmation_time E t :=
  Int.add_le_add_right (Protocol.proposal_time_mono E h) _


/-- Local copy of the private later-read adoption helper in
`W4RecoverySpineRun.lean:322-469`. -/
private theorem w4fs_adoptionSucc_of_frontierCap
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {extra : Nat}
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S extra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round}
    (hq : fgSafetyProgressDeadline S rho rGST gap extra + 3 ≤ q)
    (hcarrier : ProposerCarrierAt S rho q)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q + 3) ≤ rho.horizon)
    {D : NamedBlock V}
    (hD : proposedBlockAt S rho (S.hc.opening_slot q + 1) = some D)
    (_of_frontierCap : honestHMaxBeforeIndex S rho
        (strictEventIndex rho (Protocol.vote_time S.E
          (S.hc.opening_slot q + 2))) ≤
      (derive_named S.E S.cfg D).h + 1) :
    ∀ carrier ∈ rho.honest, ∀ w ∈ rho.honest,
      Protocol.NamedNextVoteAdoption S rho
        (Proofs.Optimistic.confStore S rho carrier (S.hc.opening_slot q + 1))
        (S.hc.opening_slot q + 1) D.erase w := by
  classical
  let deadline := fgSafetyProgressDeadline S rho rGST gap extra
  let s := S.hc.opening_slot q + 1
  have hdeadlineQ : deadline + 3 ≤ q := hq
  have hdeadline2Q : deadline + 2 ≤ q := by
    exact (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3) deadline).trans hq
  have hdeadlineSlot : S.hc.opening_slot (deadline + 2) ≤ s := by
    have hslotQ : S.hc.opening_slot (deadline + 2) ≤
        S.hc.opening_slot q :=
      Nat.mul_le_mul_right S.hc.R hdeadline2Q
    exact hslotQ.trans (Nat.le_add_right _ 1)
  have hdeadlineSlotNext : S.hc.opening_slot (deadline + 2) ≤ s + 1 :=
    hdeadlineSlot.trans (Nat.le_add_right _ 1)
  have hsPos : 0 < s := by
    dsimp only [s]
    have hqPos : 0 < q := by
      have hpos : 0 < deadline + 3 := by
        exact Nat.zero_lt_succ (deadline + 2)
      exact hpos.trans_le hdeadlineQ
    exact Nat.lt_of_lt_of_le
      (Nat.mul_pos hqPos
        (lt_of_lt_of_le (by decide : (0 : Nat) < 2) S.hc.R_ge_two))
      (Nat.le_add_right _ 1)
  have hconfS : Protocol.confirmation_time S.E s ≤ rho.horizon := by
    dsimp only [s]
    apply (w4fs_confirmation_time_mono S.E ?_).trans hhor
    exact (Nat.add_le_add_left (by decide : (1 : Nat) ≤ 3) _)
  have hvoteS : Protocol.vote_time S.E s ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E s).trans hconfS
  have hproposalS : Protocol.proposal_time S.E s ≤ rho.horizon :=
    (proposal_time_lt_vote_time S.E s).le.trans hvoteS
  have hpostDeadline : S.E.t_GST ≤ S.a deadline := by
    have hGSTdead : rGST ≤ deadline := by
      dsimp only [deadline]
      unfold fgSafetyProgressDeadline
      exact (Nat.le_succ rGST).trans (Nat.le_add_right (rGST + 1) _)
    exact hpost.trans ((action_strictMono S).monotone hGSTdead)
  have hdeadlineProposal : S.a deadline ≤
      Protocol.proposal_time S.E s := by
    have hslot : S.hc.opening_slot deadline + 2 ≤ s := by
      have hslotQ : S.hc.opening_slot deadline + 2 ≤
          S.hc.opening_slot q := by
        have hstep : S.hc.opening_slot deadline + 2 ≤
            S.hc.opening_slot (deadline + 2) :=
          openingSlot_add_two_le_openingSlot_of_lt S
            (by
              exact (Nat.lt_succ_self deadline).trans_le (Nat.le_succ _))
        exact hstep.trans
          (by simpa only [Protocol.HealConfig.opening_slot] using
            Nat.mul_le_mul_right S.hc.R hdeadline2Q)
      exact hslotQ.trans (Nat.le_add_right _ 1)
    exact (action_lt_proposal_time_two_after S deadline).le.trans
      (proposal_time_mono S.E hslot)
  have hpostProp : S.E.t_GST ≤ Protocol.proposal_time S.E s :=
    hpostDeadline.trans hdeadlineProposal
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E s :=
    hpostProp.trans (proposal_time_lt_vote_time S.E s).le
  have hvoteNext : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    dsimp only [s]
    have hconfNext : Protocol.confirmation_time S.E
        (S.hc.opening_slot q + 2) ≤ rho.horizon := by
      exact (w4fs_confirmation_time_mono S.E
        (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3)
          (S.hc.opening_slot q))).trans hhor
    exact (vote_time_le_confirmation_time S.E
      (S.hc.opening_slot q + 2)).trans hconfNext
  have hcutS : Protocol.support_cutoff S.E s ≤ rho.horizon := by
    exact (Protocol.support_cutoff_le_confirmation_time S.E s).trans hconfS
  have hrunD : RunBlock S rho D := by
    exact Protocol.proposedBlock_runBlock S adm hsPos
      hcarrier.2.1
      hproposalS hD
  have hheads : ∀ v ∈ rho.honest, voterHeadAt S rho v s = D.erase := by
    intro v hv
    exact honestProposal_voterHeadAt_eq_after_SG_healing_named_slot S adm
      (s := S.hc.opening_slot q) hcom hbelow hrec hdelay hpost hdeadlineSlot hvoteS
      hcarrier.2.1 hD v hv
  have hcone : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq D.erase X) := by
    exact honestProposal_slotVoteCone_after_SG_healing_named_of_heads S adm
      hsPos hvoteS hheads
  have hread : S.a deadline ≤ Protocol.vote_time S.E (s + 1) := by
    have hdeadlineQ' : deadline ≤ q :=
      (Nat.le_add_right deadline 3).trans hdeadlineQ
    have haction : S.a deadline ≤ S.a q :=
      (action_strictMono S).monotone hdeadlineQ'
    have hnextProposal : S.a q ≤
        Protocol.proposal_time S.E (S.hc.opening_slot q + 2) :=
      (action_lt_proposal_time_two_after S q).le
    simpa only [s, Nat.add_assoc] using
      haction.trans (hnextProposal.trans
        (proposal_time_lt_vote_time S.E (S.hc.opening_slot q + 2)).le)
  have hnextConf : Protocol.vote_time S.E (s + 1) ≤
      Protocol.confirmation_time S.E s := by
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
  have hshor : Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon := by
    rw [Proofs.Optimistic.vote_time_add_delta]
    exact (Protocol.support_cutoff_le_confirmation_time S.E s).trans hconfS
  have hsDeadline : S.hc.opening_slot deadline + 1 ≤ s := by
    have hstep : S.hc.opening_slot deadline + 1 ≤
        S.hc.opening_slot (deadline + 2) := by
      exact (Nat.add_le_add_left (by decide : (1 : Nat) ≤ 2)
        (S.hc.opening_slot deadline)).trans
        (openingSlot_add_two_le_openingSlot_of_lt S
          (by
            exact (Nat.lt_succ_self deadline).trans_le (Nat.le_succ _)))
    exact hstep.trans hdeadlineSlot
  intro carrier hcarrierHon w hw
  have hrootHead := fgRoot_preceq_previousHead_through_confirmation_after_GST
    S adm hcom hbelow hrec hdelay hpost hread hvoteNext hsDeadline hnextConf
      hshor hw hw
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) D.erase := by
    have hroot' : Block.Preceq
        (Protocol.get_fg_root
          (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG)
        (voterHeadAt S rho w s) := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.voteDutyHead] using hrootHead
    simpa only [hheads w hw] using hroot'
  exact w4_adoptionAt_slot_of_frontierCap S adm hcom hbelow hrec hdelay hpost
    hdeadlineSlot hpostProp hconfS hvoteNext hcutS hpostVote hrunD hheads hcone
    hcarrierHon hw _of_frontierCap hroot

/-- Named-boundary twin of
`w4PreparedHandoffBoundary_of_frontierCap`. The later-read cap still supplies
the prepared handoff. Its honest carrier and genuine confirmation then
supply the named boundary core without an erased-height comparison. -/
theorem w4PreparedNamedHandoffBoundary_of_frontierCap
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hop : ProposerOpeningCarrierRecurrence S rho gap)
    {extra : Nat} (hdelay : TimeoutDelayBound S extra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {q q0 : Round}
    (hq0 : fgSafetyProgressDeadline S rho rGST gap extra + 3 ≤ q0)
    (hwindow : q0 + 3 * progressLag' gap extra ≤ q)
    (hcarrier : ProposerOpeningCarrierAt S rho q)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q + 3) ≤ rho.horizon)
    {D : NamedBlock V}
    (hD : proposedBlockAt S rho (S.hc.opening_slot q + 1) = some D)
    (_of_frontierCap : honestHMaxBeforeIndex S rho
        (strictEventIndex rho (Protocol.vote_time S.E
          (S.hc.opening_slot q + 2))) ≤
      (derive_named S.E S.cfg D).h + 1) :
    ∃ carrier : V,
      HealedTwoSlotHandoffPrepared S rho q D.erase carrier ∧
      W4NamedHandoffBoundaryCore S rho q
        (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2))
        (derive_named S.E S.cfg D).h D := by
  have hrec : MultiProposerRecurrence S rho gap :=
    proposerRecurrence_of_openingCarrierRecurrence S hop
  have hq0q : q0 ≤ q := (Nat.le_add_right q0 _).trans hwindow
  have hq : fgSafetyProgressDeadline S rho rGST gap extra + 3 ≤ q :=
    hq0.trans hq0q
  have hhor1 : Protocol.confirmation_time S.E
      (S.hc.opening_slot q + 1) ≤ rho.horizon :=
    (w4fs_confirmation_time_mono S.E
      (Nat.add_le_add_left (by decide : (1 : Nat) ≤ 3)
        (S.hc.opening_slot q))).trans hhor
  have hadoption := w4fs_adoptionSucc_of_frontierCap S adm hcom hbelow
    hrec hdelay hpost hq hcarrier.2.2 hhor hD _of_frontierCap
  obtain ⟨carrier, hhandoff⟩ :=
    w4_healedTwoSlotHandoffPrepared_of_carrier_after_GST S adm hcom hbelow
      hrec hdelay hpost hq hcarrier.2.2 hhor1 hD hadoption
  have hboundary :=
    w4NamedHandoffBoundaryCore_at_openingCarrier_public S adm hcom hbelow
      hop hdelay hpost hq0 hwindow hcarrier hhor hD
      hhandoff.carrier_honest hhandoff.carrier_genuine
  exact ⟨carrier, hhandoff, hboundary⟩

#print axioms w4PreparedNamedHandoffBoundary_of_frontierCap









end HealingSurface
end Proofs
end DecoupledConsensusModel

end
