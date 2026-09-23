module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ProposalConfirmationPreparedLiveNamed
public import DecoupledConsensusProofs.Execution.HandoverHeightNamedDirect
public import DecoupledConsensusProofs.Protocol.Handlers.HandoverUpdatedStable
public import DecoupledConsensusProofs.Protocol.Handlers.UserConfirmationRecovery

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Latest confirmation of an arbitrary healed named proposal -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem update_confirmation_with_latest_confirmed_of_eligible_p7
    (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot)
    (hfirst : Block.Preceq
      (Protocol.update_confirmation_with contract E hc st s).latest_stable
      (Protocol.advance_confirmed st.latest_confirmed
        (confWalkWith contract E hc st s)))
    (helig : confEligible E st s (confWalkWith contract E hc st s) = true) :
    (Protocol.update_confirmation_with contract E hc st s).latest_confirmed =
      Protocol.advance_confirmed st.latest_confirmed
        (confWalkWith contract E hc st s) := by
  have hval : (Protocol.update_confirmation_with contract E hc st s).latest_confirmed =
      Protocol.floor_on_stable
        (Protocol.update_confirmation_with contract E hc st s).latest_stable
        (match contract.confirmationSG with
          | .optional select =>
              if confEligible E st s (confWalkWith contract E hc st s) then
                Protocol.advance_confirmed st.latest_confirmed
                  (confWalkWith contract E hc st s)
              else
                match select E hc st.toHealing s with
                | some candidate =>
                    Protocol.advance_confirmed st.latest_confirmed candidate
                | none => st.latest_confirmed)
        st.latest_confirmed := rfl
  cases hmode : contract.confirmationSG with
  | optional select =>
      have hval' := hval
      simp only [hmode, if_pos helig] at hval'
      rw [hval']
      unfold Protocol.floor_on_stable
      have hfirst' : Block.preceq
          (Protocol.update_confirmation_with contract E hc st s).latest_stable
          (Protocol.advance_confirmed st.latest_confirmed
            (confWalkWith contract E hc st s)) = true := hfirst
      rw [if_pos hfirst']





/-- Closed P7b under the  post-recovery window. -/
theorem honestProposal_confirmationSeedPrepared_latest_after_SG_healing_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round} {P : NamedBlock V}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      2 * progressLag' gap delayExtra +
      max (1 + S.hc.η_SG) (gap + 3) ≤ m)
    (hcarrier : ProposerCarrierAt S rho m)
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      (Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (confirmationInputRead S rho v (S.hc.opening_slot m)).cache)
        S.E S.hc (confStore S rho v (S.hc.opening_slot m))
        (S.hc.opening_slot m)).latest_confirmed = P.erase := by
  classical
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let L := progressLag' gap delayExtra
  let base : Round := D + 2 * L + 1
  let start := S.hc.opening_slot m
  have hmOld : D + 2 * L + 1 + S.hc.η_SG ≤ m := by
    have hmax : 1 + S.hc.η_SG ≤ max (1 + S.hc.η_SG) (gap + 3) :=
      le_max_left _ _
    have hold := (Nat.add_le_add_left hmax (D + 2 * L)).trans (by
      simpa only [D, L, Nat.add_assoc] using hm)
    simpa only [Nat.add_assoc] using hold
  have hmTwo : D + 2 ≤ m := by
    have hlag : 1 ≤ L := by simpa only [L] using progressLag'_pos gap
    have htwolag : 2 ≤ 2 * L := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left 2 hlag
    have htail : 2 ≤ 2 * L + 1 + S.hc.η_SG :=
      htwolag.trans (by
        simpa only [Nat.add_assoc] using Nat.le_add_right (2 * L) (1 + S.hc.η_SG))
    exact (Nat.add_le_add_left htail D).trans (by
      simpa only [D, L, Nat.add_assoc] using hmOld)
  have hmPos : 2 ≤ m := (Nat.le_add_left 2 D).trans hmTwo
  have hstartPos : 0 < start := by
    unfold start Protocol.HealConfig.opening_slot
    exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_two hmPos)
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hvoteHor : Protocol.vote_time S.E start ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E start).trans hhor
  have hvoteDelta : Protocol.vote_time S.E start + S.E.Δ ≤ rho.horizon := by
    rw [vote_time_add_delta]
    exact (support_cutoff_le_confirmation_time S.E start).trans hhor
  have hdeadlineSlot : S.hc.opening_slot D + 1 ≤ start := by
    have hstep : S.hc.opening_slot D + 1 <
        S.hc.opening_slot (D + 1) := by
      simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
        using Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two)
          (D * S.hc.R)
    have hround : D + 1 ≤ m :=
      (Nat.le_succ (D + 1)).trans (by
        simpa only [Nat.add_assoc] using hmTwo)
    exact hstep.le.trans (by
      simpa only [start, Protocol.HealConfig.opening_slot] using
        Nat.mul_le_mul_right S.hc.R hround)
  have hdeadlineProposal : S.a D ≤ Protocol.proposal_time S.E start := by
    have hround : S.hc.opening_slot D + 2 ≤ start := by
      have hstep : S.hc.opening_slot D + 2 ≤
          S.hc.opening_slot (D + 1) := by
        simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add_left S.hc.R_ge_two (D * S.hc.R)
      have hDm : D + 1 ≤ m :=
        (Nat.le_succ (D + 1)).trans (by
          simpa only [Nat.add_assoc] using hmTwo)
      exact hstep.trans (by
        simpa only [start, Protocol.HealConfig.opening_slot] using
          Nat.mul_le_mul_right S.hc.R hDm)
    exact (action_lt_proposal_time_two_after S D).le.trans
      (proposal_time_mono S.E hround)
  have hdeadlineRead : S.a D ≤ Protocol.confirmation_time S.E start :=
    hdeadlineProposal.trans (proposal_time_le_confirmation_time S.E start)
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E start := by
    have hGSTdead : rGST ≤ D := by
      unfold D fgSafetyProgressDeadline
      exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
    exact hpost.trans (((action_strictMono S).monotone hGSTdead).trans
      (hdeadlineProposal.trans (proposal_time_lt_vote_time S.E start).le))
  have hheads : ∀ w ∈ rho.honest, voterHeadAt S rho w start = P.erase :=
    honestProposal_voterHeadAt_eq_after_SG_healing_named
      S adm hcom hbelow hrec hdelay hpost
        (by simpa only [D] using hmTwo) (by simpa only [start] using hvoteHor)
        hcarrier (by simpa only [start] using hP)
  have hcone : NamedHonestVotesCone S rho start
      (fun X => Block.Preceq P.erase X) :=
    honestProposal_openingVoteCone_after_SG_healing_named
      S adm hcom (by simpa only [D] using hmTwo) hcarrier
        (by simpa only [start] using hvoteHor) (by simpa only [start] using hP)
        (by simpa only [start] using hheads)
  have hread := honestProposal_confirmationReadFacts_after_SG_healing_named
    S adm hcom hbelow hrec hdelay hpost (by simpa only [D] using hmTwo)
      (by simpa only [start] using hhor) hcarrier
      (by simpa only [start] using hP)
  have hheights : Handover.HandoverHeights S rho base (D + 1) start P :=
    Handover.handoverHeights_of_carrier_named
      S adm hcom hbelow hrec hdelay hpost
        (by exact Nat.le_refl _)
        (by simpa only [base, D, L, Nat.add_assoc] using hmOld)
        hcarrier (by simpa only [start] using hhor)
        (by simpa only [start] using hP)
  have hlive := honestProposal_confirmationSeedPrepared_live_after_SG_healing_named
    S adm hcom hbelow hrec hdelay hpost hmOld hcarrier hP hhor
  intro v hv
  obtain ⟨hanchor, hcandidate⟩ := hread v hv
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (confirmationInputRead S rho v start).st.core.toHealing.toFG) P.erase := by
    have hrootHead := fgRoot_preceq_previousHead_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hdeadlineRead hhor
        hdeadlineSlot (le_refl _) hvoteDelta hv hv
    have hrootHead' : Block.Preceq
        (Protocol.get_fg_root
          (confirmationInputRead S rho v start).st.core.toHealing.toFG)
        (voterHeadAt S rho v start) := by
      simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.voteDutyHead] using hrootHead
    simpa only [hheads v hv] using hrootHead'
  have hgenuineSelected := genuineConfirmationAndPreceq_of_postHealingCone
    S adm hcom hstartPos hpostVote hhor hv hcone hroot hanchor hcandidate
  have hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract (confirmationInputRead S rho v start).cache)
      S.E S.hc (confStore S rho v start) start P.erase :=
    ⟨by simpa only [start] using hlive v hv, hgenuineSelected.1.genuine⟩
  let contract := NamedProfile.gradeContract
    (confirmationInputRead S rho v start).cache
  let st := confStore S rho v start
  have hliveFormula := update_confirmation_with_live_confirmed
    contract S.E S.hc st start
  have hwalk : confWalkWith contract S.E S.hc st start = P.erase := by
    rw [if_pos (by simpa only [contract, st] using hgenuine.genuine)] at hliveFormula
    exact hliveFormula.symm.trans (by
      simpa only [contract, st] using hgenuine.selected)
  have hstableSome : ∃ G : Block V,
      DecoupledConsensusModel.Protocol.frameStableRoot
        (confirmationInputRead S rho v start).cache S.E S.hc
        (confirmationInputRead S rho v start).st.core.toHealing
        (S.hc.round_of (S.E.slotOf
          (Protocol.confirmation_time S.E start))) = some G := by
    unfold DecoupledConsensusModel.Protocol.frameStableRoot
    cases hslot : ((DecoupledConsensusModel.Protocol.readFrame
        (confirmationInputRead S rho v start).cache
        (confirmationInputRead S rho v start).st.core.toHealing
        (S.hc.round_of (S.E.slotOf
          (Protocol.confirmation_time S.E start)))).g2.bind id) with
    | none =>
        exact ⟨Protocol.get_fg_root
          (confirmationInputRead S rho v start).st.core.toHealing.toFG, by
            rfl⟩
    | some raw =>
        cases hactive : DecoupledConsensusModel.Protocol.activePrefix
            (Protocol.get_filtered_block_tree
              (confirmationInputRead S rho v start).st.core.toHealing.toFG) raw with
        | none =>
            exact ⟨Protocol.get_fg_root
              (confirmationInputRead S rho v start).st.core.toHealing.toFG, by
                simp only [Option.bind_some, hactive]⟩
        | some G =>
            exact ⟨G, by simp only [Option.bind_some, hactive]⟩
  obtain ⟨G, hG⟩ := hstableSome
  have hstableP : Block.Preceq
      (Protocol.advance_confirmed
        (confirmationInputRead S rho v start).st.core.latest_stable G) P.erase :=
    Handover.updatedStable_preceq_walk_at_openingConfirmation S adm hcom hbelow hrec hdelay hpost hm hcarrier hP
      (by simpa only [start] using hheads)
      (by simpa only [base, D, L, start] using hheights)
      (by simpa only [start] using hhor) hv
      (by simpa only [start] using hG)
  have hstableEq :
      (Protocol.update_confirmation_with contract S.E S.hc st start).latest_stable =
        Protocol.advance_confirmed st.latest_stable G := by
    change (match DecoupledConsensusModel.Protocol.frameStableRoot
        (confirmationInputRead S rho v start).cache S.E S.hc
        (confirmationInputRead S rho v start).st.core.toHealing
        (S.hc.round_of (S.E.slotOf
          (Protocol.confirmation_time S.E start))) with
      | some G => Protocol.advance_confirmed
          (confirmationInputRead S rho v start).st.core.latest_stable G
      | none => (confirmationInputRead S rho v start).st.core.latest_stable) =
        Protocol.advance_confirmed
          (confirmationInputRead S rho v start).st.core.latest_stable G
    rw [hG]
  have hslotP : start ≤ P.erase.slot := by
    rw [Proofs.NamedWire.erase_slot, proposedBlockAt_slot S rho start hP]
  have hadvance : Protocol.advance_confirmed st.latest_confirmed P.erase = P.erase := by
    simpa only [st, confStore, tickStore] using
      ConfirmationOrigin.advance_confirmed_eq_of_read_slot_le
        S adm.toNamedAdmissibleCore v start hslotP
  have hfirst : Block.Preceq
      (Protocol.update_confirmation_with contract S.E S.hc st start).latest_stable
      (Protocol.advance_confirmed st.latest_confirmed
        (confWalkWith contract S.E S.hc st start)) := by
    rw [hstableEq, hwalk, hadvance]
    simpa only [st] using hstableP
  have hlatest := update_confirmation_with_latest_confirmed_of_eligible_p7
    contract S.E S.hc st start hfirst
      (by simpa only [contract, st] using hgenuine.genuine)
  rw [hwalk, hadvance] at hlatest
  simpa only [contract, st, start] using hlatest


#print axioms honestProposal_confirmationSeedPrepared_latest_after_SG_healing_named



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
