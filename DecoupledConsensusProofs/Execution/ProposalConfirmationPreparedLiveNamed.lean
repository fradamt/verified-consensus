module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalAdoptionNamedClosed
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryConeConfirmation

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Live confirmation of an arbitrary healed named proposal -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- P7a: the prepared opening confirmation selects the arbitrary healed
carrier proposal as its live value. -/
theorem honestProposal_confirmationSeedPrepared_live_after_SG_healing_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round} {P : NamedBlock V}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      2 * progressLag' gap delayExtra + 1 + S.hc.η_SG ≤ m)
    (hcarrier : ProposerCarrierAt S rho m)
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      (Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (confirmationInputRead S rho v (S.hc.opening_slot m)).cache)
        S.E S.hc (confStore S rho v (S.hc.opening_slot m))
        (S.hc.opening_slot m)).live_confirmed = P.erase := by
  classical
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let start := S.hc.opening_slot m
  have hmTwo : D + 2 ≤ m := by
    have hlag : 1 ≤ progressLag' gap delayExtra := progressLag'_pos gap
    have htwolag : 2 ≤ 2 * progressLag' gap delayExtra := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left 2 hlag
    have htail : 2 ≤
        2 * progressLag' gap delayExtra + 1 + S.hc.η_SG :=
      htwolag.trans (by
        simpa only [Nat.add_assoc] using
          Nat.le_add_right (2 * progressLag' gap delayExtra) (1 + S.hc.η_SG))
    exact (Nat.add_le_add_left htail D).trans (by
      simpa only [D, Nat.add_assoc] using hm)
  have hmPos : 2 ≤ m := (Nat.le_add_left 2 D).trans hmTwo
  have hstartPos : 0 < start := by
    unfold start Protocol.HealConfig.opening_slot
    exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_two hmPos)
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hprop : S.E.proposer start ∈ rho.honest := by
    simpa only [start] using hcarrier.1
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
  have hPrun : RunBlock S rho P :=
    proposedBlock_runBlock S adm hstartPos hprop
      ((proposal_time_le_confirmation_time S.E start).trans hhor) hP
  have hnames : NamedHonestVotesName S rho start P.erase := by
    intro w hw hwc
    obtain ⟨X, hXhead, -, hXemit⟩ := WeakGoldfish.voterHead_runBlock_and_emits
      S adm.toNamedAdmissibleCore hw hstartPos hwc hvoteHor
    have hX : X.erase = P.erase := hXhead.trans (hheads w hw)
    simpa only [hX] using hXemit
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
  have hgenuine := genuineConfirmationAndPreceq_of_postHealingCone
    S adm hcom hstartPos hpostVote hhor hv hcone hroot hanchor hcandidate
  have hsupport := honestSupport_confVotes_after_gst_of_names
    S adm hcom hstartPos hpostVote hhor hPrun hnames hv hroot hcandidate
  have hvalid : Protocol.VoteSetValid S.E start
      (confLate S.E (confStore S rho v start) start) := by
    simpa only [confStore, tickStore] using
      voteSetValid_confLate_stateBeforeTime S adm.toNamedScheduleWellFormed v
        (Protocol.confirmation_time S.E start) start
  have hpath : ∀ C : Block V,
      Block.Preceq
          (confAnchorWith
            (NamedProfile.gradeContract
              (confirmationInputRead S rho v start).cache)
            S.E S.hc (confStore S rho v start)) C →
      C ≠ confAnchorWith
          (NamedProfile.gradeContract
            (confirmationInputRead S rho v start).cache)
          S.E S.hc (confStore S rho v start) →
      Block.Preceq C P.erase → C ∈ confTree (confStore S rho v start) := by
    have hpath' := confPath_of_candidate S
      (show P.erase ∈ confTree (confStore S rho v start) from by
        simpa only [confStore_eq_confirmationInputRead] using hcandidate)
    simpa only [confAnchorWith, namedConfirmationAnchor,
      confStore_eq_confirmationInputRead] using hpath'
  have hanchor' : Block.Preceq
      (confAnchorWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho v start).cache)
        S.E S.hc (confStore S rho v start)) P.erase := by
    simpa only [confAnchorWith, namedConfirmationAnchor,
      confStore_eq_confirmationInputRead] using hanchor
  obtain ⟨hwalk, -⟩ := confWalkWith_eq_of_support
    (NamedProfile.gradeContract (confirmationInputRead S rho v start).cache)
    S.E S.hc (confStore S rho v start) start rho.honest P.erase
      (by simpa only [confStore_eq_confirmationInputRead, confVotes,
        confirmationVotes] using hsupport) hvalid hanchor' hpath
  have helig : confEligible S.E (confStore S rho v start) start P.erase = true := by
    rw [← hwalk]
    exact hgenuine.1.genuine
  change (Protocol.update_confirmation_with
    (NamedProfile.gradeContract (confirmationInputRead S rho v start).cache)
    S.E S.hc (confStore S rho v start) start).live_confirmed = P.erase
  rw [update_confirmation_with_live_confirmed, hwalk, if_pos helig]

#print axioms honestProposal_confirmationSeedPrepared_live_after_SG_healing_named



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
