module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.FixedHeightRootAdmission
public import DecoupledConsensusProofs.Objects.SGTargetG1Concentration
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.FixedHeightRootOpeningFrozenVote
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedRootGradePersistence
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGOpeningFrozenSuffix
public import DecoupledConsensusProofs.Objects.GSTZeroProposalEvaluation
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroSelectionSafety
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroConfirmationZero
public import DecoupledConsensusProofs.Protocol.Handlers.HonestProposalAdmission
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Fixed-height opening proposal next activity

The opening proposal is relayed through both following honest proposers before
it is installed in every honest next-round action store. The fixed-height
root facts then place it in the selected filtered tree.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]


/-
/-- Frozen proposal-to-voter comparisons produce the transferred opening
proposal walks without requiring an already assembled lifecycle record. -/
theorem honestProposalWalksTransferred_of_openingFrozenVotes
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    {s: Slot} {A: Block V}
    (hs: 0 < s)
    (hpostProposal: S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hcutHor: Protocol.support_cutoff S.E s ≤ rho.horizon)
    (hvoteHor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hprop: S.E.proposer (s + 1) ∈ rho.honest)
    (hcone: HonestVotesCone S rho s (fun X => Block.Preceq A X))
    (hsourceAnchor:
      Proofs.Optimistic.healAnchor S.E S.hc
          (Protocol.proposerDutyStore S rho (s + 1)).toHealing = A)
    (hpivotParent: Block.Preceq A
      (Protocol.proposedParent S rho (s + 1)))
    (hfrozen: ∀ v ∈ rho.honest, v ∈ S.E.committee (s + 1) →
      SGOpeningFrozenVoteAt S rho s A v):
    HonestProposalWalksTransferred S rho (s + 1):= by
  have hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E s:=
    hpostProposal.trans
      (le_of_lt (Protocol.proposal_time_lt_vote_time S.E s))
  intro v hv hcommittee
  have frozen:= hfrozen v hv hcommittee
  have hpivotFree: Block.Preceq A
      (Protocol.ghost
        (Proofs.Optimistic.healAnchor S.E S.hc
          (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).toHealing)
        (proposalWalkTargetTree S rho (s + 1) v)
        (proposalWalkTargetScore S rho (s + 1) v)
        (proposalWalkTargetEligible S rho (s + 1) v)):= by
    let duty:= Proofs.Optimistic.voteDutyStore S rho v (s + 1)
    let votes:= Protocol.voter_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s
    let support:= Protocol.voter_support_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s
    have hslot: duty.s = s + 1:=
      Proofs.Optimistic.voteDutyStore_slot S rho v (s + 1)
    have hidx: duty.s - 1 = s:= by
      rw [hslot]
      exact Nat.add_sub_cancel s 1
    have hAfrozen: A ∈ Proofs.Optimistic.voter_candidate_tree S.E duty.toHealing:= by
      simpa only [proposalWalkTargetTree, duty] using
        Finset.mem_of_mem_erase frozen.pivotCandidate
    have hAfiltered: A ∈
        Protocol.get_filtered_block_tree duty.toHealing.toFG:=
      frozenVoterCandidateTree_subset_filtered S.E duty.toHealing hAfrozen
    have hroot: Block.Preceq
        (Protocol.get_fg_root duty.toHealing.toFG) A:=
      Proofs.Records.preceq_get_fg_root_of_mem_filtered hAfiltered
    have hresolve:=
      Protocol.headsResolveIn_voteDutyStore_succ_of_postHealingCone
        S adm hv hpostVote hcutHor hroot hcone
    have hbase:= Protocol.coneSupport_voter_view_after_gst
      S adm hcom hs hpostVote hcutHor hcone hv
      (Proofs.Optimistic.support_cutoff_le_vote_time_succ S.E s)
      (gst:= duty.toHealing.toFG.toSG.toGoldfishStore)
      ((Proofs.Optimistic.voteStore_fields S _ (s + 1)).1)
      ((Proofs.Optimistic.voteStore_fields S _ (s + 1)).2.1)
      (Proofs.Optimistic.voteStore_T S _ (s + 1))
      (hresolve.of_eq rfl rfl)
    have hconeDuty: Proofs.Optimistic.ConeSupport S.E duty.T votes support votes
        (duty.s - 1) rho.honest (fun X => Block.Preceq A X):= by
      simpa only [duty, votes, support, hslot, hidx] using hbase
    have hvalid: Protocol.VoteSetValid S.E (duty.s - 1) votes:= by
      simpa only [duty, votes] using
        Proofs.Optimistic.voteDutyStore_voter_view_valid S adm v (s + 1)
    have hhead:= Protocol.goldfish_fork_choice_captures_supporter_majority
      S.E duty.σ duty.h_max duty.T
      (proposalWalkTargetTree S rho (s + 1) v)
      duty.s votes support (duty.s - 1)
      (Proofs.Optimistic.ConeSupport.sub hconeDuty)
      (Protocol.supporterMajority_of_cone S.E hconeDuty hvalid)
      frozen.pivotAnchorCompatible frozen.pivotPath
    simpa only [Protocol.goldfish_fork_choice,
      proposalWalkTargetScore, proposalWalkTargetEligible,
      duty, votes, support] using hhead
  have hscore: ∀ C,
      C ∈ proposalWalkSourceTree S rho (s + 1) →
      C ∈ proposalWalkTargetTree S rho (s + 1) v →
      proposalWalkTargetScore S rho (s + 1) v C =
        proposalWalkSourceScore S rho (s + 1) C:= by
    intro C hCsource hCtarget
    have hproposalFiltered: proposedBlock S rho (s + 1) ∈
        Protocol.get_filtered_block_tree
          (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).toHealing.toFG:=
      frozenVoterCandidateTree_subset_filtered S.E _
        frozen.proposalCandidate
    have hCtargetCandidate: C ∈
        Proofs.Optimistic.voter_candidate_tree S.E
          (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).toHealing:= by
      simpa only [proposalWalkTargetTree] using
        Finset.mem_of_mem_erase hCtarget
    have hCtargetFiltered: C ∈ Protocol.get_filtered_block_tree
        (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).toHealing.toFG:=
      frozenVoterCandidateTree_subset_filtered S.E _ hCtargetCandidate
    have hext:=
      Protocol.candidateScorePreservingViewExtension_proposedBlock_afterGST_of_candidates
        S adm (s:= s + 1) (Nat.succ_pos s)
        (by simpa only [Nat.add_sub_cancel] using hpostProposal)
        hprop hv hvoteHor hproposalFiltered frozen.rawExtra
        (by simpa only [proposalWalkSourceTree] using hCsource)
        hCtargetFiltered
    have hscoreEq:= hext.goldfish_score_eq S.E (s + 1 - 1)
    have hsourceSlot:
        (Protocol.proposerDutyStore S rho (s + 1)).s = s + 1:= by
      simp only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
        Proofs.Optimistic.slotOf_proposal_time]
    have htargetSlot:
        (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).s = s + 1:=
      Proofs.Optimistic.voteDutyStore_slot S rho v (s + 1)
    symm
    simpa only [proposalWalkSourceTree, proposalWalkTargetTree,
      proposalWalkSourceScore, proposalWalkTargetScore,
      Protocol.proposedBlock_gf_votes,
      Protocol.proposedBlock_gf_support_votes,
      hsourceSlot, htargetSlot, Nat.add_sub_cancel] using hscoreEq
  have hsourcePivot: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (Protocol.proposerDutyStore S rho (s + 1)).toHealing) A:= by
    rw [hsourceAnchor]
    exact Block.preceq_self A
  exact Protocol.proposalWalkTransferred_of_frozenCompatiblePivot
    S adm hprop hv frozen.proposalCandidate
      frozen.proposalAnchorCompatible hsourcePivot hpivotParent
      hpivotFree frozen.suffix hscore


/-- A standalone, non-circular conversion from transferred proposal walks to
the exact honest vote name needed by the lifecycle record. -/
theorem honestVotesName_of_honestProposalWalksTransferred
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} (hs: 0 < s)
    (hvoteHor: Protocol.vote_time S.E s ≤ rho.horizon)
    (htrans: HonestProposalWalksTransferred S rho s):
    HonestVotesName S rho s (proposedBlock S rho s):= by
  have hstores: VoteStoresExtend S rho s (proposedBlock S rho s):=
    Protocol.voteStoresExtend_of_transferred S adm htrans
  exact Protocol.honestVotesName_of_voteStoresExtend
    S adm hs hvoteHor hstores


/-- Under the fixed no-rise cap, the opening proposal is admitted through both
following honest proposers and belongs to every honest next-action filtered
tree. If the cap does not hold, the result exposes the public Claim-1 endpoint
height rise. -/
theorem fixedHeightJustificationRoot_openingProposal_nextActive_or_hMaxRise
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {H: Height} {w: V} {read: Time}
    (hfix: FixedHeightJustificationRootAtRead S rho H w read)
    {r gap q: Round}
    (hpost: S.E.t_GST ≤ read)
    (hreadAction: read ≤ S.a r)
    (hqlo: r + 3 ≤ q)
    (hqhi: q ≤ r + 3 + gap)
    (hcarrier: ProposerCarrierAt S rho q)
    (hnames: HonestVotesName S rho (S.hc.opening_slot q)
      (proposedBlock S rho (S.hc.opening_slot q)))
    (hJB: Block.Preceq (rho.storeBeforeTime S w read).J
      (proposedBlock S rho (S.hc.opening_slot q)))
    (hendHor: S.a (r + 4 + gap) ≤ rho.horizon):
    H < honestHMaxAt S rho (S.a (r + 4 + gap)) ∨
      ∀ v ∈ rho.honest,
        proposedBlock S rho (S.hc.opening_slot q) ∈
          Protocol.get_filtered_block_tree
            (healStoreAt S rho v (q + 1)).toFG:= by
  let s0: Slot:= S.hc.opening_slot q
  let s1: Slot:= s0 + 1
  let s2: Slot:= s1 + 1
  let B: Block V:= proposedBlock S rho s0
  let J: Block V:= (rho.storeBeforeTime S w read).J
  have hrq: r < q:= by
    exact (Nat.lt_succ_self r).trans_le
      ((Nat.add_le_add_left (by decide: 1 ≤ 3) r).trans hqlo)
  have hqpos: 0 < q:= (Nat.zero_le r).trans_lt hrq
  have hqEnd: q + 1 ≤ r + 4 + gap:= by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_le_add_right hqhi 1
  have hs0pos: 0 < s0:= by
    unfold s0 Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hqpos
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hs01: s0 ≤ s1:= by
    simpa only [s1] using Nat.le_succ s0
  have hs12: s1 ≤ s2:= by
    simpa only [s2] using Nat.le_succ s1
  have hs02: s0 ≤ s2:= hs01.trans hs12
  have hs2Next: s2 ≤ S.hc.opening_slot (q + 1):= by
    have hslots: S.hc.opening_slot q + 2 ≤
        S.hc.opening_slot (q + 1):= by
      rw [opening_slot_succ_eq]
      exact Nat.add_le_add_left S.hc.R_ge_two _
    simpa only [s2, s1, s0, Nat.add_assoc] using hslots
  have hs1Next: s1 ≤ S.hc.opening_slot (q + 1):= hs12.trans hs2Next
  have hs0Next: s0 ≤ S.hc.opening_slot (q + 1):= hs02.trans hs2Next
  have hproposalOpenNextAction:
      Protocol.proposal_time S.E (S.hc.opening_slot (q + 1)) ≤
        S.a (q + 1):= by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact Protocol.proposal_time_le_confirmation_time S.E _
  have hsupportOpenNextAction:
      Protocol.support_cutoff S.E (S.hc.opening_slot (q + 1)) ≤
        S.a (q + 1):= by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact Protocol.support_cutoff_le_confirmation_time S.E _
  have hproposal0Action: Protocol.proposal_time S.E s0 ≤ S.a (q + 1):=
    (Protocol.proposal_time_mono S.E hs0Next).trans
      hproposalOpenNextAction
  have hproposal1Action: Protocol.proposal_time S.E s1 ≤ S.a (q + 1):=
    (Protocol.proposal_time_mono S.E hs1Next).trans
      hproposalOpenNextAction
  have hproposal2Action: Protocol.proposal_time S.E s2 ≤ S.a (q + 1):=
    (Protocol.proposal_time_mono S.E hs2Next).trans
      hproposalOpenNextAction
  have hsupport2Action: Protocol.support_cutoff S.E s2 ≤ S.a (q + 1):=
    (Proofs.Optimistic.support_cutoff_mono S.E hs2Next).trans
      hsupportOpenNextAction
  have hactionNextEnd: S.a (q + 1) ≤ S.a (r + 4 + gap):=
    Assembly.a_mono S hqEnd
  have hnextHor: S.a (q + 1) ≤ rho.horizon:=
    hactionNextEnd.trans hendHor
  have hproposal0Hor: Protocol.proposal_time S.E s0 ≤ rho.horizon:=
    hproposal0Action.trans hnextHor
  have hproposal1Hor: Protocol.proposal_time S.E s1 ≤ rho.horizon:=
    hproposal1Action.trans hnextHor
  have hproposal2Hor: Protocol.proposal_time S.E s2 ≤ rho.horizon:=
    hproposal2Action.trans hnextHor
  have hsupport01: Protocol.support_cutoff S.E s0 ≤
      Protocol.proposal_time S.E s1:= by
    simpa only [s1] using
      Protocol.support_cutoff_le_proposal_time_succ S.E s0
  have hsupport12: Protocol.support_cutoff S.E s1 ≤
      Protocol.proposal_time S.E s2:= by
    simpa only [s2] using
      Protocol.support_cutoff_le_proposal_time_succ S.E s1
  have hsupport0Hor: Protocol.support_cutoff S.E s0 ≤ rho.horizon:=
    hsupport01.trans hproposal1Hor
  have hsupport1Hor: Protocol.support_cutoff S.E s1 ≤ rho.horizon:=
    hsupport12.trans hproposal2Hor
  have hsupport2Hor: Protocol.support_cutoff S.E s2 ≤ rho.horizon:=
    hsupport2Action.trans hnextHor
  have hactionDelay: S.a r + S.E.Δ ≤ Protocol.proposal_time S.E s0:= by
    simpa only [s0] using
      (Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S hrq)
  have hreadDelay0: read + S.E.Δ ≤ Protocol.proposal_time S.E s0:=
    (Int.add_le_add_right hreadAction S.E.Δ).trans hactionDelay
  have hreadDelay1: read + S.E.Δ ≤ Protocol.proposal_time S.E s1:=
    hreadDelay0.trans (Protocol.proposal_time_mono S.E hs01)
  have hreadDelay2: read + S.E.Δ ≤ Protocol.proposal_time S.E s2:=
    hreadDelay0.trans (Protocol.proposal_time_mono S.E hs02)
  have hreadDelayNext: read + S.E.Δ ≤ S.a (q + 1):=
    hreadDelay0.trans hproposal0Action
  have hpostProposal0: S.E.t_GST ≤ Protocol.proposal_time S.E s0:=
    (hpost.trans (Int.le_add_of_nonneg_right
      (le_of_lt S.E.Δ_pos))).trans hreadDelay0
  have hpostVote0: S.E.t_GST ≤ Protocol.vote_time S.E s0:=
    hpostProposal0.trans
      (le_of_lt (Protocol.proposal_time_lt_vote_time S.E s0))
  have hpostVote1: S.E.t_GST ≤ Protocol.vote_time S.E s1:=
    hpostVote0.trans (Protocol.vote_time_mono_slots S.E hs01)
  have hpostVote2: S.E.t_GST ≤ Protocol.vote_time S.E s2:=
    hpostVote1.trans (Protocol.vote_time_mono_slots S.E hs12)
  have hprop0: S.E.proposer s0 ∈ rho.honest:= by
    simpa only [s0] using hcarrier.1
  have hprop1: S.E.proposer s1 ∈ rho.honest:= by
    simpa only [s1, s0] using hcarrier.2.1
  have hprop2: S.E.proposer s2 ∈ rho.honest:= by
    simpa only [s2, s1, s0, Nat.add_assoc] using hcarrier.2.2
  have hBpos: 0 < B.slot:= by
    simpa only [B, Protocol.proposedBlock_slot] using hs0pos
  have hBneGenesis: B ≠ Block.genesis:= by
    intro hgen
    have hzero: B.slot = 0:= by rw [hgen]; rfl
    exact (Nat.ne_of_gt hBpos) hzero
  have hBrun: RunBlock S rho B:=
    Protocol.proposedBlock_runBlock S adm hs0pos hprop0 hproposal0Hor
  have hnames': HonestVotesName S rho s0 B:= by
    simpa only [s0, B] using hnames
  have hcone: HonestVotesCone S rho s0
      (fun X => Block.Preceq B X):=
    Proofs.Optimistic.honestVotesCone_preceq S rho s0 hBrun hnames'
  have hJB': Block.Preceq J B:= by
    simpa only [J, B] using hJB
  have hHone: 1 ≤ H:=
    Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hfix.targetHeightPositive)
  have htargetHeightSucc:
      (derived_state S.E S.cfg J).h + 1 = H:= by
    rw [show (derived_state S.E S.cfg J).h = H - 1 by
      simpa only [J] using hfix.targetDerivedHeight]
    exact Nat.sub_add_cancel hHone
  by_cases hrise: H < honestHMaxAt S rho (S.a (r + 4 + gap))
  · exact Or.inl hrise
  right
  have hcapEnd: honestHMaxAt S rho (S.a (r + 4 + gap)) ≤ H:=
    Nat.le_of_not_gt hrise
  have hcap1: honestHMaxAt S rho
      (Protocol.proposal_time S.E s1) ≤ H:=
    (honestHMaxAt_mono S adm.toScheduleWellFormed
      (hproposal1Action.trans hactionNextEnd)).trans hcapEnd
  have hcap2: honestHMaxAt S rho
      (Protocol.proposal_time S.E s2) ≤ H:=
    (honestHMaxAt_mono S adm.toScheduleWellFormed
      (hproposal2Action.trans hactionNextEnd)).trans hcapEnd
  have hcapNext: honestHMaxAt S rho (S.a (q + 1)) ≤ H:=
    (honestHMaxAt_mono S adm.toScheduleWellFormed hactionNextEnd).trans hcapEnd
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  obtain ⟨hroot1, _hmax1⟩:=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hprop1 hpost hreadDelay1 hproposal1Hor hcap1
  obtain ⟨hroot2, _hmax2⟩:=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hprop2 hpost hreadDelay2 hproposal2Hor hcap2
  have hroot1B: Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S (S.E.proposer s1)
          (Protocol.proposal_time S.E s1)).toHealing.toFG) B:= by
    rw [hroot1]
    exact hJB'
  have hroot2B: Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S (S.E.proposer s2)
          (Protocol.proposal_time S.E s2)).toHealing.toFG) B:= by
    rw [hroot2]
    exact hJB'
  obtain ⟨x, hx, hxcommittee⟩:=
    Protocol.HonestWeightMajority.exists_honest_committee_member hcom s0
  have hBhead: HonestHead S rho s0 B:=
    ⟨x, hx, hxcommittee, hBrun, hnames' x hx hxcommittee⟩
  have havailable1: HonestHeadsAvailableBefore S rho s0
      (S.E.proposer s1) (Protocol.support_cutoff S.E s0):=
    Protocol.honestHeadsAvailableBefore_of_postHealingCone_at
      S adm hprop1 hpostVote0 hsupport0Hor hsupport01 hroot1B hcone
  have hadmit1: AdmittedBefore S rho (S.E.proposer s1) B
      (Protocol.support_cutoff S.E s0):= by
    rcases havailable1 B hBhead with hgen | hadmit
    · exact False.elim (hBneGenesis hgen)
    · exact hadmit
  obtain ⟨i1, t1, hacc1, ht1⟩:= hadmit1
  have ht1In: t1 < Protocol.vote_time S.E s1:=
    ht1.trans_le (by
      simpa only [s1] using
        Proofs.Optimistic.support_cutoff_le_vote_time_succ S.E s0)
  have hFhist2 : BlockFinalizedBelowAtDeliveriesBefore
      S rho (S.E.proposer s2) B (Protocol.support_cutoff S.E s1) := by
    intro i hi
    exact finalized_preceq_at_prefix_of_storeBeforeRoot_preceq S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted hroot2B
      (hi.trans (strict_filter_length_mono rho hsupport12))
  have hadmit2 : AdmittedBefore S rho (S.E.proposer s2) B
      (Protocol.support_cutoff S.E s1) :=
    Protocol.block_admittedBefore_of_accepted_after_cutoff
      S adm hprop1 hprop2 hBpos hacc1 ht1In hpostVote1
        (Proofs.Optimistic.vote_time_add_delta S.E s1) hsupport1Hor hFhist2
  obtain ⟨i2, t2, hacc2, ht2⟩:= hadmit2
  have ht2In: t2 < Protocol.vote_time S.E s2:=
    ht2.trans_le (by
      simpa only [s2] using
        Proofs.Optimistic.support_cutoff_le_vote_time_succ S.E s1)
  intro v hv
  obtain ⟨hrootFinal, hmaxFinal⟩:=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hv hpost hreadDelayNext hnextHor hcapNext
  have hrootFinalB: Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v (S.a (q + 1))).toHealing.toFG) B:= by
    rw [hrootFinal]
    exact hJB'
  have hFhistFinal : BlockFinalizedBelowAtDeliveriesBefore
      S rho v B (Protocol.support_cutoff S.E s2) := by
    intro i hi
    exact finalized_preceq_at_prefix_of_storeBeforeRoot_preceq S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted hrootFinalB
      (hi.trans (strict_filter_length_mono rho hsupport2Action))
  have hadmitFinal : AdmittedBefore S rho v B
      (Protocol.support_cutoff S.E s2) :=
    Protocol.block_admittedBefore_of_accepted_after_cutoff
      S adm hprop2 hv hBpos hacc2 ht2In hpostVote2
        (Proofs.Optimistic.vote_time_add_delta S.E s2) hsupport2Hor hFhistFinal
  have hBmem: B ∈ (rho.storeBeforeTime S v (S.a (q + 1))).T:=
    (Protocol.admittedBefore_mem_and_stamp_at S
      adm.toScheduleWellFormed hadmitFinal hsupport2Action).1
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v)
      (rho.storeBeforeTime S v (S.a (q + 1))):=
    Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
      adm.toDeliveryWellFormed (S.a (q + 1)) v
  have hheightCap: (rho.storeBeforeTime S v (S.a (q + 1))).h_max ≤
      (derived_state S.E S.cfg J).h + 1:= by
    rw [hmaxFinal, htargetHeightSucc]
  have hfiltered:= mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
    S.E S.hc S.cfg (S.node v) hdep hBmem hrootFinal hJB' hheightCap
  simpa only [healStoreAt, B] using hfiltered

/-- Compatibility corollary for the original strict-read interference record. -/
theorem fixedHeightRoot_openingProposal_nextActive_or_hMaxRise
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {H: Height} {w: V} {read: Time} {P: Block V}
    (hfix: FixedHeightRootInterferenceAtRead S rho H w read P)
    {r gap q: Round}
    (hpost: S.E.t_GST ≤ read)
    (hreadAction: read ≤ S.a r)
    (hqlo: r + 3 ≤ q)
    (hqhi: q ≤ r + 3 + gap)
    (hcarrier: ProposerCarrierAt S rho q)
    (hnames: HonestVotesName S rho (S.hc.opening_slot q)
      (proposedBlock S rho (S.hc.opening_slot q)))
    (hJB: Block.Preceq (rho.storeBeforeTime S w read).J
      (proposedBlock S rho (S.hc.opening_slot q)))
    (hendHor: S.a (r + 4 + gap) ≤ rho.horizon):
    H < honestHMaxAt S rho (S.a (r + 4 + gap)) ∨
      ∀ v ∈ rho.honest,
        proposedBlock S rho (S.hc.opening_slot q) ∈
          Protocol.get_filtered_block_tree
            (healStoreAt S rho v (q + 1)).toFG:=
  fixedHeightJustificationRoot_openingProposal_nextActive_or_hMaxRise
    S adm hcom hfb hfix.toJustificationRootAtRead hpost hreadAction hqlo hqhi
      hcarrier hnames hJB hendHor


end HealingSurface
end Proofs
end DecoupledConsensusModel
 -/

/-- A named vote-store extension gives the named honest vote names. -/
theorem namedHonestVotesName_of_namedVoteStoresExtend
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon)
    {P : NamedBlock V}
    (hstores : Protocol.VoteStoresExtend S rho s P) :
    NamedHonestVotesName S rho s P.erase :=
  Protocol.honestVotesName_of_voteStoresExtend S adm hs hvoteHor hstores

private theorem fixedHeight_supportCutoff_opening_add_two_le_nextGammaNeg1
    (S : Setup V) (q : Round) :
    Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) ≤
      S.hc.Γ_neg1 S.E.Δ (q + 1) := by
  rw [show Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) =
      (4 * (((S.hc.opening_slot q + 2 : Slot) : Time)) + 2) * S.E.Δ by
        unfold Protocol.support_cutoff Env.t slotStart
        ring,
    show S.hc.Γ_neg1 S.E.Δ (q + 1) =
      (4 * ((S.hc.opening_slot (q + 1) : Slot) : Time) - 1) * S.E.Δ by
        unfold Protocol.HealConfig.Γ_neg1 slotStart
        ring]
  refine Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt S.E.Δ_pos)
  simp only [Protocol.HealConfig.opening_slot]
  push_cast
  have hR : (3 : Int) ≤ S.hc.R := by exact_mod_cast S.hc.R_ge_three
  ring_nf
  omega

/-- A named fixed-root opening proposal is active at both reads needed by the
successor-grade handoff, unless the public frontier has already risen. -/
theorem fixedHeightJustificationRoot_namedOpeningProposal_nextActive_or_hMaxRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {r gap q : Round}
    (hpost : S.E.t_GST ≤ read)
    (hreadAction : read ≤ S.a r)
    (hqlo : r + 3 ≤ q)
    (hqhi : q ≤ r + 3 + gap)
    (hcarrier : ProposerCarrierAt S rho q)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hJP : Block.Preceq (rho.storeBeforeTime S w read).J P.erase)
    (hendHor : S.a (r + 4 + gap) ≤ rho.horizon) :
    H < honestHMaxAt S rho (S.a (r + 4 + gap)) ∨
      (∀ v ∈ rho.honest,
        P.erase ∈ Protocol.get_filtered_block_tree
          (healStoreAt S rho v (q + 1)).toFG) ∧
      (∀ v ∈ rho.honest,
        P.erase ∈ PhaseGrades.filteredTree
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g2) v)) := by
  let s0 : Slot := S.hc.opening_slot q
  let s1 : Slot := s0 + 1
  let s2 : Slot := s1 + 1
  have hrq : r < q :=
    (Nat.lt_succ_self r).trans_le
      ((Nat.add_le_add_left (by decide : 1 ≤ 3) r).trans hqlo)
  have hqpos : 0 < q := (Nat.zero_le r).trans_lt hrq
  have hqEnd : q + 1 ≤ r + 4 + gap := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_le_add_right hqhi 1
  have hs0pos : 0 < s0 := by
    unfold s0 Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hqpos
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hs01 : s0 ≤ s1 := by simpa only [s1] using Nat.le_succ s0
  have hs12 : s1 ≤ s2 := by simpa only [s2] using Nat.le_succ s1
  have hs02 : s0 ≤ s2 := hs01.trans hs12
  have hs2Next : s2 ≤ S.hc.opening_slot (q + 1) := by
    have hslots : S.hc.opening_slot q + 2 ≤
        S.hc.opening_slot (q + 1) := by
      rw [opening_slot_succ_eq]
      exact Nat.add_le_add_left S.hc.R_ge_two _
    simpa only [s2, s1, s0, Nat.add_assoc] using hslots
  have hs1Next : s1 ≤ S.hc.opening_slot (q + 1) := hs12.trans hs2Next
  have hs0Next : s0 ≤ S.hc.opening_slot (q + 1) := hs02.trans hs2Next
  have hproposalOpenNextAction :
      Protocol.proposal_time S.E (S.hc.opening_slot (q + 1)) ≤
        S.a (q + 1) := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact Protocol.proposal_time_le_confirmation_time S.E _
  have hsupportOpenNextAction :
      Protocol.support_cutoff S.E (S.hc.opening_slot (q + 1)) ≤
        S.a (q + 1) := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact Protocol.support_cutoff_le_confirmation_time S.E _
  have hproposal0Action : Protocol.proposal_time S.E s0 ≤ S.a (q + 1) :=
    (Protocol.proposal_time_mono S.E hs0Next).trans hproposalOpenNextAction
  have hproposal1Action : Protocol.proposal_time S.E s1 ≤ S.a (q + 1) :=
    (Protocol.proposal_time_mono S.E hs1Next).trans hproposalOpenNextAction
  have hproposal2Action : Protocol.proposal_time S.E s2 ≤ S.a (q + 1) :=
    (Protocol.proposal_time_mono S.E hs2Next).trans hproposalOpenNextAction
  have hsupport2Action : Protocol.support_cutoff S.E s2 ≤ S.a (q + 1) :=
    (Proofs.Optimistic.support_cutoff_mono S.E hs2Next).trans hsupportOpenNextAction
  have hactionNextEnd : S.a (q + 1) ≤ S.a (r + 4 + gap) :=
    Assembly.a_mono S hqEnd
  have hnextHor : S.a (q + 1) ≤ rho.horizon := hactionNextEnd.trans hendHor
  have hproposal0Hor : Protocol.proposal_time S.E s0 ≤ rho.horizon :=
    hproposal0Action.trans hnextHor
  have hproposal1Hor : Protocol.proposal_time S.E s1 ≤ rho.horizon :=
    hproposal1Action.trans hnextHor
  have hproposal2Hor : Protocol.proposal_time S.E s2 ≤ rho.horizon :=
    hproposal2Action.trans hnextHor
  have hsupport01 : Protocol.support_cutoff S.E s0 ≤
      Protocol.proposal_time S.E s1 := by
    simpa only [s1] using
      Protocol.support_cutoff_le_proposal_time_succ S.E s0
  have hsupport12 : Protocol.support_cutoff S.E s1 ≤
      Protocol.proposal_time S.E s2 := by
    simpa only [s2] using
      Protocol.support_cutoff_le_proposal_time_succ S.E s1
  have hsupport0Hor : Protocol.support_cutoff S.E s0 ≤ rho.horizon :=
    hsupport01.trans hproposal1Hor
  have hsupport1Hor : Protocol.support_cutoff S.E s1 ≤ rho.horizon :=
    hsupport12.trans hproposal2Hor
  have hsupport2Hor : Protocol.support_cutoff S.E s2 ≤ rho.horizon :=
    hsupport2Action.trans hnextHor
  have hactionDelay : S.a r + S.E.Δ ≤ Protocol.proposal_time S.E s0 := by
    simpa only [s0] using
      (Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S hrq)
  have hreadDelay0 : read + S.E.Δ ≤ Protocol.proposal_time S.E s0 :=
    (Int.add_le_add_right hreadAction S.E.Δ).trans hactionDelay
  have hreadDelay1 : read + S.E.Δ ≤ Protocol.proposal_time S.E s1 :=
    hreadDelay0.trans (Protocol.proposal_time_mono S.E hs01)
  have hreadDelay2 : read + S.E.Δ ≤ Protocol.proposal_time S.E s2 :=
    hreadDelay0.trans (Protocol.proposal_time_mono S.E hs02)
  have hreadDelayNext : read + S.E.Δ ≤ S.a (q + 1) :=
    hreadDelay0.trans hproposal0Action
  have hpostProposal0 : S.E.t_GST ≤ Protocol.proposal_time S.E s0 :=
    (hpost.trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))).trans
      hreadDelay0
  have hpostVote0 : S.E.t_GST ≤ Protocol.vote_time S.E s0 :=
    hpostProposal0.trans
      (le_of_lt (Protocol.proposal_time_lt_vote_time S.E s0))
  have hpostVote1 : S.E.t_GST ≤ Protocol.vote_time S.E s1 :=
    hpostVote0.trans (Protocol.vote_time_mono_slots S.E hs01)
  have hpostVote2 : S.E.t_GST ≤ Protocol.vote_time S.E s2 :=
    hpostVote1.trans (Protocol.vote_time_mono_slots S.E hs12)
  have hprop0 : S.E.proposer s0 ∈ rho.honest := by
    simpa only [s0] using hcarrier.1
  have hprop1 : S.E.proposer s1 ∈ rho.honest := by
    simpa only [s1, s0] using hcarrier.2.1
  have hprop2 : S.E.proposer s2 ∈ rho.honest := by
    simpa only [s2, s1, s0, Nat.add_assoc] using hcarrier.2.2
  have hPslot : 0 < P.slot := by
    rw [proposedBlockAt_slot S rho (S.hc.opening_slot q) hP]
    simpa only [s0] using hs0pos
  have hPrun : RunBlock S rho P :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot q) (by simpa only [s0] using hs0pos)
      (by simpa only [s0] using hprop0)
      (by simpa only [s0] using hproposal0Hor) hP
  obtain ⟨Jn, hJnErase, hJnRun, hJnHeight⟩ :=
    fixedRoot_namedTarget_of_fixedRoot S hfix
  obtain ⟨Jp, hJpP, hJpErase⟩ := Proofs.NamedAncestry.erased_ancestor_lift P hJP
  have hJpRun : RunBlock S rho Jp :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hPrun hJpP
  have hJpEq : Jp = Jn := by
    apply adm.toNamedRootCollisionFree.root_injective Jp Jn hJpRun hJnRun Jp Jn
      (Or.inl (Proofs.NamedAncestry.named_self Jp))
      (Or.inr (Proofs.NamedAncestry.named_self Jn))
    rw [← Proofs.NamedWire.erase_root Jp, ← Proofs.NamedWire.erase_root Jn,
      hJpErase, hJnErase]
  have hPheight : H - 1 ≤ (Protocol.derive_named S.E S.cfg P).h := by
    rw [← hJnHeight, ← hJpEq]
    exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hJpP
  by_cases hrise : H < honestHMaxAt S rho (S.a (r + 4 + gap))
  · exact Or.inl hrise
  right
  have hcapEnd : honestHMaxAt S rho (S.a (r + 4 + gap)) ≤ H :=
    Nat.le_of_not_gt hrise
  have hcap1 : honestHMaxAt S rho (Protocol.proposal_time S.E s1) ≤ H :=
    (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
      (hproposal1Action.trans hactionNextEnd)).trans hcapEnd
  have hcap2 : honestHMaxAt S rho (Protocol.proposal_time S.E s2) ≤ H :=
    (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
      (hproposal2Action.trans hactionNextEnd)).trans hcapEnd
  have hcapNext : honestHMaxAt S rho (S.a (q + 1)) ≤ H :=
    (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hactionNextEnd).trans hcapEnd
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  obtain ⟨hroot1, -⟩ :=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hprop1 hpost hreadDelay1 hproposal1Hor hcap1
  obtain ⟨hroot2, -⟩ :=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hprop2 hpost hreadDelay2 hproposal2Hor hcap2
  have hroot1P : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S (S.E.proposer s1)
          (Protocol.proposal_time S.E s1)).toHealing.toFG) P.erase := by
    rw [hroot1]
    exact hJP
  have hroot2P : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S (S.E.proposer s2)
          (Protocol.proposal_time S.E s2)).toHealing.toFG) P.erase := by
    rw [hroot2]
    exact hJP
  obtain ⟨i0, hacc0⟩ := Protocol.acceptsAt_proposedBlock S adm
    (by simpa only [s0] using hs0pos) (by simpa only [s0] using hprop0)
      (by simpa only [s0] using hproposal0Hor) hP
  have hFhist1 : BlockFinalizedBelowAtDeliveriesBefore S rho
      (S.E.proposer s1) P (Protocol.support_cutoff S.E s0) := by
    intro i hi
    exact finalized_preceq_at_prefix_of_storeBeforeRoot_preceq S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted hroot1P
      (hi.trans (strict_filter_length_mono rho hsupport01))
  have hadmit1 : AdmittedBefore S rho (S.E.proposer s1) P.erase
      (Protocol.support_cutoff S.E s0) :=
    Protocol.block_admittedBefore_of_accepted_after_cutoff
      S adm hprop0 hprop1 hPslot hacc0
        (Protocol.proposal_time_lt_vote_time S.E s0) hpostVote0
        (Proofs.Optimistic.vote_time_add_delta S.E s0) hsupport0Hor hFhist1
  obtain ⟨P1, hP1erase, i1, t1, hacc1, ht1⟩ := hadmit1
  have hP1slot : 0 < P1.slot := by
    rw [← Proofs.NamedWire.erase_slot P1, hP1erase, Proofs.NamedWire.erase_slot P]
    exact hPslot
  have ht1In : t1 < Protocol.vote_time S.E s1 :=
    ht1.trans_le (by simpa only [s1] using
      Proofs.Optimistic.support_cutoff_le_vote_time_succ S.E s0)
  have hFhist2 : BlockFinalizedBelowAtDeliveriesBefore S rho
      (S.E.proposer s2) P1 (Protocol.support_cutoff S.E s1) := by
    intro i hi
    have hroot2P1 : Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S (S.E.proposer s2)
            (Protocol.proposal_time S.E s2)).toHealing.toFG) P1.erase := by
      simpa only [hP1erase] using hroot2P
    exact finalized_preceq_at_prefix_of_storeBeforeRoot_preceq S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted hroot2P1
      (hi.trans (strict_filter_length_mono rho hsupport12))
  have hadmit2 : AdmittedBefore S rho (S.E.proposer s2) P1.erase
      (Protocol.support_cutoff S.E s1) :=
    Protocol.block_admittedBefore_of_accepted_after_cutoff
      S adm hprop1 hprop2 hP1slot hacc1 ht1In hpostVote1
        (Proofs.Optimistic.vote_time_add_delta S.E s1) hsupport1Hor hFhist2
  obtain ⟨P2, hP2erase, i2, t2, hacc2, ht2⟩ := hadmit2
  have hP2slot : 0 < P2.slot := by
    rw [← Proofs.NamedWire.erase_slot P2, hP2erase, hP1erase,
      Proofs.NamedWire.erase_slot P]
    exact hPslot
  have ht2In : t2 < Protocol.vote_time S.E s2 :=
    ht2.trans_le (by simpa only [s2] using
      Proofs.Optimistic.support_cutoff_le_vote_time_succ S.E s1)
  have hfilteredAt : ∀ (target : Time), read + S.E.Δ ≤ target →
      Protocol.support_cutoff S.E s2 ≤ target → target ≤ rho.horizon →
      honestHMaxAt S rho target ≤ H → ∀ v ∈ rho.honest,
        P.erase ∈ Protocol.get_filtered_block_tree
          (rho.storeBeforeTime S v target).toHealing.toFG := by
    intro target hdelay hsupport htargetHor hcap v hv
    obtain ⟨hroot, hmax⟩ :=
      fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
        S adm hsb hfix hv hpost hdelay htargetHor hcap
    have hrootP : Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S v target).toHealing.toFG) P.erase := by
      rw [hroot]
      exact hJP
    have hFhist : BlockFinalizedBelowAtDeliveriesBefore S rho v P2
        (Protocol.support_cutoff S.E s2) := by
      intro i hi
      have hrootP2 : Block.Preceq
          (Protocol.get_fg_root
            (rho.storeBeforeTime S v target).toHealing.toFG) P2.erase := by
        simpa only [hP2erase, hP1erase] using hrootP
      exact finalized_preceq_at_prefix_of_storeBeforeRoot_preceq S rho
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted hrootP2
        (hi.trans (strict_filter_length_mono rho hsupport))
    have hadmitRaw : AdmittedBefore S rho v P2.erase
        (Protocol.support_cutoff S.E s2) :=
      Protocol.block_admittedBefore_of_accepted_after_cutoff
        S adm hprop2 hv hP2slot hacc2 ht2In hpostVote2
          (Proofs.Optimistic.vote_time_add_delta S.E s2) hsupport2Hor hFhist
    have hadmit : AdmittedBefore S rho v P.erase
        (Protocol.support_cutoff S.E s2) := by
      simpa only [hP2erase, hP1erase] using hadmitRaw
    have hprocessed : P.erase ∈ (rho.storeBeforeTime S v target).core.T :=
      (Protocol.admittedBefore_mem_and_stamp_at S
        adm.toNamedScheduleWellFormed hadmit hsupport).1
    exact fixedRootGrade_mem_filtered_of_exactRoot S adm hv hPrun hprocessed
      hJP hPheight hroot hmax
  refine ⟨?_, ?_⟩
  · intro v hv
    simpa only [healStoreAt] using
      hfilteredAt (S.a (q + 1)) hreadDelayNext hsupport2Action hnextHor
        hcapNext v hv
  · let target := DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g2
    have htargetAction : target ≤ S.a (q + 1) :=
      FrameForward.domain_le_a S (q + 1) .g2
    have htargetHor : target ≤ rho.horizon := htargetAction.trans hnextHor
    have hsupportTarget : Protocol.support_cutoff S.E s2 ≤ target := by
      rw [show target = S.hc.Γ_neg1 S.E.Δ (q + 1) by
        simpa only [target] using (gammaNeg1_eq_domain_g2_succ S q).symm]
      simpa only [s2, s1, s0, Nat.add_assoc] using
        fixedHeight_supportCutoff_opening_add_two_le_nextGammaNeg1 S q
    have hdelayTarget : read + S.E.Δ ≤ target :=
      hreadDelay0.trans ((Protocol.proposal_time_mono S.E hs02).trans
        ((le_of_lt (Protocol.proposal_time_lt_vote_time S.E s2)).trans
          ((Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
            ((Proofs.Optimistic.vote_time_add_delta S.E s2).le.trans hsupportTarget))))
    have hcapTarget : honestHMaxAt S rho target ≤ H :=
      (honestHMaxAt_mono S adm.toNamedScheduleWellFormed htargetAction).trans hcapNext
    intro v hv
    simpa only [PhaseGrades.filteredTree, PhaseGrades.readAt, target,
      Run.storeBeforeTime] using
      hfilteredAt target hdelayTarget hsupportTarget htargetHor hcapTarget v hv

#print axioms namedHonestVotesName_of_namedVoteStoresExtend
#print axioms fixedHeightJustificationRoot_namedOpeningProposal_nextActive_or_hMaxRise

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
