module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakProposalHeadNamed
public import DecoupledConsensusProofs.Objects.AdmissibleCore

@[expose] public section

/-!
# Canonical proposal parents in a weak continuation

One processed prior honest head supplies the candidate path. The SG
anchor is compatible, and the honest Goldfish cone supplies the vote
majority. The read bounds and availability are derived by the wrappers.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A bound on every honest duty head also bounds the actual committee cone. -/
theorem protectedVoteSlot_of_coreHeads (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) {d : Slot} (hd : 0 < d)
    (hhor : Protocol.vote_time S.E d ≤ rho.horizon) {B : Block V}
    (hheads : ∀ x ∈ rho.honest, Block.Preceq B (voteDutyHead S rho x d)) :
    ProtectedVoteSlot S rho d B := by
  refine ⟨hheads, ?_⟩
  intro x hx hxc
  obtain ⟨X, hX, hXrun, hXemit⟩ := WeakGoldfish.voterHead_runBlock_and_emits
    S adm hx hd hxc hhor
  exact ⟨X, by simpa only [hX] using hheads x hx, hXrun, hXemit⟩

#print axioms protectedVoteSlot_of_coreHeads


/-
namespace WeakProposal

/-- The local read facts imply the exact proposal-parent bound. -/
theorem protected_preceq_proposedParent_of_readFacts (S: Setup V) {rho: Run V}
    (adm: AdmissibleCore S rho) (hcom: HonestCommittees S rho.honest)
    {d: Slot} (hd: 0 < d) (hpost: S.E.t_GST ≤ Protocol.vote_time S.E d)
    (hhor: Protocol.support_cutoff S.E d ≤ rho.horizon)
    (hprop: S.E.proposer (d + 1) ∈ rho.honest) {B: Block V}
    (hB: ProtectedVoteSlot S rho d B)
    (havailable: HonestHeadsAvailableBefore S rho d (S.E.proposer (d + 1))
      (Protocol.support_cutoff S.E d))
    (hanchor: Block.compatible (healAnchor S.E S.hc
      (proposerDutyStore S rho (d + 1)).toHealing) B = true)
    (hroots: ∀ x ∈ rho.honest, Block.Preceq
      (Protocol.get_fg_root (proposerDutyStore S rho (d + 1)).toHealing.toFG)
      (voteDutyHead S rho x d))
    (hband: ∀ x ∈ rho.honest, (proposerDutyStore S rho (d + 1)).h_max - 1 ≤
      (derived_state S.E S.cfg (voteDutyHead S rho x d)).h):
    Block.Preceq B (proposedParent S rho (d + 1)):= by
  let duty:= proposerDutyStore S rho (d + 1)
  let raw:= (Protocol.proposer_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s).toFinset
  let support:= (Protocol.proposer_support_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s).toFinset
  have hdutySlot: duty.s = d + 1:= by
    simp only [duty, proposerDutyStore, tickStore, slotOf_proposal_time]
  have hcutRead:= support_cutoff_le_proposal_time_succ S.E d
  have hresolve: HeadsResolveIn S rho d duty.T duty.timestamp_block:= by
    simpa only [duty, proposerDutyStore, tickStore] using
      WeakGoldfish.headsResolveIn_storeBeforeTime_of_availableBefore_at S adm hprop d
        hcutRead havailable
  have hcone0:= coneSupport_proposerDutyStore_after_gst
    S adm hcom hd hpost hhor hB.cone hprop hresolve
  have hcone: ConeSupport S.E duty.T raw support raw d rho.honest
      (fun X => Block.Preceq B X):= by
    simpa only [duty, raw, support, hdutySlot] using hcone0
  have hvalid: Protocol.VoteSetValid S.E d raw:= by
    simpa only [duty, raw, hdutySlot, Nat.add_sub_cancel] using
      proposerDutyStore_proposer_view_valid S adm (d + 1)
  have hcpos: 0 < ((S.E.committee d) ∩ rho.honest).card:= by
    have hc:= hcom d
    omega
  obtain ⟨x, hxc⟩:= Finset.card_pos.mp hcpos
  have hx:= (Finset.mem_inter.mp hxc).2
  have hxCommittee:= (Finset.mem_inter.mp hxc).1
  let X:= voteDutyHead S rho x d
  have hvoteHor: Protocol.vote_time S.E d ≤ rho.horizon:= by
    apply le_trans ?_ hhor
    rw [← vote_time_add_delta]
    exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
  have hXhead: HonestHead S rho d X:=
    ⟨x, hx, hxCommittee, WeakGoldfish.voteDutyHead_runBlock S adm hx d,
      WeakGoldfish.seedVoteDutyHead_emits S adm.toScheduleWellFormed hx hd hxCommittee hvoteHor⟩
  have hXT: X ∈ duty.T:= by
    simpa only [duty, proposerDutyStore, tickStore] using
      (WeakGoldfish.relayedWitness_mem_and_stamp S adm.toScheduleWellFormed hcutRead
        (havailable X hXhead)).1
  have hcandidate:= proposalCandidate_of_mem_height_root S adm hXT (hband x hx) (hroots x hx)
  have hpath: ∀ C: Block V, Block.Preceq (healAnchor S.E S.hc duty.toHealing) C →
      C ≠ healAnchor S.E S.hc duty.toHealing → Block.Preceq C B →
      C ∈ Protocol.get_filtered_block_tree duty.toHealing.toFG:= by
    intro C hAC hCne hCB
    exact proposalPath_of_candidate S adm hcandidate C hAC hCne
      (Block.preceq_trans hCB (hB.heads x hx))
  have hhead:= goldfish_fork_choice_captures_supporter_majority
    S.E duty.σ duty.h_max duty.T (Protocol.get_filtered_block_tree duty.toHealing.toFG)
    duty.s raw support d (ConeSupport.sub hcone)
    (supporterMajority_of_cone S.E hcone hvalid) hanchor (fun _ => hpath)
  change Block.Preceq B (Protocol.get_head_in_tree_hc S.E S.hc duty.toHealing
    (Protocol.get_filtered_block_tree duty.toHealing.toFG) raw support (duty.s - 1))
  rw [hdutySlot, Nat.add_sub_cancel]
  exact hhead

end WeakProposal
 -/




/-
namespace Handover

/-- Settled safety keeps each protected block below the next honest proposal parent.
No common local height, grade, or availability premise is required. -/
theorem SettledBootstrap.protected_preceq_proposedParent (S: Setup V) {rho: Run V}
    (adm: AdmissibleCore S rho) (hcom: HonestCommittees S rho.honest)
    {fresh base: Round} {start last d: Slot} {P: Block V} {cap: Height}
    (hboot: SettledBootstrap S rho fresh base start P cap)
    (hawake: ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest S.hc.η_SG r)
    (hfinality: FinalizedRootsBelowAtRead S rho cap P)
    (hhor: Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd: start ≤ d) (hupper: d ≤ last + 1)
    (hpropHor: Protocol.proposal_time S.E (d + 1) ≤ rho.horizon)
    (hprop: S.E.proposer (d + 1) ∈ rho.honest)
    {B: Block V} (hB: ProtectedVoteSlot S rho d B):
    Block.Preceq B (proposedParent S rho (d + 1)):= by
  have hcutpos: 0 < base + S.hc.η_SG:=
    Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt S.hc.η_SG_ge_one) (Nat.le_add_left _ _)
  have hdpos: 0 < d:=
    (Nat.mul_pos hcutpos (lt_of_lt_of_le (by decide: 0 < 2) S.hc.R_ge_two)).trans_le
      (hboot.settled.trans hd)
  have hpost: S.E.t_GST ≤ Protocol.vote_time S.E d:=
    hboot.basePost.trans
      ((Assembly.a_mono S (Nat.le_sub_of_add_le
        (Nat.add_le_add_left S.hc.η_SG_ge_one base))).trans
        (windowSourceTime_le_vote_of_opening_le S hcutpos (hboot.settled.trans hd)))
  have hcut: Protocol.support_cutoff S.E d ≤ rho.horizon:= by
    rw [Protocol.confirmation_time_eq_support_cutoff_succ] at hhor
    exact (support_cutoff_mono S.E hupper).trans hhor
  have htime: Protocol.proposal_time S.E (d + 1) ≤
      Protocol.vote_time S.E (d + 1):= (proposal_time_lt_vote_time S.E (d + 1)).le
  have hread: min (S.a (base + S.hc.η_SG)) (Protocol.vote_time S.E start) ≤
      Protocol.proposal_time S.E (d + 1):=
    (min_le_right _ _).trans ((vote_time_mono_slots S.E hd).trans
      (voteTime_lt_nextProposal S.E d).le)
  apply WeakProposal.protected_preceq_proposedParent_of_readFacts
    S adm hcom hdpos hpost hcut hprop hB
    (SettledBootstrap.honestHeadsAvailableBefore S adm hcom hboot hawake hfinality
      hhor hd hupper hprop)
  · simpa only [healAnchor_eq_get_sg_root, proposerDutyStore, tickStore,
      slotOf_proposal_time] using SettledBootstrap.sgRootAtRead_compatible
        S adm hcom hboot hawake hfinality hhor hd hupper
        (le_refl _) htime hpropHor hB hprop
  · intro x hx
    simpa only [proposerDutyStore, tickStore] using
      SettledBootstrap.fgRootAtRead_at_voteHead
        S adm hcom hboot hawake hfinality hhor hd hupper hread htime hprop hx
  · intro x hx
    simpa only [proposerDutyStore, tickStore] using
      SettledBootstrap.frontierAtRead_le_voteDutyHeadHeight
        S adm hcom hboot hawake hfinality hhor hd hupper htime _ hx

end Handover
 -/
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
