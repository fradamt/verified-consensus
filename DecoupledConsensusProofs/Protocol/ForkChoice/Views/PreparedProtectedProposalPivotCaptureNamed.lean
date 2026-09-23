module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PreparedProtectedProposalPivot
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.GoldfishCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakBootstrapJoin

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Prepared protected proposal-pivot capture

The prior protected vote cone gives majority support for the prepared pivot.
Its reader-local named height band puts the pivot and its strict anchor path in
the frozen candidate tree, so the proposal-free target walk reaches it.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.NamedRecoveryRead Protocol Proofs.Optimistic
  HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An available honest head is in the next prepared vote's frozen processed
tree. -/
private theorem namedHonestHead_voterProcessed_of_available_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {d : Slot} {v : V} {H : Block V}
    (havailable : ∀ X : Block V, HonestHead S rho d X →
      X = Block.genesis ∨ AdmittedBefore S rho v X
        (Protocol.support_cutoff S.E d))
    (hH : HonestHead S rho d H) :
    H ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho v (d + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho v (d + 1)).toHealing.s := by
  let duty := Proofs.Optimistic.voteDutyStore S rho v (d + 1)
  have hslot : duty.toHealing.s = d + 1 := by
    simpa only [duty, Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho v (d + 1)
  rcases havailable H hH with hgen | hadmit
  · subst H
    have hvisible := Protocol.genesis_mem_and_stamp_storeBeforeTime S
      adm.toNamedScheduleWellFormed v (Protocol.vote_time S.E (d + 1))
        (Protocol.view_freeze S.E d)
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisible.1,
      Or.inl (by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisible.2)⟩
  · have hvisible := Protocol.admittedBefore_mem_and_stamp_at S
      adm.toNamedScheduleWellFormed hadmit
        (Proofs.Optimistic.support_cutoff_le_vote_time_succ S.E d)
    have hstampCut : stampedBefore duty.toHealing.toFG.toSG.toGoldfishStore.timestamp_block
        (Protocol.support_cutoff S.E d) H = true := by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisible.2
    have hstampFreeze : stampedBefore duty.toHealing.toFG.toSG.toGoldfishStore.timestamp_block
        (Protocol.view_freeze S.E d) H = true := by
      rw [stampedBefore_eq_occurrenceBefore] at hstampCut ⊢
      exact occurrenceBefore_mono
        (le_of_lt (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E d)) hstampCut
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisible.1,
      Or.inl hstampFreeze⟩

/-- The prepared vote view contains only committee-valid votes. -/
private theorem preparedProposalPivot_voteViewValid_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (v : V) (s : Slot) :
    Protocol.VoteSetValid S.E
      ((voteDutyRead S rho v s).st.core.s - 1)
      (Protocol.voter_view S.E
        (voteDutyRead S rho v s).st.core.toHealing.toFG.toSG.toGoldfishStore
        (voteDutyRead S rho v s).st.core.s) := by
  let t := Protocol.vote_time S.E s
  let read := voteDutyRead S rho v s
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed t
  have hpool := Protocol.voteSetValid_pool_stateBefore S
    adm.toNamedScheduleWellFormed v n (read.st.core.s - 1)
  have hcarried : ∀ B ∈ (rho.stateBefore S n v).st.core.T,
      ∀ u ∈ B.gf_votes, u.val_index ∈ S.E.committee u.slot := by
    intro B hB u hu
    exact Protocol.carriedVote_committee_of_mem_T_core
      S adm v n hB u hu
  have hvalid := Protocol.voteSetValid_voter_view_of_carried
    (E := S.E) (st := (rho.stateBefore S n v).st.core)
    (s := read.st.core.s) hpool hcarried
  simpa only [read, t, voteDutyRead,
    NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock, hn] using hvalid

/-- The actual proposal-free prepared voter walk reaches the protected pivot. -/
theorem PreparedProtectedProposalPivot.preceq_proposalFreeHead_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {d : Slot} (hd : 0 < d)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E d)
    (hhor : Protocol.support_cutoff S.E d ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {A B : NamedBlock V}
    (hB : proposedBlockAt S rho (d + 1) = some B)
    (hpivot : PreparedProtectedProposalPivot S rho d v A) :
    Block.Preceq A.erase
      (Protocol.ghost (voterAnchorAt S rho v (d + 1))
        (namedWalkTargetTree S rho (d + 1) v B)
        (namedWalkTargetScore S rho (d + 1) v)
        (namedWalkTargetEligible S rho (d + 1) v)) := by
  let read := voteDutyRead S rho v (d + 1)
  let st := read.st.core
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  have hroot : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) A.erase := by
    exact Block.preceq_trans
      (NamedOutageClosure.fg_root_preceq_anchor S.E S.hc st.toHealing
        (S.hc.round_of st.s)
        (DecoupledConsensusModel.Protocol.readFrame read.cache st.toHealing
          (S.hc.round_of st.s)).g1)
      (by simpa only [st, read, voterAnchorAt] using hpivot.targetAnchor)
  have havailable := honestHeadsAvailableBefore_of_namedPostHealingCone_core
    S adm hv hpost hhor hroot hpivot.slotProtected.cone
  have hresolve0 :=
    Protocol.headsResolveIn_storeBeforeTime_of_availableBefore_at_core
      S adm hv d (Proofs.Optimistic.support_cutoff_le_vote_time_succ S.E d) havailable
  have hresolve : HeadsResolveIn S rho d st.T st.timestamp_block := by
    simpa only [st, read, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hresolve0
  have hbase := Protocol.canonicalSuffixConeSupportVoterView_core
    S adm hcom hd hpost hhor hpivot.slotProtected.cone hv
      (Proofs.Optimistic.support_cutoff_le_vote_time_succ S.E d)
      (gst := st.toHealing.toFG.toSG.toGoldfishStore) (by rfl) (by rfl) (by rfl)
      (hresolve.of_eq rfl rfl)
  have hslot : st.s = d + 1 := by
    simpa only [st, read] using Proofs.Optimistic.voteDutyRead_slot S rho v (d + 1)
  have hcone : ConeSupport S.E st.T votes support votes (st.s - 1)
      rho.honest (fun X => Block.Preceq A.erase X) := by
    simpa only [st, read, votes, support, hslot,
      Protocol.Store.toHealing] using hbase
  have hvalid : Protocol.VoteSetValid S.E (st.s - 1) votes := by
    simpa only [st, read, votes] using
      preparedProposalPivot_voteViewValid_core S adm v (d + 1)
  have hpos : 0 < ((S.E.committee d) ∩ rho.honest).card := by
    have hcommittee := hcom d
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have hxHon := (Finset.mem_inter.mp hx).2
  have hxCommittee := (Finset.mem_inter.mp hx).1
  obtain ⟨H, hAH, hHrun, hemit⟩ :=
    hpivot.slotProtected.cone x hxHon hxCommittee
  have hHhead : HonestHead S rho d H.erase :=
    ⟨x, hxHon, hxCommittee, ⟨H, rfl, hHrun⟩, hemit⟩
  have hHprocessed := namedHonestHead_voterProcessed_of_available_core
    S adm havailable hHhead
  have hAprocessed := WeakGoldfish.ancestorProcessed_of_voterProcessed
    S adm hv hHprocessed A.erase hAH
  have htargetView :
      (st.σ A.erase).h = (Protocol.derive_named S.E S.cfg A).h := by
    have hbody : A ∈ (rho.stateBeforeTime S
        (Protocol.vote_time S.E (d + 1)) v).st.bodies := by
      simpa only [read, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hpivot.targetBody
    simpa only [st, read, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using congrArg (fun q => q.h)
        (Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
          (Protocol.vote_time S.E (d + 1)) v A hbody)
  have hband : st.h_max - 1 ≤ (st.σ A.erase).h := by
    rw [htargetView]
    simpa only [st, read] using hpivot.targetBand
  have hcandidate := WeakJoint.namedCandidatePath_of_processedBandDescendant_core
    S adm hv (s := d) (C := A.erase) (D := A.erase)
      (Block.preceq_self A.erase) hAprocessed
      (by simpa only [st, read] using hband)
      (by simpa only [st, read] using hroot)
  have hparent : B.erase.parent? = some (proposedParent S rho (d + 1)) := by
    obtain ⟨p, hp, hpe⟩ := proposedBlockAt_parent S rho (d + 1) hB
    rw [Proofs.NamedWire.erase_parent_optional, hp, Option.map_some, hpe]
  have hpath : Block.Preceq (voterAnchorAt S rho v (d + 1)) A.erase →
      ∀ C : Block V, Block.Preceq (voterAnchorAt S rho v (d + 1)) C →
        C ≠ voterAnchorAt S rho v (d + 1) → Block.Preceq C A.erase →
        C ∈ namedWalkTargetTree S rho (d + 1) v B := by
    intro _ C hAC hCne hCA
    have hCmem : C ∈ voterCandidateTreeAt S rho v (d + 1) := by
      by_cases hEq : C = A.erase
      · simpa only [hEq] using hcandidate.1
      · exact hcandidate.2 C hAC hCne hCA hEq
    apply Finset.mem_erase.mpr
    refine ⟨?_, hCmem⟩
    intro hEq
    have hCP := Block.preceq_trans hCA hpivot.parent
    rw [hEq] at hCP
    have hdepth := Block.preceq_depth_le hCP
    have hstrict := Protocol.depth_of_parent? hparent
    omega
  have hanchor := Block.compatible_of_preceq_common hpivot.targetAnchor
    (Block.preceq_self A.erase)
  have hhead := Protocol.goldfish_fork_choice_captures_supporter_majority
    S.E st.σ st.h_max st.T
      (namedWalkTargetTree S rho (d + 1) v B) st.s votes support
      (st.s - 1) (ConeSupport.sub hcone)
      (Protocol.supporterMajority_of_cone S.E hcone hvalid)
      hanchor hpath
  simpa only [Protocol.goldfish_fork_choice,
    namedWalkTargetScore, namedWalkTargetEligible, st, read, votes, support]
    using hhead

#print axioms PreparedProtectedProposalPivot.preceq_proposalFreeHead_core

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
