module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FGSafetyFrozenHeadNamed
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGFirstInteriorNamed
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.GoldfishCone
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainSupporter
public import DecoupledConsensusProofs.Execution.RecoveryInitialSourceNamedActionHistory

@[expose] public section

/-!
# Prepared SG lifetime and protected-cone safety

This leaf ports the post-deadline SG lifetime route to the prepared vote-duty
anchor and head. The first theorem is independent of the concurrent SG
bootstrap pins.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface
open Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem namedVotesCone_of_allHonestVoterHeads
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon)
    {B : Block V}
    (hheads : ∀ w ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho w s)) :
    NamedHonestVotesCone S rho s (fun X => Block.Preceq B X) := by
  intro w hw hcommittee
  obtain ⟨X, hXhead, hXrun, hXemit⟩ :=
    voteDutyHead_runBlock_and_emits S adm hs hhor hw hcommittee
  exact ⟨X, by simpa only [hXhead] using hheads w hw, hXrun, hXemit⟩

private theorem preceq_voterHeadAt_of_namedNextVoteAdoption
    (S : Setup V) {rho : Run V} {source : Protocol.Store V}
    {s : Slot} {B : Block V} {w : V}
    (heligible : Protocol.voters_count S.E (confLate S.E source s) s <
      2 * Protocol.goldfish_score S.E source.T
        (confVotes S.E source s) (confVotes S.E source s) s B)
    (hadopt : NamedNextVoteAdoption S rho source s B w) :
    Block.Preceq B (voterHeadAt S rho w (s + 1)) := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)
  let st := read.st.core
  let tree := voterCandidateTreeAt S rho w (s + 1)
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  have hslot : st.s = s + 1 := by
    simpa only [st, read] using voteDutyRead_slot S rho w (s + 1)
  have hprev : st.s - 1 = s := by
    rw [hslot]
    simp
  change Block.Preceq B
    (Protocol.get_head_in_tree_with_layer
      (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
      tree votes support (st.s - 1))
  rw [get_head_in_tree_split_with, hprev]
  simpa only [Protocol.Store.toHealing, read, st] using
    (Protocol.goldfish_fork_choice_captures_of_confirmation
      S.E st.σ st.h_max source.T st.T tree st.s
      (confEarly S.E source s) (confLate S.E source s)
      (confVotes S.E source s) votes support s
      (confNumerator S.E source s) hadopt.transport heligible
        hadopt.support_subset hadopt.anchor hadopt.path)

private theorem postGST_vote_after_deadline_named
    (S : Setup V) {rho : Run V} {rGST gap : Round}
    (hpost : S.E.t_GST ≤ S.a rGST)
    {s : Slot}
    (hs : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s) :
    S.E.t_GST ≤ Protocol.vote_time S.E s := by
  have hround : rGST + 1 ≤
      fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact Nat.le_add_right _ _
  have hslot : S.hc.opening_slot (rGST + 1) ≤ s :=
    (Nat.mul_le_mul_right S.hc.R hround).trans ((Nat.le_succ _).trans hs)
  have hcutVote : S.hc.Γ_0 S.E.Δ (rGST + 1) ≤
      Protocol.vote_time S.E (S.hc.opening_slot (rGST + 1)) :=
    Int.le_add_of_nonneg_right S.E.Δ_pos.le
  exact ((gst_le_Γ_neg1_succ S rGST hpost).trans
    (Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (rGST + 1)).le).trans
    (hcutVote.trans (vote_time_mono_slots S.E hslot))

private theorem preparedVoteViewValid
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (w : V) (s : Slot) :
    Protocol.VoteSetValid S.E
      ((Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.s - 1)
      (Protocol.voter_view S.E
        (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.toHealing.toFG.toSG.toGoldfishStore
        (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.s) := by
  let t := Protocol.vote_time S.E s
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w s
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed t
  have hpool := Protocol.voteSetValid_pool_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w n
    (read.st.core.s - 1)
  have hcarried : ∀ B ∈ (rho.stateBefore S n w).st.core.T,
      ∀ u ∈ B.gf_votes, u.val_index ∈ S.E.committee u.slot := by
    intro B hB u hu
    exact Protocol.carriedVote_committee_of_mem_T S adm w n hB u hu
  have hvalid := Protocol.voteSetValid_voter_view_of_carried
    (E := S.E) (st := (rho.stateBefore S n w).st.core)
    (s := read.st.core.s) hpool hcarried
  simpa only [read, t, Internal.NamedRecoveryRead.voteDutyRead,
    NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock, hn]
    using hvalid

private theorem goldfishConeStepAtVoteHorizon
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    {B : Block V}
    (hnames : NamedHonestVotesCone S rho s (fun X => Block.Preceq B X))
    {w : V} (hw : w ∈ rho.honest)
    (hinputs : GoldfishConeVoteInputs S rho s B w) :
    Block.Preceq B (voterHeadAt S rho w (s + 1)) := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)
  let st := read.st.core
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let tree := voterCandidateTreeAt S rho w (s + 1)
  have hcutHor : Protocol.support_cutoff S.E s ≤ rho.horizon :=
    (support_cutoff_le_vote_time_succ S.E s).trans hhor
  have havailable := honestHeadsAvailableBefore_of_namedPostHealingCone
    S adm hw hpost hcutHor hinputs.root hnames
  have hresolve0 := Protocol.headsResolveIn_storeBeforeTime_of_availableBefore_at
    S adm hw s (support_cutoff_le_vote_time_succ S.E s) havailable
  have hresolve : HeadsResolveIn S rho s st.T st.timestamp_block := by
    simpa only [st, read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hresolve0
  have hbase := Protocol.canonicalSuffixConeSupportVoterView
    S adm hcom hs hpost hcutHor hnames hw
      (support_cutoff_le_vote_time_succ S.E s)
      (gst := st.toHealing.toFG.toSG.toGoldfishStore) (by rfl) (by rfl) (by rfl)
      (hresolve.of_eq rfl rfl)
  have hslot : st.s = s + 1 := by
    simpa only [st, read] using voteDutyRead_slot S rho w (s + 1)
  have hvalid := preparedVoteViewValid S adm w (s + 1)
  have hcone : ConeSupport S.E st.T votes support votes (st.s - 1)
      rho.honest (fun X => Block.Preceq B X) := by
    simpa only [st, read, votes, support, hslot, Protocol.Store.toHealing]
      using hbase
  have hmajority : Protocol.voters_count S.E votes (st.s - 1) <
      2 * (Protocol.goldfishSupporters S.E st.T votes support (st.s - 1) B).card :=
    Protocol.supporterMajority_of_cone S.E hcone hvalid
  have hpath : ∀ D : Block V,
      Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
      D ≠ voterAnchorAt S rho w (s + 1) →
      Block.Preceq D B → D ∈ tree := by
    intro D hAD hDne hDB
    by_cases hEq : D = B
    · simpa only [hEq] using hinputs.candidate
    · exact hinputs.path D hAD hDne hDB hEq
  have hhead := Protocol.goldfish_fork_choice_captures_supporter_majority
    S.E st.σ st.h_max st.T tree st.s votes support (st.s - 1)
      (ConeSupport.sub hcone) hmajority hinputs.anchor
      (fun _ D hAD hDne hDB => hpath D hAD hDne hDB)
  change Block.Preceq B
    (Protocol.get_head_in_tree_with_layer
      (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
      tree votes support (st.s - 1))
  simpa only [get_head_in_tree_eq_voterHeadAt_of_anchor, read, st, tree]
    using hhead

/-- The prepared all-honest head step. Previous honest heads produce the
named vote cone. In the strict anchor branch the frozen-head split supplies
the prepared candidate path; in the other branch the prepared anchor floor is
already enough. -/
theorem allHonestHeads_succ_of_voterAnchorCompatible_after_GST_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {s : Slot}
    (hs : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s)
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    {B : Block V}
    (hheads : ∀ w ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho w s))
    (hanchors : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) B = true) :
    ∀ w ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho w (s + 1)) := by
  have hsPos : 0 < s := (Nat.zero_lt_succ _).trans_le hs
  have hprevHor : Protocol.vote_time S.E s ≤ rho.horizon :=
    (vote_time_mono_slots S.E (Nat.le_succ s)).trans hhor
  have hnames : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B X) :=
    namedVotesCone_of_allHonestVoterHeads S adm hsPos hprevHor hheads
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E s :=
    postGST_vote_after_deadline_named S hpost hs
  have hcutHor : Protocol.support_cutoff S.E s ≤ rho.horizon :=
    (support_cutoff_le_vote_time_succ S.E s).trans hhor
  intro w hw
  have hrootAnchor : Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.toHealing.toFG)
      (voterAnchorAt S rho w (s + 1)) :=
    fg_root_preceq_get_sg_root_with_frame
      (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).cache
      S.E S.hc
      (Internal.NamedRecoveryRead.voteDutyRead S rho w
        (s + 1)).st.core.toHealing
      (S.hc.round_of
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.s)
  rcases (show Block.Preceq (voterAnchorAt S rho w (s + 1)) B ∨
      Block.Preceq B (voterAnchorAt S rho w (s + 1)) by
    simpa only [Block.compatible, Bool.or_eq_true] using hanchors w hw) with
    hanchorB | hBanchor
  · have hrootB : Block.Preceq
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.toHealing.toFG) B :=
      Block.preceq_trans hrootAnchor hanchorB
    have havailable := honestHeadsAvailableBefore_of_namedPostHealingCone
      S adm hw hpostVote hcutHor hrootB hnames
    have hpositive : 0 < ((S.E.committee s) ∩ rho.honest).card := by
      have hmajority := hcom s
      omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
    have hxCommittee : x ∈ S.E.committee s := (Finset.mem_inter.mp hx).1
    have hxHonest : x ∈ rho.honest := (Finset.mem_inter.mp hx).2
    obtain ⟨X, hBX, hXrun, hXemit⟩ := hnames x hxHonest hxCommittee
    have hXhead : HonestHead S rho s X.erase :=
      ⟨x, hxHonest, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    have hprocessed : ∀ {C : Block V}, Block.Preceq C B →
        C ∈ Protocol.voter_processed_block_tree S.E
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore (s + 1) := by
      intro C hCB
      have hmem := voterProcessed_of_availableBefore_of_honestHead
        S adm havailable hXhead (Block.preceq_trans hCB hBX)
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime,
        Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.toHealing_slot, Proofs.Optimistic.voteDutyStore_slot,
        Proofs.Optimistic.slotOf_vote_time] using hmem
    rcases honestPreviousHead_voterCandidateMem_or_preceq_root_after_GST_named
        S adm hcom hbelow hrec hdelay hpost hs hhor hw hw
        (hheads w hw) (hprocessed (Block.preceq_self B)) with
      hBcandidate | hBroot
    · apply goldfishConeStepAtVoteHorizon S adm hcom hsPos hpostVote hhor
        hnames hw
      refine
        { candidate := hBcandidate
          root := hrootB
          anchor := hanchors w hw
          path := ?_ }
      intro D hanchorD hDanchor hDB hDBne
      rcases honestPreviousHead_voterCandidateMem_or_preceq_root_after_GST_named
          S adm hcom hbelow hrec hdelay hpost hs hhor hw hw
          (Block.preceq_trans hDB (hheads w hw)) (hprocessed hDB) with
        hDcandidate | hDroot
      · exact hDcandidate
      · exact (hDanchor
          (Block.preceq_antisymm
            (Block.preceq_trans hDroot hrootAnchor) hanchorD)).elim
    · exact Block.preceq_trans hBroot
        (fgRoot_preceq_voterHeadAt S rho w (s + 1))
  · exact Block.preceq_trans hBanchor
      (voterAnchorAt_preceq_voterHeadAt S rho w (s + 1))


private theorem firstInterior_lt_nextOpening (S : Setup V) (r : Round) :
    S.hc.opening_slot r + 1 < S.hc.opening_slot (r + 1) := by
  simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul] using
    Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two) (r * S.hc.R)

private theorem slot_round_bounds (S : Setup V) (s : Slot) :
    S.hc.opening_slot (S.hc.round_of s) ≤ s ∧
      s < S.hc.opening_slot (S.hc.round_of s + 1) := by
  refine ⟨Nat.div_mul_le_self s S.hc.R, ?_⟩
  apply (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt S.hc.R_ge_two)).mp
  exact Nat.lt_succ_self _

private theorem voterAnchorAt_compatible_of_previousSGHistory_voteHorizon
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {s : Slot} {B : Block V}
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hc : 1 ≤ S.hc.round_of (s + 1))
    (hsg : HonestSGEmissionsCompatibleAtRound S rho
      (S.hc.round_of (s + 1) - 1) B)
    (hsgPost : S.E.t_GST ≤ S.a (S.hc.round_of (s + 1) - 1))
    {w : V} (hw : w ∈ rho.honest)
    (hroot : Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.toHealing.toFG) B = true) :
    Block.compatible (voterAnchorAt S rho w (s + 1)) B = true := by
  let c := S.hc.round_of (s + 1)
  rcases voterAnchorAt_cases S rho w (s + 1) with
    hfg | ⟨root, L, hframe, hactive, hanchor⟩
  · rw [hfg]
    exact hroot
  · rw [hanchor]
    have hround : S.hc.round_of (s + 1) = c := rfl
    have hslo : S.hc.opening_slot c ≤ s + 1 := by
      rw [← hround]
      exact Nat.div_mul_le_self (s + 1) S.hc.R
    have hshi : s + 1 < S.hc.opening_slot (c + 1) := by
      rw [← hround]
      apply (Nat.div_lt_iff_lt_mul
        (Nat.zero_lt_of_lt S.hc.R_ge_two)).mp
      exact Nat.lt_succ_self ((s + 1) / S.hc.R)
    have hnext : Protocol.vote_time S.E (s + 1) ≤
        DecoupledConsensusModel.Protocol.opening S.E S.hc (c + 1) := by
      have hvoteNext : Protocol.vote_time S.E (s + 1) <
          Protocol.proposal_time S.E (s + 2) := by
        apply lt_trans ?_ (support_cutoff_lt_proposal_time_succ S.E (s + 1))
        rw [← Proofs.Optimistic.vote_time_add_delta]
        exact Int.lt_add_of_pos_right _ S.E.Δ_pos
      exact hvoteNext.le.trans (by
        simpa only [DecoupledConsensusModel.Protocol.opening] using
          proposal_time_mono S.E (Nat.succ_le_iff.mpr hshi))
    have hframe' : (DecoupledConsensusModel.Protocol.readFrame
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).cache
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.toHealing c).g1 = some (some root) := by
      have hslot :
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.s = s + 1 :=
        Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
      simpa only [hslot, hround] using hframe
    obtain ⟨_, hLgrade⟩ := fixedRoot_activeVoterAnchor_g1_data
      S adm (Nat.zero_lt_of_lt hc) hslo hround hnext hhor hw hframe' hactive
    rcases (show Block.Preceq
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.toHealing.toFG) B ∨
        Block.Preceq B
          (Protocol.get_fg_root
            (Internal.NamedRecoveryRead.voteDutyRead S rho w
              (s + 1)).st.core.toHealing.toFG) by
      simpa only [Block.compatible, Bool.or_eq_true] using hroot) with
      hrootB | hBroot
    · have hdomainVote : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 ≤
          Protocol.vote_time S.E (s + 1) := by
        rw [NamedOutageClosure.domain_g1_eq_opening]
        exact (proposal_time_mono S.E hslo).trans
          (proposal_time_lt_vote_time S.E (s + 1)).le
      have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 ≤
          rho.horizon := hdomainVote.trans hhor
      have hvoteFroot : Block.Preceq
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.F
          (Protocol.get_fg_root
            (Internal.NamedRecoveryRead.voteDutyRead S rho w
              (s + 1)).st.core.toHealing.toFG) :=
        StoreFinality.finalized_preceq_fgRoot
          (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
            S rho (Protocol.vote_time S.E (s + 1)) w)
      have hdomainFvoteF : Block.Preceq
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.F
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.F := by
        simpa only [Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using
            (by
              rw [NamedOutageClosure.strict_read_eq_index S rho
                    adm.toNamedScheduleWellFormed.sorted
                    (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1),
                  NamedOutageClosure.strict_read_eq_index S rho
                    adm.toNamedScheduleWellFormed.sorted
                    (Protocol.vote_time S.E (s + 1))]
              exact Proofs.NamedRuntime.stateBefore_F_mono S rho w
                (NamedOutageClosure.strict_lengths_mono rho hdomainVote))
      have hFT : Block.Preceq
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.F B :=
        Block.preceq_trans hdomainFvoteF
          (Block.preceq_trans hvoteFroot hrootB)
      exact phaseGrade_compatible_of_previousSGHistory_named
        S adm hbelow hc hsgPost hdomainHor hw hFT hsg hLgrade
    · have hrootL : Block.Preceq
          (Protocol.get_fg_root
            (Internal.NamedRecoveryRead.voteDutyRead S rho w
              (s + 1)).st.core.toHealing.toFG) L := by
        have hLmem : L ∈ PhaseGrades.filteredTree
            (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)) := by
          unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
          exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1
        exact Proofs.Records.preceq_get_fg_root_of_mem_filtered hLmem
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr (Block.preceq_trans hBroot hrootL)


/-- Every honest prepared SG vote after the deadline stays below every later
prepared voter head. This closed form uses the available first-interior theorem
and supplies the anchor producer's delivery horizon from the induction. -/
theorem actionSGBlock_preceq_voterHeadAt_after_GST
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    {d : Slot} (hd : S.hc.opening_slot (c + 1) + 1 ≤ d)
    (hhor : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) :
    Block.Preceq (actionSGBlockAt S rho v (c + 1))
      (voterHeadAt S rho w d) := by
  let start := S.hc.opening_slot (c + 1) + 1
  let B := actionSGBlockAt S rho v (c + 1)
  have hsourceHor : S.a (c + 1) ≤ rho.horizon := by
    calc
      S.a (c + 1) = Protocol.vote_time S.E start + S.E.Δ := by
        rw [vote_time_succ_add_delta_eq_confirmation_time,
          opening_confirmation_time_eq_action]
      _ ≤ Protocol.vote_time S.E d + S.E.Δ :=
        Int.add_le_add_right (vote_time_mono_slots S.E hd) _
      _ ≤ rho.horizon := hhor
  have hstartRound : S.hc.round_of start = c + 1 :=
    round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc (le_refl _)
      (firstInterior_lt_nextOpening S (c + 1))
  have hstartDead : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ start :=
    Nat.add_le_add_right
      (Nat.mul_le_mul_right S.hc.R (hc.trans (Nat.le_succ c))) 1
  have hGSTdead : rGST ≤
      fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hall : ∀ j : Slot, start ≤ j →
      Protocol.vote_time S.E j + S.E.Δ ≤ rho.horizon →
      ∀ u ∈ rho.honest, Block.Preceq B (voterHeadAt S rho u j) := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj hjor u hu
      by_cases hbase : j = start
      · subst j
        exact actionSGBlock_preceq_firstInteriorHead_after_GST_named
          S adm hcom hbelow hrec hdelay hpost hc hsourceHor hv hu
      · cases j with
        | zero =>
          exact False.elim ((not_le_of_gt (Nat.zero_lt_succ _)) hj)
        | succ s =>
          have hsPrev : start ≤ s :=
            Nat.le_of_lt_succ (lt_of_le_of_ne hj (Ne.symm hbase))
          have hsDead := hstartDead.trans hsPrev
          have hprevHor : Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon :=
            (Int.add_le_add_right (vote_time_mono_slots S.E (Nat.le_succ s)) _).trans
              hjor
          have hprevHeads := ih s (Nat.lt_succ_self s) hsPrev hprevHor
          have hreadHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon :=
            (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hjor
          have hanchors : ∀ z ∈ rho.honest,
              Block.compatible (voterAnchorAt S rho z (s + 1)) B = true := by
            intro z hz
            let r := S.hc.round_of (s + 1)
            obtain ⟨hlower, hupper⟩ := slot_round_bounds S (s + 1)
            have hrLower : c + 1 ≤ r := by
              rw [← hstartRound]
              unfold Protocol.HealConfig.round_of
              exact Nat.div_le_div_right hj
            by_cases hrEq : r = c + 1
            · exact voterAnchorAt_firstInterior_compatible_actionSGBlock_after_GST
                S adm hcom hbelow hrec hdelay hpost hc hsourceHor hj
                (by simpa only [← hrEq] using hupper) hreadHor hjor hv hz
            · have hrGt : c + 1 < r := lt_of_le_of_ne hrLower (Ne.symm hrEq)
              let k := r - 1
              have hkSource : c + 1 ≤ k :=
                Nat.le_sub_of_add_le (Nat.succ_le_of_lt hrGt)
              have hkPos : 1 ≤ k :=
                (Nat.succ_le_succ (Nat.zero_le c)).trans hkSource
              have hrPos : 1 ≤ r :=
                (Nat.succ_le_succ (Nat.zero_le c)).trans hrLower
              have hkEq : k + 1 = r := Nat.sub_add_cancel hrPos
              have hkDead : fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 ≤ k :=
                (Nat.succ_le_succ hc).trans hkSource
              have hkBeforeRound : S.hc.opening_slot k + 1 <
                  S.hc.opening_slot r := by
                simpa only [hkEq] using firstInterior_lt_nextOpening S k
              have hkFirstLt : S.hc.opening_slot k + 1 < s + 1 :=
                hkBeforeRound.trans_le hlower
              have hkStart : start ≤ S.hc.opening_slot k + 1 :=
                Nat.add_le_add_right
                  (Nat.mul_le_mul_right S.hc.R hkSource) 1
              have hkFirstHor :
                  Protocol.vote_time S.E (S.hc.opening_slot k + 1) + S.E.Δ ≤
                    rho.horizon :=
                (Int.add_le_add_right
                  (vote_time_mono_slots S.E (Nat.le_of_lt hkFirstLt)) _).trans
                    hjor
              have hBHead := ih (S.hc.opening_slot k + 1) hkFirstLt
                hkStart hkFirstHor v hv
              have hkActionHor : S.a k ≤ rho.horizon :=
                ((action_lt_vote_time_two_after S k).le.trans
                  (vote_time_mono_slots S.E
                    (Nat.succ_le_of_lt hkFirstLt))).trans hreadHor
              have hhistory : HonestSGEmissionsCompatibleAtRound S rho k B := by
                intro x hx _
                have hSGHead := actionSGBlock_preceq_firstInteriorHead_after_GST_named
                  S adm hcom hbelow hrec hdelay hpost
                  (Nat.le_sub_of_add_le hkDead)
                  (by simpa only [Nat.sub_add_cancel hkPos] using hkActionHor)
                  hx hv
                have hSGHead' : Block.Preceq (actionSGBlockAt S rho x k)
                    (voterHeadAt S rho v (S.hc.opening_slot k + 1)) := by
                  simpa only [Nat.sub_add_cancel hkPos] using hSGHead
                exact Block.compatible_of_preceq_common hSGHead' hBHead
              have hdeadlineRead :
                  S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤
                    Protocol.vote_time S.E (s + 1) :=
                (action_lt_vote_time_two_after S _).le.trans
                  (vote_time_mono_slots S.E (Nat.succ_le_succ hsDead))
              have hrootPre := fgRoot_preceq_previousHead_after_GST
                S adm hcom hbelow hrec hdelay hpost hdeadlineRead hreadHor
                hsDead (le_refl _) hprevHor hz hz
              have hroot : Block.compatible
                  (Protocol.get_fg_root
                    (Internal.NamedRecoveryRead.voteDutyRead S rho z
                      (s + 1)).st.core.toHealing.toFG) B = true := by
                have hrootPre' : Block.Preceq
                    (Protocol.get_fg_root
                      (Internal.NamedRecoveryRead.voteDutyRead S rho z
                        (s + 1)).st.core.toHealing.toFG)
                    (voterHeadAt S rho z s) := by
                  simpa only [Internal.NamedRecoveryRead.voteDutyRead,
                    NamedActionReads.confirmationReadAt,
                    NamedActionReads.confirmationReadFrom,
                    Protocol.NamedStore.setClock, Run.storeBeforeTime] using hrootPre
                exact Block.compatible_of_preceq_common hrootPre'
                  (hprevHeads z hz)
              have hsgPost : S.E.t_GST ≤ S.a k :=
                hpost.trans (Assembly.a_mono S
                  (hGSTdead.trans ((Nat.le_succ _).trans hkDead)))
              have hround : S.hc.round_of (s + 1) = k + 1 := hkEq.symm
              apply voterAnchorAt_compatible_of_previousSGHistory_named
                S adm hbelow
              · simpa only [vote_time_succ_add_delta_eq_confirmation_time] using hjor
              · simpa only [hround] using Nat.succ_pos k
              · simpa only [hround, Nat.add_sub_cancel] using hhistory
              · simpa only [hround, Nat.add_sub_cancel] using hsgPost
              · exact hz
              · exact hroot
          exact allHonestHeads_succ_of_voterAnchorCompatible_after_GST_named
            S adm hcom hbelow hrec hdelay hpost hsDead hreadHor
            hprevHeads hanchors u hu
  exact hall d hd hhor w hw

private theorem vote_add_delta_le_nextVote (E : Env V) (s : Slot) :
    Protocol.vote_time E s + E.Δ ≤ Protocol.vote_time E (s + 1) := by
  unfold Protocol.vote_time Env.t slotStart
  push_cast
  have hd := E.Δ_pos
  calc
    _ = 4 * E.Δ * (s : Int) + 2 * E.Δ := by ring
    _ ≤ 4 * E.Δ * (s : Int) + 5 * E.Δ :=
      Int.add_le_add_left
        (Int.mul_le_mul_of_nonneg_right (show (2 : Int) ≤ 5 by decide) hd.le) _
    _ = _ := by ring

private theorem deadlineInterior_le_laterOpening (S : Setup V) (d : Round) :
    S.hc.opening_slot d + 1 ≤ S.hc.opening_slot (d + 2) :=
  (firstInterior_lt_nextOpening S d).le.trans
    (Nat.mul_le_mul_right S.hc.R (Nat.le_succ (d + 1)))


/-- Once the previous prepared SG round is protected, a block below an honest
previous head is compatible with every next prepared anchor. -/
theorem nextVoteDutyAnchor_compatible_of_honestPreviousHead_after_SG_healing_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {s : Slot}
    (hs : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ s)
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {B : Block V}
    (hB : Block.Preceq B (voterHeadAt S rho v s)) :
    Block.compatible (voterAnchorAt S rho w (s + 1)) B = true := by
  let r := S.hc.round_of (s + 1)
  let k := r - 1
  have hrLow : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ r := by
    calc
      _ = S.hc.round_of
          (S.hc.opening_slot
            (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2)) :=
        (round_of_opening_slot_eq_schedule S.hc _).symm
      _ ≤ r := by
        unfold r Protocol.HealConfig.round_of
        exact Nat.div_le_div_right (hs.trans (Nat.le_succ s))
  have hrPos : 1 ≤ r :=
    (Nat.succ_le_succ
      (Nat.zero_le (fgSafetyProgressDeadline S rho rGST gap delayExtra + 1))).trans
        hrLow
  have hkEq : k + 1 = r := Nat.sub_add_cancel hrPos
  have hkDead : fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 ≤ k :=
    Nat.le_sub_of_add_le hrLow
  have hkPos : 1 ≤ k := (Nat.succ_le_succ (Nat.zero_le _)).trans hkDead
  have hroundLower : S.hc.opening_slot r ≤ s + 1 :=
    Nat.div_mul_le_self (s + 1) S.hc.R
  have hkFirst : S.hc.opening_slot k + 1 ≤ s := by
    apply Nat.le_of_lt_succ
    have hbefore : S.hc.opening_slot k + 1 < S.hc.opening_slot r := by
      simpa only [hkEq] using firstInterior_lt_nextOpening S k
    exact hbefore.trans_le hroundLower
  have hprevHor : Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon :=
    (vote_add_delta_le_nextVote S.E s).trans hhor
  have hhistory : HonestSGEmissionsCompatibleAtRound S rho k B := by
    intro x hx _
    have hSG := actionSGBlock_preceq_voterHeadAt_after_GST
      S adm hcom hbelow hrec hdelay hpost (Nat.le_sub_of_add_le hkDead)
      (by simpa only [Nat.sub_add_cancel hkPos] using hkFirst)
      hprevHor hx hv
    have hSG' : Block.Preceq (actionSGBlockAt S rho x k)
        (voterHeadAt S rho v s) := by
      simpa only [Nat.sub_add_cancel hkPos] using hSG
    exact Block.compatible_of_preceq_common hSG' hB
  have hsDead : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s := by
    exact (deadlineInterior_le_laterOpening S _).trans hs
  have hdeadlineRead :
      S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤
        Protocol.vote_time S.E (s + 1) :=
    (action_lt_vote_time_two_after S _).le.trans
      (vote_time_mono_slots S.E (Nat.succ_le_succ hsDead))
  have hrootPre := fgRoot_preceq_previousHead_after_GST
    S adm hcom hbelow hrec hdelay hpost hdeadlineRead hhor hsDead
      (le_refl _) hprevHor hw hv
  have hrootPre' : Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.toHealing.toFG)
      (voterHeadAt S rho v s) := by
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Run.storeBeforeTime] using hrootPre
  have hroot : Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.toHealing.toFG) B = true :=
    Block.compatible_of_preceq_common hrootPre' hB
  have hGSTdead : rGST ≤
      fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hsgPost : S.E.t_GST ≤ S.a k :=
    hpost.trans (Assembly.a_mono S
      (hGSTdead.trans ((Nat.le_succ _).trans hkDead)))
  have hround : S.hc.round_of (s + 1) = k + 1 := hkEq.symm
  apply voterAnchorAt_compatible_of_previousSGHistory_voteHorizon
    S adm hbelow hhor
  · simpa only [hround] using Nat.succ_pos k
  · simpa only [hround, Nat.add_sub_cancel] using hhistory
  · simpa only [hround, Nat.add_sub_cancel] using hsgPost
  · exact hw
  · exact hroot


/-- Any block below all honest prepared voter heads at one healed slot stays
below every later prepared voter head. -/
theorem allHonestVoterHeads_persist_after_SG_healing_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {start : Slot}
    (hstart : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ start)
    {B : Block V}
    (hheads : ∀ w ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho w start))
    {d : Slot} (hd : start ≤ d)
    (hhor : Protocol.vote_time S.E d ≤ rho.horizon) :
    ∀ w ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho w d) := by
  have hall : ∀ j : Slot, start ≤ j →
      Protocol.vote_time S.E j ≤ rho.horizon →
      ∀ w ∈ rho.honest, Block.Preceq B (voterHeadAt S rho w j) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
        intro _
        exact hheads
    | succ j hj ih =>
        intro hjor
        have hprev := ih
          ((vote_time_mono_slots S.E (Nat.le_succ j)).trans hjor)
        have hjStart : S.hc.opening_slot
            (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ j :=
          hstart.trans hj
        have hanchors : ∀ w ∈ rho.honest,
            Block.compatible (voterAnchorAt S rho w (j + 1)) B = true := by
          intro w hw
          exact
            nextVoteDutyAnchor_compatible_of_honestPreviousHead_after_SG_healing_named
              S adm hcom hbelow hrec hdelay hpost hjStart hjor
              hw hw (hprev w hw)
        exact allHonestHeads_succ_of_voterAnchorCompatible_after_GST_named
          S adm hcom hbelow hrec hdelay hpost
            ((deadlineInterior_le_laterOpening S _).trans hjStart)
            hjor hprev hanchors
  exact hall d hd hhor


/-- A prepared genuine confirmation after the deadline stays below every
later prepared voter head. -/
theorem genuineConfirmationWith_preceq_laterVoterHeads_after_GST
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 ≤ c)
    {s : Slot} (hs : S.hc.opening_slot (c + 1) + 1 ≤ s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {B : Block V}
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).cache)
      S.E S.hc (confStore S rho v s) s B) :
    ∀ d, s + 1 ≤ d → Protocol.vote_time S.E d ≤ rho.horizon →
      ∀ w ∈ rho.honest, Block.Preceq B (voterHeadAt S rho w d) := by
  have hdeadline : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c :=
    Nat.le_of_succ_le hc
  have hsDead : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s :=
    (Nat.add_le_add_right
      (Nat.mul_le_mul_right S.hc.R
        (hdeadline.trans (Nat.le_succ c))) 1).trans hs
  have hsTwo : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ s :=
    (Nat.mul_le_mul_right S.hc.R (Nat.succ_le_succ hc)).trans
      (Nat.le_of_succ_le hs)
  have hsPos : 0 < s := (Nat.zero_lt_succ _).trans_le hsDead
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans ?_ hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
  have hshor : Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon := by
    calc
      Protocol.vote_time S.E s + S.E.Δ ≤
          Protocol.vote_time S.E (s + 1) + S.E.Δ :=
        Int.add_le_add_right (vote_time_mono_slots S.E (Nat.le_succ s)) _
      _ = Protocol.confirmation_time S.E s :=
        vote_time_succ_add_delta_eq_confirmation_time S.E s
      _ ≤ rho.horizon := hhor
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E s :=
    postGST_vote_after_deadline_named S hpost hsDead
  have hpostProposal : S.E.t_GST ≤ Protocol.proposal_time S.E s := by
    have hGSTdead : rGST ≤
        fgSafetyProgressDeadline S rho rGST gap delayExtra := by
      unfold fgSafetyProgressDeadline
      exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
    have hpostc : S.E.t_GST ≤ S.a c :=
      hpost.trans (Assembly.a_mono S (hGSTdead.trans hdeadline))
    have hopening : S.E.t_GST ≤
        Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)) := by
      rw [← Protocol.Γ_0_eq_proposal_time]
      exact (gst_le_Γ_neg1_succ S c hpostc).trans
        (Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (c + 1)).le
    exact hopening.trans (proposal_time_mono S.E (Nat.le_of_succ_le hs))
  have hgenuine' : GenuineConfirmation
      (contract := NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).cache)
      S.E S.hc (confStore S rho v s) s B :=
    ⟨hgenuine.selected, hgenuine.genuine⟩
  obtain ⟨u, hu, _, hBu⟩ :=
    WeakGoldfish.genuineConfirmation_exists_honestVoteSupporter_after_gst
      S adm.toNamedAdmissibleCore hcom hv hsPos hpostVote hhor hgenuine
  have hdeadlineRead :
      S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤
        Protocol.vote_time S.E (s + 1) :=
    (action_lt_vote_time_two_after S _).le.trans
      (vote_time_mono_slots S.E (Nat.succ_le_succ hsDead))
  have hbase : ∀ w ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho w (s + 1)) := by
    intro w hw
    have hanchorCompat :=
      nextVoteDutyAnchor_compatible_of_honestPreviousHead_after_SG_healing_named
        S adm hcom hbelow hrec hdelay hpost hsTwo hvoteHor hu hw hBu
    have hrootPre := fgRoot_preceq_previousHead_after_GST
      S adm hcom hbelow hrec hdelay hpost hdeadlineRead hvoteHor hsDead
        (le_refl _) hshor hw hu
    have hrootPre' : Block.Preceq
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.toHealing.toFG)
        (voterHeadAt S rho u s) := by
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock, Run.storeBeforeTime] using hrootPre
    have hrootCompat : Block.compatible
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.toHealing.toFG) B = true :=
      Block.compatible_of_preceq_common hrootPre' hBu
    rcases (show Block.Preceq
          (Protocol.get_fg_root
            (Internal.NamedRecoveryRead.voteDutyRead S rho w
              (s + 1)).st.core.toHealing.toFG) B ∨
        Block.Preceq B
          (Protocol.get_fg_root
            (Internal.NamedRecoveryRead.voteDutyRead S rho w
              (s + 1)).st.core.toHealing.toFG) by
      simpa only [Block.compatible, Bool.or_eq_true] using hrootCompat) with
      hrootB | hBroot
    · rcases (show Block.Preceq (voterAnchorAt S rho w (s + 1)) B ∨
          Block.Preceq B (voterAnchorAt S rho w (s + 1)) by
        simpa only [Block.compatible, Bool.or_eq_true] using hanchorCompat) with
        hanchorB | hBanchor
      · have hrootBare : Block.Preceq
            (Protocol.get_fg_root
              (voteDutyStore S rho w (s + 1)).toHealing.toFG) B := by
          simpa only [Internal.NamedRecoveryRead.voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
            Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hrootB
        have hprocessed :=
          Protocol.voterProcessedTarget_of_genuineConfirmation_after_gst
            S adm hv hw hpostProposal hhor hgenuine' hrootBare
        rcases honestPreviousHead_voterCandidateMem_or_preceq_root_after_GST_named
            S adm hcom hbelow hrec hdelay hpost hsDead hvoteHor hw hu hBu
            (by
              simpa only [Internal.NamedRecoveryRead.voteDutyRead,
                NamedActionReads.confirmationReadAt,
                NamedActionReads.confirmationReadFrom,
                Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
                Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
                Proofs.Optimistic.toHealing_slot, Proofs.Optimistic.voteDutyStore_slot,
                Proofs.Optimistic.slotOf_vote_time] using hprocessed) with
          hcandidate | hBroot'
        · have hadoption := nextVoteAdoption_of_recovery_after_gst
            S adm hv hw hpostProposal hhor hrootBare hanchorB hcandidate
          exact preceq_voterHeadAt_of_namedNextVoteAdoption S
            hgenuine'.eligible hadoption
        · exact Block.preceq_trans hBroot'
            (fgRoot_preceq_voterHeadAt S rho w (s + 1))
      · exact Block.preceq_trans hBanchor
          (voterAnchorAt_preceq_voterHeadAt S rho w (s + 1))
    · exact Block.preceq_trans hBroot
        (fgRoot_preceq_voterHeadAt S rho w (s + 1))
  intro d hd hdhor
  exact allHonestVoterHeads_persist_after_SG_healing_named
    S adm hcom hbelow hrec hdelay hpost
      (hsTwo.trans (Nat.le_succ s)) hbase hd hdhor

#print axioms allHonestHeads_succ_of_voterAnchorCompatible_after_GST_named
#print axioms actionSGBlock_preceq_voterHeadAt_after_GST
#print axioms nextVoteDutyAnchor_compatible_of_honestPreviousHead_after_SG_healing_named
#print axioms allHonestVoterHeads_persist_after_SG_healing_named
#print axioms genuineConfirmationWith_preceq_laterVoterHeads_after_GST

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
