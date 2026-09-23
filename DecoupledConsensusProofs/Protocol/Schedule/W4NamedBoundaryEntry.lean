module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.W4NamedBoundaryConfirmation
public import DecoupledConsensusProofs.Protocol.Schedule.W4BaseFold
public import DecoupledConsensusProofs.Protocol.Schedule.W4BoundaryProposalN
public import DecoupledConsensusProofs.Protocol.Schedule.W4ExecState

@[expose] public section

/-!
# The first named slot entry after the boundary

The Byzantine proposer does not move the boundary endpoint. The named
history can pass through that proposal without an erased base height.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The named entry constructor uses only the next vote horizon from its
old ordinary window-data input. -/
theorem MovingSlotPreEntryN.toEntryN_of_voteHorizon
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hpre : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End)
    (hvoteHor : Protocol.vote_time S.E (c + 1) ≤ rho.horizon)
    (hheadEq : S.E.proposer (c + 1) ∈ rho.honest →
      ∀ w ∈ rho.honest, voteDutyHead S rho w (c + 1) = End)
    (hbyz : S.E.proposer (c + 1) ∉ rho.honest → End = Prev)
    (hprevVotes : NamedHonestVotesCone S rho (c + 1)
      (fun X => Block.Preceq Prev X))
    (hconf : ∀ w ∈ rho.honest, ∀ D : Block V,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho w c).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho w c) c D →
      Block.compatible D End = true) :
    MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End := by
  have hvotes : NamedHonestVotesCone S rho (c + 1)
      (fun X => Block.Preceq End X) := by
    by_cases hprop : S.E.proposer (c + 1) ∈ rho.honest
    · intro u hu huc
      obtain ⟨C, hC, hCrun, hCemit⟩ :=
        w4d1_baseCoreVoterHeadEmits S adm.toNamedAdmissibleCore hu
          (s := c + 1) (Nat.succ_pos c) huc hvoteHor
      have hCEnd : C.erase = End := hC.trans (by
        simpa only [voteDutyHead] using (hheadEq hprop u hu))
      exact ⟨C, by rw [hCEnd]; exact Block.preceq_self _, hCrun, hCemit⟩
    · rw [hbyz hprop]
      exact hprevVotes
  refine
    { startTime := hpre.startTime
      prevEndpoint := hpre.prevEndpoint
      prevVotes := hpre.prevVotes
      votes := hvotes
      headEq := hheadEq
      confCompatible := ?_ }
  intro w hw D hD
  simpa only [Nat.add_sub_cancel] using hconf w hw D hD

/-- A Byzantine proposal keeps the named boundary endpoint unchanged. -/
theorem w4NamedBoundaryHistoryN_toProposal_byzantine
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {D : NamedBlock V} {carrier : V} {M0 : Height}
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    (hboundary : W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 D)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q + 1) ≤ rho.horizon)
    (hbyz : S.E.proposer (S.hc.opening_slot q + 3) ∉ rho.honest) :
    ∃ EndAt' : Nat → Block V,
      MovingFrontierChainStateN S rho
        (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
        (strictEventIndex rho
          (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)))
        (inclusiveEventIndex rho
          (Protocol.proposal_time S.E (S.hc.opening_slot q + 3))) EndAt' ∧
      EndAt' (strictEventIndex rho
        (Protocol.proposal_time S.E (S.hc.opening_slot q + 3))) =
          D.erase ∧
      EndAt' (inclusiveEventIndex rho
        (Protocol.proposal_time S.E (S.hc.opening_slot q + 3))) =
          D.erase := by
  let s := S.hc.opening_slot q + 2
  obtain ⟨EndAt, hstate, hconstAll⟩ :=
    w4NamedBoundaryHistoryN_toFreeze S adm hhandoff hboundary hhor
  have hconst : EndAt
      (inclusiveEventIndex rho (Protocol.view_freeze S.E s)) =
        D.erase :=
    hconstAll _ (Nat.le_refl _)
  have hfreezeNormal :
      Protocol.view_freeze S.E s = (4 * (s : Time) + 3) * S.E.Δ := by
    unfold Protocol.view_freeze Env.t slotStart
    ring
  have hproposalNormal :
      Protocol.proposal_time S.E (s + 1) =
        (4 * ((s + 1 : Slot) : Time) + 0) * S.E.Δ := by
    unfold Protocol.proposal_time Env.t slotStart
    ring
  have htime : Protocol.view_freeze S.E s <
      Protocol.proposal_time S.E (s + 1) := by
    rw [hfreezeNormal, hproposalNormal]
    refine Int.mul_lt_mul_of_pos_right ?_ S.E.Δ_pos
    have hcast : ((s + 1 : Nat) : Int) = (s : Int) + 1 := by
      push_cast
      ring
    rw [hcast]
    change 4 * (s : Time) + 3 < 4 * ((s : Time) + 1) + 0
    linarith
  have hfreezeStrict :
      inclusiveEventIndex rho (Protocol.view_freeze S.E s) ≤
      strictEventIndex rho (Protocol.proposal_time S.E (s + 1)) := by
    unfold inclusiveEventIndex strictEventIndex
    exact (List.monotone_filter_right rho.events (fun e he => by
      simp only [decide_eq_true_eq] at he ⊢
      exact lt_of_le_of_lt he htime)).length_le
  have hfreezeIncl :
      inclusiveEventIndex rho (Protocol.view_freeze S.E s) ≤
      inclusiveEventIndex rho (Protocol.proposal_time S.E (s + 1)) :=
    hfreezeStrict.trans (strictEventIndex_le_inclusiveEventIndex rho _)
  obtain ⟨EndAt', hlow, hhigh, hstate'⟩ :=
    hstate.through_constantEndpoint_named_public S
      (by rw [hconst]; exact Block.preceq_self _)
      ⟨D, rfl, hboundary.run⟩ hfreezeIncl (by
        intro j hj hjn
        refine movingSlotWindowTail_eventFacts_named_public S adm
          (Block.preceq_self D.erase) ?_ hj hjn
        intro u hu hev heq
        exfalso
        apply hbyz
        change S.E.proposer (s + 1) ∈ rho.honest
        rw [heq, S.node_val_index u]
        exact hu)
  refine ⟨EndAt', ?_, ?_, ?_⟩
  · simpa only [s, Nat.add_assoc] using hstate'
  · rcases Nat.eq_or_lt_of_le hfreezeStrict with heq | hlt
    · rw [← heq, hlow _ (Nat.le_refl _), hconst]
    · exact hhigh _ hlt
  · rcases Nat.eq_or_lt_of_le hfreezeIncl with heq | hlt
    · rw [← heq, hlow _ (Nat.le_refl _), hconst]
    · exact hhigh _ hlt

/-- The actual named pre-entry of the first Byzantine base slot. -/
theorem w4NamedBoundaryPreEntryN_byzantine
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {D : NamedBlock V} {carrier : V} {M0 : Height}
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    (hboundary : W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 D)
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon)
    (hbyz : S.E.proposer (S.hc.opening_slot q + 3) ∉ rho.honest) :
    MovingSlotPreEntryN S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
      (S.hc.opening_slot q + 3) D.erase D.erase := by
  have hconfHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q + 1) ≤ rho.horizon := by
    have hslots : S.hc.opening_slot q + 1 ≤
        S.hc.opening_slot q + 3 :=
      Nat.add_le_add_left (by decide : 1 ≤ 3) _
    exact (Int.add_le_add_right
      (Protocol.proposal_time_mono S.E hslots) _).trans
        hbaseTiming.2.2
  have hvoteHor : Protocol.vote_time S.E
      (S.hc.opening_slot q + 2) ≤ rho.horizon :=
    (Protocol.vote_time_mono_slots S.E
      (Nat.le_succ _)).trans
      ((Protocol.vote_time_le_confirmation_time S.E
        (S.hc.opening_slot q + 3)).trans hbaseTiming.2.2)
  have hcone : NamedHonestVotesCone S rho
      (S.hc.opening_slot q + 2)
      (fun X => Block.Preceq D.erase X) :=
    hhandoff.honestVotesCone_two_after adm hvoteHor
  have hhistory :=
    w4NamedBoundaryHistoryN_toProposal_byzantine S adm
      hhandoff hboundary hconfHor hbyz
  refine { startTime := ?_, prevEndpoint := hhistory, prevVotes := ?_ }
  · simpa only [Nat.add_assoc] using
      w4d1_support_cutoff_le_proposal_time_two S.E
        (S.hc.opening_slot q + 1)
  · simpa only [Nat.add_sub_cancel] using hcone

/-- Named vote inputs from a carrier ceiling at the base cutoff. The
initial cutoff need not precede the previous round's action. -/
theorem MovingSlotPreEntryN.voteInputs_of_ceiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) :
    GoldfishConeVoteInputs' S rho c Prev w := by
  have hprevVotes : NamedHonestVotesCone S rho c
      (fun X => Block.Preceq Prev X) := by
    simpa only [Nat.add_sub_cancel] using hentry.prevVotes
  have hrootRaw := hentry.voteRoot_preceq_prev S adm hfb hw
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG)
        Prev := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hrootRaw
  have hcutHor : Protocol.support_cutoff S.E c ≤ rho.horizon :=
    (support_cutoff_le_confirmation_time S.E c).trans hslotHor
  have hvoteHorSucc : Protocol.vote_time S.E (c + 1) ≤
      rho.horizon := by
    have hbefore : Protocol.vote_time S.E (c + 1) ≤
        Protocol.confirmation_time S.E c := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ]
      simp only [Protocol.vote_time, Protocol.support_cutoff]
      have h : ∀ x d : Int, 0 < d → x + d ≤ x + 2 * d := by
        intro x d hd
        omega
      exact h _ _ S.E.Δ_pos
    exact hbefore.trans hslotHor
  have havailable := honestHeadsAvailableBefore_of_namedPostHealingCone
    S adm hw hpostVote hcutHor hroot hprevVotes
  have hpositive : 0 < ((S.E.committee c) ∩ rho.honest).card := by
    have hcc := hcom c
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  obtain ⟨X, hPrevX, hXrun, hXemit⟩ :=
    hprevVotes x (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hx).1
  have hhead : Proofs.Optimistic.HonestHead S rho c X.erase :=
    ⟨x, (Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hx).1,
      ⟨X, rfl, hXrun⟩, hXemit⟩
  have hprocessed := voterProcessed_of_availableBefore_of_honestHead
    S adm havailable hhead (Block.preceq_self X.erase)
  obtain ⟨E, hE, hErun⟩ := hentry.prevRunAt S
  have hbandE := hentry.voteFrontier_sub_one_le_prevHeight_named
    S adm hfb hw hE hErun
  have hnamedEX : NamedBlock.Preceq E X :=
    namedPreceq_of_runBlock_erase_preceq adm hErun hXrun
      (by rw [hE]; exact hPrevX)
  have hbandX : (rho.storeBeforeTime S w
      (Protocol.vote_time S.E (c + 1))).core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg X).h :=
    hbandE.trans (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hnamedEX)
  have hmax : (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).h_max ≤
      (Protocol.derive_named S.E S.cfg X).h + 1 := by
    have hle := Nat.sub_le_iff_le_add.mp hbandX
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hle
  have hmemT : Prev ∈ (rho.storeBeforeTime S w
      (Protocol.vote_time S.E (c + 1))).T :=
    mem_storeBeforeTime_of_cone S adm hcom havailable
      (Proofs.Optimistic.support_cutoff_le_vote_time_succ S.E c) hprevVotes
  have hbodies : E ∈ (rho.storeBeforeTime S w
      (Protocol.vote_time S.E (c + 1))).bodies :=
    mem_bodies_of_mem_T S adm hw hErun (by rw [hE]; exact hmemT)
  have hfilteredRaw := storeBeforeTime_mem_filtered_of_band S adm hbodies
    (by rw [hE]; exact hrootRaw) hbandE
  have hfiltered : Prev ∈ Protocol.get_filtered_block_tree
      (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG := by
    rw [← hE]
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hfilteredRaw
  have hanchorP :=
    w4cx_movingSlotPreEntryN_voterAnchorAt_preceq_prev_of_ceiling
      S adm hcom hfb hentry hround hupper hpostAction hcut hpostVote
      hcutHor hvoteHorSucc hw
  refine ⟨Or.inl ⟨?_, ?_, ?_⟩,
    Block.compatible_of_preceq_common hanchorP
      (Block.preceq_self Prev)⟩
  · simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hroot
  · exact namedAncestorCandidate_of_processedDescendant_and_hMax_core
      S adm.toNamedAdmissibleCore hw hprocessed hXrun hPrevX hfiltered hmax
  · intro D hAD _hAne hDPrev _hDne
    have hrootAnchor : Block.Preceq
        (Protocol.get_fg_root
          (voteDutyRead S rho w (c + 1)).st.core.toHealing.toFG)
        (voterAnchorAt S rho w (c + 1)) := by
      rcases voterAnchorAt_cases S rho w (c + 1) with
        hfg | ⟨root, A, _hframe, hactive, hanchor⟩
      · rw [hfg]
        exact Block.preceq_self _
      · rw [hanchor]
        exact Proofs.Records.preceq_get_fg_root_of_mem_filtered
          (Proofs.NamedProposalParent.activePrefix_mem _ root A hactive)
    have hrootDRaw : Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S w
            (Protocol.vote_time S.E (c + 1))).toHealing.toFG) D := by
      refine Block.preceq_trans ?_ hAD
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime] using
        hrootAnchor
    have hpc : ParentClosed (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (c + 1))).core := by
      simpa only [Run.storeBeforeTime] using
        Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
          (Protocol.vote_time S.E (c + 1)) w
    have hDmemT : D ∈ (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (c + 1))).core.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
        D Prev hmemT hDPrev
    obtain ⟨Dn, hDnerase, hDnrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        adm.toNamedScheduleWellFormed hw
        (Protocol.vote_time S.E (c + 1))
        (by simpa only [Run.storeBeforeTime] using hDmemT)
    have hDfilteredRaw := storeBeforeTime_path_mem_filtered_of_band S adm
      hbodies hbandE (by rw [hDnerase]; exact hrootDRaw)
      (by rw [hDnerase, hE]; exact hDPrev)
    have hDfiltered : D ∈ Protocol.get_filtered_block_tree
        (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG := by
      rw [← hDnerase]
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hDfilteredRaw
    exact namedAncestorCandidate_of_processedDescendant_and_hMax_core
      S adm.toNamedAdmissibleCore hw hprocessed hXrun
      (Block.preceq_trans hDPrev hPrevX) hDfiltered hmax

/-- The next named vote cone from the same local carrier ceiling. -/
theorem MovingSlotPreEntryN.votesCone_prev_of_ceiling
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
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon) :
    NamedHonestVotesCone S rho (c + 1)
      (fun X => Block.Preceq Prev X) := by
  have hprevVotes : NamedHonestVotesCone S rho c
      (fun X => Block.Preceq Prev X) := by
    simpa only [Nat.add_sub_cancel] using hentry.prevVotes
  have hvoteHorSucc : Protocol.vote_time S.E (c + 1) ≤
      rho.horizon := by
    have hbefore : Protocol.vote_time S.E (c + 1) ≤
        Protocol.confirmation_time S.E c := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ]
      simp only [Protocol.vote_time, Protocol.support_cutoff]
      have h : ∀ x d : Int, 0 < d → x + d ≤ x + 2 * d := by
        intro x d hd
        omega
      exact h _ _ S.E.Δ_pos
    exact hbefore.trans hslotHor
  have hstep : ∀ u ∈ rho.honest,
      Block.Preceq Prev (voteDutyHead S rho u (c + 1)) := by
    intro u hu
    exact goldfishCone_step' S adm hcom hc hpostVote hslotHor
      hprevVotes hu
      (hentry.voteInputs_of_ceiling S adm hcom hfb hround hupper
        hpostAction hcut hpostVote hslotHor hu)
  intro u hu huc
  obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
    voteDutyHead_runBlock_and_emits S adm (Nat.succ_pos c)
      hvoteHorSucc hu huc
  exact ⟨X, by simpa only [hXerase] using hstep u hu, hXrun, hXemit⟩

/-- The complete first N fold when the base slot proposer is Byzantine. -/
theorem w4MovingSlotFoldAtN_boundary_byzantine
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} {D : NamedBlock V} {carrier : V} {M0 : Height}
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    (hboundary : W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 D)
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon)
    (hbyz : S.E.proposer (S.hc.opening_slot q + 3) ∉ rho.honest) :
    ∃ F : Slot → Block V, ∃ End : Block V,
      MovingSlotFoldAtN S rho
        (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
        (S.hc.opening_slot q + 3) (S.hc.opening_slot q + 3) F End ∧
      F (S.hc.opening_slot q + 3) = D.erase := by
  let o := S.hc.opening_slot q
  let R0 := S.hc.round_of (o + 3)
  let r0 := R0 - 1
  have hR0pos : 0 < R0 := by
    simpa only [R0, o] using hbaseTiming.1
  have hround : S.hc.round_of (o + 3) = r0 + 1 := by
    simpa only [R0, r0] using (Nat.succ_pred_eq_of_pos hR0pos).symm
  have hR0q1 : R0 ≤ q + 1 := by
    have hRpos : 0 < S.hc.R :=
      lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
    dsimp only [R0, o]
    simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
    rw [show q * S.hc.R + 3 = 3 + S.hc.R * q by ring,
      Nat.add_mul_div_left _ _ hRpos]
    have hdiv : 3 / S.hc.R ≤ 1 := by
      have hlt : 3 / S.hc.R < 2 := by
        rw [Nat.div_lt_iff_lt_mul hRpos]
        exact lt_of_lt_of_le (by decide : 3 < 4)
          (by simpa only [Nat.mul_comm] using
            Nat.mul_le_mul_left 2 S.hc.R_ge_two)
      exact Nat.le_of_lt_succ hlt
    simpa only [Nat.add_comm] using Nat.add_le_add_left hdiv q
  have hr0q : r0 ≤ q := by
    dsimp only [r0]
    exact Nat.lt_succ_iff.mp
      ((Nat.sub_lt hR0pos (by decide : 0 < 1)).trans_le hR0q1)
  have hpostAction : S.E.t_GST ≤ S.a r0 := by
    simpa only [r0, R0, o] using hbaseTiming.2.1
  have hactionProposal : S.a q ≤
      Protocol.proposal_time S.E (o + 2) := by
    have ha : S.a q =
        (4 * ((o : Slot) : Time) + 6) * S.E.Δ := by
      unfold Setup.a Protocol.HealConfig.a slotStart
      ring
    have hp : Protocol.proposal_time S.E (o + 2) =
        (4 * (((o + 2 : Slot) : Time)) + 0) * S.E.Δ := by
      unfold Protocol.proposal_time Env.t slotStart
      ring
    rw [ha, hp]
    apply Int.mul_le_mul_of_nonneg_right
    · push_cast
      omega
    · exact S.E.Δ_pos.le
  have hpostProp : S.E.t_GST ≤
      Protocol.proposal_time S.E (o + 2) :=
    hpostAction.trans ((Assembly.a_mono S hr0q).trans hactionProposal)
  have hpostVote : S.E.t_GST ≤
      Protocol.vote_time S.E (o + 2) :=
    hpostProp.trans (Protocol.proposal_time_lt_vote_time S.E _).le
  have hgammaConf : S.hc.Γ_neg1 S.E.Δ R0 ≤
      Protocol.confirmation_time S.E (o + 3) := by
    have hg : S.hc.Γ_neg1 S.E.Δ R0 =
        (4 * ((S.hc.opening_slot R0 : Slot) : Time) - 1) *
          S.E.Δ := by
      unfold Protocol.HealConfig.Γ_neg1 slotStart
      ring
    have hc : Protocol.confirmation_time S.E (o + 3) =
        (4 * (((o + 3 : Slot) : Time)) + 6) * S.E.Δ := by
      unfold Protocol.confirmation_time Env.t slotStart
      ring
    rw [hg, hc]
    apply Int.mul_le_mul_of_nonneg_right
    · have hopen : S.hc.opening_slot R0 ≤ o + 3 := by
        dsimp only [R0]
        simp only [Protocol.HealConfig.opening_slot,
          Protocol.HealConfig.round_of]
        exact Nat.div_mul_le_self (o + 3) S.hc.R
      have hcast : ((S.hc.opening_slot R0 : Slot) : Time) ≤
          ((o + 3 : Slot) : Time) := by
        exact_mod_cast hopen
      linarith
    · exact S.E.Δ_pos.le
  have hcut : S.hc.Γ_neg1 S.E.Δ (r0 + 1) ≤
      rho.horizon := by
    rw [← hround]
    exact hgammaConf.trans (by simpa only [o] using hbaseTiming.2.2)
  have hslotHor : Protocol.confirmation_time S.E (o + 2) ≤
      rho.horizon := by
    have hslot : o + 2 ≤ o + 3 := Nat.le_succ _
    exact (Int.add_le_add_right
      (Protocol.proposal_time_mono S.E hslot) _).trans
        (by simpa only [o] using hbaseTiming.2.2)
  have hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r0) D.erase :=
    hboundary.carrierCeiling r0 (by simpa only [o] using hround)
  have hpre : MovingSlotPreEntryN S rho
      (Protocol.support_cutoff S.E (o + 2)) M0
      (o + 3) D.erase D.erase :=
    w4NamedBoundaryPreEntryN_byzantine S adm
      hhandoff hboundary hbaseTiming hbyz
  have hcone := hpre.votesCone_prev_of_ceiling S adm hcom hfb
    (Nat.succ_pos (o + 1)) hround hupper hpostAction hcut
      hpostVote hslotHor
  have hcompat := hpre.confCompatible_byzantine_of_ceiling
    S adm hcom hfb (Nat.succ_pos (o + 1))
      hround hupper hpostAction hcut hpostVote hslotHor
  have hvoteHor : Protocol.vote_time S.E (o + 3) ≤
      rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E _).trans
      (by simpa only [o] using hbaseTiming.2.2)
  have hentry := hpre.toEntryN_of_voteHorizon S adm hvoteHor
    (fun hp => (hbyz hp).elim) (fun _ => rfl) hcone hcompat
  have hfold := movingSlotFoldAtN_of_entry S hentry
    (fun hp => (hbyz hp).elim) (fun hp => (hbyz hp).elim)
  exact ⟨fun _ => D.erase, D.erase, hfold, rfl⟩

#check MovingSlotPreEntryN.toEntryN_of_voteHorizon
#print axioms MovingSlotPreEntryN.toEntryN_of_voteHorizon
#check w4NamedBoundaryHistoryN_toProposal_byzantine
#print axioms w4NamedBoundaryHistoryN_toProposal_byzantine
#check w4NamedBoundaryPreEntryN_byzantine
#print axioms w4NamedBoundaryPreEntryN_byzantine
#check MovingSlotPreEntryN.voteInputs_of_ceiling
#print axioms MovingSlotPreEntryN.voteInputs_of_ceiling
#check MovingSlotPreEntryN.votesCone_prev_of_ceiling
#print axioms MovingSlotPreEntryN.votesCone_prev_of_ceiling
#check w4MovingSlotFoldAtN_boundary_byzantine
#print axioms w4MovingSlotFoldAtN_boundary_byzantine

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
