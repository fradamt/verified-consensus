module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.FGSafetyRootNamed
public import DecoupledConsensusProofs.Protocol.Grades.PreparedFrameAfterDeadline
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot

@[expose] public section

/-!
# Prepared first-interior anchor compatibility

The three prepared selector tiers are closed separately and assembled into
the restated  theorem with the delivery-horizon premise.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedRecoveryRead
open Protocol Proofs.Optimistic Proofs.HealingLemmas DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem voteTime_lt_nextProposal (E : Env V) (s : Slot) :
    Protocol.vote_time E s < Protocol.proposal_time E (s + 1) := by
  simp only [Protocol.vote_time, Protocol.proposal_time, Env.t, slotStart]
  push_cast
  nlinarith [E.Δ_pos]


/-- Tier 2 of: a sender-selected Q2 is compatible with the receiver's
prepared anchor at every interior duty of the round. -/
theorem voterAnchorAt_compatible_actionSGBlock_selectedQ2_after_GST
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : S.a (c + 1) ≤ rho.horizon)
    {d : Slot} (hdlo : S.hc.opening_slot (c + 1) + 1 ≤ d)
    (hdhi : d < S.hc.opening_slot (c + 1 + 1))
    (hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {Q : Block V}
    (hQ : nodeQ2 S (actionReadAt S rho p (c + 1)) (c + 1) = some Q)
    (hsg : actionSGBlockAt S rho p (c + 1) = Q) :
    Block.compatible (voterAnchorAt S rho w d)
      (actionSGBlockAt S rho p (c + 1)) = true := by
  have hround : S.hc.round_of d = c + 1 :=
    round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hdlo hdhi
  have hnextFrame : Protocol.vote_time S.E d ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (c + 1 + 1) := by
    have hstep : Protocol.proposal_time S.E (d + 1) ≤
        Protocol.proposal_time S.E (S.hc.opening_slot (c + 1 + 1)) :=
      proposal_time_mono S.E (Nat.succ_le_of_lt hdhi)
    exact (voteTime_lt_nextProposal S.E d).le.trans hstep
  have hroundDead : rGST + 2 ≤ c + 1 := by
    have hbase : rGST + 1 ≤
        fgSafetyProgressDeadline S rho rGST gap delayExtra := by
      unfold fgSafetyProgressDeadline
      exact Nat.le_add_right _ _
    exact Nat.succ_le_succ (hbase.trans hc)
  have hgstLagged : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ (rGST + 2) :=
    gstLagged_le_Γ_neg1_of_gst_le_a S rGST hpost
  have ready : GradeRoundReady S rho (c + 1) :=
    gradeRoundReady_of_action_horizon S hgstLagged hroundDead hhor
  rcases voterAnchorAt_cases S rho w d with hroot | hactive
  · rw [hroot]
    have hdeadlineVote :
        S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤
          Protocol.vote_time S.E d := by
      exact ((action_strictMono S).monotone hc).trans
        ((a_le_Γ_neg1_succ S.hc S.E.Δ_pos c).trans
          ((Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (c + 1)).le.trans
            (Γ_0_le_vote_time_of_round_eq S hround)))
    have hnext : Protocol.vote_time S.E d ≤ S.a (c + 1 + 1) :=
      (vote_time_mono_slots S.E (Nat.le_of_lt hdhi)).trans
        (opening_vote_time_lt_action S (c + 1 + 1)).le
    have hcompat := fgRoot_compatible_actionSGBlock_at_read_after_GST
      S adm hcom hbelow hrec hdelay hpost (hc.trans (Nat.le_succ c)) hhor
        hdeadlineVote hvoteHor hnext hw hp
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime] using hcompat
  · obtain ⟨root, L, hframe, hactive, hanchor⟩ := hactive
    have hroundRead : S.hc.round_of (voteDutyRead S rho w d).st.core.s = c + 1 := by
      simpa only [Proofs.Optimistic.voteDutyRead_slot] using hround
    rw [hroundRead] at hframe
    obtain ⟨-, hLgrade⟩ := fixedRoot_activeVoterAnchor_g1_data
      S adm (Nat.succ_pos c) ((Nat.le_succ _).trans hdlo) hround
        hnextFrame hvoteHor hw hframe hactive
    have hguard := actionQ2_crossReaderBodyReadyGuard_history
      S adm hbelow (Nat.succ_pos c) ready hp w hw Q hQ
    have hQgrade := selectedG2_G1_at_read_after_cutoff
      S adm hbelow ready hhor hp hw hQ hguard
    rw [hanchor, hsg]
    exact relativeSeed_sameReaderG1_compatible
      S rho (c + 1) w hLgrade hQgrade

/-- At the first interior duty, the delivery-horizon premise is exactly the
round-action horizon. -/
theorem firstInterior_vote_add_delta_le_horizon
    (S : Setup V) {rho : Run V} {c : Round}
    (hhor : S.a (c + 1) ≤ rho.horizon) :
    Protocol.vote_time S.E (S.hc.opening_slot (c + 1) + 1) + S.E.Δ ≤
      rho.horizon := by
  simpa only [vote_time_succ_add_delta_eq_confirmation_time,
    opening_confirmation_time_eq_action] using hhor


/-- Tier 3 of: the receiver's prepared anchor and the sender's
action-time FG root are prefixes of the same prepared vote head. -/
theorem voterAnchorAt_compatible_actionFGRoot_after_GST
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : S.a (c + 1) ≤ rho.horizon)
    {d : Slot} (hdlo : S.hc.opening_slot (c + 1) + 1 ≤ d)
    (hshor : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest) :
    Block.compatible (voterAnchorAt S rho w d)
      (Protocol.get_fg_root
        (actionStoreAt S rho p (c + 1)).st.core.toHealing.toFG) = true := by
  have hdeadlineRead :
      S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤
        S.a (c + 1) :=
    (action_strictMono S).monotone (hc.trans (Nat.le_succ c))
  have hslotDead : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ d :=
    (Nat.add_le_add_right
      (Nat.mul_le_mul_right S.hc.R (hc.trans (Nat.le_succ c))) 1).trans hdlo
  have hnextSlot : S.hc.opening_slot (c + 1) + 2 ≤ d + 1 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      (Nat.add_le_add_right hdlo 1)
  have hnext : S.a (c + 1) ≤ Protocol.vote_time S.E (d + 1) :=
    (action_lt_vote_time_two_after S (c + 1)).le.trans
      (vote_time_mono_slots S.E hnextSlot)
  have hrootHead := fgRoot_preceq_previousHead_after_GST
    S adm hcom hbelow hrec hdelay hpost hdeadlineRead hhor hslotDead
      hnext hshor hp hw
  rw [← actionStoreAt_fgRoot_eq_storeBeforeTime] at hrootHead
  exact Block.compatible_of_preceq_common
    (voterAnchorAt_preceq_voterHeadAt S rho w d) hrootHead


/-- Tier 1 of: a clear prepared action target is compatible with the
receiver's prepared anchor. -/
theorem voterAnchorAt_compatible_actionSGBlock_clear_after_GST
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : S.a (c + 1) ≤ rho.horizon)
    {d : Slot} (hdlo : S.hc.opening_slot (c + 1) + 1 ≤ d)
    (hdhi : d < S.hc.opening_slot (c + 1 + 1))
    (hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon)
    (hshor : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {B : Block V}
    (hclear : PhaseGrades.nodeClear S (actionReadAt S rho p (c + 1))
      (c + 1) B = true)
    (hsg : actionSGBlockAt S rho p (c + 1) = B) :
    Block.compatible (voterAnchorAt S rho w d)
      (actionSGBlockAt S rho p (c + 1)) = true := by
  have hround : S.hc.round_of d = c + 1 :=
    round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hdlo hdhi
  have hnextFrame : Protocol.vote_time S.E d ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (c + 1 + 1) := by
    have hstep : Protocol.proposal_time S.E (d + 1) ≤
        Protocol.proposal_time S.E (S.hc.opening_slot (c + 1 + 1)) :=
      proposal_time_mono S.E (Nat.succ_le_of_lt hdhi)
    exact (voteTime_lt_nextProposal S.E d).le.trans hstep
  have hGSTdead : rGST ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hpostc := hpost.trans
    ((action_strictMono S).monotone (hGSTdead.trans hc))
  have hroundDead : rGST + 2 ≤ c + 1 := by
    have hbase : rGST + 1 ≤
        fgSafetyProgressDeadline S rho rGST gap delayExtra := by
      unfold fgSafetyProgressDeadline
      exact Nat.le_add_right _ _
    exact Nat.succ_le_succ (hbase.trans hc)
  have hgstLagged : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ (rGST + 2) :=
    gstLagged_le_Γ_neg1_of_gst_le_a S rGST hpost
  have ready : GradeRoundReady S rho (c + 1) :=
    gradeRoundReady_of_action_horizon S hgstLagged hroundDead hhor
  rcases voterAnchorAt_cases S rho w d with hroot | hactive
  · rw [hroot]
    have hdeadlineVote :
        S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤
          Protocol.vote_time S.E d := by
      exact ((action_strictMono S).monotone hc).trans
        ((a_le_Γ_neg1_succ S.hc S.E.Δ_pos c).trans
          ((Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (c + 1)).le.trans
            (Γ_0_le_vote_time_of_round_eq S hround)))
    have hnext : Protocol.vote_time S.E d ≤ S.a (c + 1 + 1) :=
      (vote_time_mono_slots S.E (Nat.le_of_lt hdhi)).trans
        (opening_vote_time_lt_action S (c + 1 + 1)).le
    have hcompat := fgRoot_compatible_actionSGBlock_at_read_after_GST
      S adm hcom hbelow hrec hdelay hpost (hc.trans (Nat.le_succ c)) hhor
        hdeadlineVote hvoteHor hnext hw hp
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime] using hcompat
  · obtain ⟨root, L, hframe, hactive, hanchor⟩ := hactive
    have hroundRead : S.hc.round_of (voteDutyRead S rho w d).st.core.s = c + 1 := by
      simpa only [Proofs.Optimistic.voteDutyRead_slot] using hround
    rw [hroundRead] at hframe
    obtain ⟨-, hLgrade⟩ := fixedRoot_activeVoterAnchor_g1_data
      S adm (Nat.succ_pos c) ((Nat.le_succ _).trans hdlo) hround
        hnextFrame hvoteHor hw hframe hactive
    have hrootCompat := voterAnchorAt_compatible_actionFGRoot_after_GST
      S adm hcom hbelow hrec hdelay hpost hc hhor hdlo hshor hp hw
    rw [hanchor] at hrootCompat
    rcases (show Block.Preceq L
        (Protocol.get_fg_root
          (actionStoreAt S rho p (c + 1)).st.core.toHealing.toFG) ∨
        Block.Preceq
          (Protocol.get_fg_root
            (actionStoreAt S rho p (c + 1)).st.core.toHealing.toFG) L by
      simpa only [Block.compatible, Bool.or_eq_true] using hrootCompat) with
      hLroot | hrootL
    · rw [hanchor]
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inl (Block.preceq_trans hLroot
        (actionFGRoot_preceq_actionSGBlockAt S rho p (c + 1)))
    · have hFroot : Block.Preceq
          (actionStoreAt S rho p (c + 1)).st.core.F
          (Protocol.get_fg_root
            (actionStoreAt S rho p (c + 1)).st.core.toHealing.toFG) := by
        change Block.Preceq
          (rho.storeBeforeTime S p (S.a (c + 1))).core.F
          (Protocol.get_fg_root
            (rho.storeBeforeTime S p (S.a (c + 1))).core.toHealing.toFG)
        exact finalizedRoot_preceq_fgRoot S adm
      have hFL : Block.Preceq
          (actionReadAt S rho p (c + 1)).st.core.F L :=
        Block.preceq_trans hFroot hrootL
      have hgstG1 : S.E.t_GST ≤
          DecoupledConsensusModel.Protocol.early S.E S.hc (c + 1) .g1 :=
        ready.1.trans (by
          simp only [DecoupledConsensusModel.Protocol.early,
            DecoupledConsensusModel.Protocol.Phase.earlyOffset]
          linarith [S.E.Δ_pos])
      have hsb : Internal.NamedOutageEntry.SlashableBound S rho :=
        slashableBound_of_admissible_belowOneThird S adm hbelow
      have hF0L : Block.Preceq
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc (c + 1) .g0) p).st.core.F L := by
        exact Block.preceq_trans
          (NamedOutageClosure.incl_strict_F_mono S rho
            adm.toNamedScheduleWellFormed p
              (FrameForward.domain_le_a S (c + 1) .g0)) hFL
      have hforward : ∀ sender vote key H,
          vote ∈ DecoupledConsensusModel.Protocol.interpretedInputs
            (PhaseGrades.readAt S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc (c + 1) .g1) w).st.core.toHealing.gradeView
            (PhaseGrades.readAt S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc (c + 1) .g1) w).st.core.F
            S.hc.η_SG (c + 1)
              (DecoupledConsensusModel.Protocol.early S.E S.hc (c + 1) .g1) sender →
          DecoupledConsensusModel.Protocol.localCovers
            (PhaseGrades.readAt S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc (c + 1) .g1) w).st.core.toHealing.gradeView
            vote.confirmed L = true →
          vote.confirmed = some key →
          Block.find?
            (PhaseGrades.readAt S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc (c + 1) .g1) w).st.core.toHealing.gradeView.T
            key = some H →
          Block.Preceq
            (PhaseGrades.readAt S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc (c + 1) .g0) p).st.core.F H := by
        intro sender vote key H _ hcover hconf hfind
        have hLH : Block.Preceq L H := by
          unfold DecoupledConsensusModel.Protocol.localCovers Protocol.head_covers at hcover
          simp only [hconf] at hcover
          rw [hfind] at hcover
          exact hcover
        exact Block.preceq_trans hF0L hLH
      have hfinalized := g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relay
        S adm hsb hgstG1 ready.2 hw hp hforward
      have hguard := g1G0CrossReaderBodyReadyGuard_of_finalizedBelow
        S adm.toNamedAdmissibleCore (Nat.succ_pos c) hgstG1 ready.2
          hw hp hfinalized
      have hG0 := storeGrade_g0_of_storeGrade_g1_cross_reader
        S rho adm.toNamedAdmissibleCore (c + 1)
          (g1G0TwoCutoffDelivery_of_core S adm.toNamedAdmissibleCore hgstG1)
          ready.2 w p hw hp L hLgrade hguard
      rw [hanchor, hsg]
      exact relativeG0_compatible_clearSource_of_finalizedPreceq_history
        S adm (Nat.succ_pos c) hhor hp
          (storeGrade_g0_mem_domainTree S rho hG0) hG0 hFL hclear


/--  item 4': the prepared first-interior anchor is compatible with every
honest prepared SG action target when the duty's delivery interval is inside
the run horizon. -/
theorem voterAnchorAt_firstInterior_compatible_actionSGBlock_after_GST
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : S.a (c + 1) ≤ rho.horizon)
    {d : Slot} (hdlo : S.hc.opening_slot (c + 1) + 1 ≤ d)
    (hdhi : d < S.hc.opening_slot (c + 1 + 1))
    (hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon)
    (hshor : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest) :
    Block.compatible (voterAnchorAt S rho w d)
      (actionSGBlockAt S rho p (c + 1)) = true := by
  have hraw := nodeRawG2_at_action_after_recovery_deadline
    S adm hcom hbelow hrec hdelay hpost hc hhor p hp
  rcases actionSGBlockAt_tiers_of_rawG2 S rho p (c + 1) hraw with
    hclear | ⟨Q, hQ, hsg⟩ | hsg
  · exact voterAnchorAt_compatible_actionSGBlock_clear_after_GST
      S adm hcom hbelow hrec hdelay hpost hc hhor hdlo hdhi hvoteHor
        hshor hp hw hclear.2.2 rfl
  · exact voterAnchorAt_compatible_actionSGBlock_selectedQ2_after_GST
      S adm hcom hbelow hrec hdelay hpost hc hhor hdlo hdhi hvoteHor
        hp hw hQ hsg
  · rw [hsg]
    change Block.compatible (voterAnchorAt S rho w d)
      (Protocol.get_fg_root
        (actionStoreAt S rho p (c + 1)).st.core.toHealing.toFG) = true
    exact voterAnchorAt_compatible_actionFGRoot_after_GST
      S adm hcom hbelow hrec hdelay hpost hc hhor hdlo hshor hp hw

#print axioms voterAnchorAt_compatible_actionSGBlock_selectedQ2_after_GST
#print axioms firstInterior_vote_add_delta_le_horizon
#print axioms voterAnchorAt_compatible_actionFGRoot_after_GST
#print axioms voterAnchorAt_compatible_actionSGBlock_clear_after_GST
#print axioms voterAnchorAt_firstInterior_compatible_actionSGBlock_after_GST

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
