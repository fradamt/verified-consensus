module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeiling
public import DecoupledConsensusProofs.Execution.RecoveryFreshAnchorAtRead
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.VoteDutyGradeTransport
public import DecoupledConsensusProofs.Protocol.Schedule.CanonicalSuffixPostGSTCore
public import DecoupledConsensusInternal.RecoveryPrefix
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.AdoptionRun
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Protocol.ValidatorClient.FinalityPairCore
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.Grades.ProposalLifecycleCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.ProposalCore
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroHeadResolution
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Execution.RecoveryActionInterval
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Execution.PreparedReadBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Head.PreparedProposalReadBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSupporter
public import DecoupledConsensusProofs.Execution.UserConfirmationHistory

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Regime-only successor for a half-open round ceiling

This module constructs the successor inputs of `RoundCeilingAt` from exact
frontier and gate-off facts at the reads of the next round. The boundary vote
input relays the preceding honest vote cone through the availability bridge.
The same relay is then iterated through the half-open round.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.PhaseGrades
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The protocol-regime facts at all reads owned by round `q + 1`.

The half-open Goldfish boundary starts with the preceding slot. `window`
covers every vote duty and the in-round confirmation reads. The two boundary
confirmation fields cover the confirmation evaluation at
`opening_slot (q + 1) - 1`. -/
structure RoundCeilingNextRegimeAt
    (S : Setup V) (rho : Run V) (M : Height) (q : Round) : Prop where
  postOpeningProposal : S.E.t_GST ≤
    Protocol.proposal_time S.E (S.hc.opening_slot (q + 1))
  roundConfirmationInHorizon :
    Protocol.confirmation_time S.E
      (seedRoundLastSlot S (q + 1) - 1) ≤ rho.horizon
  window : GateOffSeedConeWindowAt S rho M
    (S.hc.opening_slot (q + 1))
    (seedRoundLastSlot S (q + 1) - 1)
  boundaryConfirmationFrontier : ∀ w ∈ rho.honest,
    (confStore S rho w (S.hc.opening_slot (q + 1) - 1)).h_max = M
  boundaryConfirmationGateOff : ∀ w ∈ rho.honest,
    (confStore S rho w (S.hc.opening_slot (q + 1) - 1)).h_j + 2 ≤ M
  actionFrontier : ∀ w ∈ rho.honest,
    (healStoreAt S rho w (q + 1)).h_max = M
  actionGateOff : ∀ w ∈ rho.honest,
    (healStoreAt S rho w (q + 1)).h_j + 2 ≤ M
  proposalFrontier : ∀ w ∈ rho.honest,
    (rho.storeBeforeTime S w
      (Protocol.proposal_time S.E (S.hc.opening_slot (q + 1)))).h_max = M
  proposalGateOff : ∀ w ∈ rho.honest,
    (rho.storeBeforeTime S w
      (Protocol.proposal_time S.E (S.hc.opening_slot (q + 1)))).h_j + 2 ≤ M

/-- The FG-root ordering at every read owned by round `q + 1`. A ceiling
inside the frontier band gets this from the crossing lemma; a ceiling below
the band must be at or above every finalized root read in the window. -/
structure RoundCeilingNextRootOrderAt
    (S : Setup V) (rho : Run V) (q : Round) (C : Block V) : Prop where
  voteDuty : ∀ d : Slot,
    S.hc.opening_slot (q + 1) ≤ d → d ≤ seedRoundLastSlot S (q + 1) →
      ∀ w ∈ rho.honest,
        Block.Preceq
          (Protocol.get_fg_root
            (voteDutyStore S rho w d).toHealing.toFG) C
  confirmation : ∀ s : Slot,
    S.hc.opening_slot (q + 1) - 1 ≤ s → s < seedRoundLastSlot S (q + 1) →
      ∀ w ∈ rho.honest,
        Block.Preceq (confRoot (confStore S rho w s)) C
  proposer : S.E.proposer (S.hc.opening_slot (q + 1)) ∈ rho.honest →
    Block.Preceq
      (Protocol.get_fg_root
        (proposerDutyStore S rho
          (S.hc.opening_slot (q + 1))).toHealing.toFG) C

private theorem openingSlot_pred_succ_step
    (S : Setup V) {q : Round} (hq : 0 < q) :
    S.hc.opening_slot q - 1 + 1 = S.hc.opening_slot q := by
  unfold Protocol.HealConfig.opening_slot
  have hpos : 0 < q * S.hc.R :=
    Nat.mul_pos hq (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)

private theorem confirmationTime_mono_step
    (E : Env V) {a b : Slot} (hab : a ≤ b) :
    Protocol.confirmation_time E a ≤ Protocol.confirmation_time E b := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact Proofs.Optimistic.support_cutoff_mono E (Nat.add_le_add_right hab 1)

private theorem openingSlot_lt_last_step
    (S : Setup V) (q : Round) :
    S.hc.opening_slot q < seedRoundLastSlot S q := by
  unfold seedRoundLastSlot Protocol.HealConfig.opening_slot
  have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
  apply Nat.lt_sub_of_add_lt
  rw [Nat.add_mul]
  simp only [Nat.one_mul]
  omega

private theorem openingSlot_le_lastPred_step
    (S : Setup V) (q : Round) :
    S.hc.opening_slot q ≤ seedRoundLastSlot S q - 1 :=
  Nat.le_pred_of_lt (openingSlot_lt_last_step S q)

/-- A ceiling inside the frontier band is above every next-round FG root. -/
theorem RoundCeilingNextRootOrderAt.of_thin
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {M : Height} {q : Round} {C : NamedBlock V}
    (hCrun : RunBlock S rho C)
    (hCheight : M - 1 ≤ (Protocol.derive_named S.E S.cfg C).h)
    (hreg : RoundCeilingNextRegimeAt S rho M q) :
    RoundCeilingNextRootOrderAt S rho q C.erase := by
  have hlastPos : 0 < seedRoundLastSlot S (q + 1) :=
    Nat.zero_lt_of_lt (openingSlot_lt_last_step S (q + 1))
  have hlastPred : seedRoundLastSlot S (q + 1) - 1 + 1 =
      seedRoundLastSlot S (q + 1) :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  refine ⟨?_, ?_, ?_⟩
  · intro d hdlo hdhi w hw
    have hfrontier := hreg.window.voteFrontier d hdlo
      (by simpa only [hlastPred] using hdhi) w hw
    have hgate := hreg.window.voteGateOff d hdlo
      (by simpa only [hlastPred] using hdhi) w hw
    exact frontierRoot_preceq_of_gateOff S adm hsb hw rfl hCrun hCheight
      (by simpa only [voteDutyStore, voteStore, tickStore] using hfrontier)
      (by simpa only [voteDutyStore, voteStore, tickStore] using hgate)
  · intro s hslo hshi w hw
    by_cases heq : s = S.hc.opening_slot (q + 1) - 1
    · subst s
      exact frontierRoot_preceq_of_gateOff S adm hsb hw rfl hCrun hCheight
        (by
          simpa only [confRoot, confStore, tickStore] using
            hreg.boundaryConfirmationFrontier w hw)
        (by
          simpa only [confRoot, confStore, tickStore] using
            hreg.boundaryConfirmationGateOff w hw)
    · have hslt : S.hc.opening_slot (q + 1) - 1 < s :=
        lt_of_le_of_ne hslo (Ne.symm heq)
      have hopenPos : 0 < S.hc.opening_slot (q + 1) := by
        unfold Protocol.HealConfig.opening_slot
        exact Nat.mul_pos (Nat.succ_pos q)
          (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
      have hsMain : S.hc.opening_slot (q + 1) ≤ s := by
        rw [← Nat.sub_add_cancel (Nat.succ_le_iff.mpr hopenPos)]
        exact Nat.succ_le_iff.mpr hslt
      have hfrontier := hreg.window.confirmationFrontier s hsMain
        (Nat.le_pred_of_lt hshi) w hw
      have hgate := hreg.window.confirmationGateOff s hsMain
        (Nat.le_pred_of_lt hshi) w hw
      exact frontierRoot_preceq_of_gateOff S adm hsb hw rfl hCrun hCheight
        (by simpa only [confRoot, confStore, tickStore] using hfrontier)
        (by simpa only [confRoot, confStore, tickStore] using hgate)
  · intro hprop
    exact frontierRoot_preceq_of_gateOff S adm hsb hprop rfl hCrun hCheight
      (by
        simpa only [proposerDutyStore, tickStore] using
          hreg.proposalFrontier _ hprop)
      (by
        simpa only [proposerDutyStore, tickStore] using
          hreg.proposalGateOff _ hprop)

private theorem confirmationTime_lt_proposalTime_of_two_le
    (E : Env V) {s s' : Slot} (h : s + 2 ≤ s') :
    Protocol.confirmation_time E s < Protocol.proposal_time E s' := by
  have hcast : ((s : Time) + 2) ≤ (s' : Time) := by exact_mod_cast h
  have hDelta : (0 : Time) < E.Δ := E.Δ_pos
  have hcoef : (0 : Time) ≤ 4 * E.Δ :=
    Int.mul_nonneg (by decide) (le_of_lt hDelta)
  have hmul : 4 * E.Δ * ((s : Time) + 2) ≤ 4 * E.Δ * (s' : Time) :=
    Int.mul_le_mul_of_nonneg_left hcast hcoef
  simp only [Protocol.confirmation_time, Protocol.proposal_time, Env.t,
    slotStart]
  have hexpand : 4 * E.Δ * ((s : Time) + 2) =
      4 * E.Δ * (s : Time) + 8 * E.Δ := by ring
  rw [hexpand] at hmul
  have hstrict : 4 * E.Δ * (s : Time) + 6 * E.Δ <
      4 * E.Δ * (s : Time) + 8 * E.Δ := by
    have h68 : (6 : Time) * E.Δ < 8 * E.Δ := by
      simpa using Int.mul_lt_mul_of_pos_right
        (show (6 : Time) < 8 by decide) hDelta
    exact Int.add_lt_add_left h68 _
  exact lt_of_lt_of_le hstrict hmul

/-- A pointwise gate-off window supplies the complete next-round regime. -/
theorem roundCeilingNextRegime_of_window
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round}
    (hpostAction : S.E.t_GST ≤ S.a q)
    (hhor : Protocol.confirmation_time S.E
      (seedRoundLastSlot S (q + 1) - 1) ≤ rho.horizon)
    (hwindow : ∀ read : Time, S.a q ≤ read →
      read ≤ Protocol.confirmation_time S.E
        (seedRoundLastSlot S (q + 1) - 1) →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M) :
    RoundCeilingNextRegimeAt S rho M q := by
  have hoPos : 0 < S.hc.opening_slot (q + 1) := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos (Nat.succ_pos q)
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hlastPos : 0 < seedRoundLastSlot S (q + 1) :=
    Nat.zero_lt_of_lt (openingSlot_lt_last_step S (q + 1))
  have hlastPredSucc : seedRoundLastSlot S (q + 1) - 1 + 1 =
      seedRoundLastSlot S (q + 1) :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hopenLastPred : S.hc.opening_slot (q + 1) ≤
      seedRoundLastSlot S (q + 1) - 1 :=
    openingSlot_le_lastPred_step S (q + 1)
  have hprevOpen : S.hc.opening_slot q + 2 ≤
      S.hc.opening_slot (q + 1) := by
    change q * S.hc.R + 2 ≤ (q + 1) * S.hc.R
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left S.hc.R_ge_two (q * S.hc.R)
  have hactionProposal : S.a q ≤
      Protocol.proposal_time S.E (S.hc.opening_slot (q + 1)) := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact le_of_lt
      (confirmationTime_lt_proposalTime_of_two_le S.E hprevOpen)
  have hproposalVote :
      Protocol.proposal_time S.E (S.hc.opening_slot (q + 1)) ≤
        Protocol.vote_time S.E (S.hc.opening_slot (q + 1)) :=
    le_of_lt (Protocol.proposal_time_lt_vote_time S.E _)
  have hlastVoteConf : Protocol.vote_time S.E
      (seedRoundLastSlot S (q + 1)) ≤
        Protocol.confirmation_time S.E
          (seedRoundLastSlot S (q + 1) - 1) := by
    rw [← hlastPredSucc,
      ← Protocol.vote_time_succ_add_delta_eq_confirmation_time]
    exact le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  have hboundaryLow :
      Protocol.proposal_time S.E (S.hc.opening_slot (q + 1)) <
        Protocol.confirmation_time S.E
          (S.hc.opening_slot (q + 1) - 1) := by
    have hpred : S.hc.opening_slot (q + 1) - 1 + 1 =
        S.hc.opening_slot (q + 1) :=
      Nat.sub_add_cancel (Nat.succ_le_iff.mpr hoPos)
    simpa only [hpred] using
      Protocol.proposal_time_succ_lt_confirmation_time S.E
        (S.hc.opening_slot (q + 1) - 1)
  have hlowConf : Protocol.confirmation_time S.E
      (S.hc.opening_slot (q + 1) - 1) ≤
        Protocol.confirmation_time S.E
          (seedRoundLastSlot S (q + 1) - 1) :=
    confirmationTime_mono_step S.E
      ((Nat.sub_le _ 1).trans hopenLastPred)
  have hvoteRead : ∀ d : Slot, S.hc.opening_slot (q + 1) ≤ d →
      d ≤ seedRoundLastSlot S (q + 1) → ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).h_j + 2 ≤ M ∧
        (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).h_max = M := by
    intro d hdlo hdhi w hw
    refine hwindow _ ?_ ?_ w hw
    · exact hactionProposal.trans
        (hproposalVote.trans (Protocol.vote_time_mono_slots S.E hdlo))
    · exact (Protocol.vote_time_mono_slots S.E hdhi).trans hlastVoteConf
  have hconfRead : ∀ s : Slot,
      S.hc.opening_slot (q + 1) - 1 ≤ s →
      s ≤ seedRoundLastSlot S (q + 1) - 1 → ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w
          (Protocol.confirmation_time S.E s)).h_j + 2 ≤ M ∧
        (rho.storeBeforeTime S w
          (Protocol.confirmation_time S.E s)).h_max = M := by
    intro s hslo hshi w hw
    refine hwindow _ ?_ ?_ w hw
    · exact hactionProposal.trans
        ((le_of_lt hboundaryLow).trans
          (confirmationTime_mono_step S.E hslo))
    · exact confirmationTime_mono_step S.E hshi
  have hproposalRead : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w
          (Protocol.proposal_time S.E
            (S.hc.opening_slot (q + 1)))).h_j + 2 ≤ M ∧
        (rho.storeBeforeTime S w
          (Protocol.proposal_time S.E
            (S.hc.opening_slot (q + 1)))).h_max = M := by
    intro w hw
    exact hwindow _ hactionProposal
      ((le_of_lt hboundaryLow).trans hlowConf) w hw
  have hactionRead : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a (q + 1))).h_j + 2 ≤ M ∧
        (rho.storeBeforeTime S w (S.a (q + 1))).h_max = M := by
    intro w hw
    have hin := hconfRead (S.hc.opening_slot (q + 1))
      (Nat.sub_le _ 1) hopenLastPred w hw
    rwa [show S.a (q + 1) = Protocol.confirmation_time S.E
      (S.hc.opening_slot (q + 1)) by
        rw [Setup.a, Protocol.a_eq_confirmation_time]]
  exact
    { postOpeningProposal := hpostAction.trans hactionProposal
      roundConfirmationInHorizon := hhor
      window :=
        { voteFrontier := by
            intro d hdlo hdhi w hw
            simpa only [voteDutyStore, voteStore, tickStore] using
              (hvoteRead d hdlo
                (by rw [← hlastPredSucc]; exact hdhi) w hw).2
          voteGateOff := by
            intro d hdlo hdhi w hw
            simpa only [voteDutyStore, voteStore, tickStore] using
              (hvoteRead d hdlo
                (by rw [← hlastPredSucc]; exact hdhi) w hw).1
          confirmationFrontier := by
            intro s hslo hshi w hw
            simpa only [confStore, tickStore] using
              (hconfRead s ((Nat.sub_le _ 1).trans hslo) hshi w hw).2
          confirmationGateOff := by
            intro s hslo hshi w hw
            simpa only [confStore, tickStore] using
              (hconfRead s ((Nat.sub_le _ 1).trans hslo) hshi w hw).1 }
      boundaryConfirmationFrontier := by
        intro w hw
        simpa only [confStore, tickStore] using
          (hconfRead (S.hc.opening_slot (q + 1) - 1) (le_refl _)
            ((Nat.sub_le _ 1).trans hopenLastPred) w hw).2
      boundaryConfirmationGateOff := by
        intro w hw
        simpa only [confStore, tickStore] using
          (hconfRead (S.hc.opening_slot (q + 1) - 1) (le_refl _)
            ((Nat.sub_le _ 1).trans hopenLastPred) w hw).1
      actionFrontier := by
        intro w hw
        simpa only [healStoreAt] using (hactionRead w hw).2
      actionGateOff := by
        intro w hw
        simpa only [healStoreAt] using (hactionRead w hw).1
      proposalFrontier := fun w hw => (hproposalRead w hw).2
      proposalGateOff := fun w hw => (hproposalRead w hw).1 }

#print axioms roundCeilingNextRegime_of_window

private theorem ceiling_voteTime_lt_nextProposal
    (E : Env V) (s : Slot) :
    Protocol.vote_time E s < Protocol.proposal_time E (s + 1) := by
  simp only [Protocol.vote_time, Protocol.proposal_time, Env.t, slotStart]
  push_cast
  nlinarith [E.Δ_pos]

/-- A next-round prepared voter anchor is compatible with every common upper
endpoint of the previous round's honest action carriers. -/
theorem voterAnchorAt_preceq_of_previousCarriers
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} {s : Slot} (hround : S.hc.round_of (s + 1) = q + 1)
    (hpost : S.E.t_GST ≤ S.a q)
    (hcut : S.hc.Γ_neg1 S.E.Δ (q + 1) ≤ rho.horizon)
    (hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    {C : Block V}
    (hupper : ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v q) C)
    {w : V} (hw : w ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyStore S rho w (s + 1)).toHealing.toFG) C) :
    Block.Preceq (voterAnchorAt S rho w (s + 1)) C := by
  rcases voterAnchorAt_cases S rho w (s + 1) with hfg | hactive
  · rw [hfg]
    simpa only [voteDutyStore] using hroot
  · obtain ⟨root, A, hframe, hactive, hanchor⟩ := hactive
    rw [hanchor]
    have hr : 0 < q + 1 := Nat.succ_pos q
    have hslo : S.hc.opening_slot (q + 1) ≤ s + 1 := by
      rw [← hround]
      exact Nat.div_mul_le_self (s + 1) S.hc.R
    have hshi : s + 1 < S.hc.opening_slot ((q + 1) + 1) := by
      rw [← hround]
      apply (Nat.div_lt_iff_lt_mul
        (Nat.zero_lt_of_lt S.hc.R_ge_two)).mp
      exact Nat.lt_succ_self ((s + 1) / S.hc.R)
    have hnext : Protocol.vote_time S.E (s + 1) ≤
        DecoupledConsensusModel.Protocol.opening S.E S.hc ((q + 1) + 1) :=
      (ceiling_voteTime_lt_nextProposal S.E (s + 1)).le.trans
        (Protocol.proposal_time_mono S.E (Nat.succ_le_iff.mpr hshi))
    have hframe' : (DecoupledConsensusModel.Protocol.readFrame
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).cache
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.toHealing (q + 1)).g1 = some (some root) := by
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.slotOf_vote_time, hround] using hframe
    obtain ⟨hAtree, hAGrade⟩ := fixedRoot_activeVoterAnchor_g1_data
      S adm hr hslo hround hnext hvoteHor hw hframe' hactive
    let read := PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1) w
    have hdomainVote : DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 <
        Protocol.vote_time S.E (s + 1) := by
      rw [NamedOutageClosure.domain_g1_eq_opening]
      exact (Protocol.proposal_time_mono S.E hslo).trans_lt
        (Protocol.proposal_time_lt_vote_time S.E (s + 1))
    have hFmono : Block.Preceq read.st.core.F
        (NamedRun.stateBeforeTime S rho
          (Protocol.vote_time S.E (s + 1)) w).st.core.F := by
      dsimp only [read, PhaseGrades.readAt]
      rw [NamedOutageClosure.strict_read_eq_index S rho
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
          (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1),
        NamedOutageClosure.strict_read_eq_index S rho
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
          (Protocol.vote_time S.E (s + 1))]
      exact Proofs.NamedRuntime.stateBefore_F_mono S rho w
        (NamedOutageClosure.strict_lengths_mono rho hdomainVote.le)
    have hFroot : Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (Protocol.vote_time S.E (s + 1)) w).st.core.F
        (Protocol.get_fg_root
          (voteDutyStore S rho w (s + 1)).toHealing.toFG) := by
      have hFJ :=
        Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
          (Protocol.vote_time S.E (s + 1)) w
      simpa only [voteDutyStore, voteStore, tickStore] using
        (Proofs.Records.preceq_get_fg_root_of_F
          (st := (NamedRun.stateBeforeTime S rho
            (Protocol.vote_time S.E (s + 1)) w).st.core.toHealing.toFG) hFJ)
    have hFC : Block.Preceq read.st.core.F C :=
      Block.preceq_trans hFmono (Block.preceq_trans hFroot hroot)
    have hlatest : q ∈ Protocol.latest_window S.hc.η_SG (q + 1) := by
      simpa only [Nat.add_sub_cancel] using
        Protocol.pred_mem_latest_window S.hc.η_SG (q + 1)
          S.hc.η_SG_ge_one (Nat.succ_pos q)
    have hactionDeadline : S.a q + S.E.Δ ≤
        DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 :=
      (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
        (Nat.lt_succ_self q)).trans
        (NamedOutageClosure.q10_early_g2_le_early_g1 S (q + 1))
    have hactionHor : S.a q ≤ rho.horizon :=
      (le_add_of_nonneg_right S.E.Δ_pos.le).trans
        ((action_add_delta_le_next_Γ_neg1 S q).trans hcut)
    have hearlyHor : DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 ≤
        rho.horizon :=
      (NamedOutageClosure.q10_early_g1_le_domain_g2 S (q + 1)).trans
        (by simpa only [gammaNeg1_eq_domain_g2_succ S q] using hcut)
    have hearlyDomain : DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 :=
      (NamedOutageClosure.q10_early_g1_le_domain_g2 S (q + 1)).trans
        (NamedOutageClosure.q10_domain_g2_lt_domain_g1 S (q + 1)).le
    have hinterpreted : ∀ v ∈ rho.honest,
        (DecoupledConsensusModel.Protocol.interpretedInputs
          read.st.core.toHealing.gradeView read.st.core.F S.hc.η_SG
          (q + 1) (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1) v).Nonempty := by
      intro v hv
      obtain ⟨a, hemit, hproj⟩ :=
        honest_emits_actionAttestationAt S adm hv q hactionHor
      obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
        Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
      have haval : a.val_index = v := by
        have h := congrArg Protocol.SGVote.val_index hproj
        simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
      have haround : a.round = q := by
        have h := congrArg Protocol.SGVote.round hproj
        simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
      have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
        change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
        exact hH
      have hHrun : RunBlock S rho H :=
        Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
      have hCmem : actionSGBlockAt S rho v q ∈
          (rho.storeBeforeTime S v (S.a q)).T :=
        actionSGBlockAt_mem_storeBeforeTime S rho v q
      obtain ⟨Cn, hCnerase, hCnrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
      have hconfirmedCarrier : a.confirmed =
          some (actionSGBlockAt S rho v q).root := by
        have h := congrArg Protocol.SGVote.confirmed hproj
        simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
      have hrootEq : H.erase.root = Cn.erase.root := by
        rw [Proofs.NamedWire.erase_root, hCnerase]
        exact congrArg id (Option.some.inj
          (hconfirmed.symm.trans hconfirmedCarrier))
      have hHCeq : H.erase = Cn.erase :=
        Protocol.runBlock_eq_of_root_eq
          adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hCnrun hrootEq
      have hHC : Block.Preceq H.erase C := by
        rw [hHCeq, hCnerase]
        exact hupper v hv
      have hmem :=
        action_vote_mem_interpretedInputs_after_gst_common_upper
          S adm.toNamedAdmissibleCore .g1 hlatest hv hw
          ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
          (by simpa only [haround] using hpost)
          (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
          hearlyDomain hearlyHor
      exact ⟨Protocol.sgVote a.erase, by simpa only [read] using hmem⟩
    have hrepresented : ∀ v ∈ rho.honest,
        Protocol.represented read.st.core.toHealing.sg_votes
          S.hc.η_SG v (q + 1) = true := by
      intro v hv
      obtain ⟨a, hemit, hproj⟩ :=
        honest_emits_actionAttestationAt S adm hv q hactionHor
      obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
        Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
      have haval : a.val_index = v := by
        have h := congrArg Protocol.SGVote.val_index hproj
        simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
      have haround : a.round = q := by
        have h := congrArg Protocol.SGVote.round hproj
        simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
      have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
        change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
        exact hH
      have hHrun : RunBlock S rho H :=
        Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
      have hCmem : actionSGBlockAt S rho v q ∈
          (rho.storeBeforeTime S v (S.a q)).T :=
        actionSGBlockAt_mem_storeBeforeTime S rho v q
      obtain ⟨Cn, hCnerase, hCnrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
      have hconfirmedCarrier : a.confirmed =
          some (actionSGBlockAt S rho v q).root := by
        have h := congrArg Protocol.SGVote.confirmed hproj
        simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
      have hrootEq : H.erase.root = Cn.erase.root := by
        rw [Proofs.NamedWire.erase_root, hCnerase]
        exact congrArg id (Option.some.inj
          (hconfirmed.symm.trans hconfirmedCarrier))
      have hHCeq : H.erase = Cn.erase :=
        Protocol.runBlock_eq_of_root_eq
          adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hCnrun hrootEq
      have hHC : Block.Preceq H.erase C := by
        rw [hHCeq, hCnerase]
        exact hupper v hv
      have hmem :=
        action_vote_mem_interpretedInputs_after_gst_common_upper
          S adm.toNamedAdmissibleCore .g1 hlatest hv hw
          ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
          (by simpa only [haround] using hpost)
          (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
          hearlyDomain hearlyHor
      have hraw := (Finset.mem_filter.mp hmem).1
      obtain ⟨hpool, hfields⟩ := Finset.mem_filter.mp hraw
      obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hpool
      exact Protocol.represented_of_vote_mem
        (List.mem_toFinset.mp hk) huk hfields.1
    have hwindow := windowMajorityAt_of_honestWeightMajority_of_represented
      S (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird
        (S := S) hfb) hrepresented hinterpreted
    have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
        read.st.core.toHealing.gradeView read.st.core.F S.hc.η_SG (q + 1)
        (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1)
        (DecoupledConsensusModel.Protocol.late S.E S.hc (q + 1) .g1) A = true := by
      simpa only [read, PhaseGrades.storeGrade, PhaseGrades.phaseGrade] using hAGrade
    obtain ⟨v, hv, u, hu, head, hconf, hfind, -, hAhead, -, hmax⟩ :=
      exists_honest_max_positive_supporter_of_relativeGrade
        S.E S.hc hwindow hgrade
    obtain ⟨a, hemit, hproj⟩ :=
      honest_emits_actionAttestationAt S adm hv q hactionHor
    obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
      Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
    have haval : a.val_index = v := by
      have h := congrArg Protocol.SGVote.val_index hproj
      simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
    have haround : a.round = q := by
      have h := congrArg Protocol.SGVote.round hproj
      simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
    have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
      change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
      exact hH
    have hHrun : RunBlock S rho H :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
    have hCmem : actionSGBlockAt S rho v q ∈
        (rho.storeBeforeTime S v (S.a q)).T :=
      actionSGBlockAt_mem_storeBeforeTime S rho v q
    obtain ⟨Cn, hCnerase, hCnrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
    have hconfirmedCarrier : a.confirmed =
        some (actionSGBlockAt S rho v q).root := by
      have h := congrArg Protocol.SGVote.confirmed hproj
      simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
    have hrootEq : H.erase.root = Cn.erase.root := by
      rw [Proofs.NamedWire.erase_root, hCnerase]
      exact congrArg id (Option.some.inj
        (hconfirmed.symm.trans hconfirmedCarrier))
    have hHCeq : H.erase = Cn.erase :=
      Protocol.runBlock_eq_of_root_eq
        adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hCnrun hrootEq
    have hHC : Block.Preceq H.erase C := by
      rw [hHCeq, hCnerase]
      exact hupper v hv
    have hactionInput :=
      action_vote_mem_interpretedInputs_after_gst_common_upper
        S adm.toNamedAdmissibleCore .g1 hlatest hv hw
        ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
        (by simpa only [haround] using hpost)
        (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
        hearlyDomain hearlyHor
    have hqle : q ≤ u.round := by
      have := hmax (Protocol.sgVote a.erase) hactionInput
      simpa only [Protocol.sgVote, NamedAttestation.erase, haround] using this
    have huraw := (Finset.mem_filter.mp hu).1
    obtain ⟨b, hbval, hbround, hbproj, huwindow, -, hbemit⟩ :=
      NamedOutageClosure.rawInputs_trace S rho
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
        adm.toNamedAdmissibleCore.toNamedUnforgeable
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1)
        (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1) w
        S.hc.η_SG (q + 1) v hv (by simpa only [read] using huraw)
    have hule : u.round ≤ q := Nat.le_of_lt_succ
      (NamedOutageClosure.window_bounds huwindow).2
    have huroundEq : u.round = q := Nat.le_antisymm hule hqle
    have hbroundQ : b.round = q := hbround.trans huroundEq
    have hba : b = a := Proofs.Optimistic.emits_attest_unique S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hbemit hemit
      (hbroundQ.trans haround.symm)
    have huEq : u = Protocol.sgVote a.erase := by
      rw [← hbproj, hba]
    have hheadRoot : head.root = (actionSGBlockAt S rho v q).root := by
      have huconf := congrArg Protocol.SGVote.confirmed huEq
      simpa only [Protocol.sgVote, NamedAttestation.erase, hconf,
        hconfirmedCarrier, Option.some.injEq] using huconf
    have hheadMem : head ∈ read.st.core.T := Proofs.HealingLemmas.find?_mem hfind
    obtain ⟨Headn, hHeaderase, hHeadrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1) (by
          simpa only [read] using hheadMem)
    have hheadCnRoot : Headn.erase.root = Cn.erase.root := by
      rw [hHeaderase, hCnerase]
      exact hheadRoot
    have hheadCarrier : head = actionSGBlockAt S rho v q := by
      rw [← hHeaderase, ← hCnerase]
      exact Protocol.runBlock_eq_of_root_eq
        adm.toNamedAdmissibleCore.toNamedRootCollisionFree
        hHeadrun hCnrun hheadCnRoot
    have hAC : Block.Preceq A C :=
      Block.preceq_trans (by simpa only [hheadCarrier] using hAhead) (hupper v hv)
    exact hAC


#print axioms voterAnchorAt_preceq_of_previousCarriers




omit [Fintype V] in
private theorem confirmation_localCovers_mono
    {A B : Block V} {gv : Protocol.GradeView V} {key : Option BlockId}
    (hAB : Block.Preceq A B)
    (hB : DecoupledConsensusModel.Protocol.localCovers gv key B = true) :
    DecoupledConsensusModel.Protocol.localCovers gv key A = true := by
  unfold DecoupledConsensusModel.Protocol.localCovers at hB ⊢
  unfold Protocol.head_covers at hB ⊢
  cases key with
  | none => exact hB
  | some root =>
      dsimp only at hB ⊢
      cases hfind : Block.find? gv.T root with
      | none => rw [hfind] at hB; exact absurd hB (by simp)
      | some head =>
          rw [hfind] at hB
          exact Block.preceq_trans hAB hB

omit [Fintype V] in
private theorem confirmation_positive_mono
    {A B : Block V} (hAB : Block.Preceq A B)
    (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V)
    (hB : DecoupledConsensusModel.Protocol.positive gv F eta r early late v B = true) :
    DecoupledConsensusModel.Protocol.positive gv F eta r early late v A = true := by
  simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] at hB ⊢
  rcases hB with ⟨u, hu, hmax, hcov, hclean, hlate⟩
  refine ⟨u, hu, hmax, confirmation_localCovers_mono hAB hcov, hclean, ?_⟩
  intro x hx hlt
  exact confirmation_localCovers_mono hAB (hlate x hx hlt)

omit [Fintype V] in
private theorem confirmation_opposing_mono
    {A B : Block V} (hAB : Block.Preceq A B)
    (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V)
    (hA : DecoupledConsensusModel.Protocol.opposing gv F eta r early late v A = true) :
    DecoupledConsensusModel.Protocol.opposing gv F eta r early late v B = true := by
  simp only [DecoupledConsensusModel.Protocol.opposing, decide_eq_true_eq] at hA ⊢
  rcases hA with ⟨x, hx, hmax, hnot⟩ |
      ⟨x, hx, y, hy, hmax, heq, hkey⟩
  · left
    refine ⟨x, hx, hmax, ?_⟩
    intro hcov
    exact hnot (confirmation_localCovers_mono hAB hcov)
  · exact Or.inr ⟨x, hx, y, hy, hmax, heq, hkey⟩

theorem confirmation_phaseGrade_mono
    (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (r : Round) (phase : DecoupledConsensusModel.Protocol.Phase)
    {A B : Block V}
    (hAB : Block.Preceq A B)
    (hB : PhaseGrades.phaseGrade E hc gv F r phase B = true) :
    PhaseGrades.phaseGrade E hc gv F r phase A = true := by
  simp only [PhaseGrades.phaseGrade, DecoupledConsensusModel.Protocol.gradeBool,
    decide_eq_true_eq] at hB ⊢
  have hOpp : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r phase)
        (DecoupledConsensusModel.Protocol.late E hc r phase) v A = true) ⊆
      Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r
          (DecoupledConsensusModel.Protocol.early E hc r phase)
          (DecoupledConsensusModel.Protocol.late E hc r phase) v B = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      confirmation_opposing_mono hAB gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r phase)
        (DecoupledConsensusModel.Protocol.late E hc r phase) v
        (Finset.mem_filter.mp hv).2⟩
  have hPos : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r phase)
        (DecoupledConsensusModel.Protocol.late E hc r phase) v B = true) ⊆
      Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r
          (DecoupledConsensusModel.Protocol.early E hc r phase)
          (DecoupledConsensusModel.Protocol.late E hc r phase) v A = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      confirmation_positive_mono hAB gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r phase)
        (DecoupledConsensusModel.Protocol.late E hc r phase) v
        (Finset.mem_filter.mp hv).2⟩
  exact lt_of_le_of_lt (E.electorate.weightOf_mono hOpp)
    (lt_of_lt_of_le hB (E.electorate.weightOf_mono hPos))

private theorem activeConfirmationAnchor_g1_data
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {t : Time} (hr : 0 < r)
    (hround : S.hc.round_of (S.E.slotOf t) = r)
    (hdomain : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 < t)
    (hnext : t ≤ DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1))
    (hreadHor : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) {root L : Block V}
    (hframe : (DecoupledConsensusModel.Protocol.readFrame
      (NamedActionReads.confirmationReadAt S rho w t).cache
      (NamedActionReads.confirmationReadAt S rho w t).st.core.toHealing r).g1 =
        some (some root))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (Protocol.get_filtered_block_tree
        (NamedActionReads.confirmationReadAt S rho w t).st.core.toHealing.toFG) root =
        some L) :
    L ∈ (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.T ∧
      PhaseGrades.storeGrade S.E S.hc
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1 L = true := by
  let before := NamedRun.stateBeforeTime S rho t w
  let read := NamedActionReads.confirmationReadAt S rho w t
  let domainRead := PhaseGrades.readAt S rho
    (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w
  have hbase := FrameCompleted.frame_phase_completed_in_round
    S rho adm.toNamedAdmissibleCore w hw r hr .g1 t hdomain hnext hreadHor
  have hbase' :
      (DecoupledConsensusModel.Protocol.readFrame before.cache
        before.st.core.toHealing r).g1 =
        some ((PhaseGrades.storeRoot S.E S.hc domainRead.st r .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X before.st.core.F)) := by
    simpa only [before, domainRead, PhaseGrades.storeRoot,
      PhaseGrades.phaseRoot, PhaseGrades.readAt] using hbase
  have hprepared := NamedOutageClosure.frame_phase_prepared_eq
    S rho w r .g1 t hround _ hbase'
  have hreadFrame :
      (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing r).g1 =
        some ((PhaseGrades.storeRoot S.E S.hc domainRead.st r .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X read.st.core.F)) := by
    simpa only [read, before, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom] using hprepared
  cases hstore : PhaseGrades.storeRoot S.E S.hc domainRead.st r .g1 with
  | none =>
      simp only [hstore, Option.map_none] at hreadFrame
      rw [hframe] at hreadFrame
      cases hreadFrame
  | some raw =>
      have hrootEq : root =
          DecoupledConsensusModel.Protocol.clipGrade raw read.st.core.F := by
        have hopt : some (some root) = some
            (some (DecoupledConsensusModel.Protocol.clipGrade raw read.st.core.F)) :=
          hframe.symm.trans (by
            simpa only [hstore, Option.map_some] using hreadFrame)
        exact Option.some.inj (Option.some.inj hopt)
      have hLroot : Block.Preceq L root := by
        unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
      have hLraw : Block.Preceq L raw := by
        rw [hrootEq] at hLroot
        exact Block.preceq_trans hLroot
          (NamedOutageClosure.q10_clip_preceq raw read.st.core.F)
      have hrawData := Proofs.Engine.deepest?_mem hstore
      have hrawTree : raw ∈ domainRead.st.core.T :=
        (Finset.mem_filter.mp hrawData).1
      have hLtree : L ∈ domainRead.st.core.T := by
        have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w
        exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
          L raw hrawTree hLraw
      have hrawGrade : PhaseGrades.phaseGrade S.E S.hc
          domainRead.st.core.toHealing.gradeView domainRead.st.core.F
          r .g1 raw = true := (Finset.mem_filter.mp hrawData).2
      refine ⟨hLtree, ?_⟩
      exact confirmation_phaseGrade_mono S.E S.hc _ _ r .g1 hLraw hrawGrade

/-- A next-round prepared confirmation anchor is compatible with every common
upper endpoint of the previous round's honest action carriers. -/
theorem confirmationAnchorAt_preceq_of_previousCarriers
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} {s : Slot} (hround : S.hc.round_of (s + 1) = q + 1)
    (hpost : S.E.t_GST ≤ S.a q)
    (hcut : S.hc.Γ_neg1 S.E.Δ (q + 1) ≤ rho.horizon)
    (hconfHor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hupper : ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v q) C)
    {w : V} (hw : w ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.confirmationInputRead S rho w s).st.core.toHealing.toFG) C) :
    Block.Preceq (confirmationAnchorAt S rho w s) C := by
  rcases confirmationAnchorAt_cases S rho w s with hfg | hactive
  · rw [hfg]
    exact hroot
  · obtain ⟨root, A, hframe, hactive, hanchor⟩ := hactive
    rw [hanchor]
    have hr : 0 < q + 1 := Nat.succ_pos q
    have hslo : S.hc.opening_slot (q + 1) ≤ s + 1 := by
      rw [← hround]
      exact Nat.div_mul_le_self (s + 1) S.hc.R
    have hshi : s + 1 < S.hc.opening_slot ((q + 1) + 1) := by
      rw [← hround]
      apply (Nat.div_lt_iff_lt_mul
        (Nat.zero_lt_of_lt S.hc.R_ge_two)).mp
      exact Nat.lt_succ_self ((s + 1) / S.hc.R)
    have hdomain : DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 <
        Protocol.confirmation_time S.E s := by
      rw [NamedOutageClosure.domain_g1_eq_opening]
      exact (Protocol.proposal_time_mono S.E hslo).trans_lt
        (Protocol.proposal_time_succ_lt_confirmation_time S.E s)
    have hnext : Protocol.confirmation_time S.E s ≤
        DecoupledConsensusModel.Protocol.opening S.E S.hc ((q + 1) + 1) := by
      change Protocol.confirmation_time S.E s ≤
        Protocol.proposal_time S.E (S.hc.opening_slot ((q + 1) + 1))
      exact (confirmationTime_lt_proposalTime_of_two_le S.E
        (Nat.succ_le_of_lt hshi)).le
    have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 ≤
        rho.horizon := hdomain.le.trans hconfHor
    have hround' : S.hc.round_of
        (S.E.slotOf (Protocol.confirmation_time S.E s)) = q + 1 := by
      simpa only [Proofs.Optimistic.slotOf_confirmation_time] using hround
    have hroundSt : S.hc.round_of
        (Internal.NamedRecoveryRead.confirmationInputRead S rho w s).st.core.s = q + 1 := by
      simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.slotOf_confirmation_time] using hround
    have hframe' := hframe
    rw [hroundSt] at hframe'
    obtain ⟨hAtree, hAGrade⟩ := activeConfirmationAnchor_g1_data
      S adm hr hround' hdomain hnext hdomainHor hw
      (by simpa only [Internal.NamedRecoveryRead.confirmationInputRead] using hframe')
      (by simpa only [Internal.NamedRecoveryRead.confirmationInputRead] using hactive)
    let read := PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1) w
    have hFmono : Block.Preceq read.st.core.F
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E s) w).st.core.F := by
      dsimp only [read, PhaseGrades.readAt]
      rw [NamedOutageClosure.strict_read_eq_index S rho
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
          (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1),
        NamedOutageClosure.strict_read_eq_index S rho
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
          (Protocol.confirmation_time S.E s)]
      exact Proofs.NamedRuntime.stateBefore_F_mono S rho w
        (NamedOutageClosure.strict_lengths_mono rho hdomain.le)
    have hFroot : Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E s) w).st.core.F
      (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.confirmationInputRead S rho w s).st.core.toHealing.toFG) := by
      have hFJ :=
        Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
          (Protocol.confirmation_time S.E s) w
      simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
        (Proofs.Records.preceq_get_fg_root_of_F
          (st := (NamedRun.stateBeforeTime S rho
            (Protocol.confirmation_time S.E s) w).st.core.toHealing.toFG) hFJ)
    have hFC : Block.Preceq read.st.core.F C :=
      Block.preceq_trans hFmono (Block.preceq_trans hFroot hroot)
    have hlatest : q ∈ Protocol.latest_window S.hc.η_SG (q + 1) := by
      simpa only [Nat.add_sub_cancel] using
        Protocol.pred_mem_latest_window S.hc.η_SG (q + 1)
          S.hc.η_SG_ge_one (Nat.succ_pos q)
    have hactionDeadline : S.a q + S.E.Δ ≤
        DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 :=
      (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
        (Nat.lt_succ_self q)).trans
        (NamedOutageClosure.q10_early_g2_le_early_g1 S (q + 1))
    have hactionHor : S.a q ≤ rho.horizon :=
      (le_add_of_nonneg_right S.E.Δ_pos.le).trans
        ((action_add_delta_le_next_Γ_neg1 S q).trans hcut)
    have hearlyHor : DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 ≤
        rho.horizon :=
      (NamedOutageClosure.q10_early_g1_le_domain_g2 S (q + 1)).trans
        (by simpa only [gammaNeg1_eq_domain_g2_succ S q] using hcut)
    have hearlyDomain : DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 :=
      (NamedOutageClosure.q10_early_g1_le_domain_g2 S (q + 1)).trans
        (NamedOutageClosure.q10_domain_g2_lt_domain_g1 S (q + 1)).le
    have hinterpreted : ∀ v ∈ rho.honest,
        (DecoupledConsensusModel.Protocol.interpretedInputs
          read.st.core.toHealing.gradeView read.st.core.F S.hc.η_SG
          (q + 1) (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1) v).Nonempty := by
      intro v hv
      obtain ⟨a, hemit, hproj⟩ :=
        honest_emits_actionAttestationAt S adm hv q hactionHor
      obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
        Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
      have haval : a.val_index = v := by
        have h := congrArg Protocol.SGVote.val_index hproj
        simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
      have haround : a.round = q := by
        have h := congrArg Protocol.SGVote.round hproj
        simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
      have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
        change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
        exact hH
      have hHrun : RunBlock S rho H :=
        Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
      have hCmem : actionSGBlockAt S rho v q ∈
          (rho.storeBeforeTime S v (S.a q)).T :=
        actionSGBlockAt_mem_storeBeforeTime S rho v q
      obtain ⟨Cn, hCnerase, hCnrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
      have hconfirmedCarrier : a.confirmed =
          some (actionSGBlockAt S rho v q).root := by
        have h := congrArg Protocol.SGVote.confirmed hproj
        simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
      have hrootEq : H.erase.root = Cn.erase.root := by
        rw [Proofs.NamedWire.erase_root, hCnerase]
        exact congrArg id (Option.some.inj
          (hconfirmed.symm.trans hconfirmedCarrier))
      have hHCeq : H.erase = Cn.erase :=
        Protocol.runBlock_eq_of_root_eq
          adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hCnrun hrootEq
      have hHC : Block.Preceq H.erase C := by
        rw [hHCeq, hCnerase]
        exact hupper v hv
      have hmem :=
        action_vote_mem_interpretedInputs_after_gst_common_upper
          S adm.toNamedAdmissibleCore .g1 hlatest hv hw
          ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
          (by simpa only [haround] using hpost)
          (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
          hearlyDomain hearlyHor
      exact ⟨Protocol.sgVote a.erase, by simpa only [read] using hmem⟩
    have hrepresented : ∀ v ∈ rho.honest,
        Protocol.represented read.st.core.toHealing.sg_votes
          S.hc.η_SG v (q + 1) = true := by
      intro v hv
      obtain ⟨a, hemit, hproj⟩ :=
        honest_emits_actionAttestationAt S adm hv q hactionHor
      obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
        Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
      have haval : a.val_index = v := by
        have h := congrArg Protocol.SGVote.val_index hproj
        simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
      have haround : a.round = q := by
        have h := congrArg Protocol.SGVote.round hproj
        simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
      have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
        change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
        exact hH
      have hHrun : RunBlock S rho H :=
        Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
      have hCmem : actionSGBlockAt S rho v q ∈
          (rho.storeBeforeTime S v (S.a q)).T :=
        actionSGBlockAt_mem_storeBeforeTime S rho v q
      obtain ⟨Cn, hCnerase, hCnrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
      have hconfirmedCarrier : a.confirmed =
          some (actionSGBlockAt S rho v q).root := by
        have h := congrArg Protocol.SGVote.confirmed hproj
        simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
      have hrootEq : H.erase.root = Cn.erase.root := by
        rw [Proofs.NamedWire.erase_root, hCnerase]
        exact congrArg id (Option.some.inj
          (hconfirmed.symm.trans hconfirmedCarrier))
      have hHCeq : H.erase = Cn.erase :=
        Protocol.runBlock_eq_of_root_eq
          adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hCnrun hrootEq
      have hHC : Block.Preceq H.erase C := by
        rw [hHCeq, hCnerase]
        exact hupper v hv
      have hmem :=
        action_vote_mem_interpretedInputs_after_gst_common_upper
          S adm.toNamedAdmissibleCore .g1 hlatest hv hw
          ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
          (by simpa only [haround] using hpost)
          (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
          hearlyDomain hearlyHor
      have hraw := (Finset.mem_filter.mp hmem).1
      obtain ⟨hpool, hfields⟩ := Finset.mem_filter.mp hraw
      obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hpool
      exact Protocol.represented_of_vote_mem
        (List.mem_toFinset.mp hk) huk hfields.1
    have hwindow := windowMajorityAt_of_honestWeightMajority_of_represented
      S (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird
        (S := S) hfb) hrepresented hinterpreted
    have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
        read.st.core.toHealing.gradeView read.st.core.F S.hc.η_SG (q + 1)
        (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1)
        (DecoupledConsensusModel.Protocol.late S.E S.hc (q + 1) .g1) A = true := by
      simpa only [read, PhaseGrades.storeGrade, PhaseGrades.phaseGrade] using hAGrade
    obtain ⟨v, hv, u, hu, head, hconf, hfind, -, hAhead, -, hmax⟩ :=
      exists_honest_max_positive_supporter_of_relativeGrade
        S.E S.hc hwindow hgrade
    obtain ⟨a, hemit, hproj⟩ :=
      honest_emits_actionAttestationAt S adm hv q hactionHor
    obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
      Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
    have haval : a.val_index = v := by
      have h := congrArg Protocol.SGVote.val_index hproj
      simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
    have haround : a.round = q := by
      have h := congrArg Protocol.SGVote.round hproj
      simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
    have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
      change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
      exact hH
    have hHrun : RunBlock S rho H :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
    have hCmem : actionSGBlockAt S rho v q ∈
        (rho.storeBeforeTime S v (S.a q)).T :=
      actionSGBlockAt_mem_storeBeforeTime S rho v q
    obtain ⟨Cn, hCnerase, hCnrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
    have hconfirmedCarrier : a.confirmed =
        some (actionSGBlockAt S rho v q).root := by
      have h := congrArg Protocol.SGVote.confirmed hproj
      simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
    have hrootEq : H.erase.root = Cn.erase.root := by
      rw [Proofs.NamedWire.erase_root, hCnerase]
      exact congrArg id (Option.some.inj
        (hconfirmed.symm.trans hconfirmedCarrier))
    have hHCeq : H.erase = Cn.erase :=
      Protocol.runBlock_eq_of_root_eq
        adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hCnrun hrootEq
    have hHC : Block.Preceq H.erase C := by
      rw [hHCeq, hCnerase]
      exact hupper v hv
    have hactionInput :=
      action_vote_mem_interpretedInputs_after_gst_common_upper
        S adm.toNamedAdmissibleCore .g1 hlatest hv hw
        ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
        (by simpa only [haround] using hpost)
        (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
        hearlyDomain hearlyHor
    have hqle : q ≤ u.round := by
      have := hmax (Protocol.sgVote a.erase) hactionInput
      simpa only [Protocol.sgVote, NamedAttestation.erase, haround] using this
    have huraw := (Finset.mem_filter.mp hu).1
    obtain ⟨b, hbval, hbround, hbproj, huwindow, -, hbemit⟩ :=
      NamedOutageClosure.rawInputs_trace S rho
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
        adm.toNamedAdmissibleCore.toNamedUnforgeable
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1)
        (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1) w
        S.hc.η_SG (q + 1) v hv (by simpa only [read] using huraw)
    have hule : u.round ≤ q := Nat.le_of_lt_succ
      (NamedOutageClosure.window_bounds huwindow).2
    have huroundEq : u.round = q := Nat.le_antisymm hule hqle
    have hbroundQ : b.round = q := hbround.trans huroundEq
    have hba : b = a := Proofs.Optimistic.emits_attest_unique S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hbemit hemit
      (hbroundQ.trans haround.symm)
    have huEq : u = Protocol.sgVote a.erase := by
      rw [← hbproj, hba]
    have hheadRoot : head.root = (actionSGBlockAt S rho v q).root := by
      have huconf := congrArg Protocol.SGVote.confirmed huEq
      simpa only [Protocol.sgVote, NamedAttestation.erase, hconf,
        hconfirmedCarrier, Option.some.injEq] using huconf
    have hheadMem : head ∈ read.st.core.T := Proofs.HealingLemmas.find?_mem hfind
    obtain ⟨Headn, hHeaderase, hHeadrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1) (by
          simpa only [read] using hheadMem)
    have hheadCnRoot : Headn.erase.root = Cn.erase.root := by
      rw [hHeaderase, hCnerase]
      exact hheadRoot
    have hheadCarrier : head = actionSGBlockAt S rho v q := by
      rw [← hHeaderase, ← hCnerase]
      exact Protocol.runBlock_eq_of_root_eq
        adm.toNamedAdmissibleCore.toNamedRootCollisionFree
        hHeadrun hCnrun hheadCnRoot
    have hAC : Block.Preceq A C :=
      Block.preceq_trans (by simpa only [hheadCarrier] using hAhead) (hupper v hv)
    exact hAC

#print axioms confirmationAnchorAt_preceq_of_previousCarriers





private theorem voterCandidatePathAt_of_candidate
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {C : Block V}
    (hC : C ∈ voterCandidateTreeAt S rho w (s + 1)) :
    ∀ D : Block V,
      Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
      D ≠ voterAnchorAt S rho w (s + 1) → Block.Preceq D C → D ≠ C →
      D ∈ voterCandidateTreeAt S rho w (s + 1) := by
  let duty := voteDutyStore S rho w (s + 1)
  have hCraw : C ∈ voter_candidate_tree S.E duty.toHealing := by
    simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, duty, voteDutyStore] using hC
  have hCfull : C ∈ Protocol.get_filtered_block_tree duty.toHealing.toFG :=
    frozenVoterCandidateTree_subset_filtered S.E duty.toHealing hCraw
  have hCT : C ∈ duty.T :=
    Proofs.Records.get_filtered_block_tree_subset duty.toHealing.toFG hCfull
  have hpc : ParentClosed duty := by
    simpa only [duty, voteDutyStore, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w
  have hFJ : Block.Preceq duty.F duty.J := by
    simpa only [duty, voteDutyStore, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w
  have hrootAnchor : Block.Preceq
      (Protocol.get_fg_root duty.toHealing.toFG)
      (voterAnchorAt S rho w (s + 1)) := by
    simpa only [duty, voteDutyStore, voterAnchorAt, nodeAnchor, nodeRead,
      Internal.NamedRecoveryRead.voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      fg_root_preceq_get_sg_root_with_frame
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).cache S.E S.hc
        duty.toHealing (S.hc.round_of duty.toHealing.s)
  intro D hAD _hDne hDC _hDneC
  have hDT : D ∈ duty.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff duty).mp hpc).2 D C hCT hDC
  have hCprocessed : C ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s := by
    have hCdata := hCraw
    simp only [voter_candidate_tree, Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Finset.mem_filter] at hCdata
    exact hCdata.1.1.1
  have hDfull : D ∈ Protocol.get_filtered_block_tree duty.toHealing.toFG := by
    apply Proofs.Records.mem_filtered_of_preceq (st := duty.toHealing.toFG)
      hFJ hCfull hDT hDC
    exact Block.preceq_trans hrootAnchor hAD
  have hDprocessed : D ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s := by
    have hDprocessed' := WeakGoldfish.ancestorProcessed_of_voterProcessed
      (S := S) (rho := rho) (w := w) (s := s) (B := C)
      (adm := adm.toNamedAdmissibleCore) hw hCprocessed D hDC
    simpa only [duty] using hDprocessed'
  have hCdata := hCraw
  have hDdata := hDfull
  simp only [voter_candidate_tree, Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hCdata hDdata
  obtain ⟨W, hWprocessed, hCW, hheight⟩ := hCdata.1.2
  have hDcandidate' : D ∈ voter_candidate_tree S.E duty.toHealing := by
    simp only [voter_candidate_tree, Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hDprocessed, hDdata.1.1.2⟩, W, hWprocessed,
      Block.preceq_trans hDC hCW, hheight⟩, hDdata.2⟩
  simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
    NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock, duty, voteDutyStore] using hDcandidate'



/-- The vote-only form used at the half-open boundary, where the confirmation
read belongs to the preceding record. -/
private theorem relayVoteInputs_step
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    (hsb : SlashableBound S rho)
    {r : Round} {s : Slot} (hround : S.hc.round_of (s + 1) = r + 1)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V} {M : Height}
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq C X))
    (hthin : ThinHonestHeadAt S rho M s C)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) C)
    (hvoteFrontier : ∀ w ∈ rho.honest,
      (voteDutyStore S rho w (s + 1)).h_max = M)
    (hvoteGate : ∀ w ∈ rho.honest,
      (voteDutyStore S rho w (s + 1)).h_j + 2 ≤ M)
    (hvoteRoot : ∀ w ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (voteDutyStore S rho w (s + 1)).toHealing.toFG) C) :
    (∀ w ∈ rho.honest, GoldfishConeVoteInputs S rho s C w) ∧
      ∀ w ∈ rho.honest,
        Block.Preceq (voterAnchorAt S rho w (s + 1)) C := by
  have hvoteFacts := fun w (hw : w ∈ rho.honest) =>
    seedRelayVoteFacts S adm hsb hpost hhor hvotes hthin hw
      (hvoteFrontier w hw) (hvoteGate w hw) (hvoteRoot w hw)
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  have hanchor : ∀ w ∈ rho.honest, Block.Preceq
      (voterAnchorAt S rho w (s + 1)) C := by
    intro w hw
    exact voterAnchorAt_preceq_of_previousCarriers S adm hfb hround
      hpostAction hcut hvoteHor hupper hw (hvoteRoot w hw)
  refine ⟨?_, hanchor⟩
  intro w hw
  have hcandidate : C ∈ voterCandidateTreeAt S rho w (s + 1) := by
    simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      voteDutyStore] using (hvoteFacts w hw).1
  exact
    { candidate := hcandidate
      root := hvoteRoot w hw
      anchor := by
        simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inl (hanchor w hw)
      path := voterCandidatePathAt_of_candidate S adm hw hcandidate }

/-- The complete slot input after relaying the preceding honest vote cone. -/
private theorem relaySlotInputs_step
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    (hsb : SlashableBound S rho)
    {r : Round} {s : Slot} (hround : S.hc.round_of (s + 1) = r + 1)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V} {M : Height}
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq C X))
    (hthin : ThinHonestHeadAt S rho M s C)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) C)
    (hvoteFrontier : ∀ w ∈ rho.honest,
      (voteDutyStore S rho w (s + 1)).h_max = M)
    (hvoteGate : ∀ w ∈ rho.honest,
      (voteDutyStore S rho w (s + 1)).h_j + 2 ≤ M)
    (hvoteRoot : ∀ w ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (voteDutyStore S rho w (s + 1)).toHealing.toFG) C)
    (hconfFrontier : ∀ w ∈ rho.honest,
      (confStore S rho w s).h_max = M)
    (hconfGate : ∀ w ∈ rho.honest,
      (confStore S rho w s).h_j + 2 ≤ M)
    (hconfRoot : ∀ w ∈ rho.honest,
      Block.Preceq (confRoot (confStore S rho w s)) C) :
    GoldfishConeSlotInputs S rho s C ∧
      ∀ w ∈ rho.honest,
        Block.Preceq (voterAnchorAt S rho w (s + 1)) C := by
  have hvoteFacts := fun w (hw : w ∈ rho.honest) =>
    seedRelayVoteFacts S adm hsb hpost hhor hvotes hthin hw
      (hvoteFrontier w hw) (hvoteGate w hw) (hvoteRoot w hw)
  have hcanMem : ∀ w ∈ rho.honest,
      C ∈ (voteDutyStore S rho w (s + 1)).T := by
    intro w hw
    exact Proofs.Records.get_filtered_block_tree_subset _
      (frozenVoterCandidateTree_subset_filtered S.E _ (hvoteFacts w hw).1)
  have hsupportVote := voteDutySupportAligned_of_previousActionCeiling
    S adm hround hpostAction hcut hcanMem hupper
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  have hvoteAnchor : ∀ w ∈ rho.honest,
      Block.Preceq (voterAnchorAt S rho w (s + 1)) C := by
    intro w hw
    exact voterAnchorAt_preceq_of_previousCarriers S adm hfb hround
      hpostAction hcut
      hvoteHor
      hupper hw (hvoteRoot w hw)
  have hconfFacts := fun w (hw : w ∈ rho.honest) =>
    seedRelayConfirmationFacts S adm hsb hpost hhor hvotes hthin hw
      (hconfFrontier w hw) (hconfGate w hw) (hconfRoot w hw)
  have hconfAnchor : ∀ w ∈ rho.honest,
      Block.Preceq (confirmationAnchorAt S rho w s) C := by
    intro w hw
    exact confirmationAnchorAt_preceq_of_previousCarriers S adm hfb hround
      hpostAction hcut hhor hupper hw (by
        simpa only [confRoot, confStore, tickStore,
          Internal.NamedRecoveryRead.confirmationInputRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
          hconfRoot w hw)
  refine ⟨?_, hvoteAnchor⟩
  exact
    { vote := by
        intro w hw
        have hcandidate : C ∈ voterCandidateTreeAt S rho w (s + 1) := by
          simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
            voteDutyStore] using (hvoteFacts w hw).1
        exact
          { candidate := (hvoteFacts w hw).1
            root := hvoteRoot w hw
            anchor := by
              simp only [Block.compatible, Bool.or_eq_true]
              exact Or.inl (hvoteAnchor w hw)
            path := voterCandidatePathAt_of_candidate S adm hw hcandidate }
      confirmation := by
        intro w hw
        exact
          { candidate := by
              simpa only [filteredTree, confTree, confStore, tickStore,
                Internal.NamedRecoveryRead.confirmationInputRead,
                NamedActionReads.confirmationReadAt,
                NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
                (hconfFacts w hw).1
            root := by
              simpa only [confRoot, confStore, tickStore,
                Internal.NamedRecoveryRead.confirmationInputRead,
                NamedActionReads.confirmationReadAt,
                NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
                hconfRoot w hw
            anchor := by
              simp only [Block.compatible, Bool.or_eq_true]
              exact Or.inl (hconfAnchor w hw)
            path := (hconfFacts w hw).2 } }

/-- A genuine prepared confirmation names a block held by its input read. -/
theorem genuineConfirmation_runBlock_step
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {D : Block V}
    (hD : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho w s).cache)
      S.E S.hc (confStore S rho w s) s D) :
    ∃ Dn : NamedBlock V, Dn.erase = D ∧ RunBlock S rho Dn := by
  let read := Internal.NamedRecoveryRead.confirmationInputRead S rho w s
  let contract := NamedProfile.gradeContract read.cache
  have hwalk : namedConfirmationWalk S read s = D := by
    have hselected := hD.selected
    rw [update_confirmation_with_live_confirmed, if_pos hD.genuine] at hselected
    simpa only [read, contract, namedConfirmationWalk, confWalkWith,
      Proofs.Optimistic.confStore_eq_confirmationInputRead] using hselected
  have hroots : Proofs.NamedStoreRoots.RootsInTree read.st := by
    have hbase :=
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
        (Protocol.confirmation_time S.E s) w).1.1.2
    simpa only [read, Internal.NamedRecoveryRead.confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom] using
        Proofs.NamedStoreRoots.roots_clock S.E
          (NamedRun.stateBeforeTime S rho
            (Protocol.confirmation_time S.E s) w).st
          (Protocol.confirmation_time S.E s) hbase
  have hDread : D ∈ read.st.core.T := by
    rw [← hwalk]
    exact Proofs.UserConfirmation.namedConfirmationWalk_mem S read s hroots
  have hDstrict : D ∈
      (NamedRun.stateBeforeTime S rho
        (Protocol.confirmation_time S.E s) w).st.core.T := by
    simpa only [read, Internal.NamedRecoveryRead.confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hDread
  exact Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
    (Protocol.confirmation_time S.E s) hDstrict

#print axioms genuineConfirmation_runBlock_step

/-! ## Ceiling persistence -/

/-- A genuine opening confirmation persists through every later vote and
genuine confirmation in the round. The confirmation may itself be below the
frontier band: the honest vote heads of the round supply its activity, and the
ceiling's root ordering supplies the local root floor. -/
theorem roundCeiling_persistence
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsb : SlashableBound S rho)
    {M : Height} {q : Round} {C : NamedBlock V} {D : Block V}
    (h : RoundCeilingAt S rho M q C)
    {v : V} (hv : v ∈ rho.honest)
    (hD : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v
          (S.hc.opening_slot q)).cache)
      S.E S.hc (confStore S rho v (S.hc.opening_slot q))
      (S.hc.opening_slot q) D) :
    (∀ s : Slot, S.hc.opening_slot q + 1 ≤ s →
      s ≤ seedRoundLastSlot S q →
        NamedHonestVotesCone S rho s (fun X => Block.Preceq D X)) ∧
    (∀ s : Slot, S.hc.opening_slot q + 1 ≤ s →
      s < seedRoundLastSlot S q →
        GoldfishConeSlotInputs S rho s D) ∧
    (∀ s : Slot, S.hc.opening_slot q + 1 ≤ s →
      s < seedRoundLastSlot S q → ∀ w ∈ rho.honest,
        ∀ E : Block V,
          GenuineConfirmationWith
            (NamedProfile.gradeContract
              (Internal.NamedRecoveryRead.confirmationInputRead S rho w s).cache)
            S.E S.hc (confStore S rho w s) s E →
            Block.Preceq D E) := by
  have hopenPos : 0 < S.hc.opening_slot q := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos h.roundPositive
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have holast : S.hc.opening_slot q < seedRoundLastSlot S q :=
    openingSlot_lt_last_step S q
  have hlastPos : 0 < seedRoundLastSlot S q := Nat.zero_lt_of_lt holast
  have hlastPred : seedRoundLastSlot S q - 1 + 1 = seedRoundLastSlot S q :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hosucc : S.hc.opening_slot q + 1 ≤ seedRoundLastSlot S q :=
    Nat.succ_le_iff.mpr holast
  have hCD : Block.Preceq C.erase D :=
    roundCeiling_openingConfirmation S adm hcom h hv hD
  have hopeningHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon :=
    (confirmationTime_mono_step S.E
      (openingSlot_le_lastPred_step S q)).trans
      h.roundConfirmationInHorizon
  have hopeningVotes := roundCeiling_openingVotes S adm hcom h
  obtain ⟨x, hxHonest, hxCommittee, hDH⟩ :=
    genuineConfirmation_exists_honestVoteSupporter_ceiling
      S adm hcom hv hopenPos h.postOpeningVote hopeningHor hD
  have hvoteHor : Protocol.vote_time S.E (S.hc.opening_slot q) ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E _).trans hopeningHor
  obtain ⟨H, hHerase, hHrun⟩ :=
    seedVoteDutyHead_runBlock S adm hxHonest (S.hc.opening_slot q)
  have hHemit := seedVoteDutyHead_emits S adm hxHonest
    (by
      unfold Protocol.HealConfig.opening_slot
      exact Nat.mul_pos h.roundPositive
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)) hxCommittee hvoteHor
  have hHemit' : rho.emits S x
      (.gfVote ⟨x, S.hc.opening_slot q, H.erase.root⟩)
      (Protocol.vote_time S.E (S.hc.opening_slot q)) := by
    rw [hHerase]
    exact hHemit
  have hH : NamedHonestHead S rho (S.hc.opening_slot q) H :=
    ⟨x, hxHonest, hxCommittee, hHrun, hHemit'⟩
  have hDH' : Block.Preceq D H.erase := by
    rw [hHerase]
    exact hDH
  have hHthin : M - 1 ≤ (derive_named S.E S.cfg H).h :=
    roundCeiling_headThin S adm h (le_refl _) (Nat.le_of_lt holast) hH
  have hH' : HonestHead S rho (S.hc.opening_slot q) H.erase :=
    ⟨x, hxHonest, hxCommittee, ⟨H, rfl, hHrun⟩, hHemit'⟩
  have hseedCandidate : ∀ w ∈ rho.honest,
      w ∈ S.E.committee (S.hc.opening_slot q + 1) →
      D ∈ voter_candidate_tree S.E
        (voteDutyStore S rho w (S.hc.opening_slot q + 1)).toHealing := by
    intro w hw _
    have hrootC := h.aboveRoot.voteDuty (S.hc.opening_slot q + 1)
      (Nat.le_succ _) hosucc w hw
    have hrootD : Block.Preceq
        (Protocol.get_fg_root
          (voteDutyStore S rho w
            (S.hc.opening_slot q + 1)).toHealing.toFG) D :=
      Block.preceq_trans hrootC hCD
    have hHprocessed := honestHead_voterProcessed_at_nextDuty_of_postHealingCone
      S adm h.postOpeningVote hopeningHor hopeningVotes hH' hw hrootC
    have hHmem : H.erase ∈ (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (S.hc.opening_slot q + 1))).T := by
      have hdata := hHprocessed
      simp only [Protocol.voter_processed_block_tree,
        Finset.mem_filter] at hdata
      simpa only [voteDutyStore, voteStore, tickStore] using hdata.1
    have hfrontier := h.gateOff.voteFrontier (S.hc.opening_slot q + 1)
      (Nat.le_succ _) (by simpa only [hlastPred] using hosucc) w hw
    have hgate := h.gateOff.voteGateOff (S.hc.opening_slot q + 1)
      (Nat.le_succ _) (by simpa only [hlastPred] using hosucc) w hw
    have hM : 1 ≤ M :=
      (Nat.succ_le_succ (Nat.zero_le 1)).trans
        ((Nat.le_add_left 2
          (voteDutyStore S rho w (S.hc.opening_slot q + 1)).h_j).trans hgate)
    have hvoteNextHor : Protocol.vote_time S.E
        (S.hc.opening_slot q + 1) ≤ rho.horizon := by
      apply le_trans (le_of_lt ?_) hopeningHor
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time
        S.E (S.hc.opening_slot q)]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos
    have hfilteredPre := frontierAncestor_filtered_of_gateOff
      S adm hsb hw hvoteNextHor hHmem rfl hHrun hDH' hHthin hM
        (by simpa only [voteDutyStore, voteStore, tickStore] using hfrontier)
        (by simpa only [voteDutyStore, voteStore, tickStore] using hgate)
        (by simpa only [voteDutyStore, voteStore, tickStore] using hrootD)
    have hfiltered : D ∈ Protocol.get_filtered_block_tree
        (voteDutyStore S rho w
          (S.hc.opening_slot q + 1)).toHealing.toFG := by
      simpa only [voteDutyStore, voteStore, tickStore] using hfilteredPre
    have hmax : (voteDutyStore S rho w (S.hc.opening_slot q + 1)).h_max ≤
        (derive_named S.E S.cfg H).h + 1 := by
      rw [hfrontier]
      exact Nat.sub_le_iff_le_add.mp hHthin
    exact namedAncestorCandidate_of_processedDescendant_and_hMax
      S adm hw hHprocessed hHrun hDH' hfiltered hmax
  have hseedAnchor : ∀ w ∈ rho.honest,
      w ∈ S.E.committee (S.hc.opening_slot q + 1) →
      Block.Preceq
        (voterAnchorAt S rho w (S.hc.opening_slot q + 1)) D := by
    intro w hw _
    exact Block.preceq_trans
      (h.voteAnchor (S.hc.opening_slot q + 1) (Nat.le_succ _) hosucc w hw) hCD
  have hconeSucc :=
    honestVotesCone_succ_of_genuineConfirmation_of_frozenVoteReads
      S adm hv h.postOpeningProposal hopeningHor
      (show GenuineConfirmation (contract :=
        NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v
            (S.hc.opening_slot q)).cache)
          S.E S.hc (confStore S rho v (S.hc.opening_slot q))
            (S.hc.opening_slot q) D from ⟨hD.selected, hD.genuine⟩)
      hseedCandidate hseedAnchor
  have hstep : ∀ s : Slot, S.hc.opening_slot q + 1 ≤ s →
      s ≤ seedRoundLastSlot S q - 1 →
      NamedHonestVotesCone S rho s (fun X => Block.Preceq D X) →
      GoldfishConeSlotInputs S rho s D := by
    intro s hlo hhi hcone
    have hslo : S.hc.opening_slot q ≤ s := (Nat.le_succ _).trans hlo
    have hsuccHi : s + 1 ≤ seedRoundLastSlot S q := by
      rw [← hlastPred]
      exact Nat.succ_le_succ hhi
    have hshi : s ≤ seedRoundLastSlot S q := (Nat.le_succ s).trans hsuccHi
    have hslt : s < seedRoundLastSlot S q :=
      lt_of_lt_of_le (Nat.lt_succ_self s) hsuccHi
    have hthin : ThinHonestHeadAt S rho M s D :=
      roundCeiling_thinHead_of_cone S adm hcom h hslo hshi hcone
    have hpostS : S.E.t_GST ≤ Protocol.vote_time S.E s :=
      h.postOpeningVote.trans (Protocol.vote_time_mono_slots S.E hslo)
    have hhorS : Protocol.confirmation_time S.E s ≤ rho.horizon :=
      (confirmationTime_mono_step S.E hhi).trans h.roundConfirmationInHorizon
    constructor
    · intro w hw
      have hfrontier := h.gateOff.voteFrontier (s + 1)
        (hslo.trans (Nat.le_succ s))
        (by simpa only [hlastPred] using hsuccHi) w hw
      have hgate := h.gateOff.voteGateOff (s + 1)
        (hslo.trans (Nat.le_succ s))
        (by simpa only [hlastPred] using hsuccHi) w hw
      have hrootC := h.aboveRoot.voteDuty (s + 1)
        (hslo.trans (Nat.le_succ s)) hsuccHi w hw
      have hrootD : Block.Preceq
          (Protocol.get_fg_root
            (voteDutyStore S rho w (s + 1)).toHealing.toFG) D :=
        Block.preceq_trans hrootC hCD
      have hfacts := seedRelayVoteFacts S adm hsb hpostS hhorS hcone hthin
        hw hfrontier hgate hrootD
      have hcandidate : D ∈ voterCandidateTreeAt S rho w (s + 1) := by
        simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
          voteDutyStore] using hfacts.1
      exact
        { candidate := hcandidate
          root := hrootD
          anchor := by
            simp only [Block.compatible, Bool.or_eq_true]
            exact Or.inl (Block.preceq_trans
              (h.voteAnchor (s + 1) (hslo.trans (Nat.le_succ s))
                hsuccHi w hw) hCD)
          path := voterCandidatePathAt_of_candidate S adm hw hcandidate }
    · intro w hw
      have hfrontier := h.gateOff.confirmationFrontier s hslo hhi w hw
      have hgate := h.gateOff.confirmationGateOff s hslo hhi w hw
      have hrootC := h.aboveRoot.confirmation s hslo hslt w hw
      have hrootD : Block.Preceq (confRoot (confStore S rho w s)) D :=
        Block.preceq_trans hrootC hCD
      have hfacts := seedRelayConfirmationFacts S adm hsb hpostS hhorS hcone
        hthin hw hfrontier hgate hrootD
      exact
        { candidate := hfacts.1
          root := hrootD
          anchor := by
            simp only [Block.compatible, Bool.or_eq_true]
            exact Or.inl (Block.preceq_trans
              (h.confirmationAnchor s
                ((Nat.sub_le _ _).trans hslo) hslt w hw) hCD)
          path := hfacts.2 }
  have hfold : ∀ s : Slot, S.hc.opening_slot q + 1 ≤ s →
      s ≤ seedRoundLastSlot S q →
      NamedHonestVotesCone S rho s (fun X => Block.Preceq D X) := by
    intro s hlo
    induction s, hlo using Nat.le_induction with
    | base => intro _; exact hconeSucc
    | succ s hlo ih =>
        intro hsuccHi
        have hshi : s ≤ seedRoundLastSlot S q - 1 :=
          Nat.le_pred_of_lt
            (lt_of_lt_of_le (Nat.lt_succ_self s) hsuccHi)
        have hcone := ih (hshi.trans (Nat.sub_le _ _))
        have hslo : S.hc.opening_slot q ≤ s := (Nat.le_succ _).trans hlo
        have hsPos : 0 < s := lt_of_lt_of_le hopenPos hslo
        have hpostS : S.E.t_GST ≤ Protocol.vote_time S.E s :=
          h.postOpeningVote.trans (Protocol.vote_time_mono_slots S.E hslo)
        have hhorS : Protocol.confirmation_time S.E s ≤ rho.horizon :=
          (confirmationTime_mono_step S.E hshi).trans h.roundConfirmationInHorizon
        have hinputs := hstep s hlo hshi hcone
        exact seedHonestVotesCone_succ S adm hcom hsPos hpostS hhorS hcone
          (fun w hw => hinputs.vote w hw)
  refine ⟨hfold, ?_, ?_⟩
  · intro s hlo hhi
    exact hstep s hlo (Nat.le_pred_of_lt hhi)
      (hfold s hlo (Nat.le_of_lt hhi))
  intro s hlo hhi w hw E hE
  have hshi : s ≤ seedRoundLastSlot S q - 1 := Nat.le_pred_of_lt hhi
  have hcone := hfold s hlo (hshi.trans (Nat.sub_le _ _))
  have hslo : S.hc.opening_slot q ≤ s := (Nat.le_succ _).trans hlo
  have hsPos : 0 < s := lt_of_lt_of_le hopenPos hslo
  have hpostS : S.E.t_GST ≤ Protocol.vote_time S.E s :=
    h.postOpeningVote.trans (Protocol.vote_time_mono_slots S.E hslo)
  have hhorS : Protocol.confirmation_time S.E s ≤ rho.horizon :=
    (confirmationTime_mono_step S.E hshi).trans h.roundConfirmationInHorizon
  have hinputs := hstep s hlo hshi hcone
  exact goldfishCone_confirmation S adm hcom hsPos hpostS hhorS hcone hw
    (hinputs.confirmation w hw) hE

#print axioms roundCeiling_persistence



/-- The named vote-cone successor used by the ceiling fold. -/
private theorem honestVotesCone_succ_step
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq C X))
    (hinputs : ∀ w ∈ rho.honest, GoldfishConeVoteInputs S rho s C w) :
    NamedHonestVotesCone S rho (s + 1) (fun X => Block.Preceq C X) :=
  seedHonestVotesCone_succ S adm hcom hs hpost hhor hvotes hinputs

private theorem last_lt_nextOpening_step
    (S : Setup V) (q : Round) :
    seedRoundLastSlot S q < S.hc.opening_slot (q + 1) := by
  unfold seedRoundLastSlot
  have hpos : 0 < S.hc.opening_slot (q + 1) := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos (Nat.succ_pos q)
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  exact Nat.sub_lt hpos Nat.zero_lt_one

private theorem roundOf_succ_eq_step
    (S : Setup V) {q : Round} {s : Slot}
    (hlo : S.hc.opening_slot (q + 1) ≤ s)
    (hhi : s ≤ seedRoundLastSlot S (q + 1) - 1) :
    S.hc.round_of (s + 1) = q + 1 := by
  apply round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc
  · exact Nat.succ_le_succ hlo
  · have hlastPos : 0 < seedRoundLastSlot S (q + 1) :=
      Nat.zero_lt_of_lt (openingSlot_lt_last_step S (q + 1))
    have hsuccLast : s + 1 ≤ seedRoundLastSlot S (q + 1) := by
      rw [← Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)]
      exact Nat.succ_le_succ hhi
    exact hsuccLast.trans_lt (last_lt_nextOpening_step S (q + 1))

/-- The common boundary cone needed by the regime-only successor proof. This
is the exact data that a first-ceiling producer must construct. -/
structure RoundCeilingBoundaryConeAt
    (S : Setup V) (rho : Run V) (M : Height) (q : Round) (C : NamedBlock V) :
    Prop where
  run : RunBlock S rho C
  /-- The boundary vote cone contains a head that reaches the local viability
  boundary. The ceiling itself may be below the frontier band. -/
  boundaryThinHead : ThinHonestHeadAt S rho M
    (S.hc.opening_slot (q + 1) - 1) C.erase
  postAction : S.E.t_GST ≤ S.a q
  postBoundaryVote : S.E.t_GST ≤
    Protocol.vote_time S.E (S.hc.opening_slot (q + 1) - 1)
  boundaryVotes : NamedHonestVotesCone S rho
    (S.hc.opening_slot (q + 1) - 1) (fun X => Block.Preceq C.erase X)
  previousCarriers : ∀ v ∈ rho.honest,
    Block.Preceq (actionSGBlockAt S rho v q) C.erase
  /-- Every FG root read in round `q + 1` is at or below the ceiling. -/
  rootOrder : RoundCeilingNextRootOrderAt S rho q C.erase

private structure RoundCeilingRelayFoldAt
    (S : Setup V) (rho : Run V) (q : Round) (C : Block V) : Prop where
  openingStepInputs : ∀ w ∈ rho.honest,
    GoldfishConeVoteInputs S rho (S.hc.opening_slot (q + 1) - 1) C w
  roundInputs : ∀ s : Slot,
    S.hc.opening_slot (q + 1) ≤ s →
      s < seedRoundLastSlot S (q + 1) →
        GoldfishConeSlotInputs S rho s C
  voteActive : ∀ d : Slot,
    S.hc.opening_slot (q + 1) ≤ d →
      d ≤ seedRoundLastSlot S (q + 1) → ∀ w ∈ rho.honest,
        C ∈ Protocol.get_filtered_block_tree
          (voteDutyStore S rho w d).toHealing.toFG
  voteAnchor : ∀ d : Slot,
    S.hc.opening_slot (q + 1) ≤ d →
      d ≤ seedRoundLastSlot S (q + 1) → ∀ w ∈ rho.honest,
        Block.Preceq (voterAnchorAt S rho w d) C
  confirmationAnchor : ∀ s : Slot,
    S.hc.opening_slot (q + 1) - 1 ≤ s →
      s < seedRoundLastSlot S (q + 1) → ∀ w ∈ rho.honest,
        Block.Preceq (confirmationAnchorAt S rho w s) C

set_option maxHeartbeats 800000 in
private theorem roundCeilingRelayFold_of_regime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    (hsb : SlashableBound S rho)
    {M : Height} {q : Round} {C : Block V}
    (hpostAction : S.E.t_GST ≤ S.a q)
    (hcut : S.hc.Γ_neg1 S.E.Δ (q + 1) ≤ rho.horizon)
    (hpost0 : S.E.t_GST ≤ Protocol.vote_time S.E
      (S.hc.opening_slot (q + 1) - 1))
    (hhor0 : Protocol.confirmation_time S.E
      (S.hc.opening_slot (q + 1) - 1) ≤ rho.horizon)
    (hlastVotes : NamedHonestVotesCone S rho
      (S.hc.opening_slot (q + 1) - 1) (fun X => Block.Preceq C X))
    (hboundaryThin : ThinHonestHeadAt S rho M
      (S.hc.opening_slot (q + 1) - 1) C)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u q) C)
    (hrootOrder : RoundCeilingNextRootOrderAt S rho q C)
    (hreg : RoundCeilingNextRegimeAt S rho M q) :
    RoundCeilingRelayFoldAt S rho q C := by
  let o := S.hc.opening_slot (q + 1)
  let last := seedRoundLastSlot S (q + 1)
  let s0 := o - 1
  have hs0Pos : 0 < s0 := by
    unfold s0 o Protocol.HealConfig.opening_slot
    have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
    have hopenTwo : 2 ≤ (q + 1) * S.hc.R := by
      simpa only [Nat.one_mul] using
        Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le q)) hR
    exact Nat.sub_pos_of_lt (Nat.one_lt_two.trans_le hopenTwo)
  have hs0Succ : s0 + 1 = o := by
    simpa only [s0, o] using openingSlot_pred_succ_step S (Nat.succ_pos q)
  have hlastPos : 0 < last := by
    exact Nat.zero_lt_of_lt (by
      simpa only [o, last] using openingSlot_lt_last_step S (q + 1))
  have hoPos : 0 < o := by
    unfold o Protocol.HealConfig.opening_slot
    exact Nat.mul_pos (Nat.succ_pos q)
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hopenLast : o ≤ last := by
    exact Nat.le_of_lt (by
      simpa only [o, last] using openingSlot_lt_last_step S (q + 1))
  have hlastPredSucc : last - 1 + 1 = last :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hopenHiSucc : o ≤ (last - 1) + 1 := by
    rw [hlastPredSucc]
    exact hopenLast
  have hround0 : S.hc.round_of (s0 + 1) = q + 1 := by
    rw [hs0Succ]
    exact round_of_opening_slot_eq_schedule S.hc (q + 1)
  have hvoteHorAt : ∀ d : Slot, d ≤ last →
      Protocol.vote_time S.E d ≤ rho.horizon := by
    intro d hd
    have hlastToConf : Protocol.vote_time S.E last ≤
        Protocol.confirmation_time S.E (last - 1) := by
      rw [← hlastPredSucc,
        ← Protocol.vote_time_succ_add_delta_eq_confirmation_time]
      exact le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
    exact (Protocol.vote_time_mono_slots S.E hd).trans
      (hlastToConf.trans (by simpa only [last] using
        hreg.roundConfirmationInHorizon))
  have hopening := relayVoteInputs_step S adm hfb hsb hround0 hpostAction hcut
    (by simpa only [s0, o] using hpost0)
    (by simpa only [s0, o] using hhor0)
    (by simpa only [s0, o] using hlastVotes)
    (by simpa only [s0, o] using hboundaryThin) hupper
    (by
      intro w hw
      simpa only [hs0Succ] using
        hreg.window.voteFrontier o (le_refl _) hopenHiSucc w hw)
    (by
      intro w hw
      simpa only [hs0Succ] using
        hreg.window.voteGateOff o (le_refl _) hopenHiSucc w hw)
    (by
      intro w hw
      simpa only [hs0Succ] using
        hrootOrder.voteDuty o (le_refl _) hopenLast w hw)
  have hopeningInput := hopening.1
  have hopeningAnchor := hopening.2
  have hopeningVotes : NamedHonestVotesCone S rho o
      (fun X => Block.Preceq C X) := by
    simpa only [hs0Succ] using honestVotesCone_succ_step
      S adm hcom hs0Pos (by simpa only [s0, o] using hpost0)
        (by simpa only [s0, o] using hhor0)
        (by simpa only [s0, o] using hlastVotes) hopeningInput
  have hopeningThin : ThinHonestHeadAt S rho M o C := by
    have hthin := seedThinHead_of_voteInputs S adm hcom
      (s := s0) (C := C) (E := C)
      (by
        rw [hs0Succ]
        exact hvoteHorAt o hopenLast)
      hopeningInput hopeningAnchor
      (by
        intro w hw
        simpa only [hs0Succ] using
          hreg.window.voteFrontier o (le_refl _) hopenHiSucc w hw)
      (by simpa only [hs0Succ] using hopeningVotes)
    simpa only [hs0Succ] using hthin
  have hslotInput : ∀ s : Slot, o ≤ s → s ≤ last - 1 →
      NamedHonestVotesCone S rho s (fun X => Block.Preceq C X) →
      ThinHonestHeadAt S rho M s C →
      GoldfishConeSlotInputs S rho s C ∧
        (∀ w ∈ rho.honest,
          Block.Preceq (voterAnchorAt S rho w (s + 1)) C) := by
    intro s hlo hhi hvotes hthin
    have hround : S.hc.round_of (s + 1) = q + 1 := by
      exact roundOf_succ_eq_step S (by simpa only [o] using hlo)
        (by simpa only [last] using hhi)
    have hpostBase : S.E.t_GST ≤ Protocol.vote_time S.E s0 := by
      simpa only [s0, o] using hpost0
    have hs0s : s0 ≤ s := by
      have hs0o : s0 ≤ o := by rw [← hs0Succ]; exact Nat.le_succ s0
      exact hs0o.trans hlo
    have hpostS : S.E.t_GST ≤ Protocol.vote_time S.E s :=
      hpostBase.trans (vote_time_mono_slots S.E hs0s)
    have hhorS : Protocol.confirmation_time S.E s ≤ rho.horizon :=
      (confirmationTime_mono_step S.E hhi).trans
        (by simpa only [last] using hreg.roundConfirmationInHorizon)
    have hsuccLast : s + 1 ≤ last := by
      rw [← hlastPredSucc]
      exact Nat.succ_le_succ hhi
    refine relaySlotInputs_step S adm hfb hsb hround hpostAction hcut
      hpostS hhorS hvotes hthin hupper ?_ ?_ ?_ ?_ ?_ ?_
    · intro w hw
      exact hreg.window.voteFrontier (s + 1)
        (hlo.trans (Nat.le_succ s))
        (Nat.succ_le_succ hhi) w hw
    · intro w hw
      exact hreg.window.voteGateOff (s + 1)
        (hlo.trans (Nat.le_succ s))
        (Nat.succ_le_succ hhi) w hw
    · intro w hw
      exact hrootOrder.voteDuty (s + 1)
        (by simpa only [o] using hlo.trans (Nat.le_succ s))
        (by simpa only [last] using hsuccLast) w hw
    · intro w hw
      exact hreg.window.confirmationFrontier s
        (by simpa only [o] using hlo) hhi w hw
    · intro w hw
      exact hreg.window.confirmationGateOff s
        (by simpa only [o] using hlo) hhi w hw
    · intro w hw
      exact hrootOrder.confirmation s
        (by
          simpa only [o, s0] using
            (Nat.sub_le o 1).trans hlo)
        (by
          simpa only [last] using
            lt_of_le_of_lt hhi (Nat.sub_lt hlastPos Nat.zero_lt_one)) w hw
  have hfold : ∀ s : Slot, o ≤ s → s ≤ last - 1 →
      NamedHonestVotesCone S rho s (fun X => Block.Preceq C X) ∧
        ThinHonestHeadAt S rho M s C ∧
        GoldfishConeSlotInputs S rho s C ∧
        (∀ w ∈ rho.honest,
          Block.Preceq (voterAnchorAt S rho w (s + 1)) C) := by
    intro s hlo
    induction s, hlo using Nat.le_induction with
    | base =>
        intro hhi
        have hin := hslotInput o (le_refl _) hhi hopeningVotes hopeningThin
        exact ⟨hopeningVotes, hopeningThin, hin.1, hin.2⟩
    | succ s hlo ih =>
        intro hsuccHi
        have hsHi : s ≤ last - 1 := (Nat.le_succ s).trans hsuccHi
        obtain ⟨hcone, hthin, hinp, hanch⟩ := ih hsHi
        have hsPos : 0 < s := lt_of_lt_of_le hoPos hlo
        have hpostBase : S.E.t_GST ≤ Protocol.vote_time S.E s0 := by
          simpa only [s0, o] using hpost0
        have hs0s : s0 ≤ s := by
          have hs0o : s0 ≤ o := by rw [← hs0Succ]; exact Nat.le_succ s0
          exact hs0o.trans hlo
        have hpostS : S.E.t_GST ≤ Protocol.vote_time S.E s :=
          hpostBase.trans (vote_time_mono_slots S.E hs0s)
        have hhorS : Protocol.confirmation_time S.E s ≤ rho.horizon :=
          (confirmationTime_mono_step S.E hsHi).trans
            (by simpa only [last] using hreg.roundConfirmationInHorizon)
        have hsuccLast : s + 1 ≤ last := by
          rw [← hlastPredSucc]
          exact Nat.succ_le_succ hsHi
        have hvotesNext := honestVotesCone_succ_step S adm hcom hsPos
          hpostS hhorS hcone (fun w hw => hinp.vote w hw)
        have hthinNext : ThinHonestHeadAt S rho M (s + 1) C :=
          seedThinHead_of_voteInputs S adm hcom
            (hvoteHorAt (s + 1) hsuccLast)
            (fun w hw => hinp.vote w hw) hanch
            (fun w hw => hreg.window.voteFrontier (s + 1)
              (hlo.trans (Nat.le_succ s)) (Nat.succ_le_succ hsHi) w hw)
            hvotesNext
        have hin := hslotInput (s + 1) (hlo.trans (Nat.le_succ s)) hsuccHi
          hvotesNext hthinNext
        exact ⟨hvotesNext, hthinNext, hin.1, hin.2⟩
  have hroundInputs : ∀ s : Slot, o ≤ s → s < last →
      GoldfishConeSlotInputs S rho s C := by
    intro s hlo hhi
    exact (hfold s hlo (Nat.le_pred_of_lt hhi)).2.2.1
  refine
    { openingStepInputs := by
        simpa only [s0, o] using hopeningInput
      roundInputs := by
        intro s hlo hhi
        exact hroundInputs s (by simpa only [o] using hlo)
          (by simpa only [last] using hhi)
      voteActive := ?_
      voteAnchor := ?_
      confirmationAnchor := ?_ }
  · intro d hdlo hdhi w hw
    by_cases heq : d = o
    · subst d
      exact frozenVoterCandidateTree_subset_filtered S.E _
        (by simpa only [hs0Succ] using (hopeningInput w hw).candidate)
    · have hdLt : o < d := lt_of_le_of_ne hdlo (Ne.symm heq)
      have hdPred : o ≤ d - 1 := Nat.le_pred_of_lt hdLt
      have hdPos : 0 < d := hoPos.trans_le hdlo
      have hdSucc : d - 1 + 1 = d := Nat.sub_add_cancel
        (Nat.succ_le_iff.mpr hdPos)
      have hpredLt : d - 1 < last := by
        exact lt_of_lt_of_le (Nat.sub_lt hdPos Nat.zero_lt_one) hdhi
      have hin := hroundInputs (d - 1) hdPred hpredLt
      simpa only [hdSucc] using
        frozenVoterCandidateTree_subset_filtered S.E _ (hin.vote w hw).candidate
  · intro d hdlo hdhi w hw
    by_cases heq : d = o
    · subst d
      simpa only [hs0Succ] using hopeningAnchor w hw
    · have hdLt : o < d := lt_of_le_of_ne hdlo (Ne.symm heq)
      have hdPred : o ≤ d - 1 := Nat.le_pred_of_lt hdLt
      have hdPos : 0 < d := hoPos.trans_le hdlo
      have hdSucc : d - 1 + 1 = d := Nat.sub_add_cancel
        (Nat.succ_le_iff.mpr hdPos)
      have hpredLt : d - 1 < last := by
        exact lt_of_lt_of_le (Nat.sub_lt hdPos Nat.zero_lt_one) hdhi
      have hanch := (hfold (d - 1) hdPred
        (Nat.le_pred_of_lt hpredLt)).2.2.2
      simpa only [hdSucc] using hanch w hw
  · intro s hslo hshi w hw
    by_cases heq : s = s0
    · subst s
      exact confirmationAnchorAt_preceq_of_previousCarriers S adm hfb hround0
        hpostAction hcut hhor0 hupper hw (by
          simpa only [confRoot, confStore, tickStore,
            Internal.NamedRecoveryRead.confirmationInputRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
            hrootOrder.confirmation s0 (le_refl _)
              (by
                simpa only [s0, last] using
                  lt_of_lt_of_le (Nat.sub_lt hoPos Nat.zero_lt_one) hopenLast)
              w hw)
    · have hsLt : s0 < s := lt_of_le_of_ne hslo (Ne.symm heq)
      have hsMain : o ≤ s := by
        rw [← hs0Succ]
        exact Nat.succ_le_iff.mpr hsLt
      have hround := roundOf_succ_eq_step S
        (by simpa only [o] using hsMain)
        (by simpa only [last] using Nat.le_pred_of_lt hshi)
      have hhorS : Protocol.confirmation_time S.E s ≤ rho.horizon :=
        (confirmationTime_mono_step S.E
          (Nat.le_pred_of_lt hshi)).trans
          (by simpa only [last] using hreg.roundConfirmationInHorizon)
      exact confirmationAnchorAt_preceq_of_previousCarriers S adm hfb hround
        hpostAction hcut hhorS hupper hw (by
          simpa only [confRoot, confStore, tickStore,
            Internal.NamedRecoveryRead.confirmationInputRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
            hrootOrder.confirmation s
              (by
                simpa only [o, s0] using
                  (Nat.sub_le o 1).trans hsMain)
              (by simpa only [last] using
                hshi)
              w hw)

private theorem actionAnchor_eq_confirmationAnchorAt_opening_step
    (S : Setup V) (rho : Run V) (w : V) (q : Round) :
    PhaseGrades.nodeAnchor S
        (Internal.NamedRecoveryRead.actionDutyRead S rho w q) q =
      confirmationAnchorAt S rho w (S.hc.opening_slot q) := by
  let action := NamedActionReads.actionReadAt S rho w q
  let conf := Internal.NamedRecoveryRead.confirmationInputRead S rho w
    (S.hc.opening_slot q)
  have hroundConf : S.hc.round_of conf.st.core.s = q := by
    simpa only [conf, Internal.NamedRecoveryRead.confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.slotOf_confirmation_time] using
      Proofs.HealingLemmas.round_of_opening_succ S.hc q
  have hconfAnchor : confirmationAnchorAt S rho w
        (S.hc.opening_slot q) = nodeAnchor S conf q := by
    unfold confirmationAnchorAt namedConfirmationAnchor
    rw [hroundConf]
    rfl
  have htree : Protocol.get_filtered_block_tree
        action.st.core.toHealing.toFG =
      Protocol.get_filtered_block_tree conf.st.core.toHealing.toFG := by
    calc
      _ = Protocol.get_filtered_block_tree
          (Proofs.Optimistic.confStore S rho w (S.hc.opening_slot q)).toHealing.toFG := by
        simpa only [action, actionReadAt, actionStoreAt] using
          actionStoreAt_filteredTree_eq_openingConfStore S rho w q
      _ = Protocol.get_filtered_block_tree conf.st.core.toHealing.toFG := by
        simpa only [conf, Proofs.Optimistic.confStore_eq_confirmationInputRead]
  have hroot : Protocol.get_fg_root action.st.core.toHealing.toFG =
      Protocol.get_fg_root conf.st.core.toHealing.toFG := by
    calc
      _ = Protocol.get_fg_root
          (Proofs.Optimistic.confStore S rho w (S.hc.opening_slot q)).toHealing.toFG := by
        simpa only [action, actionReadAt, actionStoreAt] using
          actionStoreAt_fgRoot_eq_openingConfStore S rho w q
      _ = Protocol.get_fg_root conf.st.core.toHealing.toFG := by
        simpa only [conf, Proofs.Optimistic.confStore_eq_confirmationInputRead]
  have hframe : DecoupledConsensusModel.Protocol.readFrame action.cache
        action.st.core.toHealing q =
      DecoupledConsensusModel.Protocol.readFrame conf.cache conf.st.core.toHealing q := by
    rfl
  have hnode : nodeAnchor S action q = nodeAnchor S conf q := by
    change DecoupledConsensusModel.Protocol.anchor S.E S.hc action.st.core.toHealing q
        (DecoupledConsensusModel.Protocol.readFrame action.cache
          action.st.core.toHealing q).g1 =
      DecoupledConsensusModel.Protocol.anchor S.E S.hc conf.st.core.toHealing q
        (DecoupledConsensusModel.Protocol.readFrame conf.cache conf.st.core.toHealing q).g1
    rw [hframe]
    unfold DecoupledConsensusModel.Protocol.anchor
    rw [htree, hroot]
  simpa only [action, Internal.NamedRecoveryRead.actionDutyRead, actionReadAt,
    confirmationAnchorAt] using hnode.trans hconfAnchor.symm

private theorem ceiling_cacheAtRound_align_self_opening
    (c : DecoupledConsensusModel.Protocol.Cache V) (r : Round) :
    DecoupledConsensusModel.Protocol.cacheAtRound (DecoupledConsensusModel.Protocol.alignRound c r) r =
      DecoupledConsensusModel.Protocol.cacheAtRound c r := by
  by_cases h1 : r = c.round
  · rw [show DecoupledConsensusModel.Protocol.alignRound c r = c by
      unfold DecoupledConsensusModel.Protocol.alignRound
      rw [if_pos h1]]
  · by_cases h2 : r = c.round + 1
    · rw [show DecoupledConsensusModel.Protocol.alignRound c r =
        ⟨r, c.next, DecoupledConsensusModel.Protocol.pendingFrame⟩ by
        unfold DecoupledConsensusModel.Protocol.alignRound
        rw [if_neg h1, if_pos h2]]
      subst h2
      simp [DecoupledConsensusModel.Protocol.cacheAtRound]
    · rw [show DecoupledConsensusModel.Protocol.alignRound c r =
        ⟨r, DecoupledConsensusModel.Protocol.pendingFrame, DecoupledConsensusModel.Protocol.pendingFrame⟩ by
        unfold DecoupledConsensusModel.Protocol.alignRound
        rw [if_neg h1, if_neg h2]]
      simp [DecoupledConsensusModel.Protocol.cacheAtRound, h1, h2]

private theorem ceiling_clip_grade_compatible_opening (g F : Block V) :
    Block.compatible (DecoupledConsensusModel.Protocol.clipGrade g F) F = true := by
  induction g with
  | genesis => simp [DecoupledConsensusModel.Protocol.clipGrade,
      Block.compatible, Protocol.preceq_genesis]
  | node p s root gv gsv ats v ih =>
      simp only [DecoupledConsensusModel.Protocol.clipGrade]
      split
      · assumption
      · exact ih

private theorem ceiling_clip_grade_keeps_opening (g F : Block V)
    (h : Block.compatible g F = true) :
    DecoupledConsensusModel.Protocol.clipGrade g F = g := by
  cases g with
  | genesis => rfl
  | node p s root gv gsv ats v =>
      simp only [DecoupledConsensusModel.Protocol.clipGrade, h, ↓reduceIte]

private theorem ceiling_clip_grade_idempotent_opening (g F : Block V) :
    DecoupledConsensusModel.Protocol.clipGrade
        (DecoupledConsensusModel.Protocol.clipGrade g F) F =
      DecoupledConsensusModel.Protocol.clipGrade g F :=
  ceiling_clip_grade_keeps_opening _ _
    (ceiling_clip_grade_compatible_opening g F)

private theorem ceiling_clip_result_idempotent_opening
    (F : Block V) (x : Option (Option (Block V))) :
    DecoupledConsensusModel.Protocol.clipResult F (DecoupledConsensusModel.Protocol.clipResult F x) =
      DecoupledConsensusModel.Protocol.clipResult F x := by
  cases x with
  | none => rfl
  | some y =>
      cases y with
      | none => rfl
      | some B =>
          simp only [DecoupledConsensusModel.Protocol.clipResult, Option.map_some]
          rw [ceiling_clip_grade_idempotent_opening]

private theorem ceiling_clip_frame_idempotent_opening
    (F : Block V) (f : DecoupledConsensusModel.Protocol.Frame V) :
    DecoupledConsensusModel.Protocol.clipFrame F (DecoupledConsensusModel.Protocol.clipFrame F f) =
      DecoupledConsensusModel.Protocol.clipFrame F f := by
  cases f
  simp only [DecoupledConsensusModel.Protocol.clipFrame]
  congr 1 <;> exact ceiling_clip_result_idempotent_opening F _

theorem preparedFrame_g1_eq_storeRoot_at_opening
    (S : Setup V) (rho : Run V) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (r : Round) (hr : 0 < r) (t : Time)
    (hround : S.hc.round_of (S.E.slotOf t) = r)
    (hopen : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 = t)
    (hhor : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ rho.horizon) :
    (DecoupledConsensusModel.Protocol.readFrame
      (NamedActionReads.confirmationReadAt S rho w t).cache
      (NamedActionReads.confirmationReadAt S rho w t).st.core.toHealing r).g1 =
      some ((PhaseGrades.storeRoot S.E S.hc
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1).map
        (fun X => DecoupledConsensusModel.Protocol.clipGrade X
          (NamedActionReads.confirmationReadAt S rho w t).st.core.F)) := by
  let before := NamedRun.stateBeforeTime S rho t w
  let read := NamedActionReads.confirmationReadFrom S before t
  have hnotg2 : t ≠ DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2 := by
    intro heq
    exact (ne_of_gt (NamedOutageClosure.q10_domain_g2_lt_domain_g1 S r))
      (hopen.trans heq)
  have hnotg0 : t ≠ DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 := by
    intro heq
    have h10 : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 <
        DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 := by
      unfold DecoupledConsensusModel.Protocol.domain
      simp only [DecoupledConsensusModel.Protocol.Phase.domainOffset, zero_mul, one_mul, add_zero]
      exact lt_add_of_pos_right _ S.E.Δ_pos
    exact (ne_of_gt h10) (hopen.trans heq).symm
  have hrawNone : DecoupledConsensusModel.Protocol.phaseResult
        (DecoupledConsensusModel.Protocol.cacheAtRound before.cache r) .g1 = none := by
    by_contra hnone
    obtain ⟨root, hroot⟩ := Option.ne_none_iff_exists'.mp hnone
    rcases NamedCacheProvenance.completed_phase_before_read S rho core.sorted
      core.nodup t w r .g1 root hroot with hzero | hdone
    · exact (Nat.ne_of_gt hr) hzero.1
    · obtain ⟨j, u, hj, hu, hdom, hvalue⟩ := hdone
      have hlt : t < t := by
        calc
          t = DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 := hopen.symm
          _ = u := hdom.symm
          _ < t := hu
      exact (lt_irrefl t) hlt
  let aligned := DecoupledConsensusModel.Protocol.alignRound before.cache r
  have halign : DecoupledConsensusModel.Protocol.cacheAtRound aligned r =
      DecoupledConsensusModel.Protocol.cacheAtRound before.cache r := by
    exact ceiling_cacheAtRound_align_self_opening before.cache r
  have halignedNone : DecoupledConsensusModel.Protocol.phaseResult
        (DecoupledConsensusModel.Protocol.cacheAtRound aligned r) .g1 = none := by
    rw [halign]
    exact hrawNone
  have hcomplete : DecoupledConsensusModel.Protocol.phaseResult
        (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc before.st.core.toHealing
          r t (DecoupledConsensusModel.Protocol.cacheAtRound aligned r)) .g1 =
      some (PhaseGrades.storeRoot S.E S.hc
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1) := by
    have hG1 : (DecoupledConsensusModel.Protocol.cacheAtRound aligned r).g1 = none :=
      halignedNone
    cases hG2 : (DecoupledConsensusModel.Protocol.cacheAtRound aligned r).g2 <;>
      cases hG0 : (DecoupledConsensusModel.Protocol.cacheAtRound aligned r).g0 <;>
        simp [DecoupledConsensusModel.Protocol.completeFrame, DecoupledConsensusModel.Protocol.completeOne,
          DecoupledConsensusModel.Protocol.putPhase, DecoupledConsensusModel.Protocol.phaseResult, hG2,
          hG0, hG1, hnotg2, hnotg0, before, hopen,
          PhaseGrades.storeRoot, PhaseGrades.phaseRoot,
          Protocol.Store.toHealing]
  have hframe :
      (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing r).g1 =
        some ((PhaseGrades.storeRoot S.E S.hc
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X read.st.core.F)) := by
    dsimp only [read, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache]
    have halignedRound : aligned.round = r := by
      dsimp only [aligned]
      unfold DecoupledConsensusModel.Protocol.alignRound
      split_ifs with h
      · exact h.symm
      · rfl
      · rfl
    have hcacheTick :
        DecoupledConsensusModel.Protocol.cacheAtRound
            (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc before.st.core.toHealing
              t before.cache) r =
          DecoupledConsensusModel.Protocol.clipFrame before.st.core.F
            (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc
              before.st.core.toHealing r t aligned.current) := by
      unfold DecoupledConsensusModel.Protocol.onPhaseTick
      rw [hround]
      simp [aligned, DecoupledConsensusModel.Protocol.cacheAtRound, halignedRound,
        DecoupledConsensusModel.Protocol.clipCache, Protocol.Store.toHealing]
    change (DecoupledConsensusModel.Protocol.readFrame
      (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc before.st.core.toHealing
        t before.cache) before.st.core.toHealing r).g1 = _
    unfold DecoupledConsensusModel.Protocol.readFrame
    change (DecoupledConsensusModel.Protocol.clipFrame before.st.core.F
      (DecoupledConsensusModel.Protocol.cacheAtRound
        (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc before.st.core.toHealing
          t before.cache) r)).g1 = _
    rw [hcacheTick, ceiling_clip_frame_idempotent_opening]
    have hcache : DecoupledConsensusModel.Protocol.cacheAtRound aligned r = aligned.current := by
      simp [DecoupledConsensusModel.Protocol.cacheAtRound, halignedRound]
    have hcomplete' := hcomplete
    rw [hcache] at hcomplete'
    have hcomplete'' :
        (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc before.st.core.toHealing
          r t aligned.current).g1 =
        some (PhaseGrades.storeRoot S.E S.hc
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1) := by
      simpa only [DecoupledConsensusModel.Protocol.phaseResult] using hcomplete'
    simp only [DecoupledConsensusModel.Protocol.clipFrame, DecoupledConsensusModel.Protocol.clipResult]
    rw [hcomplete'']
    rfl
  simpa only [before, read, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom] using hframe

private theorem proposalAnchorAt_preceq_of_previousCarriers
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {q : Round}
    (hpost : S.E.t_GST ≤ S.a q)
    (hcut : S.hc.Γ_neg1 S.E.Δ (q + 1) ≤ rho.horizon)
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot (q + 1)) ≤ rho.horizon)
    {C : Block V}
    (hupper : ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v q) C)
    (hprop : S.E.proposer (S.hc.opening_slot (q + 1)) ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (proposerReadAt S rho
          (S.hc.opening_slot (q + 1))).st.core.toHealing.toFG) C) :
    Block.Preceq
      (nodeAnchor S
        (Internal.NamedRecoveryRead.proposalDutyRead S rho
          (S.hc.opening_slot (q + 1))) (q + 1)) C := by
  let o := S.hc.opening_slot (q + 1)
  let w := S.E.proposer o
  have hw : w ∈ rho.honest := by simpa only [w] using hprop
  have hround : S.hc.round_of o = q + 1 :=
    round_of_opening_slot_eq_schedule S.hc (q + 1)
  have hopen : DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 =
      Protocol.proposal_time S.E o := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    rfl
  have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 ≤
      rho.horizon := by
    rw [hopen]
    exact hproposalHor
  have hroundTime : S.hc.round_of (S.E.slotOf
      (Protocol.proposal_time S.E o)) = q + 1 := by
    simpa only [Proofs.Optimistic.slotOf_proposal_time] using hround
  have hframeStore := preparedFrame_g1_eq_storeRoot_at_opening S rho
    adm.toNamedAdmissibleCore (S.E.proposer o) hprop (q + 1) (Nat.succ_pos q)
    (Protocol.proposal_time S.E o) hroundTime hopen hdomainHor
  have hroundSt : S.hc.round_of
      (Internal.NamedRecoveryRead.proposalDutyRead S rho o).st.core.s = q + 1 := by
    simpa only [Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.slotOf_proposal_time] using hround
  change Block.Preceq
    (nodeAnchor S (Internal.NamedRecoveryRead.proposalDutyRead S rho o)
      (q + 1)) C
  rcases proposalAnchor_cases S rho o with hfg | hactive
  · rw [hroundSt] at hfg
    rw [hfg]
    exact hroot
  · obtain ⟨root, A, hframe, hactive, hanchor⟩ := hactive
    have hanchor' : nodeAnchor S
        (Internal.NamedRecoveryRead.proposalDutyRead S rho o) (q + 1) = A := by
      simpa only [hroundSt] using hanchor
    rw [hanchor']
    have hframe' := hframe
    rw [hroundSt] at hframe'
    have hframe'' :
        (DecoupledConsensusModel.Protocol.readFrame
          (proposerReadAt S rho o).cache
        (proposerReadAt S rho o).st.core.toHealing (q + 1)).g1 =
          some (some root) := by
      simpa only [Internal.NamedRecoveryRead.proposalDutyRead,
        proposerReadAt] using hframe'
    let read := PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1)
      (S.E.proposer o)
    have hframeRead :
        (DecoupledConsensusModel.Protocol.readFrame
          (proposerReadAt S rho o).cache
          (proposerReadAt S rho o).st.core.toHealing (q + 1)).g1 =
          some ((PhaseGrades.storeRoot S.E S.hc read.st (q + 1) .g1).map
            (fun X => DecoupledConsensusModel.Protocol.clipGrade X
              (proposerReadAt S rho o).st.core.F)) := by
      simpa only [read, Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
        hframeStore
    cases hstore : PhaseGrades.storeRoot S.E S.hc read.st (q + 1) .g1 with
    | none =>
        simp only [hstore, Option.map_none] at hframeRead
        rw [hframe''] at hframeRead
        cases hframeRead
    | some raw =>
        have hrootEq : root =
            DecoupledConsensusModel.Protocol.clipGrade raw
              (proposerReadAt S rho o).st.core.F := by
          have hopt : some (some root) = some
              (some (DecoupledConsensusModel.Protocol.clipGrade raw
                (proposerReadAt S rho o).st.core.F)) :=
            hframe''.symm.trans (by
              simpa only [hstore, Option.map_some] using hframeRead)
          exact Option.some.inj (Option.some.inj hopt)
        have hLroot : Block.Preceq A root := by
          unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
          exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
        have hLraw : Block.Preceq A raw := by
          rw [hrootEq] at hLroot
          exact Block.preceq_trans hLroot
            (NamedOutageClosure.q10_clip_preceq raw
              (proposerReadAt S rho o).st.core.F)
        have hrawData := Proofs.Engine.deepest?_mem hstore
        have hrawTree : raw ∈ read.st.core.T :=
          (Finset.mem_filter.mp hrawData).1
        have hLtree : A ∈ read.st.core.T := by
          have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1)
            (S.E.proposer o)
          exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
            A raw hrawTree hLraw
        have hrawGrade : PhaseGrades.phaseGrade S.E S.hc
            read.st.core.toHealing.gradeView read.st.core.F
            (q + 1) .g1 raw = true := (Finset.mem_filter.mp hrawData).2
        have hAGrade := confirmation_phaseGrade_mono S.E S.hc _ _ (q + 1) .g1
          hLraw hrawGrade
        have hFroot : Block.Preceq read.st.core.F
            (Protocol.get_fg_root
              (proposerReadAt S rho o).st.core.toHealing.toFG) := by
          have hFJ :=
            Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
              (Protocol.proposal_time S.E o) (S.E.proposer o)
          simpa only [read, PhaseGrades.readAt, proposerReadAt,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, hopen,
            Protocol.NamedStore.setClock] using
            (Proofs.Records.preceq_get_fg_root_of_F
              (st := (NamedRun.stateBeforeTime S rho
                (Protocol.proposal_time S.E o) (S.E.proposer o)).st.core.toHealing.toFG)
              hFJ)
        have hFC : Block.Preceq read.st.core.F C :=
          Block.preceq_trans hFroot hroot
        have hlatest : q ∈ Protocol.latest_window S.hc.η_SG (q + 1) := by
          simpa only [Nat.add_sub_cancel] using
            Protocol.pred_mem_latest_window S.hc.η_SG (q + 1)
              S.hc.η_SG_ge_one (Nat.succ_pos q)
        have hactionDeadline : S.a q + S.E.Δ ≤
            DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 :=
          (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
            (Nat.lt_succ_self q)).trans
            (NamedOutageClosure.q10_early_g2_le_early_g1 S (q + 1))
        have hactionHor : S.a q ≤ rho.horizon :=
          (le_add_of_nonneg_right S.E.Δ_pos.le).trans
            ((action_add_delta_le_next_Γ_neg1 S q).trans hcut)
        have hearlyHor : DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 ≤
            rho.horizon :=
          (NamedOutageClosure.q10_early_g1_le_domain_g2 S (q + 1)).trans
            (by simpa only [gammaNeg1_eq_domain_g2_succ S q] using hcut)
        have hearlyDomain : DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 ≤
            DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 :=
          (NamedOutageClosure.q10_early_g1_le_domain_g2 S (q + 1)).trans
            (NamedOutageClosure.q10_domain_g2_lt_domain_g1 S (q + 1)).le
        have hinterpreted : ∀ v ∈ rho.honest,
            (DecoupledConsensusModel.Protocol.interpretedInputs
              read.st.core.toHealing.gradeView read.st.core.F S.hc.η_SG
              (q + 1) (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1) v).Nonempty := by
          intro v hv
          obtain ⟨a, hemit, hproj⟩ :=
            honest_emits_actionAttestationAt S adm hv q hactionHor
          obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
            Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
          have haval : a.val_index = v := by
            have h := congrArg Protocol.SGVote.val_index hproj
            simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
          have haround : a.round = q := by
            have h := congrArg Protocol.SGVote.round hproj
            simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
          have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
            change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
            exact hH
          have hHrun : RunBlock S rho H :=
            Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
          have hCmem : actionSGBlockAt S rho v q ∈
              (rho.storeBeforeTime S v (S.a q)).T :=
            actionSGBlockAt_mem_storeBeforeTime S rho v q
          obtain ⟨Cn, hCnerase, hCnrun⟩ :=
            Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
              adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
          have hconfirmedCarrier : a.confirmed =
              some (actionSGBlockAt S rho v q).root := by
            have h := congrArg Protocol.SGVote.confirmed hproj
            simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
          have hrootEq : H.erase.root = Cn.erase.root := by
            rw [Proofs.NamedWire.erase_root, hCnerase]
            exact congrArg id (Option.some.inj
              (hconfirmed.symm.trans hconfirmedCarrier))
          have hHCeq : H.erase = Cn.erase :=
            Protocol.runBlock_eq_of_root_eq
              adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hCnrun hrootEq
          have hHC : Block.Preceq H.erase C := by
            rw [hHCeq, hCnerase]
            exact hupper v hv
          have hmem :=
            action_vote_mem_interpretedInputs_after_gst_common_upper
              S adm.toNamedAdmissibleCore .g1 hlatest hv hw
              ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
              (by simpa only [haround] using hpost)
              (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
              hearlyDomain hearlyHor
          exact ⟨Protocol.sgVote a.erase, by simpa only [read] using hmem⟩
        have hrepresented : ∀ v ∈ rho.honest,
            Protocol.represented read.st.core.toHealing.sg_votes
              S.hc.η_SG v (q + 1) = true := by
          intro v hv
          obtain ⟨a, hemit, hproj⟩ :=
            honest_emits_actionAttestationAt S adm hv q hactionHor
          obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
            Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
          have haval : a.val_index = v := by
            have h := congrArg Protocol.SGVote.val_index hproj
            simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
          have haround : a.round = q := by
            have h := congrArg Protocol.SGVote.round hproj
            simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
          have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
            change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
            exact hH
          have hHrun : RunBlock S rho H :=
            Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
          have hCmem : actionSGBlockAt S rho v q ∈
              (rho.storeBeforeTime S v (S.a q)).T :=
            actionSGBlockAt_mem_storeBeforeTime S rho v q
          obtain ⟨Cn, hCnerase, hCnrun⟩ :=
            Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
              adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
          have hconfirmedCarrier : a.confirmed =
              some (actionSGBlockAt S rho v q).root := by
            have h := congrArg Protocol.SGVote.confirmed hproj
            simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
          have hrootEq : H.erase.root = Cn.erase.root := by
            rw [Proofs.NamedWire.erase_root, hCnerase]
            exact congrArg id (Option.some.inj
              (hconfirmed.symm.trans hconfirmedCarrier))
          have hHCeq : H.erase = Cn.erase :=
            Protocol.runBlock_eq_of_root_eq
              adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hCnrun hrootEq
          have hHC : Block.Preceq H.erase C := by
            rw [hHCeq, hCnerase]
            exact hupper v hv
          have hmem :=
            action_vote_mem_interpretedInputs_after_gst_common_upper
              S adm.toNamedAdmissibleCore .g1 hlatest hv hw
              ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
              (by simpa only [haround] using hpost)
              (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
              hearlyDomain hearlyHor
          have hraw := (Finset.mem_filter.mp hmem).1
          obtain ⟨hpool, hfields⟩ := Finset.mem_filter.mp hraw
          obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hpool
          exact Protocol.represented_of_vote_mem
            (List.mem_toFinset.mp hk) huk hfields.1
        have hwindow := windowMajorityAt_of_honestWeightMajority_of_represented
          S (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird
            (S := S) hfb) hrepresented hinterpreted
        have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
            read.st.core.toHealing.gradeView read.st.core.F S.hc.η_SG (q + 1)
            (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1)
            (DecoupledConsensusModel.Protocol.late S.E S.hc (q + 1) .g1) A = true := by
          simpa only [read, PhaseGrades.storeGrade, PhaseGrades.phaseGrade] using hAGrade
        obtain ⟨v, hv, u, hu, head, hconf, hfind, -, hAhead, -, hmax⟩ :=
          exists_honest_max_positive_supporter_of_relativeGrade
            S.E S.hc hwindow hgrade
        obtain ⟨a, hemit, hproj⟩ :=
          honest_emits_actionAttestationAt S adm hv q hactionHor
        obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
          Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
        have haval : a.val_index = v := by
          have h := congrArg Protocol.SGVote.val_index hproj
          simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
        have haround : a.round = q := by
          have h := congrArg Protocol.SGVote.round hproj
          simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
        have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
          change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
          exact hH
        have hHrun : RunBlock S rho H :=
          Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
        have hCmem : actionSGBlockAt S rho v q ∈
            (rho.storeBeforeTime S v (S.a q)).T :=
          actionSGBlockAt_mem_storeBeforeTime S rho v q
        obtain ⟨Cn, hCnerase, hCnrun⟩ :=
          Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
        have hconfirmedCarrier : a.confirmed =
            some (actionSGBlockAt S rho v q).root := by
          have h := congrArg Protocol.SGVote.confirmed hproj
          simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
        have hrootEq : H.erase.root = Cn.erase.root := by
          rw [Proofs.NamedWire.erase_root, hCnerase]
          exact congrArg id (Option.some.inj
            (hconfirmed.symm.trans hconfirmedCarrier))
        have hHCeq : H.erase = Cn.erase :=
          Protocol.runBlock_eq_of_root_eq
            adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hCnrun hrootEq
        have hHC : Block.Preceq H.erase C := by
          rw [hHCeq, hCnerase]
          exact hupper v hv
        have hactionInput :=
          action_vote_mem_interpretedInputs_after_gst_common_upper
            S adm.toNamedAdmissibleCore .g1 hlatest hv hw
            ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
            (by simpa only [haround] using hpost)
            (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
            hearlyDomain hearlyHor
        have hqle : q ≤ u.round := by
          have := hmax (Protocol.sgVote a.erase) hactionInput
          simpa only [Protocol.sgVote, NamedAttestation.erase, haround] using this
        have huraw := (Finset.mem_filter.mp hu).1
        obtain ⟨b, hbval, hbround, hbproj, huwindow, -, hbemit⟩ :=
          NamedOutageClosure.rawInputs_trace S rho
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
            adm.toNamedAdmissibleCore.toNamedUnforgeable
            (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1)
            (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1) w
            S.hc.η_SG (q + 1) v hv (by simpa only [read] using huraw)
        have hule : u.round ≤ q := Nat.le_of_lt_succ
          (NamedOutageClosure.window_bounds huwindow).2
        have huroundEq : u.round = q := Nat.le_antisymm hule hqle
        have hbroundQ : b.round = q := hbround.trans huroundEq
        have hba : b = a := Proofs.Optimistic.emits_attest_unique S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hbemit hemit
          (hbroundQ.trans haround.symm)
        have huEq : u = Protocol.sgVote a.erase := by
          rw [← hbproj, hba]
        have hheadRoot : head.root = (actionSGBlockAt S rho v q).root := by
          have huconf := congrArg Protocol.SGVote.confirmed huEq
          simpa only [Protocol.sgVote, NamedAttestation.erase, hconf,
            hconfirmedCarrier, Option.some.injEq] using huconf
        have hheadMem : head ∈ read.st.core.T := Proofs.HealingLemmas.find?_mem hfind
        obtain ⟨Headn, hHeaderase, hHeadrun⟩ :=
          Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
            (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1) (by
              simpa only [read] using hheadMem)
        have hheadCnRoot : Headn.erase.root = Cn.erase.root := by
          rw [hHeaderase, hCnerase]
          exact hheadRoot
        have hheadCarrier : head = actionSGBlockAt S rho v q := by
          rw [← hHeaderase, ← hCnerase]
          exact Protocol.runBlock_eq_of_root_eq
            adm.toNamedAdmissibleCore.toNamedRootCollisionFree
            hHeadrun hCnrun hheadCnRoot
        have hAC : Block.Preceq A C :=
          Block.preceq_trans (by simpa only [hheadCarrier] using hAhead) (hupper v hv)
        exact hAC

/-- The proposal anchor is below a carrier ceiling at any slot in the round.

The opening-slot producer above is kept as the specialized seed route. This
additive form also covers later slots: frame completion at the round's G1
domain is transported to the prepared proposer read before the carrier proof
is replayed. -/
theorem proposalAnchorAt_preceq_of_previousCarriers_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} {s : Slot}
    (hround : S.hc.round_of s = q + 1)
    (hpost : S.E.t_GST ≤ S.a q)
    (hcut : S.hc.Γ_neg1 S.E.Δ (q + 1) ≤ rho.horizon)
    (hproposalHor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hupper : ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v q) C)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (proposerReadAt S rho s).st.core.toHealing.toFG) C) :
    Block.Preceq
      (nodeAnchor S (Internal.NamedRecoveryRead.proposalDutyRead S rho s)
        (S.hc.round_of
          (Internal.NamedRecoveryRead.proposalDutyRead S rho s).st.core.s)) C := by
  let o := s
  let w := S.E.proposer o
  have hw : w ∈ rho.honest := by simpa only [w, o] using hprop
  have hroundSt : S.hc.round_of
      (Internal.NamedRecoveryRead.proposalDutyRead S rho o).st.core.s = q + 1 := by
    simpa only [Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.slotOf_proposal_time] using hround
  have hopen : S.hc.opening_slot (q + 1) ≤ o := by
    have hround' := hround
    unfold Protocol.HealConfig.round_of at hround'
    unfold Protocol.HealConfig.opening_slot
    rw [← hround']
    exact Nat.div_mul_le_self o S.hc.R
  by_cases hopening : o = S.hc.opening_slot (q + 1)
  · have hso : s = S.hc.opening_slot (q + 1) := by
      simpa only [o] using hopening
    have hprop' : S.E.proposer (S.hc.opening_slot (q + 1)) ∈ rho.honest := by
      simpa only [← hso] using hprop
    have hroot' : Block.Preceq
        (Protocol.get_fg_root
          (proposerReadAt S rho (S.hc.opening_slot (q + 1))).st.core.toHealing.toFG) C := by
      simpa only [← hso] using hroot
    have hroundSt' : S.hc.round_of
        (Internal.NamedRecoveryRead.proposalDutyRead S rho
          (S.hc.opening_slot (q + 1))).st.core.s = q + 1 := by
      simpa only [hso, o] using hroundSt
    rw [hso, hroundSt']
    exact proposalAnchorAt_preceq_of_previousCarriers S adm hfb hpost hcut
      ((Protocol.proposal_time_mono S.E hopen).trans hproposalHor)
      hupper hprop' hroot'
  have hopenLt : S.hc.opening_slot (q + 1) < o :=
    lt_of_le_of_ne hopen (Ne.symm hopening)
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
  have hdiv : o / S.hc.R < q + 2 := by
    change S.hc.round_of o < q + 2
    rw [hround]
    exact Nat.lt_succ_self _
  have hsUpper : o < S.hc.opening_slot (q + 2) := by
    unfold Protocol.HealConfig.opening_slot
    exact (Nat.div_lt_iff_lt_mul hRpos).mp hdiv
  have hproposalOpenLt : Protocol.proposal_time S.E
      (S.hc.opening_slot (q + 1)) < Protocol.proposal_time S.E o := by
    unfold Protocol.proposal_time Env.t slotStart
    exact Int.mul_lt_mul_of_pos_left (by exact_mod_cast hopenLt)
      (Int.mul_pos (by norm_num) S.E.Δ_pos)
  have hdomainLe : DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 ≤
      Protocol.proposal_time S.E o := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact Protocol.proposal_time_mono S.E hopen
  have hdomainLt : DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 <
      Protocol.proposal_time S.E o := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact hproposalOpenLt
  have hta : Protocol.proposal_time S.E o ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (q + 2) := by
    rw [DecoupledConsensusModel.Protocol.opening]
    exact Protocol.proposal_time_mono S.E (Nat.le_of_lt hsUpper)
  have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 ≤
      rho.horizon := hdomainLe.trans hproposalHor
  have hroundTime : S.hc.round_of (S.E.slotOf
      (Protocol.proposal_time S.E o)) = q + 1 := by
    simpa only [Proofs.Optimistic.slotOf_proposal_time] using hround
  have hframeBase :
      (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho
          (Protocol.proposal_time S.E o) w).cache
        (NamedRun.stateBeforeTime S rho
          (Protocol.proposal_time S.E o) w).st.core.toHealing (q + 1)).g1 =
        some ((PhaseGrades.storeRoot S.E S.hc
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1) w).st (q + 1) .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X
      (NamedRun.stateBeforeTime S rho
              (Protocol.proposal_time S.E o) w).st.core.F)) := by
    simpa only [PhaseGrades.storeRoot, PhaseGrades.phaseRoot] using
      (FrameCompleted.frame_phase_completed_in_round S rho
        adm.toNamedAdmissibleCore w hw (q + 1) (Nat.succ_pos q) .g1
        (Protocol.proposal_time S.E o) hdomainLt hta hdomainHor)
  have hframePrepared := NamedOutageClosure.frame_phase_prepared_eq S rho w
    (q + 1) .g1 (Protocol.proposal_time S.E o) hroundTime _ hframeBase
  have hframeStore :
      (DecoupledConsensusModel.Protocol.readFrame
        (proposerReadAt S rho o).cache
        (proposerReadAt S rho o).st.core.toHealing (q + 1)).g1 =
        some ((PhaseGrades.storeRoot S.E S.hc
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1) w).st (q + 1) .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X
            (proposerReadAt S rho o).st.core.F)) := by
    simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom] using hframePrepared
  suffices htarget : Block.Preceq
      (nodeAnchor S (Internal.NamedRecoveryRead.proposalDutyRead S rho o)
        (q + 1)) C by
    simpa only [o, hroundSt] using htarget
  rcases proposalAnchor_cases S rho o with hfg | hactive
  · rw [hroundSt] at hfg
    rw [hfg]
    exact hroot
  · obtain ⟨root, A, hframe, hactive, hanchor⟩ := hactive
    have hanchor' : nodeAnchor S
        (Internal.NamedRecoveryRead.proposalDutyRead S rho o) (q + 1) = A := by
      simpa only [hroundSt] using hanchor
    rw [hanchor']
    have hframe' := hframe
    rw [hroundSt] at hframe'
    have hframe'' :
        (DecoupledConsensusModel.Protocol.readFrame
          (proposerReadAt S rho o).cache
        (proposerReadAt S rho o).st.core.toHealing (q + 1)).g1 =
          some (some root) := by
      simpa only [Internal.NamedRecoveryRead.proposalDutyRead,
        proposerReadAt] using hframe'
    let read := PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1) (S.E.proposer o)
    have hframeRead :
        (DecoupledConsensusModel.Protocol.readFrame
          (proposerReadAt S rho o).cache
          (proposerReadAt S rho o).st.core.toHealing (q + 1)).g1 =
          some ((PhaseGrades.storeRoot S.E S.hc read.st (q + 1) .g1).map
            (fun X => DecoupledConsensusModel.Protocol.clipGrade X
              (proposerReadAt S rho o).st.core.F)) := by
      simpa only [read, Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
        hframeStore
    cases hstore : PhaseGrades.storeRoot S.E S.hc read.st (q + 1) .g1 with
    | none =>
        simp only [hstore, Option.map_none] at hframeRead
        rw [hframe''] at hframeRead
        cases hframeRead
    | some raw =>
        have hrootEq : root =
            DecoupledConsensusModel.Protocol.clipGrade raw
              (proposerReadAt S rho o).st.core.F := by
          have hopt : some (some root) = some
              (some (DecoupledConsensusModel.Protocol.clipGrade raw
                (proposerReadAt S rho o).st.core.F)) :=
            hframe''.symm.trans (by
              simpa only [hstore, Option.map_some] using hframeRead)
          exact Option.some.inj (Option.some.inj hopt)
        have hLroot : Block.Preceq A root := by
          unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
          exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
        have hLraw : Block.Preceq A raw := by
          rw [hrootEq] at hLroot
          exact Block.preceq_trans hLroot
            (NamedOutageClosure.q10_clip_preceq raw
              (proposerReadAt S rho o).st.core.F)
        have hrawData := Proofs.Engine.deepest?_mem hstore
        have hrawTree : raw ∈ read.st.core.T :=
          (Finset.mem_filter.mp hrawData).1
        have hLtree : A ∈ read.st.core.T := by
          have hpc : ParentClosed read.st.core := by
            simpa only [read, PhaseGrades.readAt] using
              (Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
                (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1) (S.E.proposer o))
          exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
            A raw hrawTree hLraw
        have hrawGrade : PhaseGrades.phaseGrade S.E S.hc
            read.st.core.toHealing.gradeView read.st.core.F
            (q + 1) .g1 raw = true := (Finset.mem_filter.mp hrawData).2
        have hAGrade := confirmation_phaseGrade_mono S.E S.hc _ _ (q + 1) .g1
          hLraw hrawGrade
        have hFroot : Block.Preceq read.st.core.F
            (Protocol.get_fg_root
              (proposerReadAt S rho o).st.core.toHealing.toFG) := by
          have hFrootForward :=
            NamedOutageClosure.preceq_fg_root_of_preceq_F_fwd S rho
              adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
              (S.E.proposer o) read.st.core.F
              (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1)
              (Protocol.proposal_time S.E o) hdomainLe (Block.preceq_self _)
          simpa only [read, PhaseGrades.readAt, proposerReadAt,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using hFrootForward
        have hFC : Block.Preceq read.st.core.F C :=
          Block.preceq_trans hFroot hroot
        have hlatest : q ∈ Protocol.latest_window S.hc.η_SG (q + 1) := by
          simpa only [Nat.add_sub_cancel] using
            Protocol.pred_mem_latest_window S.hc.η_SG (q + 1)
              S.hc.η_SG_ge_one (Nat.succ_pos q)
        have hactionDeadline : S.a q + S.E.Δ ≤
            DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 :=
          (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
            (Nat.lt_succ_self q)).trans
            (NamedOutageClosure.q10_early_g2_le_early_g1 S (q + 1))
        have hactionHor : S.a q ≤ rho.horizon :=
          (le_add_of_nonneg_right S.E.Δ_pos.le).trans
            ((action_add_delta_le_next_Γ_neg1 S q).trans hcut)
        have hearlyHor : DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 ≤
            rho.horizon :=
          (NamedOutageClosure.q10_early_g1_le_domain_g2 S (q + 1)).trans
            (by simpa only [gammaNeg1_eq_domain_g2_succ S q] using hcut)
        have hearlyDomain : DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 ≤
            DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 :=
          (NamedOutageClosure.q10_early_g1_le_domain_g2 S (q + 1)).trans
            (NamedOutageClosure.q10_domain_g2_lt_domain_g1 S (q + 1)).le
        have hinterpreted : ∀ v ∈ rho.honest,
            (DecoupledConsensusModel.Protocol.interpretedInputs
              read.st.core.toHealing.gradeView read.st.core.F S.hc.η_SG
              (q + 1) (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1) v).Nonempty := by
          intro v hv
          obtain ⟨a, hemit, hproj⟩ :=
            honest_emits_actionAttestationAt S adm hv q hactionHor
          obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
            Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
          have haval : a.val_index = v := by
            have h := congrArg Protocol.SGVote.val_index hproj
            simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
          have haround : a.round = q := by
            have h := congrArg Protocol.SGVote.round hproj
            simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
          have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
            change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
            exact hH
          have hHrun : RunBlock S rho H :=
            Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
          have hCmem : actionSGBlockAt S rho v q ∈
              (rho.storeBeforeTime S v (S.a q)).T :=
            actionSGBlockAt_mem_storeBeforeTime S rho v q
          obtain ⟨Cn, hCnerase, hCnrun⟩ :=
            Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
              adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
          have hconfirmedCarrier : a.confirmed =
              some (actionSGBlockAt S rho v q).root := by
            have h := congrArg Protocol.SGVote.confirmed hproj
            simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
          have hrootEq : H.erase.root = Cn.erase.root := by
            rw [Proofs.NamedWire.erase_root, hCnerase]
            exact congrArg id (Option.some.inj
              (hconfirmed.symm.trans hconfirmedCarrier))
          have hHCeq : H.erase = Cn.erase :=
            Protocol.runBlock_eq_of_root_eq
              adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hCnrun hrootEq
          have hHC : Block.Preceq H.erase C := by
            rw [hHCeq, hCnerase]
            exact hupper v hv
          have hmem :=
            action_vote_mem_interpretedInputs_after_gst_common_upper
              S adm.toNamedAdmissibleCore .g1 hlatest hv hw
              ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
              (by simpa only [haround] using hpost)
              (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
              hearlyDomain hearlyHor
          exact ⟨Protocol.sgVote a.erase, by simpa only [read] using hmem⟩
        have hrepresented : ∀ v ∈ rho.honest,
            Protocol.represented read.st.core.toHealing.sg_votes
              S.hc.η_SG v (q + 1) = true := by
          intro v hv
          obtain ⟨a, hemit, hproj⟩ :=
            honest_emits_actionAttestationAt S adm hv q hactionHor
          obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
            Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
          have haval : a.val_index = v := by
            have h := congrArg Protocol.SGVote.val_index hproj
            simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
          have haround : a.round = q := by
            have h := congrArg Protocol.SGVote.round hproj
            simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
          have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
            change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
            exact hH
          have hHrun : RunBlock S rho H :=
            Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
          have hCmem : actionSGBlockAt S rho v q ∈
              (rho.storeBeforeTime S v (S.a q)).T :=
            actionSGBlockAt_mem_storeBeforeTime S rho v q
          obtain ⟨Cn, hCnerase, hCnrun⟩ :=
            Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
              adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
          have hconfirmedCarrier : a.confirmed =
              some (actionSGBlockAt S rho v q).root := by
            have h := congrArg Protocol.SGVote.confirmed hproj
            simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
          have hrootEq : H.erase.root = Cn.erase.root := by
            rw [Proofs.NamedWire.erase_root, hCnerase]
            exact congrArg id (Option.some.inj
              (hconfirmed.symm.trans hconfirmedCarrier))
          have hHCeq : H.erase = Cn.erase :=
            Protocol.runBlock_eq_of_root_eq
              adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hCnrun hrootEq
          have hHC : Block.Preceq H.erase C := by
            rw [hHCeq, hCnerase]
            exact hupper v hv
          have hmem :=
            action_vote_mem_interpretedInputs_after_gst_common_upper
              S adm.toNamedAdmissibleCore .g1 hlatest hv hw
              ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
              (by simpa only [haround] using hpost)
              (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
              hearlyDomain hearlyHor
          have hraw := (Finset.mem_filter.mp hmem).1
          obtain ⟨hpool, hfields⟩ := Finset.mem_filter.mp hraw
          obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hpool
          exact Protocol.represented_of_vote_mem
            (List.mem_toFinset.mp hk) huk hfields.1
        have hwindow := windowMajorityAt_of_honestWeightMajority_of_represented
          S (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird
            (S := S) hfb) hrepresented hinterpreted
        have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
            read.st.core.toHealing.gradeView read.st.core.F S.hc.η_SG (q + 1)
            (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1)
            (DecoupledConsensusModel.Protocol.late S.E S.hc (q + 1) .g1) A = true := by
          simpa only [read, PhaseGrades.storeGrade, PhaseGrades.phaseGrade] using hAGrade
        obtain ⟨v, hv, u, hu, head, hconf, hfind, -, hAhead, -, hmax⟩ :=
          exists_honest_max_positive_supporter_of_relativeGrade
            S.E S.hc hwindow hgrade
        obtain ⟨a, hemit, hproj⟩ :=
          honest_emits_actionAttestationAt S adm hv q hactionHor
        obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
          Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
        have haval : a.val_index = v := by
          have h := congrArg Protocol.SGVote.val_index hproj
          simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
        have haround : a.round = q := by
          have h := congrArg Protocol.SGVote.round hproj
          simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
        have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
          change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
          exact hH
        have hHrun : RunBlock S rho H :=
          Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
        have hCmem : actionSGBlockAt S rho v q ∈
            (rho.storeBeforeTime S v (S.a q)).T :=
          actionSGBlockAt_mem_storeBeforeTime S rho v q
        obtain ⟨Cn, hCnerase, hCnrun⟩ :=
          Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
        have hconfirmedCarrier : a.confirmed =
            some (actionSGBlockAt S rho v q).root := by
          have h := congrArg Protocol.SGVote.confirmed hproj
          simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
        have hrootEq : H.erase.root = Cn.erase.root := by
          rw [Proofs.NamedWire.erase_root, hCnerase]
          exact congrArg id (Option.some.inj
            (hconfirmed.symm.trans hconfirmedCarrier))
        have hHCeq : H.erase = Cn.erase :=
          Protocol.runBlock_eq_of_root_eq
            adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hCnrun hrootEq
        have hHC : Block.Preceq H.erase C := by
          rw [hHCeq, hCnerase]
          exact hupper v hv
        have hactionInput :=
          action_vote_mem_interpretedInputs_after_gst_common_upper
            S adm.toNamedAdmissibleCore .g1 hlatest hv hw
            ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
            (by simpa only [haround] using hpost)
            (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
            hearlyDomain hearlyHor
        have hqle : q ≤ u.round := by
          have := hmax (Protocol.sgVote a.erase) hactionInput
          simpa only [Protocol.sgVote, NamedAttestation.erase, haround] using this
        have huraw := (Finset.mem_filter.mp hu).1
        obtain ⟨b, hbval, hbround, hbproj, huwindow, -, hbemit⟩ :=
          NamedOutageClosure.rawInputs_trace S rho
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
            adm.toNamedAdmissibleCore.toNamedUnforgeable
            (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1)
            (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1) w
            S.hc.η_SG (q + 1) v hv (by simpa only [read] using huraw)
        have hule : u.round ≤ q := Nat.le_of_lt_succ
          (NamedOutageClosure.window_bounds huwindow).2
        have huroundEq : u.round = q := Nat.le_antisymm hule hqle
        have hbroundQ : b.round = q := hbround.trans huroundEq
        have hba : b = a := Proofs.Optimistic.emits_attest_unique S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hbemit hemit
          (hbroundQ.trans haround.symm)
        have huEq : u = Protocol.sgVote a.erase := by
          rw [← hbproj, hba]
        have hheadRoot : head.root = (actionSGBlockAt S rho v q).root := by
          have huconf := congrArg Protocol.SGVote.confirmed huEq
          simpa only [Protocol.sgVote, NamedAttestation.erase, hconf,
            hconfirmedCarrier, Option.some.injEq] using huconf
        have hheadMem : head ∈ read.st.core.T := Proofs.HealingLemmas.find?_mem hfind
        obtain ⟨Headn, hHeaderase, hHeadrun⟩ :=
          Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
            (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1) (by
              simpa only [read] using hheadMem)
        have hheadCnRoot : Headn.erase.root = Cn.erase.root := by
          rw [hHeaderase, hCnerase]
          exact hheadRoot
        have hheadCarrier : head = actionSGBlockAt S rho v q := by
          rw [← hHeaderase, ← hCnerase]
          exact Protocol.runBlock_eq_of_root_eq
            adm.toNamedAdmissibleCore.toNamedRootCollisionFree
            hHeadrun hCnrun hheadCnRoot
        have hAC : Block.Preceq A C :=
          Block.preceq_trans (by simpa only [hheadCarrier] using hAhead) (hupper v hv)
        exact hAC


#print axioms proposalAnchorAt_preceq_of_previousCarriers_named
#print axioms proposalAnchorAt_preceq_of_previousCarriers







set_option maxHeartbeats 800000 in
/-- A common boundary cone and the pointwise next-round regime construct every
residual field of the half-open round-ceiling step. -/
theorem roundCeilingStepResidual_of_boundaryCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round} {Cstar : NamedBlock V}
    (hboundary : RoundCeilingBoundaryConeAt S rho M q Cstar)
    (hreg : RoundCeilingNextRegimeAt S rho M q) :
    RoundCeilingStepResidualAt S rho M q Cstar.erase := by
  let o := S.hc.opening_slot (q + 1)
  let last := seedRoundLastSlot S (q + 1)
  let s0 := o - 1
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hrun : RunBlock S rho Cstar := hboundary.run
  have hupper : ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v q) Cstar.erase :=
    hboundary.previousCarriers
  have hpost0 : S.E.t_GST ≤ Protocol.vote_time S.E s0 := by
    simpa only [s0, o] using hboundary.postBoundaryVote
  have hlastVotes : NamedHonestVotesCone S rho s0
      (fun X => Block.Preceq Cstar.erase X) := by
    simpa only [s0, o] using hboundary.boundaryVotes
  have hlastPos : 0 < last :=
    Nat.zero_lt_of_lt (by
      simpa only [o, last] using openingSlot_lt_last_step S (q + 1))
  have hopenLastPred : o ≤ last - 1 := by
    simpa only [o, last] using openingSlot_le_lastPred_step S (q + 1)
  have hs0LastPred : s0 ≤ last - 1 :=
    (Nat.sub_le o 1).trans hopenLastPred
  have hhor0 : Protocol.confirmation_time S.E s0 ≤ rho.horizon :=
    (confirmationTime_mono_step S.E hs0LastPred).trans
      (by simpa only [last] using hreg.roundConfirmationInHorizon)
  have hpostAction : S.E.t_GST ≤ S.a q := hboundary.postAction
  have hactionHor : S.a (q + 1) ≤ rho.horizon := by
    have hopenConf := confirmationTime_mono_step S.E hopenLastPred
    simpa only [o, Protocol.a_eq_confirmation_time] using
      hopenConf.trans (by simpa only [last] using
        hreg.roundConfirmationInHorizon)
  have hcut : S.hc.Γ_neg1 S.E.Δ (q + 1) ≤ rho.horizon :=
    (le_of_lt (next_Γ_neg1_lt_action S q)).trans hactionHor
  have hwindowTop : o ≤ (last - 1) + 1 := by
    rw [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)]
    exact Nat.le_of_lt (by
      simpa only [o, last] using openingSlot_lt_last_step S (q + 1))
  have hM : 1 ≤ M := by
    have hpositive : 0 < ((S.E.committee o) ∩ rho.honest).card := by
      have hc := hcom o
      omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
    have hgate := hreg.window.voteGateOff o (le_refl _) hwindowTop w
      (Finset.mem_inter.mp hw).2
    exact (by decide : 1 ≤ 2).trans
      ((Nat.le_add_left 2 (voteDutyStore S rho w o).h_j).trans hgate)
  have hfold := roundCeilingRelayFold_of_regime S adm hcom hfb hsb
    hpostAction hcut
      (by simpa only [s0, o] using hpost0)
      (by simpa only [s0, o] using hhor0)
      (by simpa only [s0, o] using hlastVotes)
      hboundary.boundaryThinHead hupper hboundary.rootOrder hreg
  have hoLast : o < last := by
    simpa only [o, last] using openingSlot_lt_last_step S (q + 1)
  have hactionActive : ∀ w ∈ rho.honest,
      Cstar.erase ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w (q + 1)).toFG := by
    intro w hw
    rw [← actionStoreAt_filteredTree S rho w (q + 1),
      actionStoreAt_filteredTree_eq_openingConfStore]
    exact (hfold.roundInputs o (le_refl _) hoLast).confirmation w hw |>.candidate
  have hactionAnchor : ∀ w ∈ rho.honest,
      Block.Preceq
        (PhaseGrades.nodeAnchor S
          (Internal.NamedRecoveryRead.actionDutyRead S rho w (q + 1)) (q + 1))
        Cstar.erase := by
    intro w hw
    rw [actionAnchor_eq_confirmationAnchorAt_opening_step S rho w (q + 1)]
    exact hfold.confirmationAnchor o (Nat.sub_le _ _) hoLast w hw
  have hpropFacts : S.E.proposer o ∈ rho.honest →
      Cstar.erase ∈ Protocol.get_filtered_block_tree
          (proposerDutyStore S rho o).toHealing.toFG ∧
        Block.Preceq
          (PhaseGrades.nodeAnchor S
            (Internal.NamedRecoveryRead.proposalDutyRead S rho o) (q + 1))
          Cstar.erase := by
    intro hprop
    have hroot : Block.Preceq
        (Protocol.get_fg_root
          (proposerDutyStore S rho o).toHealing.toFG) Cstar.erase := by
      simpa only [o] using hboundary.rootOrder.proposer (by simpa only [o] using hprop)
    have hs0Succ : s0 + 1 = o := by
      simpa only [s0, o] using openingSlot_pred_succ_step S (Nat.succ_pos q)
    have hresolve := headsResolveIn_proposerDutyStore_of_postHealingCone
      S adm (by simpa only [s0, o] using hpost0)
        ((support_cutoff_le_confirmation_time S.E s0).trans hhor0)
        (by simpa only [hs0Succ] using hprop)
        (by simpa only [hs0Succ, proposerDutyStore, tickStore] using hroot)
        (by simpa only [s0, o] using hlastVotes)
    obtain ⟨X, hXhonest, hCX, hXheight⟩ :
        ThinHonestHeadAt S rho M s0 Cstar.erase := by
      simpa only [s0, o] using hboundary.boundaryThinHead
    obtain ⟨x, hxHonest, hxCommittee, hXrun, hXemit⟩ := hXhonest
    have hXhead : HonestHead S rho s0 X.erase :=
      ⟨x, hxHonest, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    have hfind := (hresolve X.erase hXhead).1
    have hXmem : X.erase ∈ (proposerDutyStore S rho o).T := by
      simpa only [hs0Succ] using Proofs.HealingLemmas.find?_mem hfind
    let pre := rho.storeBeforeTime S (S.E.proposer o)
      (Protocol.proposal_time S.E o)
    have hXpre : X.erase ∈ pre.T := by
      simpa only [pre, proposerDutyStore, tickStore] using hXmem
    have hproposalHor : Protocol.proposal_time S.E o ≤ rho.horizon :=
      (le_of_lt (by simpa only [hs0Succ] using
        proposal_time_succ_lt_confirmation_time S.E s0)).trans hhor0
    have hfilteredPre := frontierAncestor_filtered_of_gateOff
      S adm hsb hprop hproposalHor hXpre rfl hXrun hCX hXheight hM
        (by simpa only [pre, o] using hreg.proposalFrontier _ hprop)
        (by simpa only [pre, o] using hreg.proposalGateOff _ hprop)
        (by simpa only [pre, o, proposerDutyStore, tickStore] using hroot)
    have hfiltered : Cstar.erase ∈ Protocol.get_filtered_block_tree
        (proposerDutyStore S rho o).toHealing.toFG := by
      simpa only [pre, proposerDutyStore, tickStore] using hfilteredPre
    have hrootRead : Block.Preceq
        (Protocol.get_fg_root
          (proposerReadAt S rho o).st.core.toHealing.toFG) Cstar.erase := by
      simpa only [proposerDutyStore, tickStore, proposerReadAt,
        Internal.NamedRecoveryRead.proposalDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hroot
    have hanchor := proposalAnchorAt_preceq_of_previousCarriers
      S adm hfb hpostAction hcut hproposalHor hupper hprop hrootRead
    refine ⟨hfiltered, ?_⟩
    simpa only [o] using hanchor
  exact
    { postOpeningProposal := hreg.postOpeningProposal
      roundConfirmationInHorizon := hreg.roundConfirmationInHorizon
      openingStepInputs := hfold.openingStepInputs
      roundInputs := hfold.roundInputs
      voteActive := hfold.voteActive
      actionActive := hactionActive
      voteAnchor := hfold.voteAnchor
      confirmationAnchor := hfold.confirmationAnchor
      actionAnchor := hactionAnchor
      proposerAnchorCeiling := fun hp => (hpropFacts hp).2
      proposerActive := fun hp => (hpropFacts hp).1
      gateOff := hreg.window
      genuineRun := fun w hw D hD =>
        genuineConfirmation_runBlock_step S adm hw hD }

#print axioms roundCeilingStepResidual_of_boundaryCone
/-! ## Named root re-basing helpers -/

/-- An inclusive slot interval as a finite set. -/
private def seedSlotRange (lo hi : Slot) : Finset Slot :=
  (Finset.range (hi + 1)).filter (fun d => lo ≤ d)

private theorem mem_seedSlotRange {lo hi d : Slot} :
    d ∈ seedSlotRange lo hi ↔ lo ≤ d ∧ d ≤ hi := by
  simp only [seedSlotRange, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- The FG roots read by honest validators at the reads owned by round
`q + 1`. -/
private def seedRootReadCandidates
    (S : Setup V) (rho : Run V) (q : Round) : Finset (Block V) :=
  ((seedSlotRange (S.hc.opening_slot (q + 1))
      (seedRoundLastSlot S (q + 1))).biUnion
      (fun d => rho.honest.image (fun w =>
        Protocol.get_fg_root
          (voteDutyStore S rho w d).toHealing.toFG))) ∪
    (((seedSlotRange (S.hc.opening_slot (q + 1) - 1)
        (seedRoundLastSlot S (q + 1) - 1)).biUnion
        (fun s => rho.honest.image (fun w =>
          confRoot (confStore S rho w s)))) ∪
      (rho.honest.image (fun w =>
        Protocol.get_fg_root
          (rho.storeBeforeTime S w
            (Protocol.proposal_time S.E
              (S.hc.opening_slot (q + 1)))).toHealing.toFG)))

/-- The selected FG root of an honest strict read is an actual run block. -/
private theorem seedRootRunBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) (read : Time) :
    ∃ R : NamedBlock V,
      R.erase = Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG ∧
      RunBlock S rho R := by
  have hroot := named_fgRoot_mem_filtered_stateBeforeTime S rho read w
  have hmem := Proofs.Records.get_filtered_block_tree_subset
    (NamedRun.stateBeforeTime S rho read w).st.core.toHealing.toFG hroot
  exact Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw read
    (by simpa only [Run.storeBeforeTime] using hmem)

/-- Every FG root read in round `q + 1` is below every thin run block. -/
private theorem seedRootReadCandidate_preceq_thin
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {M : Height} {q : Round} (hreg : RoundCeilingNextRegimeAt S rho M q)
    {Y : Block V} (hY : Y ∈ seedRootReadCandidates S rho q)
    {X : NamedBlock V} (hXrun : RunBlock S rho X)
    (hXthin : M - 1 ≤
      (Protocol.derive_named S.E S.cfg X).h) :
    Block.Preceq Y X.erase := by
  have hlastPos : 0 < seedRoundLastSlot S (q + 1) :=
    Nat.zero_lt_of_lt (openingSlot_lt_last_step S (q + 1))
  have hlastPredSucc : seedRoundLastSlot S (q + 1) - 1 + 1 =
      seedRoundLastSlot S (q + 1) :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hopenPos : 0 < S.hc.opening_slot (q + 1) := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos (Nat.succ_pos q)
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  simp only [seedRootReadCandidates, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_image, mem_seedSlotRange] at hY
  rcases hY with hvote | hconf | hprop
  · obtain ⟨d, ⟨hdlo, hdhi⟩, w, hw, hYeq⟩ := hvote
    rw [← hYeq]
    have hfrontier := hreg.window.voteFrontier d hdlo
      (by simpa only [hlastPredSucc] using hdhi) w hw
    have hgate := hreg.window.voteGateOff d hdlo
      (by simpa only [hlastPredSucc] using hdhi) w hw
    exact frontierRoot_preceq_of_gateOff S adm hsb hw rfl hXrun hXthin
      (by simpa only [voteDutyStore, voteStore, tickStore] using hfrontier)
      (by simpa only [voteDutyStore, voteStore, tickStore] using hgate)
  · obtain ⟨s, ⟨hslo, hshi⟩, w, hw, hYeq⟩ := hconf
    rw [← hYeq]
    by_cases heq : s = S.hc.opening_slot (q + 1) - 1
    · subst s
      exact frontierRoot_preceq_of_gateOff S adm hsb hw rfl hXrun hXthin
        (by
          simpa only [confRoot, confStore, tickStore] using
            hreg.boundaryConfirmationFrontier w hw)
        (by
          simpa only [confRoot, confStore, tickStore] using
            hreg.boundaryConfirmationGateOff w hw)
    · have hslt : S.hc.opening_slot (q + 1) - 1 < s :=
        lt_of_le_of_ne hslo (Ne.symm heq)
      have hsMain : S.hc.opening_slot (q + 1) ≤ s := by
        rw [← Nat.sub_add_cancel (Nat.succ_le_iff.mpr hopenPos)]
        exact Nat.succ_le_iff.mpr hslt
      exact frontierRoot_preceq_of_gateOff S adm hsb hw rfl hXrun hXthin
        (by
          simpa only [confRoot, confStore, tickStore] using
            hreg.window.confirmationFrontier s hsMain hshi w hw)
        (by
          simpa only [confRoot, confStore, tickStore] using
            hreg.window.confirmationGateOff s hsMain hshi w hw)
  · obtain ⟨w, hw, hYeq⟩ := hprop
    rw [← hYeq]
    exact frontierRoot_preceq_of_gateOff S adm hsb hw rfl hXrun hXthin
      (hreg.proposalFrontier w hw) (hreg.proposalGateOff w hw)

/-- Every FG root read in round `q + 1` is an actual run block. -/
private theorem seedRootReadCandidate_runBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {Y : Block V} (hY : Y ∈ seedRootReadCandidates S rho q) :
    ∃ R : NamedBlock V, R.erase = Y ∧ RunBlock S rho R := by
  simp only [seedRootReadCandidates, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_image, mem_seedSlotRange] at hY
  rcases hY with hvote | hconf | hprop
  · obtain ⟨d, -, w, hw, hYeq⟩ := hvote
    rw [← hYeq]
    exact seedRootRunBlock S adm hw (Protocol.vote_time S.E d)
  · obtain ⟨s, -, w, hw, hYeq⟩ := hconf
    rw [← hYeq]
    exact seedRootRunBlock S adm hw (Protocol.confirmation_time S.E s)
  · obtain ⟨w, hw, hYeq⟩ := hprop
    rw [← hYeq]
    exact seedRootRunBlock S adm hw _

/-- The re-based successor ceiling: the deepest of the prior ceiling and the FG
roots read in round `q + 1`. -/
private theorem exists_seedRebaseCeiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {M : Height} {q : Round} {C X0 : NamedBlock V}
    (hreg : RoundCeilingNextRegimeAt S rho M q)
    (hCrun : RunBlock S rho C)
    (hX0run : RunBlock S rho X0)
    (hX0thin : M - 1 ≤
      (Protocol.derive_named S.E S.cfg X0).h)
    (hCX0 : Block.Preceq C.erase X0.erase) :
    ∃ R : NamedBlock V,
      RunBlock S rho R ∧
        Block.Preceq C.erase R.erase ∧
        (∀ Y ∈ seedRootReadCandidates S rho q,
          Block.Preceq Y R.erase) ∧
        (∀ X : NamedBlock V, RunBlock S rho X →
          M - 1 ≤ (Protocol.derive_named S.E S.cfg X).h →
            Block.Preceq C.erase X.erase →
            Block.Preceq R.erase X.erase) := by
  let candidates := insert C.erase (seedRootReadCandidates S rho q)
  have hbelow : ∀ Y ∈ candidates, ∀ X : NamedBlock V, RunBlock S rho X →
      M - 1 ≤ (Protocol.derive_named S.E S.cfg X).h →
        Block.Preceq C.erase X.erase → Block.Preceq Y X.erase := by
    intro Y hY X hXrun hXthin hCX
    rcases Finset.mem_insert.mp hY with hYC | hYroot
    · rw [hYC]
      exact hCX
    · exact seedRootReadCandidate_preceq_thin
        S adm hsb hreg hYroot hXrun hXthin
  have hcompatible : ∀ Y ∈ candidates, ∀ Z ∈ candidates,
      Block.compatible Y Z = true := by
    intro Y hY Z hZ
    exact Block.compatible_of_preceq_common
      (hbelow Y hY X0 hX0run hX0thin hCX0)
      (hbelow Z hZ X0 hX0run hX0thin hCX0)
  have hnonempty : candidates.Nonempty :=
    ⟨C.erase, Finset.mem_insert_self _ _⟩
  obtain ⟨Rraw, hR⟩ := Option.isSome_iff_exists.mp
    (deepest?_isSome_of_compatible hcompatible hnonempty)
  have hRmem : Rraw ∈ candidates := Proofs.Engine.deepest?_mem hR
  have hCmem : C.erase ∈ candidates := Finset.mem_insert_self _ _
  obtain ⟨R, hRerase, hRrun⟩ : ∃ R : NamedBlock V,
      R.erase = Rraw ∧ RunBlock S rho R := by
    rcases Finset.mem_insert.mp hRmem with hRC | hRroot
    · exact ⟨C, hRC.symm, hCrun⟩
    · exact seedRootReadCandidate_runBlock S adm hRroot
  have hCRraw : Block.Preceq C.erase Rraw :=
    deepest?_dominates hR hCmem (hcompatible C.erase hCmem Rraw hRmem)
  refine ⟨R, hRrun, ?_, ?_, ?_⟩
  · simpa only [hRerase] using hCRraw
  · intro Y hY
    have hYmem : Y ∈ candidates := Finset.mem_insert_of_mem hY
    have hYRraw := deepest?_dominates hR hYmem
      (hcompatible Y hYmem Rraw hRmem)
    simpa only [hRerase] using hYRraw
  · intro X hXrun hXthin hCX
    have hRXraw := hbelow Rraw hRmem X hXrun hXthin hCX
    simpa only [hRerase] using hRXraw

/-- The re-based ceiling candidate, in public form. The deepest of a
carrier ceiling and the FG roots read in round `q + 1` is a run block above
the ceiling, above every one of those roots, and still below every run block
of height at least `M - 1` that the ceiling is below.

This is `exists_seedRebaseCeiling` exported: a first-ceiling producer needs the
same re-basing as the successor step, because a certificate revealed inside
round `q + 1` moves an honest FG root above any carrier ceiling. -/
theorem exists_roundCeilingRebase
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {M : Height} {q : Round} {C X0 : NamedBlock V}
    (hreg : RoundCeilingNextRegimeAt S rho M q)
    (hCrun : RunBlock S rho C)
    (hX0run : RunBlock S rho X0)
    (hX0thin : M - 1 ≤
      (Protocol.derive_named S.E S.cfg X0).h)
    (hCX0 : Block.Preceq C.erase X0.erase) :
    ∃ R : NamedBlock V,
      RunBlock S rho R ∧
        Block.Preceq C.erase R.erase ∧
        RoundCeilingNextRootOrderAt S rho q R.erase ∧
        (∀ X : NamedBlock V, RunBlock S rho X →
          M - 1 ≤ (Protocol.derive_named S.E S.cfg X).h →
            Block.Preceq C.erase X.erase →
            Block.Preceq R.erase X.erase) := by
  obtain ⟨R, hRrun, hCR, hRoots, hRbelow⟩ :=
    exists_seedRebaseCeiling S adm hsb hreg hCrun hX0run hX0thin hCX0
  have hlastPos : 0 < seedRoundLastSlot S (q + 1) :=
    Nat.zero_lt_of_lt (openingSlot_lt_last_step S (q + 1))
  refine ⟨R, hRrun, hCR, ?_, hRbelow⟩
  refine ⟨?_, ?_, ?_⟩
  · intro d hdlo hdhi w hw
    apply hRoots
    simp only [seedRootReadCandidates, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_image, mem_seedSlotRange]
    exact Or.inl ⟨d, ⟨hdlo, hdhi⟩, w, hw, rfl⟩
  · intro s hslo hshi w hw
    apply hRoots
    simp only [seedRootReadCandidates, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_image, mem_seedSlotRange]
    exact Or.inr (Or.inl ⟨s, ⟨hslo, Nat.le_pred_of_lt hshi⟩, w, hw, rfl⟩)
  · intro hprop
    have hmem : Protocol.get_fg_root
        (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot (q + 1)))
          (Protocol.proposal_time S.E
            (S.hc.opening_slot (q + 1)))).toHealing.toFG ∈
        seedRootReadCandidates S rho q := by
      simp only [seedRootReadCandidates, Finset.mem_union, Finset.mem_biUnion,
        Finset.mem_image, mem_seedSlotRange]
      exact Or.inr (Or.inr ⟨_, hprop, rfl⟩)
    simpa only [proposerDutyStore, tickStore] using hRoots _ hmem





/-- A boundary cone plus the pointwise next-round regime is the complete
first-ceiling constructor. -/
theorem roundCeiling_of_boundaryCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round} {C : NamedBlock V}
    (hboundaryConfirmationInHorizon :
      Protocol.confirmation_time S.E
        (S.hc.opening_slot (q + 1) - 1) ≤ rho.horizon)
    (hcone : RoundCeilingBoundaryConeAt S rho M q C)
    (hreg : RoundCeilingNextRegimeAt S rho M q) :
    RoundCeilingAt S rho M (q + 1) C := by
  have hnext :=
    roundCeilingStepResidual_of_boundaryCone S adm hcom hfb hcone hreg
  have hreadSupport := roundCeiling_readSupport_of_inputs S
    (q := q + 1) (C := C.erase) (Nat.succ_pos q)
      hnext.openingStepInputs hnext.roundInputs hnext.actionActive
      hnext.proposerActive
  exact
    { roundPositive := Nat.succ_pos q
      run := hcone.run
      boundaryThinHead := hcone.boundaryThinHead
      aboveRoot := hreadSupport.1
      active := hreadSupport.2
      postPreviousVote := hcone.postBoundaryVote
      previousConfirmationInHorizon := hboundaryConfirmationInHorizon
      postOpeningProposal := hnext.postOpeningProposal
      postOpeningVote := hnext.postOpeningProposal.trans
        (le_of_lt (Protocol.proposal_time_lt_vote_time S.E _))
      roundConfirmationInHorizon := hnext.roundConfirmationInHorizon
      lastVotes := hcone.boundaryVotes
      openingStepInputs := hnext.openingStepInputs
      roundInputs := hnext.roundInputs
      voteActive := hnext.voteActive
      actionActive := hnext.actionActive
      voteAnchor := hnext.voteAnchor
      confirmationAnchor := hnext.confirmationAnchor
      actionAnchor := hnext.actionAnchor
      proposerAnchorCeiling := hnext.proposerAnchorCeiling
      proposerActive := hnext.proposerActive
      previousCarriers := hcone.previousCarriers
      gateOff := hnext.gateOff
      genuineRun := hnext.genuineRun }

#print axioms roundCeiling_of_boundaryCone


/- The named proof is active above the relay consumers. -/
/-- **The first ceiling from a carrier frontier.** -/
theorem roundCeiling_base_of_carrierFrontier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round} {C W : NamedBlock V}
    (hpostAction : S.E.t_GST ≤ S.a q)
    (hpostBoundaryVote : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot (q + 1) - 1))
    (hboundaryConfirmationInHorizon :
      Protocol.confirmation_time S.E
        (S.hc.opening_slot (q + 1) - 1) ≤ rho.horizon)
    (hCrun : RunBlock S rho C)
    (hWrun : RunBlock S rho W)
    (hCW : Block.Preceq C.erase W.erase)
    (hWthin : M - 1 ≤
      (Protocol.derive_named S.E S.cfg W).h)
    (hcarriers : ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v q) C.erase)
    (hcone : NamedHonestVotesCone S rho
      (S.hc.opening_slot (q + 1) - 1)
      (fun X => Block.Preceq C.erase X))
    (hheadThin : ∀ X : NamedBlock V,
      NamedHonestHead S rho (S.hc.opening_slot (q + 1) - 1) X →
        M - 1 ≤ (Protocol.derive_named S.E S.cfg X).h)
    (hreg : RoundCeilingNextRegimeAt S rho M q) :
    ∃ B : NamedBlock V,
      RoundCeilingAt S rho M (q + 1) B ∧
        Block.Preceq C.erase B.erase := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  obtain ⟨R, hRrun, hCR, hrootOrder, hRbelow⟩ :=
    exists_roundCeilingRebase S adm hsb hreg hCrun hWrun hWthin hCW
  have hvotesR : NamedHonestVotesCone S rho
      (S.hc.opening_slot (q + 1) - 1)
      (fun X => Block.Preceq R.erase X) := by
    intro w hw hwcommittee
    obtain ⟨X, hCX, hXrun, hXemit⟩ := hcone w hw hwcommittee
    exact ⟨X,
      hRbelow X hXrun
        (hheadThin X ⟨w, hw, hwcommittee, hXrun, hXemit⟩) hCX,
      hXrun, hXemit⟩
  have hthinHead : ThinHonestHeadAt S rho M
      (S.hc.opening_slot (q + 1) - 1) R.erase := by
    have hpositive : 0 < ((S.E.committee
        (S.hc.opening_slot (q + 1) - 1)) ∩ rho.honest).card := by
      have hc := hcom (S.hc.opening_slot (q + 1) - 1)
      omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
    have hwCommittee : w ∈ S.E.committee
        (S.hc.opening_slot (q + 1) - 1) :=
      (Finset.mem_inter.mp hw).1
    have hwHonest : w ∈ rho.honest :=
      (Finset.mem_inter.mp hw).2
    obtain ⟨X, hRX, hXrun, hXemit⟩ :=
      hvotesR w hwHonest hwCommittee
    exact ⟨X, ⟨w, hwHonest, hwCommittee, hXrun, hXemit⟩, hRX,
      hheadThin X ⟨w, hwHonest, hwCommittee, hXrun, hXemit⟩⟩
  refine ⟨R, roundCeiling_of_boundaryCone S adm hcom hfb
    hboundaryConfirmationInHorizon
    { run := hRrun
      boundaryThinHead := hthinHead
      postAction := hpostAction
      postBoundaryVote := hpostBoundaryVote
      boundaryVotes := hvotesR
      previousCarriers := fun v hv =>
        Block.preceq_trans (hcarriers v hv) hCR
      rootOrder := hrootOrder } hreg, hCR⟩

#print axioms roundCeiling_base_of_carrierFrontier

/-! ## Named successor ceiling -/

private theorem roundCeiling_actionCarriersBelowFrontier_of_admissible
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M : Height} {q : Round} {C Cstar : NamedBlock V}
    (h : RoundCeilingAt S rho M q C)
    (hfrontier : RoundCeilingFrontierAt S rho q C Cstar) :
    ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v q) Cstar.erase := by
  intro v hv
  set n := actionReadAt S rho v q with hn
  set ast := n.st.core.toHealing with hast
  set grades := DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc ast q
    with hgrades
  have hround : S.hc.round_of ast.s = q :=
    Proofs.HealingLemmas.round_of_slotOf_a S q
  have hlive : Block.Preceq ast.live_confirmed Cstar.erase := by
    have hout := hfrontier.outputsPreceq v hv
    simpa only [roundCeilingOpeningOutput, actionStoreAt, actionReadAt,
      n, ast] using hout
  have hroot : Block.Preceq grades.anchor Cstar.erase := by
    have hanchor : Block.Preceq (PhaseGrades.nodeAnchor S n q) C.erase := by
      simpa only [Internal.NamedRecoveryRead.actionDutyRead, n] using
        h.actionAnchor v hv
    have hanchor' : Block.Preceq grades.anchor C.erase := by
      change Block.Preceq (PhaseGrades.nodeAnchor S n q) C.erase
      exact hanchor
    exact Block.preceq_trans hanchor' hfrontier.oldPreceq
  have hsg : actionSGBlockAt S rho v q = Protocol.currentSGVote ast grades := by
    show Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache) S.E S.hc ast
        (S.hc.round_of ast.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc ast
          (S.hc.round_of ast.s)) = Protocol.currentSGVote ast grades
    rw [hround]
    rfl
  rw [hsg]
  unfold Protocol.currentSGVote
  cases hclear : Protocol.deepest_clear (some grades.anchor) ast.live_confirmed
      grades.clear with
  | some B =>
      exact Block.preceq_trans (Proofs.Engine.deepest_clear_preceq hclear) hlive
  | none =>
      cases hgrade : grades.Q2 with
      | some Q =>
          have hQ2 : PhaseGrades.nodeQ2 S n q = some Q := by
            change grades.Q2 = some Q
            exact hgrade
          have hactionHor : S.a q ≤ rho.horizon := by
            rw [Setup.a, Protocol.a_eq_confirmation_time]
            exact (confirmationTime_mono_step S.E
              (openingSlot_le_lastPred_step S q)).trans
              h.roundConfirmationInHorizon
          have hQA := actionQ2_preceq_actionAnchor S
            adm.toNamedAdmissibleCore hv h.roundPositive hactionHor hQ2
          have hQA' : Block.Preceq Q grades.anchor := by
            change Block.Preceq Q (PhaseGrades.nodeAnchor S n q)
            simpa only [n] using hQA
          simp only [hclear, hgrade]
          exact Block.preceq_trans hQA' hroot
      | none =>
          by_cases hraw : grades.rawG2
          · have hFGanchor : Block.Preceq
                (Protocol.get_fg_root ast.toFG) grades.anchor := by
              change Block.Preceq
                (Protocol.get_fg_root ast.toFG)
                (PhaseGrades.nodeAnchor S n q)
              exact fg_root_preceq_get_sg_root_with_frame n.cache S.E S.hc ast q
            simp only [hclear, hgrade, hraw]
            exact Block.preceq_trans hFGanchor hroot
          · simp only [hclear, hgrade, hraw]
            exact hroot

/-- One successor ceiling from only the pointwise next-round regime facts.
When a certificate revealed inside the round moves an honest FG root above the
selected frontier, the successor is re-based on the deepest such root. -/
theorem roundCeiling_step_or_rebase
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round} {C : NamedBlock V}
    (h : RoundCeilingAt S rho M q C)
    (hreg : RoundCeilingNextRegimeAt S rho M q) :
    ∃ B : NamedBlock V, RoundCeilingAt S rho M (q + 1) B ∧
      Block.Preceq C.erase B.erase ∧
      ∀ v ∈ rho.honest,
        Block.Preceq (roundCeilingOpeningOutput S rho q v) B.erase := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  obtain ⟨Cstar, hfrontier⟩ := roundCeiling_existsFrontier S adm hcom h
  have hrun : RunBlock S rho Cstar := hfrontier.run
  have hupper : ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v q) Cstar.erase :=
    roundCeiling_actionCarriersBelowFrontier_of_admissible
      S adm h hfrontier
  have hopenLastQ : S.hc.opening_slot q ≤ seedRoundLastSlot S q :=
    Nat.le_of_lt (openingSlot_lt_last_step S q)
  have hpostBoundary : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot (q + 1) - 1) := by
    have hpostLast : S.E.t_GST ≤
        Protocol.vote_time S.E (seedRoundLastSlot S q) :=
      h.postOpeningVote.trans (vote_time_mono_slots S.E hopenLastQ)
    simpa only [seedRoundLastSlot] using hpostLast
  have hlastVotes : NamedHonestVotesCone S rho
      (seedRoundLastSlot S q)
      (fun X => Block.Preceq Cstar.erase X) := by
    by_cases heq : Cstar = C
    · subst Cstar
      exact roundCeiling_votesThrough S adm hcom h (seedRoundLastSlot S q)
        hopenLastQ (le_refl _)
    · obtain ⟨v, hv, hgen⟩ :=
        RoundCeilingFrontierAt.genuine_of_ne S adm hcom h hfrontier heq
      exact (roundCeiling_persistence S adm hcom hsb h hv hgen).1
        (seedRoundLastSlot S q)
        (Nat.succ_le_iff.mpr (openingSlot_lt_last_step S q)) (le_refl _)
  have hpostAction : S.E.t_GST ≤ S.a q := by
    simpa only [Protocol.a_eq_confirmation_time] using
      h.postOpeningVote.trans
        (Protocol.vote_time_le_confirmation_time S.E
          (S.hc.opening_slot q))
  obtain ⟨X0, hX0honest, hCstarX0, hX0thin⟩ :=
    roundCeiling_thinHead_of_cone S adm hcom h hopenLastQ (le_refl _) hlastVotes
  have hX0run : RunBlock S rho X0 := by
    obtain ⟨-, -, -, hrunX0, -⟩ := hX0honest
    exact hrunX0
  obtain ⟨R, hRrun, hCstarR, hRoots, hRbelow⟩ :=
    exists_roundCeilingRebase S adm hsb hreg hrun hX0run hX0thin hCstarX0
  have hlastVotesR : NamedHonestVotesCone S rho
      (seedRoundLastSlot S q)
      (fun X => Block.Preceq R.erase X) := by
    intro w hw hwcommittee
    obtain ⟨X, hCstarX, hXrun, hXemit⟩ := hlastVotes w hw hwcommittee
    exact ⟨X,
      hRbelow X hXrun
        (roundCeiling_headThin S adm h hopenLastQ (le_refl _)
          ⟨w, hw, hwcommittee, hXrun, hXemit⟩) hCstarX,
      hXrun, hXemit⟩
  have hboundaryThinR : ThinHonestHeadAt S rho M
      (S.hc.opening_slot (q + 1) - 1) R.erase := by
    have hthinHead := roundCeiling_thinHead_of_cone S adm hcom h hopenLastQ
      (le_refl _) hlastVotesR
    simpa only [seedRoundLastSlot] using hthinHead
  have hrootOrder : RoundCeilingNextRootOrderAt S rho q R.erase := hRoots
  have hboundaryHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (q + 1) - 1) ≤ rho.horizon :=
    (confirmationTime_mono_step S.E
      ((Nat.sub_le _ 1).trans
        (openingSlot_le_lastPred_step S (q + 1)))).trans
      hreg.roundConfirmationInHorizon
  refine ⟨R, roundCeiling_of_boundaryCone S adm hcom hfb hboundaryHor
    { run := hRrun
      boundaryThinHead := hboundaryThinR
      postAction := hpostAction
      postBoundaryVote := hpostBoundary
      boundaryVotes := by simpa only [seedRoundLastSlot] using hlastVotesR
      previousCarriers := fun v hv =>
        Block.preceq_trans (hupper v hv) hCstarR
      rootOrder := hrootOrder } hreg, ?_, ?_⟩
  · exact Block.preceq_trans hfrontier.oldPreceq hCstarR
  · intro v hv
    exact Block.preceq_trans (hfrontier.outputsPreceq v hv) hCstarR

/-- Iterate the re-basing successor over an inclusive round interval. -/
theorem roundCeiling_through_or_rebase
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {base last : Round} {C : NamedBlock V}
    (hbase : RoundCeilingAt S rho M base C)
    (hregime : ∀ k : Round, base ≤ k → k < last →
      RoundCeilingNextRegimeAt S rho M k) :
    ∀ k : Round, base ≤ k → k ≤ last →
      ∃ B : NamedBlock V, RoundCeilingAt S rho M k B ∧
        Block.Preceq C.erase B.erase := by
  intro k hklo
  induction k, hklo using Nat.le_induction with
  | base =>
      intro _
      exact ⟨C, hbase, Block.preceq_self C.erase⟩
  | succ k hklo ih =>
      intro hsuccLast
      have hkLast : k ≤ last := (Nat.le_succ k).trans hsuccLast
      obtain ⟨B, hB, hCB⟩ := ih hkLast
      have hklt : k < last :=
        lt_of_lt_of_le (Nat.lt_succ_self k) hsuccLast
      obtain ⟨Bnext, hBnext, hBBnext, -⟩ :=
        roundCeiling_step_or_rebase S adm hcom hfb hB
          (hregime k hklo hklt)
      exact ⟨Bnext, hBnext, Block.preceq_trans hCB hBBnext⟩

#print axioms roundCeiling_step_or_rebase
#print axioms roundCeiling_through_or_rebase





end HealingSurface
end Proofs
end DecoupledConsensusModel

end
