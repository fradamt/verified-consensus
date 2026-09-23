module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.MovingChainHandoffBase
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainRoundRead
public import DecoupledConsensusProofs.Objects.MovingChainStep
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroActionHead
public import DecoupledConsensusProofs.Execution.W4HandoffStructures
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.AdoptionRun
public import DecoupledConsensusProofs.Protocol.ChainState.RowFreshness
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Execution.MovingChainBandCover
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainFold
public import DecoupledConsensusProofs.Protocol.ValidatorClient.CanonicalRegimeFirstVote
public import DecoupledConsensusProofs.Generic.CanonicalRegimeFromChain
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainBatch
public import DecoupledConsensusProofs.Protocol.Schedule.SeedBase
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.MovingChainCeiling
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryConeConfirmation

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Moving-chain records from a healed handoff

This module runs the moving-slot fold through the finite horizon and exports
the two records used by the finality track. The handoff round supplies its
height-source provenance through its genuine confirmation. The successor
round uses its own genuine confirmation and the later event endpoint,
including when `R = 2`. Neither source history is a caller premise.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]















































/-- Full FG source history supplies the canonical origin of every stored
target above the boundary frontier. No carrier or grade premise is needed. -/
theorem canonicalTargetHistoryAt_of_heightHistory
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 r : Round} {P : NamedBlock V}
    (hheightHistory : CanonicalHeightSourceHistoryAt S rho q0 r P) :
    CanonicalTargetHistoryAt S rho q0 r P := by
  intro v hv hh X habove hrow
  obtain ⟨N, hN, hbefore⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
  rw [hN] at hrow
  obtain ⟨j, t, hjN, hjev, a, hmem, hhp⟩ :=
    stateBefore_target_own_emission S rho v N hrow
  have hemits : rho.emits S v (Object.attest a) t := ⟨j, hjev, hmem⟩
  obtain ⟨-, ht⟩ := Proofs.Optimistic.emits_attest_shape S hemits
  have htick : Event.tick v t ∈ rho.events := List.mem_of_getElem? hjev
  have hhorRound : S.a a.round ≤ rho.horizon := by
    have hle := (adm.in_horizon _ htick).2
    rw [ht] at hle
    exact hle
  have hexact := honest_emits_exact_actionAttestationAt
    S adm hv a.round hhorRound
  have haEq : a = actionAttestationAt S rho v a.round := by
    refine Proofs.Optimistic.emits_attest_unique S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      hemits hexact ?_
    exact (actionAttestationAt_shape S rho v a.round).2.1.symm
  have hrowAction : (actionAttestationAt S rho v a.round).height_pair.erase =
      HeightPair.target hh X := by
    rw [← haEq]
    exact hhp
  have hheight :
      (actionAttestationAt S rho v a.round).height_pair.erase.height? = some hh := by
    rw [hrowAction]
    rfl
  have hq0 : q0 < a.round :=
    honestRow_after_frontier S adm hv habove hheight
  have hlt : a.round < r := by
    have hbeforeT : t < S.a r := hbefore j (Event.tick v t) hjN hjev
    rw [ht] at hbeforeT
    exact (action_strictMono S).lt_iff_lt.mp hbeforeT
  obtain ⟨Q, hsource, hrun, hpreceq, hQheight⟩ :=
    hheightHistory a.round (Nat.le_of_lt hq0) hlt v hv hh hheight
  refine ⟨Q, hrun, hpreceq, hQheight, ?_⟩
  generalize hp : (actionAttestationAt S rho v a.round).height_pair = pair
    at hrowAction
  cases pair with
  | empty => simp [hp, NamedHeightPair.erase] at hrowAction
  | vote h' entry timeout =>
      have hrowPair : h' = hh ∧ entry = X := by
        cases timeout <;>
          simpa [hp, NamedHeightPair.erase] using hrowAction
      have hh' : h' = hh := hrowPair.1
      have hentry : entry = X := hrowPair.2
      subst h'
      subst entry
      have hpair : (actionAttestationAt S rho v a.round).height_pair =
          NamedHeightPair.vote hh X timeout := by simpa [hp]
      obtain ⟨Cfg, hCfg, hCfgHeight, hCfgRoot⟩ :=
        NamedActionSources.action_source S rho v a.round hh X timeout hpair
      obtain ⟨Q', hQbody, hQerase, hQderive, -⟩ :=
        NamedActionSources.action_witness S rho v a.round Cfg hCfg
      have hQbodyPre : Q' ∈
          (rho.stateBeforeTime S (S.a a.round) v).st.bodies := by
        simpa only [actionStoreAt, actionReadAt,
          NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
          NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
          NamedRun.stateBeforeTime] using hQbody
      obtain ⟨N, hN, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a a.round)
      have hQrun : RunBlock S rho Q' := by
        apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := N)
        simpa only [hN] using hQbodyPre
      have hCfgQ : Cfg = Q.erase := Option.some.inj (hCfg.symm.trans hsource)
      have hroots : Q'.root = Q.root := by
        rw [← Proofs.NamedWire.erase_root Q', ← Proofs.NamedWire.erase_root Q,
          hQerase, hCfgQ]
      have hQQ := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
        Q' Q hQrun hrun Q' Q
        (Or.inl (Proofs.NamedAncestry.named_self Q'))
        (Or.inr (Proofs.NamedAncestry.named_self Q)) hroots
      have hderiveQ :
          (actionReadAt S rho v a.round).st.core.σ Q.erase =
            Protocol.derive_named S.E S.cfg Q := by
        rw [← hCfgQ, hQderive, hQQ]
      rw [← hderiveQ]
      simpa only [hCfgQ] using hCfgRoot




/-
  obtain ⟨s, F, FoldEnd, hfold, hbaseEq, hcov⟩:=
    handoffFoldCover S adm hcom hfb h hboundary hbaseTiming
      _of_movingSlotFoldAt_of_handoff
  have hpostAtQ: S.E.t_GST ≤ S.a q:=
    post_action_of_baseTiming_handoffExport S hbaseTiming.1
      hbaseTiming.2.1 (Nat.le_refl q)
  have hpostAtBoundaryProposal: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q + 2):=
    hpostAtQ.trans (action_le_proposal_plus_two_handoffExport S q)
  have hlive: ∀ r: Round, q + 1 < r → S.a r ≤ rho.horizon →
      ∀ v ∈ rho.honest,
        Block.Preceq (F (S.hc.opening_slot r))
          (actionStoreAt S rho v r).live_confirmed:= by
    exact _of_liveAboveEndpoint hfold hcov
    intro r hr hhor v hv
    obtain ⟨hlow, hhigh⟩:= hcov.mem_range_round hr hhor
    have hrpos: 0 < r:=
      (Nat.zero_lt_succ (q + 1)).trans_le (Nat.succ_le_iff.mpr hr)
    have hp: r - 1 + 1 = r:= Nat.sub_add_cancel hrpos
    have hpred: q + 1 ≤ r - 1:=
      nat_pred_ge_of_succ_le_handoffExport (Nat.succ_le_iff.mpr hr)
    have ht1:= cutoff_le_action_of_q_succ_le_handoffExport S hpred
    have hpostPred:= hpostAtQ.trans
      (action_time_mono_handoffExport S ((Nat.le_succ q).trans hpred))
    have hpredHor: S.a (r - 1) ≤ rho.horizon:=
      (action_time_mono_handoffExport S (Nat.sub_le r 1)).trans hhor
    have hstep:= hfold.mono _ _ hlow (Nat.le_succ (S.hc.opening_slot r))
      (Nat.succ_le_iff.mpr hhigh)
    have hupper: ∀ u ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho u (r - 1))
          (F (S.hc.opening_slot r + 1)):= by
      intro u hu
      have hcarrier:= hfold.actionCarriers_preceq_endpoint S adm ht1 hpredHor
        (by rw [hp]; exact hlow) (by rw [hp]; exact le_of_lt hhigh) u hu
      rw [hp] at hcarrier
      exact Block.preceq_trans hcarrier hstep
    have hslots: S.hc.opening_slot (r - 1) + 2 ≤ S.hc.opening_slot r:= by
      simpa only [← Nat.add_one, hp] using openingSlot_add_two_le_openingSlot_of_lt S
        (Nat.lt_succ_self (r - 1))
    have hstart: Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) ≤
        Protocol.proposal_time S.E (S.hc.opening_slot r + 1):=
      ht1.trans ((action_le_proposal_plus_two_handoffExport S (r - 1)).trans
        (proposal_time_mono_handoffExport S.E (hslots.trans (Nat.le_succ _))))
    have hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot r):=
      hpostPred.trans ((action_le_proposal_plus_two_handoffExport S (r - 1)).trans
        ((proposal_time_mono_handoffExport S.E hslots).trans
          (le_of_lt (Protocol.proposal_time_lt_vote_time S.E _))))
    have hout:= hfold.confOutcome_at_cursor_of_ceiling S adm hcom hfb (r:= r - 1)
      (lt_of_lt_of_le (by decide: 0 < 3) ((Nat.le_add_left 3 _).trans hlow))
      hlow hhigh hstart
      (by rw [hp]; exact Proofs.HealingLemmas.round_of_opening_succ S.hc r)
      hupper hpostPred (by rw [hp]; exact (gammaNegOne_le_action_handoffExport S r).trans hhor)
      hpostVote (by simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hhor) hv
    rw [actionStoreAt_eq_update_confirmation_openingConfStore]
    exact Block.preceq_trans hstep hout.2
  have hbatch: ∀ r: Round, q + 1 < r → S.a r ≤ rho.horizon →
      ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
        CanonicalBatchVoteAt S rho r
          (actionStoreAt S rho v r).toHealing.gradeView w:= by
    intro r hr hhor v hv
    have hq2r: q + 2 ≤ r:= Nat.succ_le_iff.mpr hr
    have hrPos: 0 < r:= (Nat.zero_lt_succ (q + 1)).trans_le hq2r
    let p:= r - 1
    let d:= S.hc.opening_slot r - 1
    have hpSucc: p + 1 = r:= by
      dsimp only [p]
      exact nat_pred_add_one_handoffExport hrPos
    have hopenPos: 0 < S.hc.opening_slot r:= by
      have hbasePos: 0 < S.hc.opening_slot q + 3:=
        nat_zero_lt_add_three_handoffExport _
      exact hbasePos.trans_le
        (base_le_opening_of_q_add_two_le_handoffExport S hq2r)
    have hdSucc: d + 1 = S.hc.opening_slot r:= by
      dsimp only [d]
      exact nat_pred_add_one_handoffExport hopenPos
    have hq1p: q + 1 ≤ p:= by
      dsimp only [p]
      exact nat_pred_ge_of_succ_le_handoffExport hq2r
    have hdLow: S.hc.opening_slot q + 3 ≤ d:= by
      dsimp only [d]
      exact nat_le_pred_of_succ_le_handoffExport
        (base_succ_le_opening_of_q_add_two_le_handoffExport S hq2r)
    obtain ⟨hlow, hhigh⟩:= hcov.mem_range_round hr hhor
    have hdHigh: d < s:= by
      exact lt_of_le_of_lt (Nat.sub_le _ _) hhigh
    have ht1: Protocol.support_cutoff S.E
        (S.hc.opening_slot q + 2) ≤ S.a p:=
      cutoff_le_action_of_q_succ_le_handoffExport S hq1p
    have hpost: S.E.t_GST ≤ S.a p:=
      post_action_of_baseTiming_handoffExport S hbaseTiming.1
        hbaseTiming.2.1 ((Nat.le_succ q).trans hq1p)
    have hpLeR: p ≤ r:= by
      dsimp only [p]
      exact Nat.sub_le _ _
    have hhorP: S.a p ≤ rho.horizon:=
      (action_time_mono_handoffExport S hpLeR).trans hhor
    have hcutHor: S.hc.Γ_neg1 S.E.Δ r ≤ rho.horizon:=
      (gammaNegOne_le_action_handoffExport S r).trans hhor
    have hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E d:= by
      refine hpostAtBoundaryProposal.trans ?_
      have hslot: S.hc.opening_slot q + 2 ≤ d:=
        (Nat.le_succ (S.hc.opening_slot q + 2)).trans hdLow
      exact (proposal_time_mono_handoffExport S.E hslot).trans
        (le_of_lt (proposal_time_lt_vote_time S.E d))
    have hstart: Protocol.support_cutoff S.E
        (S.hc.opening_slot q + 2) ≤ S.a r:=
      cutoff_le_action_of_q_succ_le_handoffExport S
        (Nat.le_of_lt hr)
    have hbatchAt:= hfold.batchComplete S adm hcom hfb
      (r:= p) (d:= d) (by rw [hpSucc]; exact hdSucc) hdLow hdHigh
      ht1 hpost hhorP (by rw [hpSucc]; exact hcutHor) hpostVote
      (by rw [hpSucc]; exact hhor) hv (by rw [hpSucc]; exact hstart)
      (by intro w hw
          simpa only [d] using
            (_of_honestHeadsAvailableBefore r hr hhor w hw))
    simpa only [hpSucc] using hbatchAt
  have hcarriers: ∀ r: Round, q + 1 < r → S.a r ≤ rho.horizon →
      ∀ w ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho w (r - 1))
          (F (S.hc.opening_slot r)):= by
    intro r hr hhor
    have hq2r: q + 2 ≤ r:= Nat.succ_le_iff.mpr hr
    have hrPos: 0 < r:= (Nat.zero_lt_succ (q + 1)).trans_le hq2r
    obtain ⟨hlow, hhigh⟩:= hcov.mem_range_round hr hhor
    have hq1pred: q + 1 ≤ r - 1:=
      nat_pred_ge_of_succ_le_handoffExport hq2r
    have ht1:= cutoff_le_action_of_q_succ_le_handoffExport S hq1pred
    have hpredLe: r - 1 ≤ r:= Nat.sub_le _ _
    have hhorPred: S.a (r - 1) ≤ rho.horizon:=
      (action_time_mono_handoffExport S hpredLe).trans hhor
    have hpredSucc: r - 1 + 1 = r:=
      nat_pred_add_one_handoffExport hrPos
    have hout:= hfold.actionCarriers_preceq_endpoint S adm
      (r:= r - 1) ht1 hhorPred (by rw [hpredSucc]; exact hlow)
      (by rw [hpredSucc]
          exact le_of_lt hhigh)
    simpa only [hpredSucc] using hout
  have hanchors: ∀ r: Round, q + 1 < r → S.a r ≤ rho.horizon →
      ∀ v ∈ rho.honest,
        Block.Preceq
          (Proofs.Optimistic.healAnchor S.E S.hc
            (actionStoreAt S rho v r).toHealing)
          (F (S.hc.opening_slot r)):= by
    intro r hr hhor v hv
    exact _of_actionAnchor_preceq_endpoint hfold hcov r hr hhor v hv
  have hheightHistory: ∀ r: Round, q + 1 < r →
      S.a r ≤ rho.horizon → ∀ P: NamedBlock V,
        proposedBlockAt S rho (S.hc.opening_slot r) = some P →
        CanonicalHeightSourceHistoryAt S rho q r P:= by
    intro r hr hhor P hP
    obtain ⟨hlow, hhigh⟩:= hcov.mem_range_round hr hhor
    have hFP:= _of_endpoint_preceq_openingProposal hfold hcov r hr hhor P hP
    exact canonicalHeightSourceHistoryAt_of_handoffFold S adm hcom hfb h hboundary
      hbaseTiming _of_preparedBoundaryOutput _of_preparedSuccessorConfirmation
        _of_handoffRoundPos _of_movingSlotFoldAt_of_handoff
        hfold hbaseEq hlow hhigh hhor hP hFP
        (_of_proposedBlock_runBlock r P hP)
        _of_selectedG2_preceq_honestPreviousCarrier
        (_of_successorHeightSource hfold hcov)
  have htargetHistory: ∀ r: Round, q + 1 < r →
      S.a r ≤ rho.horizon → ∀ P: NamedBlock V,
        proposedBlockAt S rho (S.hc.opening_slot r) = some P →
        CanonicalTargetHistoryAt S rho q r P:= by
    intro r hr hhor P hP
    exact canonicalTargetHistoryAt_of_heightHistory S adm
      (hheightHistory r hr hhor P hP)
  have htimeoutHistory: ∀ r: Round, q + 1 < r →
      S.a r ≤ rho.horizon → ∀ P: NamedBlock V,
        proposedBlockAt S rho (S.hc.opening_slot r) = some P →
        CanonicalTimeoutHistoryAt S rho q r P:= by
    intro r hr hhor P hP
    exact _of_timeoutHistory r hr hhor P hP
  have hmem: ∀ r: Round, q + 1 < r → S.a r ≤ rho.horizon →
      ∀ v ∈ rho.honest,
        F (S.hc.opening_slot r) ∈
          (rho.storeBeforeTime S v (S.a r)).T:= by
    intro r hr hhor v hv
    have hq2r: q + 2 ≤ r:= Nat.succ_le_iff.mpr hr
    have hopenPos: 0 < S.hc.opening_slot r:= by
      exact (nat_zero_lt_add_three_handoffExport
        (S.hc.opening_slot q)).trans_le
          (base_le_opening_of_q_add_two_le_handoffExport S hq2r)
    let d:= S.hc.opening_slot r - 1
    have hdSucc: d + 1 = S.hc.opening_slot r:= by
      dsimp only [d]
      exact nat_pred_add_one_handoffExport hopenPos
    have hdLow: S.hc.opening_slot q + 3 ≤ d:= by
      dsimp only [d]
      exact nat_le_pred_of_succ_le_handoffExport
        (base_succ_le_opening_of_q_add_two_le_handoffExport S hq2r)
    obtain ⟨hlow, hhigh⟩:= hcov.mem_range_round hr hhor
    have hdHigh: d < s:=
      lt_of_le_of_lt (Nat.sub_le _ _) hhigh
    have hvotes: NamedHonestVotesCone S rho d
        (fun X => Block.Preceq (F (S.hc.opening_slot r)) X):= by
      rw [← hdSucc]
      exact hfold.windowCone d hdLow hdHigh
    have hroot:= _of_actionRoot_preceq_endpoint hfold hcov r hr hhor v hv
    have hcut: Protocol.support_cutoff S.E d ≤ S.a r:=
      support_cutoff_before_action_handoffExport S hdSucc
    have hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E d:= by
      refine hpostAtBoundaryProposal.trans ?_
      have hslot: S.hc.opening_slot q + 2 ≤ d:=
        (Nat.le_succ (S.hc.opening_slot q + 2)).trans hdLow
      exact (proposal_time_mono_handoffExport S.E hslot).trans
        (le_of_lt (proposal_time_lt_vote_time S.E d))
    have havailable:= _of_honestHeadsAvailableBefore r hr hhor v hv
    obtain ⟨hmem, _hstamp⟩:= storeBeforeTime_mem_stamp_of_cone
      S adm hcom havailable hcut hvotes (Block.preceq_self _)
    exact hmem
  exact movingChainRoundFloorFrom_of_bandCover S adm hcom hfb hfold hcov
    _of_namedBand (_of_actionFrontier_sub_one_le_endpointHeight hfold hcov)
    hlive (hfold.endpointMonotone_guarded S hcov)
    (_of_endpointBelowHonestParent hfold hcov)
    (_of_honestProposalAbsorbed hfold hcov) hbatch hcarriers hanchors
    hheightHistory htargetHistory htimeoutHistory hmem

-/

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
