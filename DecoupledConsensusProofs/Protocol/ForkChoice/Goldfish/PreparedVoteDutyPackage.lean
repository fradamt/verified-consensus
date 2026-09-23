module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapAction
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakBootstrapGradePersistence
public import DecoupledConsensusProofs.Protocol.Store.WeakSGHistory
public import DecoupledConsensusProofs.Protocol.Grades.SeedRelativeGrade
public import DecoupledConsensusProofs.Protocol.Grades.HeightProgressClosureBatchAlignedSite

@[expose] public section

/-!
# Prepared vote-duty inputs

This module collects the three reader-local facts consumed by the prepared
Goldfish successor. The cached G1 fact is stated on the active-prefix branch:
the frame-grade persistence result is only valid after the later reader has
selected an active prefix of the cached raw value.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakJoint

open Internal Execution Protocol Proofs.Optimistic
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


private theorem persistentVoteTime_lt_nextProposal
    (E : Env V) (s : Slot) :
    Protocol.vote_time E s < Protocol.proposal_time E (s + 1) := by
  apply lt_trans ?_ (support_cutoff_lt_proposal_time_succ E s)
  rw [← vote_time_add_delta]
  exact Int.lt_add_of_pos_right _ E.Δ_pos

private theorem voteDuty_before_next_round_opening
    (S : Setup V) (d : Slot) :
    Protocol.vote_time S.E d ≤ DecoupledConsensusModel.Protocol.opening S.E S.hc
      (S.hc.round_of d + 1) := by
  have hRpos : 0 < S.hc.R := Nat.zero_lt_of_lt S.hc.R_ge_two
  have hslot : d < S.hc.opening_slot (S.hc.round_of d + 1) := by
    apply (Nat.div_lt_iff_lt_mul hRpos).mp
    exact Nat.lt_succ_self (S.hc.round_of d)
  exact (persistentVoteTime_lt_nextProposal S.E d).le.trans
    (by
      simpa only [DecoupledConsensusModel.Protocol.opening] using
        proposal_time_mono S.E (Nat.succ_le_of_lt hslot))


set_option maxHeartbeats 400000 in
private theorem interpretedInputs_nonempty_at_voteDuty_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : NamedHealthyPrefixDelivery S rho cap)
    {base r : Round} {d : Slot} {B : Block V}
    (hround : S.hc.round_of d = r) (hr : 0 < r)
    (hspan : base ≤ r - S.hc.η_SG)
    (hcarriers : ∀ k, base ≤ k → k < r → ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
      Block.Preceq (actionSGBlockAt S rho u k) B)
    (hroots : ∀ w ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG) B = true)
    (hcapEarly : DecoupledConsensusModel.Protocol.early S.E S.hc r .g1 ≤ cap)
    (hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon) :
    ∀ w ∈ rho.honest, ∀ u ∈ rho.honest,
      ∀ k ∈ Protocol.latest_window S.hc.η_SG r,
      (S.node u).awake k = true →
      ∃ y ∈ interpretedInputs
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.gradeView
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F
          S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1) u,
        y.round = k ∧
        y.confirmed = some (actionSGBlockAt S rho u k).root ∧
        Block.find?
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.T
          (actionSGBlockAt S rho u k).root = some (actionSGBlockAt S rho u k) := by
  intro w hw u hu k hk huk
  have hklt : k < r := mem_latestWindow_lt hk
  have hkbase : base ≤ k :=
    hspan.trans (WeakSG.mem_latestWindow_lower_bound hk)
  have hdeadlineG2 : S.a k + S.E.Δ ≤ early S.E S.hc r .g2 :=
    NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt
  have hdeadline : S.a k + S.E.Δ ≤ early S.E S.hc r .g1 :=
    hdeadlineG2.trans (NamedOutageClosure.q10_early_g2_le_early_g1 S r)
  have hopen : S.hc.opening_slot r ≤ d := by
    exact hround ▸ Nat.div_mul_le_self d S.hc.R
  have hearlyVote : early S.E S.hc r .g1 ≤ Protocol.vote_time S.E d := by
    have hearlyOpening : early S.E S.hc r .g1 ≤
        Protocol.proposal_time S.E (S.hc.opening_slot r) := by
      simp only [early, DecoupledConsensusModel.Protocol.Phase.earlyOffset,
        DecoupledConsensusModel.Protocol.opening]
      linarith [S.E.Δ_pos]
    exact hearlyOpening.trans ((proposal_time_mono S.E hopen).trans
      (proposal_time_lt_vote_time S.E d).le)
  have hactionHor : S.a k ≤ rho.horizon :=
    (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (hdeadline.trans (hearlyVote.trans hvoteHor))
  have hemit := honest_emits_exact_actionAttestationAt_of_awake
    S adm.toNamedScheduleWellFormed hu k huk hactionHor
  obtain ⟨i, hi, _, hbody⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
  dsimp at hbody
  obtain ⟨K, hKstaged, haK⟩ := hbody
  have hKindex : K ∈ (NamedRun.stateBefore S rho i u).st.bodies := by
    change K ∈ (NamedRun.stateBefore S rho i u).st.bodies at hKstaged
    exact hKstaged
  have hcarrierMem : actionSGBlockAt S rho u k ∈
      (NamedRun.stateBeforeTime S rho (S.a k) u).st.core.T :=
    actionSGBlockAt_mem_storeBeforeTime S rho u k
  obtain ⟨D', hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a k) u hcarrierMem
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted (S.a k)
  have hDprefix : D' ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hDbody
  have hKprefix : K ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact (by
      have hstate := NamedActionSources.action_read_index S rho
        adm.toNamedScheduleWellFormed i u k hi
      rw [← hstate]
      exact hKindex)
  have hDrun : RunBlock S rho D' :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu hDprefix
  have hKrun : RunBlock S rho K :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu hKprefix
  have hDKroot : D'.root = K.root := by
    rw [← Proofs.NamedWire.erase_root D', hDerase]
    exact Option.some.inj ((actionAttestationAt_shape S rho u k).2.2.symm.trans haK)
  have hDK : D' = K :=
    adm.toNamedRootCollisionFree.root_injective D' K hDrun hKrun D' K
      (Or.inl (Proofs.NamedAncestry.named_self D'))
      (Or.inr (Proofs.NamedAncestry.named_self K)) hDKroot
  have hHErase : K.erase = actionSGBlockAt S rho u k := by
    rw [← hDK, hDerase]
  have hcarrierB := hcarriers k hkbase hklt u hu hemit
  have hFroot : Block.Preceq
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG) := by
    exact Proofs.Records.preceq_get_fg_root_of_F
      (st := (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG)
      (by
        simpa only [Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock, Protocol.Store.toHealing] using
          Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
            (Protocol.vote_time S.E d) w)
  have hrootCompat := hroots w hw
  rcases (show Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG) B ∨
      Block.Preceq B
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG) by
    simpa only [Block.compatible, Bool.or_eq_true] using hrootCompat) with hFB | hBF
  · have hinput := interpretedInputs_nonempty_of_honest_window_vote_of_delivery_common_upper
      S adm .g1 hdelivery hk hu hw
      (hvote := by
        refine ⟨(actionAttestationAt_shape S rho u k).1,
          (actionAttestationAt_shape S rho u k).2.1, hemit⟩)
      (hhead := ⟨i, hi, hKstaged, haK⟩)
      (hHC := by rw [hHErase]; exact hcarrierB)
      (hFC := Block.preceq_trans hFroot hFB)
      (by simpa only [actionAttestationAt_shape] using hdeadline) hearlyVote hcapEarly
    obtain ⟨y, hy, hyround, hyconfirmed, hyfind⟩ := hinput
    refine ⟨y, ?_, hyround, ?_, ?_⟩
    · simpa only [hHErase] using hy
    · simpa only [hHErase] using hyconfirmed
    · have hKroot : K.root = (actionSGBlockAt S rho u k).root := by
        rw [← hDK, ← Proofs.NamedWire.erase_root D', hDerase]
      rw [hHErase, hKroot] at hyfind
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hyfind
  · have hinput := interpretedInputs_nonempty_of_honest_window_vote_of_delivery_common_upper
      S adm .g1 hdelivery hk hu hw
      (hvote := by
        refine ⟨(actionAttestationAt_shape S rho u k).1,
          (actionAttestationAt_shape S rho u k).2.1, hemit⟩)
      (hhead := ⟨i, hi, hKstaged, haK⟩)
      (hHC := by
        rw [hHErase]
        exact Block.preceq_trans hcarrierB hBF)
      (hFC := hFroot)
      (by simpa only [actionAttestationAt_shape] using hdeadline) hearlyVote hcapEarly
    obtain ⟨y, hy, hyround, hyconfirmed, hyfind⟩ := hinput
    refine ⟨y, ?_, hyround, ?_, ?_⟩
    · simpa only [hHErase] using hy
    · simpa only [hHErase] using hyconfirmed
    · have hKroot : K.root = (actionSGBlockAt S rho u k).root := by
        rw [← hDK, ← Proofs.NamedWire.erase_root D', hDerase]
      rw [hHErase, hKroot] at hyfind
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hyfind

set_option maxHeartbeats 400000 in
/-- Windowed post-GST transport of the preceding carrier rows to a vote-duty
read. -/
private theorem interpretedInputs_nonempty_at_voteDuty_w
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {lo cap : Time} (_hdelivery : NamedHealthyWindowDelivery S rho lo cap)
    (hgstLo : S.E.t_GST ≤ lo)
    {base r : Round} {d : Slot} {B : Block V}
    (hround : S.hc.round_of d = r) (hr : 0 < r)
    (hspan : base ≤ r - S.hc.η_SG)
    (hsendLo : ∀ k, base ≤ k → k < r → lo ≤ S.a k)
    (hcarriers : ∀ k, base ≤ k → k < r → ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
      Block.Preceq (actionSGBlockAt S rho u k) B)
    (hroots : ∀ w ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG) B = true)
    (hcapEarly : DecoupledConsensusModel.Protocol.early S.E S.hc r .g1 ≤ cap)
    (hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon) :
    ∀ w ∈ rho.honest, ∀ u ∈ rho.honest,
      ∀ k ∈ Protocol.latest_window S.hc.η_SG r,
      (S.node u).awake k = true →
      ∃ y ∈ interpretedInputs
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.gradeView
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F
          S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1) u,
        y.round = k ∧
        y.confirmed = some (actionSGBlockAt S rho u k).root ∧
        Block.find?
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.T
          (actionSGBlockAt S rho u k).root = some (actionSGBlockAt S rho u k) := by
  intro w hw u hu k hk huk
  have hklt : k < r := mem_latestWindow_lt hk
  have hkbase : base ≤ k :=
    hspan.trans (WeakSG.mem_latestWindow_lower_bound hk)
  have hdeadlineG2 : S.a k + S.E.Δ ≤ early S.E S.hc r .g2 :=
    NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt
  have hdeadline : S.a k + S.E.Δ ≤ early S.E S.hc r .g1 :=
    hdeadlineG2.trans (NamedOutageClosure.q10_early_g2_le_early_g1 S r)
  have hopen : S.hc.opening_slot r ≤ d := by
    exact hround ▸ Nat.div_mul_le_self d S.hc.R
  have hearlyVote : early S.E S.hc r .g1 ≤ Protocol.vote_time S.E d := by
    have hearlyOpening : early S.E S.hc r .g1 ≤
        Protocol.proposal_time S.E (S.hc.opening_slot r) := by
      simp only [early, DecoupledConsensusModel.Protocol.Phase.earlyOffset,
        DecoupledConsensusModel.Protocol.opening]
      linarith [S.E.Δ_pos]
    exact hearlyOpening.trans ((proposal_time_mono S.E hopen).trans
      (proposal_time_lt_vote_time S.E d).le)
  have hactionHor : S.a k ≤ rho.horizon :=
    (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (hdeadline.trans (hearlyVote.trans hvoteHor))
  have hemit := honest_emits_exact_actionAttestationAt_of_awake
    S adm.toNamedScheduleWellFormed hu k huk hactionHor
  obtain ⟨i, hi, _, hbody⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
  dsimp at hbody
  obtain ⟨K, hKstaged, haK⟩ := hbody
  have hKindex : K ∈ (NamedRun.stateBefore S rho i u).st.bodies := by
    change K ∈ (NamedRun.stateBefore S rho i u).st.bodies at hKstaged
    exact hKstaged
  have hcarrierMem : actionSGBlockAt S rho u k ∈
      (NamedRun.stateBeforeTime S rho (S.a k) u).st.core.T :=
    actionSGBlockAt_mem_storeBeforeTime S rho u k
  obtain ⟨D', hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a k) u hcarrierMem
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted (S.a k)
  have hDprefix : D' ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hDbody
  have hKprefix : K ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact (by
      have hstate := NamedActionSources.action_read_index S rho
        adm.toNamedScheduleWellFormed i u k hi
      rw [← hstate]
      exact hKindex)
  have hDrun : RunBlock S rho D' :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu hDprefix
  have hKrun : RunBlock S rho K :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu hKprefix
  have hDKroot : D'.root = K.root := by
    rw [← Proofs.NamedWire.erase_root D', hDerase]
    exact Option.some.inj ((actionAttestationAt_shape S rho u k).2.2.symm.trans haK)
  have hDK : D' = K :=
    adm.toNamedRootCollisionFree.root_injective D' K hDrun hKrun D' K
      (Or.inl (Proofs.NamedAncestry.named_self D'))
      (Or.inr (Proofs.NamedAncestry.named_self K)) hDKroot
  have hHErase : K.erase = actionSGBlockAt S rho u k := by
    rw [← hDK, hDerase]
  have hcarrierB := hcarriers k hkbase hklt u hu hemit
  have hFroot : Block.Preceq
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG) := by
    exact Proofs.Records.preceq_get_fg_root_of_F
      (st := (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG)
      (by
        simpa only [Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock, Protocol.Store.toHealing] using
          Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
            (Protocol.vote_time S.E d) w)
  have hrootCompat := hroots w hw
  rcases (show Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG) B ∨
      Block.Preceq B
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG) by
    simpa only [Block.compatible, Bool.or_eq_true] using hrootCompat) with hFB | hBF
  · have hinput := interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
      S adm .g1 hk hu hw
      (hvote := by
        refine ⟨(actionAttestationAt_shape S rho u k).1,
          (actionAttestationAt_shape S rho u k).2.1, hemit⟩)
      (hhead := ⟨i, hi, hKstaged, haK⟩)
      (hHC := by rw [hHErase]; exact hcarrierB)
      (hFC := Block.preceq_trans hFroot hFB)
      (hpost := by
        simpa only [actionAttestationAt_shape] using
          hgstLo.trans (hsendLo k hkbase hklt))
      (by
        have hpostK := hgstLo.trans (hsendLo k hkbase hklt)
        have hmaxK : max (S.a k) S.E.t_GST = S.a k := max_eq_left hpostK
        simpa only [actionAttestationAt_shape, hmaxK] using hdeadline)
      hearlyVote (hearlyVote.trans hvoteHor)
    obtain ⟨y, hy, hyround, hyconfirmed, hyfind⟩ := hinput
    refine ⟨y, ?_, hyround, ?_, ?_⟩
    · simpa only [hHErase] using hy
    · simpa only [hHErase] using hyconfirmed
    · have hKroot : K.root = (actionSGBlockAt S rho u k).root := by
        rw [← hDK, ← Proofs.NamedWire.erase_root D', hDerase]
      rw [hHErase, hKroot] at hyfind
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hyfind
  · have hinput := interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
      S adm .g1 hk hu hw
      (hvote := by
        refine ⟨(actionAttestationAt_shape S rho u k).1,
          (actionAttestationAt_shape S rho u k).2.1, hemit⟩)
      (hhead := ⟨i, hi, hKstaged, haK⟩)
      (hHC := by
        rw [hHErase]
        exact Block.preceq_trans hcarrierB hBF)
      (hFC := hFroot)
      (hpost := by
        simpa only [actionAttestationAt_shape] using
          hgstLo.trans (hsendLo k hkbase hklt))
      (by
        have hpostK := hgstLo.trans (hsendLo k hkbase hklt)
        have hmaxK : max (S.a k) S.E.t_GST = S.a k := max_eq_left hpostK
        simpa only [actionAttestationAt_shape, hmaxK] using hdeadline)
      hearlyVote (hearlyVote.trans hvoteHor)
    obtain ⟨y, hy, hyround, hyconfirmed, hyfind⟩ := hinput
    refine ⟨y, ?_, hyround, ?_, ?_⟩
    · simpa only [hHErase] using hy
    · simpa only [hHErase] using hyconfirmed
    · have hKroot : K.root = (actionSGBlockAt S rho u k).root := by
        rw [← hDK, ← Proofs.NamedWire.erase_root D', hDerase]
      rw [hHErase, hKroot] at hyfind
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hyfind

set_option maxHeartbeats 400000 in
/-- Delivery of the preceding carrier rows gives the exact interpreted inputs
used by a positive-round vote-duty anchor. -/
theorem interpretedInputs_at_voteDuty_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : NamedHealthyPrefixDelivery S rho cap)
    {base r : Round} {d : Slot} {B : Block V}
    (hround : S.hc.round_of d = r) (hr : 0 < r)
    (hspan : base ≤ r - S.hc.η_SG)
    (hcarriers : ∀ k, base ≤ k → k < r → ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
      Block.Preceq (actionSGBlockAt S rho u k) B)
    (hroots : ∀ w ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG) B = true)
    (hcapEarly : DecoupledConsensusModel.Protocol.early S.E S.hc r .g1 ≤ cap)
    (hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon) :
    ∀ w ∈ rho.honest, ∀ u ∈ rho.honest,
      ∀ k ∈ Protocol.latest_window S.hc.η_SG r,
      (S.node u).awake k = true →
      ∃ y ∈ interpretedInputs
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.gradeView
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F
          S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1) u,
        y.round = k ∧
        y.confirmed = some (actionSGBlockAt S rho u k).root ∧
        Block.find?
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.T
          (actionSGBlockAt S rho u k).root = some (actionSGBlockAt S rho u k) := by
  exact interpretedInputs_nonempty_at_voteDuty_of_delivery S adm hdelivery
    hround hr hspan hcarriers hroots hcapEarly hvoteHor

#print axioms interpretedInputs_at_voteDuty_of_delivery
theorem interpretedInputs_at_voteDuty_w
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {lo cap : Time} (hdelivery : NamedHealthyWindowDelivery S rho lo cap)
    (hgstLo : S.E.t_GST ≤ lo)
    {base r : Round} {d : Slot} {B : Block V}
    (hround : S.hc.round_of d = r) (hr : 0 < r)
    (hspan : base ≤ r - S.hc.η_SG)
    (hsendLo : ∀ k, base ≤ k → k < r → lo ≤ S.a k)
    (hcarriers : ∀ k, base ≤ k → k < r → ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
      Block.Preceq (actionSGBlockAt S rho u k) B)
    (hroots : ∀ w ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG) B = true)
    (hcapEarly : DecoupledConsensusModel.Protocol.early S.E S.hc r .g1 ≤ cap)
    (hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon) :
    ∀ w ∈ rho.honest, ∀ u ∈ rho.honest,
      ∀ k ∈ Protocol.latest_window S.hc.η_SG r,
      (S.node u).awake k = true →
      ∃ y ∈ interpretedInputs
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.gradeView
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F
          S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1) u,
        y.round = k ∧
        y.confirmed = some (actionSGBlockAt S rho u k).root ∧
        Block.find?
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.T
          (actionSGBlockAt S rho u k).root = some (actionSGBlockAt S rho u k) := by
  exact interpretedInputs_nonempty_at_voteDuty_w S adm hdelivery hgstLo
    hround hr hspan hsendLo hcarriers hroots hcapEarly hvoteHor


#print axioms interpretedInputs_at_voteDuty_w


set_option maxHeartbeats 400000 in
theorem preparedVoteDutyG1FrameGrade_of_activePrefix
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {d : Slot} {r : Round} (hround : S.hc.round_of d = r)
    (hr : 0 < r) (hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon) :
    ∀ w ∈ rho.honest, ∀ raw,
      (DecoupledConsensusModel.Protocol.readFrame
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).cache
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing r).g1 =
          some (some raw) →
      ∀ A,
        DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree
            (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG)
          raw = some A →
      Internal.PhaseGrades.phaseGrade S.E S.hc
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.gradeView
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F r .g1 raw = true := by
  intro w hw raw hframe A hactive
  have hnext : Protocol.vote_time S.E d ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1) := by
    simpa only [hround] using voteDuty_before_next_round_opening S d
  exact WeakSG.phaseGrade_voteDuty_of_preparedFrame_g1_of_activePrefix
    S adm hround hr hnext hvoteHor hw
    (read := Internal.NamedRecoveryRead.voteDutyRead S rho w d) rfl hframe hactive

/- The exact carrier token is retained from the G1 domain read to the later
vote-duty read. The SG row and named body are carried by the strict-read
bridges; the body remains compatible with the later finalized prefix because
both it and the protected block have a common upper block. -/











end WeakJoint
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
