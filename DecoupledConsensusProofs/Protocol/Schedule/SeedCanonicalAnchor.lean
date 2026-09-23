module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Protocol.Grades.SeedFinalizedCanonical
public import DecoupledConsensusProofs.Protocol.Schedule.SeedBoundaryConeLead
public import DecoupledConsensusProofs.Execution.SeedGradeExistence
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.VoteDutyHeadBand
public import DecoupledConsensusProofs.Protocol.Grades.SeedActionQ2
public import DecoupledConsensusProofs.Protocol.Grades.Q31_actionSGBlock_tiers

@[expose] public section

/-!
# Canonical anchor compatibility and band reach (CANON1: K3, K5)

`g1_exists_at_duty` / `healAnchor_cases` (K2) live in `SeedRawG1Run.lean` and
are imported here. This module builds on them: the anchor-carrier
compatibility argument (K3, `healAnchor_compatible_carrier_or_freshFresh`)
and the unconditional vote-duty-head band reach (K5,
`voteDutyHead_band_at_duty`), both from K1's canonicity
(`SeedFinalizedCanonicalRun.finalizedRoot_preceq_of_band`) rather than a
common root.
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








/-- Two run blocks with the same geometry are the same named block. -/
private theorem runBlock_unique_of_erase_eq
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {A D : NamedBlock V} (hA : RunBlock S rho A) (hD : RunBlock S rho D)
    (herase : A.erase = D.erase) : A = D :=
  adm.toNamedRootCollisionFree.root_injective A D hA hD A D
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self D))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])

/-- A relayed witness is in the store, stamped before the freeze, at every
read from the freeze on. -/
private theorem seedCanonicalRelayedWitness_mem_and_stamp
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} {W : Block V} {freeze read : Time} (hle : freeze ≤ read)
    (h : W = Block.genesis ∨ AdmittedBefore S rho w W freeze) :
    W ∈ (rho.storeBeforeTime S w read).T ∧
      stampedBefore (rho.storeBeforeTime S w read).timestamp_block freeze W
        = true := by
  rcases h with hgen | hadmit
  · simpa only [hgen] using
      (Protocol.genesis_mem_and_stamp_storeBeforeTime S
        adm.toNamedScheduleWellFormed w read freeze)
  · exact Protocol.admittedBefore_mem_and_stamp_at S
      adm.toNamedScheduleWellFormed hadmit hle


/-- A raw finalized-root bound at a later strict read gives the finalized
history needed to relay a descendant before an earlier cutoff.

design note (earlier statement, byte-exact):

    theorem finalizedBelowAtDeliveriesBefore_of_finalizedPreceqAtLaterRead
        (S: Setup V) {rho: Run V} (adm: Admissible S rho)
        {w: V} {P C: Block V} {cut read: Time}
        (hcut: cut ≤ read)
        (hFP: Block.Preceq (rho.storeBeforeTime S w read).F P)
        (hPC: Block.Preceq P C):
        Protocol.BlockFinalizedBelowAtDeliveriesBefore S rho w C cut

`BlockFinalizedBelowAtDeliveriesBefore` now quantifies the delivered *named*
block, so the relayed descendant `C` is a `NamedBlock V` and the prefix bound
reads `C.erase`. The meaning is unchanged. -/
theorem finalizedBelowAtDeliveriesBefore_of_finalizedPreceqAtLaterRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} {P : Block V} {C : NamedBlock V} {cut read : Time}
    (hcut : cut ≤ read)
    (hFP : Block.Preceq (rho.storeBeforeTime S w read).core.F P)
    (hPC : Block.Preceq P C.erase) :
    Protocol.BlockFinalizedBelowAtDeliveriesBefore S rho w C cut := by
  let N := (rho.events.filter (fun e => decide (e.time < read))).length
  have hread : rho.storeBeforeTime S w read =
      (rho.stateBefore S N w).st :=
    congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
        adm.toNamedScheduleWellFormed read) w)
  have hFread : Block.Preceq (rho.stateBefore S N w).st.core.F P := by
    rwa [← hread]
  intro i hi
  have hiN : i ≤ N := hi.trans (strict_filter_length_mono rho hcut)
  exact Block.preceq_trans
    (Protocol.stateBefore_F_mono S rho w hiN)
    (Block.preceq_trans hFread hPC)







/-- **K3, the collapsed-anchor arm (named).** The prepared vote-duty anchor is
compatible with every honest round-`c` action carrier, or it is the active
prefix of the round's own saved grade-one root.

The first arm is the whole of K3 whenever the anchor collapses to the vote
read's fork-choice root: under the gate-off frame that root is the reader's
finalized block, `actionSGBlockAt_frontierWitness` puts the carrier below a run
block at the band, and `finalizedRoot_preceq_of_band` puts the finalized block
below that same witness. No grade, delivery or open premise is used, so
this arm needs neither `GradeRoundReady` nor its lagged-GST premise.

The second arm is K3's residual on the selection: the anchor is the round's saved
grade-one root clipped to the active tree, and comparing THAT with another
honest node's frame-selected SG vote is the cross-node relative-grade step
recorded in the Open below. -/
theorem preparedAnchor_compatible_carrier_or_activePrefix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 1))
    (hhorNext : S.a (c + 1) ≤ rho.horizon)
    {w v : V} (hw : w ∈ rho.honest) (hv : v ∈ rho.honest) {d : Slot}
    (hd1 : S.hc.opening_slot c ≤ d) (hd2 : d ≤ seedRoundLastSlot S c)
    (hround : S.hc.round_of d = c) :
    Block.compatible
        (voterAnchorAt S rho w d) (actionSGBlockAt S rho v c) = true ∨
      ∃ root A : Block V,
        (DecoupledConsensusModel.Protocol.readFrame
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).cache
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing
          c).g1 = some (some root) ∧
        DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree
            (Internal.NamedRecoveryRead.voteDutyRead S rho w
              d).st.core.toHealing.toFG) root = some A ∧
        voterAnchorAt S rho w d = A := by
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have haPredC : S.a (c - 1) ≤ S.a c :=
    Assembly.a_mono S (Nat.sub_le c 1)
  have haCSucc : S.a c ≤ S.a (c + 1) :=
    Assembly.a_mono S (Nat.le_succ c)
  have hvoteLo : S.a (c - 1) ≤ Protocol.vote_time S.E d := by
    have hpredLt : c - 1 < c := Nat.sub_lt hcPos Nat.zero_lt_one
    have h1 := action_add_delta_le_openingProposal_of_round_lt S hpredLt
    exact ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1).trans
      ((Protocol.proposal_time_mono S.E hd1).trans
        (le_of_lt (Protocol.proposal_time_lt_vote_time S.E d)))
  have hdNext : d ≤ S.hc.opening_slot (c + 1) := by
    exact hd2.trans (by
      unfold seedRoundLastSlot
      exact Nat.sub_le _ _)
  have hvoteHi : Protocol.vote_time S.E d ≤ S.a (c + 1) := by
    have hconfMono : Protocol.confirmation_time S.E d ≤
        Protocol.confirmation_time S.E (S.hc.opening_slot (c + 1)) := by
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E d,
        ← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E
          (S.hc.opening_slot (c + 1))]
      exact Int.add_le_add_right
        (Protocol.vote_time_mono_slots S.E (Nat.succ_le_succ hdNext)) _
    exact (Protocol.vote_time_le_confirmation_time S.E d).trans
      (hconfMono.trans (by
        rw [Setup.a, Protocol.a_eq_confirmation_time]))
  have hgateRead :
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).h_j + 2 ≤ M :=
    (hframe (Protocol.vote_time S.E d) hvoteLo hvoteHi w hw).1
  have hfrontierRead :
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).h_max = M :=
    (hframe (Protocol.vote_time S.E d) hvoteLo hvoteHi w hw).2
  have hgateDuty : (voteDutyStore S rho w d).h_j + 2 ≤ M := by
    simpa only [voteDutyStore, voteStore, tickStore] using hgateRead
  have hfrontierDuty : (voteDutyStore S rho w d).h_max = M := by
    simpa only [voteDutyStore, voteStore, tickStore] using hfrontierRead
  have hrootEq : Protocol.get_fg_root
      (voteDutyStore S rho w d).toHealing.toFG =
        (voteDutyStore S rho w d).F :=
    fgRoot_eq_F_of_frame hgateDuty hfrontierDuty
  rcases voterAnchorAt_cases S rho w d with
    hfgAnchor | ⟨root, A, hframeG1, hactivePrefix, hanchorEq⟩
  · left
    have hfrontierV : (rho.storeBeforeTime S v (S.a c)).h_max = M :=
      (hframe (S.a c) haPredC haCSucc v hv).2
    obtain ⟨W, hWbody, hcarrierW, hWh⟩ :=
      actionSGBlockAt_frontierWitness S adm hfrontierV
    have hWpre : W ∈ (rho.storeBeforeTime S v (S.a c)).bodies := by
      simpa only [actionStoreAt, actionReadAt,
        NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, NamedRun.stateBeforeTime,
        Run.storeBeforeTime] using hWbody
    have hWrun : RunBlock S rho W := by
      obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
        S adm.toNamedScheduleWellFormed (S.a c)
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := n)
      rw [← hn]
      exact hWpre
    have hFW : Block.Preceq
        (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).core.F W.erase :=
      finalizedRoot_preceq_of_band S adm hfb hw hgateRead hWrun hWh
    have hrootW : Block.Preceq
        (Protocol.get_fg_root (voteDutyStore S rho w d).toHealing.toFG)
        W.erase := by
      rw [hrootEq]
      simpa only [voteDutyStore, voteStore, tickStore] using hFW
    rw [hfgAnchor]
    exact Block.compatible_of_preceq_common hrootW hcarrierW
  · right
    refine ⟨root, A, ?_, hactivePrefix, hanchorEq⟩
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.slotOf_vote_time, hround] using hframeG1




/-- The previous action is two relay delays before the round's opening
proposal. -/
private theorem k5_prevAction_add_two_delta_le_openingProposal
    (S : Setup V) {c : Round} (hc : 1 ≤ c) :
    S.a (c - 1) + 2 * S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot c) := by
  have hcR : S.hc.opening_slot c =
      S.hc.opening_slot (c - 1) + S.hc.R := by
    unfold Protocol.HealConfig.opening_slot
    calc
      c * S.hc.R = (c - 1 + 1) * S.hc.R := by
        rw [Nat.sub_add_cancel hc]
      _ = (c - 1) * S.hc.R + S.hc.R := Nat.succ_mul _ _
  have hΔ : (0 : Time) ≤ S.E.Δ := le_of_lt S.E.Δ_pos
  have hR : (2 : Time) ≤ (S.hc.R : Time) := by
    exact_mod_cast S.hc.R_ge_two
  have h4 : (0 : Time) ≤ 4 * S.E.Δ := Int.mul_nonneg (by decide) hΔ
  have hmul : 4 * S.E.Δ * 2 ≤ 4 * S.E.Δ * (S.hc.R : Time) :=
    Int.mul_le_mul_of_nonneg_left hR h4
  rw [Setup.a]
  unfold Protocol.HealConfig.a Protocol.proposal_time Env.t slotStart
  rw [hcR]
  push_cast
  rw [mul_add]
  have hre :
      4 * S.E.Δ * (S.hc.opening_slot (c - 1) : Time) +
          6 * S.E.Δ + 2 * S.E.Δ =
        4 * S.E.Δ * (S.hc.opening_slot (c - 1) : Time) +
          4 * S.E.Δ * 2 := by
    ring
  rw [hre]
  exact Int.add_le_add_left hmul _

/-- The previous slot's support cutoff is two relay delays before the current
slot's proposal. -/
private theorem k5_supportCutoff_pred_add_two_delta
    (E : Env V) {d : Slot} (hd : 0 < d) :
    Protocol.support_cutoff E (d - 1) + 2 * E.Δ =
      Protocol.proposal_time E d := by
  unfold Protocol.support_cutoff Protocol.proposal_time Env.t slotStart
  have hcast : ((d : Nat) : Time) = ((d - 1 : Nat) : Time) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hd).symm
  rw [hcast]
  ring



/-- The vote instant of a slot is before the next slot's proposal. -/
private theorem k5_voteTime_lt_nextProposal (E : Env V) (s : Slot) :
    Protocol.vote_time E s < Protocol.proposal_time E (s + 1) := by
  simp only [Protocol.vote_time, Protocol.proposal_time, Env.t, slotStart]
  push_cast
  nlinarith [E.Δ_pos]


/-- **K5, delivery half at the PREPARED anchor (named).** The same relay and
canonicity content as `voteDutyAnchor_bandDescendant_processed`, stated at the
anchor the prepared vote-duty walk actually starts from.

`voterAnchorAt` is the frame contract's anchor at the vote-duty read, not the
recomputed `healAnchor` on the erased vote-duty store; the two are the 
head-equality class and are not identified here. The case split is
`PreparedReadBridgeRun.voterAnchorAt_cases` instead of `healAnchor_cases`, and
the active-prefix arm reaches an honest previous-round action carrier through
the RELATIVE grade route (`fixedRoot_activeVoterAnchor_g1_data`,
`relativeGrade_has_roundCarrier`) rather than through the absolute
`G1_preceq_honestPreviousActionCarrier`. The window majority that route needs
comes from the gate-off frame itself
(`relativeCarrierWindowAt_of_gateOff`), so no carrier-cover premise is
added. -/
theorem voteDutyPreparedAnchor_bandDescendant_processed
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 1))
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhorNext : S.a (c + 1) ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) {d : Slot}
    (hd1 : S.hc.opening_slot c ≤ d) (hd2 : d ≤ seedRoundLastSlot S c)
    (hround : S.hc.round_of d = c) :
    ∃ C : NamedBlock V,
      Block.Preceq (voterAnchorAt S rho w d) C.erase ∧
      RunBlock S rho C ∧
      C.erase ∈ Protocol.voter_processed_block_tree S.E
        (voteDutyStore S rho w d).toHealing.toFG.toSG.toGoldfishStore
        (voteDutyStore S rho w d).toHealing.s ∧
      (voteDutyStore S rho w d).h_max ≤
        (Protocol.derive_named S.E S.cfg C).h + 1 := by
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have hpredSucc : c - 1 + 1 = c := Nat.sub_add_cancel hc
  have haPredC : S.a (c - 1) ≤ S.a c :=
    Assembly.a_mono S (Nat.sub_le c 1)
  have haCSucc : S.a c ≤ S.a (c + 1) :=
    Assembly.a_mono S (Nat.le_succ c)
  have hhorC : S.a c ≤ rho.horizon := haCSucc.trans hhorNext
  have hoPos : 0 < S.hc.opening_slot c := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hcPos
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hdPos : 0 < d := lt_of_lt_of_le hoPos hd1
  have hdSucc : d - 1 + 1 = d := Nat.sub_add_cancel hdPos
  have hΓ0Action : S.hc.Γ_0 S.E.Δ c ≤ S.a c := by
    rw [Protocol.Γ_0_eq_proposal_time, Setup.a,
      Protocol.a_eq_confirmation_time]
    exact Protocol.proposal_time_le_confirmation_time S.E _
  have hvoteLo : S.a (c - 1) ≤ Protocol.vote_time S.E d := by
    have hpredLt : c - 1 < c := Nat.sub_lt hcPos Nat.zero_lt_one
    have h1 := action_add_delta_le_openingProposal_of_round_lt S hpredLt
    exact ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1).trans
      ((Protocol.proposal_time_mono S.E hd1).trans
        (le_of_lt (Protocol.proposal_time_lt_vote_time S.E d)))
  have hdNext : d ≤ S.hc.opening_slot (c + 1) := by
    exact hd2.trans (by
      unfold seedRoundLastSlot
      exact Nat.sub_le _ _)
  have hvoteHi : Protocol.vote_time S.E d ≤ S.a (c + 1) := by
    have hconfMono : Protocol.confirmation_time S.E d ≤
        Protocol.confirmation_time S.E (S.hc.opening_slot (c + 1)) := by
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E d,
        ← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E
          (S.hc.opening_slot (c + 1))]
      exact Int.add_le_add_right
        (Protocol.vote_time_mono_slots S.E (Nat.succ_le_succ hdNext)) _
    exact (Protocol.vote_time_le_confirmation_time S.E d).trans
      (hconfMono.trans (by
        rw [Setup.a, Protocol.a_eq_confirmation_time]))
  have hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon :=
    hvoteHi.trans hhorNext
  have hfreezeLe : Protocol.view_freeze S.E (d - 1) ≤
      Protocol.vote_time S.E d := by
    have h := Protocol.view_freeze_lt_vote_time_succ S.E (d - 1)
    rw [hdSucc] at h
    exact le_of_lt h
  have hprevLeCut : S.a (c - 1) ≤
      Protocol.support_cutoff S.E (d - 1) := by
    have h1 := k5_prevAction_add_two_delta_le_openingProposal S hc
    have h2 := k5_supportCutoff_pred_add_two_delta S.E hdPos
    have h3 : Protocol.proposal_time S.E (S.hc.opening_slot c) ≤
        Protocol.proposal_time S.E d :=
      Protocol.proposal_time_mono S.E hd1
    have h4 : S.a (c - 1) + 2 * S.E.Δ ≤
        Protocol.support_cutoff S.E (d - 1) + 2 * S.E.Δ := by
      rw [h2]
      exact h1.trans h3
    exact le_of_add_le_add_right h4
  have hcutLeFreeze : Protocol.support_cutoff S.E (d - 1) ≤
      Protocol.view_freeze S.E (d - 1) := by
    rw [← Protocol.support_cutoff_add_delta_eq_view_freeze]
    exact le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  have hprevLeFreeze : S.a (c - 1) ≤
      Protocol.view_freeze S.E (d - 1) :=
    hprevLeCut.trans hcutLeFreeze
  have hcutIn : S.E.t_GST ≤ Protocol.support_cutoff S.E (d - 1) :=
    hpost.trans hprevLeCut
  have hfreezeHor : Protocol.view_freeze S.E (d - 1) ≤ rho.horizon :=
    hfreezeLe.trans hvoteHor
  have hgateRead :
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).h_j + 2 ≤ M :=
    (hframe (Protocol.vote_time S.E d) hvoteLo hvoteHi w hw).1
  have hfrontierRead :
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).h_max = M :=
    (hframe (Protocol.vote_time S.E d) hvoteLo hvoteHi w hw).2
  have hgateDuty : (voteDutyStore S rho w d).h_j + 2 ≤ M := by
    simpa only [voteDutyStore, voteStore, tickStore] using hgateRead
  have hfrontierDuty : (voteDutyStore S rho w d).h_max = M := by
    simpa only [voteDutyStore, voteStore, tickStore] using hfrontierRead
  have hrootEq : Protocol.get_fg_root
      (voteDutyStore S rho w d).toHealing.toFG =
        (voteDutyStore S rho w d).F :=
    fgRoot_eq_F_of_frame hgateDuty hfrontierDuty
  have hslot : (voteDutyStore S rho w d).toHealing.s = d := by
    simpa only [Proofs.Optimistic.toHealing_slot] using
      voteDutyStore_slot S rho w d
  rcases voterAnchorAt_cases S rho w d with
    hfgAnchor | ⟨root, A, hframeG1, hactivePrefix, hanchorEq⟩
  · -- The prepared anchor collapses to the read's own FG root, which the
    -- gate-off frame identifies with the finalized block.
    obtain ⟨X, hXbody, hXmax⟩ :=
      Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime S rho (S.a (c - 1)) w
    have hprevFrontier :
        (rho.storeBeforeTime S w (S.a (c - 1))).h_max = M :=
      (hframe (S.a (c - 1)) le_rfl
        (haPredC.trans haCSucc) w hw).2
    have hXpre : X ∈ (rho.storeBeforeTime S w (S.a (c - 1))).bodies := by
      simpa only [Run.storeBeforeTime] using hXbody
    have hXheight : (Protocol.derive_named S.E S.cfg X).h = M := by
      rw [show (Protocol.derive_named S.E S.cfg X).h =
        (rho.storeBeforeTime S w (S.a (c - 1))).core.h_max from hXmax]
      exact hprevFrontier
    have hXband : M - 1 ≤ (Protocol.derive_named S.E S.cfg X).h := by
      rw [hXheight]
      exact Nat.sub_le M 1
    have hXcore : X.erase ∈ (rho.storeBeforeTime S w (S.a (c - 1))).core.T := by
      have htree : (rho.storeBeforeTime S w (S.a (c - 1))).core.T =
          (rho.storeBeforeTime S w (S.a (c - 1))).bodies.image
            NamedBlock.erase := by
        simpa only [Run.storeBeforeTime] using
          (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
            (S.a (c - 1)) w).1.1.1.1
      rw [htree]
      exact Finset.mem_image_of_mem NamedBlock.erase hXpre
    have hXrun : RunBlock S rho X := by
      obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
        S adm.toNamedScheduleWellFormed (S.a (c - 1))
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i := n)
      rw [← hn]
      exact hXpre
    have hFX : Block.Preceq
        (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).core.F X.erase :=
      finalizedRoot_preceq_of_band
        S adm hfb hw hgateRead hXrun hXband
    have hXrelay : X.erase = Block.genesis ∨
        AdmittedBefore S rho w X.erase
          (Protocol.view_freeze S.E (d - 1)) := by
      rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime
          S adm.toNamedScheduleWellFormed w (S.a (c - 1)) hXcore with
        hgen | ⟨D, i, t, hDerase, hacc, ht⟩
      · exact Or.inl hgen
      · exact Or.inr ⟨D, hDerase, i, t, hacc,
          lt_of_lt_of_le ht hprevLeFreeze⟩
    have hvisible := seedCanonicalRelayedWitness_mem_and_stamp
      S adm hfreezeLe hXrelay
    have hXmemDuty : X.erase ∈ (voteDutyStore S rho w d).T := by
      simpa only [voteDutyStore, voteStore, tickStore] using hvisible.1
    have hXstampDuty : stampedBefore
        (voteDutyStore S rho w d).timestamp_block
          (Protocol.view_freeze S.E (d - 1)) X.erase = true := by
      simpa only [voteDutyStore, voteStore, tickStore] using hvisible.2
    have hXprocessed : X.erase ∈ Protocol.voter_processed_block_tree S.E
        (voteDutyStore S rho w d).toHealing.toFG.toSG.toGoldfishStore
        (voteDutyStore S rho w d).toHealing.s := by
      simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      rw [hslot]
      exact ⟨by simpa only [Protocol.Store.toHealing] using hXmemDuty,
        Or.inl (by
          simpa only [Protocol.Store.toHealing] using hXstampDuty)⟩
    refine ⟨X, ?_, hXrun, hXprocessed, ?_⟩
    · have hgoal : Block.Preceq
          (Protocol.get_fg_root
            (voteDutyStore S rho w d).toHealing.toFG) X.erase := by
        rw [hrootEq]
        simpa only [voteDutyStore, voteStore, tickStore] using hFX
      rw [hfgAnchor]
      exact hgoal
    · rw [hfrontierDuty, hXheight]
      exact Nat.le_add_right M 1
  · -- The prepared anchor is the active prefix of the round's saved grade-one
    -- root, so it carries that round's relative grade and has an honest
    -- previous-round action carrier above it.
    have hnextOpening : Protocol.vote_time S.E d ≤
        DecoupledConsensusModel.Protocol.opening S.E S.hc (c + 1) := by
      have hlt : d < S.hc.opening_slot (c + 1) := by
        have hpos : 0 < S.hc.opening_slot (c + 1) := by
          unfold Protocol.HealConfig.opening_slot
          exact Nat.mul_pos (Nat.succ_pos c)
            (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
        have hb : S.hc.opening_slot (c + 1) - 1 < S.hc.opening_slot (c + 1) :=
          Nat.sub_lt hpos Nat.zero_lt_one
        refine lt_of_le_of_lt ?_ hb
        unfold seedRoundLastSlot at hd2
        exact hd2
      have hstep : Protocol.proposal_time S.E (d + 1) ≤
          Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)) :=
        Protocol.proposal_time_mono S.E (Nat.succ_le_of_lt hlt)
      have hopen : DecoupledConsensusModel.Protocol.opening S.E S.hc (c + 1) =
          Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)) := rfl
      rw [hopen]
      exact (le_of_lt (k5_voteTime_lt_nextProposal S.E d)).trans hstep
    have hframeRead : (DecoupledConsensusModel.Protocol.readFrame
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).cache
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          d).st.core.toHealing c).g1 = some (some root) := by
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.slotOf_vote_time, hround] using hframeG1
    obtain ⟨-, hAGrade⟩ := fixedRoot_activeVoterAnchor_g1_data
      S adm hcPos hd1 hround hnextOpening hvoteHor hw hframeRead hactivePrefix
    have hdomainG1Hor : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 ≤ rho.horizon :=
      (FrameForward.domain_le_a S c .g1).trans hhorC
    have hdomainG2Hor : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g2 ≤ rho.horizon :=
      (FrameForward.domain_le_a S c .g2).trans hhorC
    have hwindow : RelativeCarrierWindowAt S rho (c - 1) .g1 :=
      relativeCarrierWindowAt_of_gateOff S adm hfb hcPos hpost
        (fun u hu => (hframe (S.a (c - 1)) le_rfl
          (haPredC.trans haCSucc) u hu).2)
        (fun u hu => (hframe (S.a c) haPredC haCSucc u hu).2)
        (fun u hu => (hframe (S.a c) haPredC haCSucc u hu).1)
        hdomainG1Hor
    have hmajorityC : Internal.NamedOutageEntry.GradeFormingMajority S rho c :=
      gradeFormingMajority_of_admissible_belowOneThird S adm hfb hcPos
        hdomainG2Hor
    have hgradeC : DecoupledConsensusModel.Protocol.gradeBool S.E
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.F
        S.hc.η_SG c
        (DecoupledConsensusModel.Protocol.early S.E S.hc c .g1)
        (DecoupledConsensusModel.Protocol.late S.E S.hc c .g1) A = true := by
      simpa only [PhaseGrades.readAt, PhaseGrades.storeGrade,
        PhaseGrades.phaseGrade] using hAGrade
    obtain ⟨u, hu, hAcarrier⟩ :=
      relativeGrade_has_roundCarrier (r := c - 1) (p := .g1)
        S adm.toNamedAdmissibleCore hwindow
        (by simpa only [hpredSucc] using hmajorityC) hw
        (by simpa only [hpredSucc] using hgradeC)
    have huHon : u ∈ rho.honest :=
      ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u (c - 1)).mp hu).1
    have hprevFrontier :
        (rho.storeBeforeTime S u (S.a (c - 1))).h_max = M :=
      (hframe (S.a (c - 1)) le_rfl
        (haPredC.trans haCSucc) u huHon).2
    obtain ⟨W, hWT, hcarrierW, hWh⟩ :=
      actionSGBlockAt_frontierWitness S adm hprevFrontier
    have hWpre : W ∈ (rho.storeBeforeTime S u (S.a (c - 1))).bodies := by
      simpa only [actionStoreAt, actionReadAt,
        NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, NamedRun.stateBeforeTime,
        Run.storeBeforeTime] using hWT
    have hWcore : W.erase ∈ (rho.storeBeforeTime S u (S.a (c - 1))).core.T := by
      have htree : (rho.storeBeforeTime S u (S.a (c - 1))).core.T =
          (rho.storeBeforeTime S u (S.a (c - 1))).bodies.image
            NamedBlock.erase := by
        simpa only [Run.storeBeforeTime] using
          (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
            (S.a (c - 1)) u).1.1.1.1
      rw [htree]
      exact Finset.mem_image_of_mem NamedBlock.erase hWpre
    have hWrun : RunBlock S rho W := by
      obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
        S adm.toNamedScheduleWellFormed (S.a (c - 1))
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S huHon (i := n)
      rw [← hn]
      exact hWpre
    have hAW : Block.Preceq A W.erase :=
      Block.preceq_trans hAcarrier hcarrierW
    have hFW : Block.Preceq
        (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).core.F W.erase :=
      finalizedRoot_preceq_of_band
        S adm hfb hw hgateRead hWrun hWh
    have hFhist : Protocol.BlockFinalizedBelowAtDeliveriesBefore
        S rho w W (Protocol.view_freeze S.E (d - 1)) :=
      finalizedBelowAtDeliveriesBefore_of_finalizedPreceqAtLaterRead
        S adm hfreezeLe hFW (Block.preceq_self W.erase)
    have hrelay : W.erase = Block.genesis ∨
        AdmittedBefore S rho w W.erase
          (Protocol.view_freeze S.E (d - 1)) := by
      rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime
          S adm.toNamedScheduleWellFormed u (S.a (c - 1)) hWcore with
        hgen | ⟨D, i, t, hDerase, hacc, ht⟩
      · exact Or.inl hgen
      · right
        have htIn : t < Protocol.support_cutoff S.E (d - 1) :=
          lt_of_lt_of_le ht hprevLeCut
        have hDbody : D ∈ (rho.stateBefore S (i + 1) u).st.bodies := by
          simpa only [NamedReceipt.processed, decide_eq_true_eq] using hacc.2.2
        have hDrun : RunBlock S rho D :=
          Proofs.Bridges.runBlock_of_stateBefore_mem S huHon hDbody
        have hDW : D = W :=
          runBlock_unique_of_erase_eq adm hDrun hWrun hDerase
        subst hDW
        have hDpos : 0 < D.slot := by
          rw [← Proofs.NamedWire.erase_slot D]
          exact Nat.zero_lt_of_lt
            (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
        exact Protocol.block_admittedBefore_of_accepted_after_cutoff
          S adm huHon hw hDpos hacc htIn hcutIn
            (Protocol.support_cutoff_add_delta_eq_view_freeze
              S.E (d - 1))
            hfreezeHor hFhist
    have hvisible := seedCanonicalRelayedWitness_mem_and_stamp
      S adm hfreezeLe hrelay
    have hWmemDuty : W.erase ∈ (voteDutyStore S rho w d).T := by
      simpa only [voteDutyStore, voteStore, tickStore] using hvisible.1
    have hWstampDuty : stampedBefore
        (voteDutyStore S rho w d).timestamp_block
          (Protocol.view_freeze S.E (d - 1)) W.erase = true := by
      simpa only [voteDutyStore, voteStore, tickStore] using hvisible.2
    have hWprocessed : W.erase ∈ Protocol.voter_processed_block_tree S.E
        (voteDutyStore S rho w d).toHealing.toFG.toSG.toGoldfishStore
        (voteDutyStore S rho w d).toHealing.s := by
      simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      rw [hslot]
      exact ⟨by simpa only [Protocol.Store.toHealing] using hWmemDuty,
        Or.inl (by
          simpa only [Protocol.Store.toHealing] using hWstampDuty)⟩
    refine ⟨W, ?_, hWrun, hWprocessed, ?_⟩
    · rw [hanchorEq]
      exact hAW
    · rw [hfrontierDuty]
      exact Nat.sub_le_iff_le_add.mp hWh

/-- **K5 (named).** Every honest round-`c` vote-duty head reaches the local
band, unconditionally: the head is named by a run block whose named derivation
already clears `M - 1`. -/
theorem voteDutyHead_band_at_duty
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 1))
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhorNext : S.a (c + 1) ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) {d : Slot}
    (hd1 : S.hc.opening_slot c ≤ d) (hd2 : d ≤ seedRoundLastSlot S c)
    (hround : S.hc.round_of d = c) :
    ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho w d ∧ RunBlock S rho Hn ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h := by
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have hoPos : 0 < S.hc.opening_slot c := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hcPos
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hdPos : 0 < d := lt_of_lt_of_le hoPos hd1
  have hdSucc : d - 1 + 1 = d := Nat.sub_add_cancel hdPos
  have hvoteLo : S.a (c - 1) ≤ Protocol.vote_time S.E d := by
    have hpredLt : c - 1 < c := Nat.sub_lt hcPos Nat.zero_lt_one
    have h1 := action_add_delta_le_openingProposal_of_round_lt S hpredLt
    exact ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1).trans
      ((Protocol.proposal_time_mono S.E hd1).trans
        (le_of_lt (Protocol.proposal_time_lt_vote_time S.E d)))
  have hdNext : d ≤ S.hc.opening_slot (c + 1) := by
    exact hd2.trans (by
      unfold seedRoundLastSlot
      exact Nat.sub_le _ _)
  have hvoteHi : Protocol.vote_time S.E d ≤ S.a (c + 1) := by
    have hconfMono : Protocol.confirmation_time S.E d ≤
        Protocol.confirmation_time S.E (S.hc.opening_slot (c + 1)) := by
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E d,
        ← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E
          (S.hc.opening_slot (c + 1))]
      exact Int.add_le_add_right
        (Protocol.vote_time_mono_slots S.E (Nat.succ_le_succ hdNext)) _
    exact (Protocol.vote_time_le_confirmation_time S.E d).trans
      (hconfMono.trans (by
        rw [Setup.a, Protocol.a_eq_confirmation_time]))
  have hfrontierRead :
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).h_max = M :=
    (hframe (Protocol.vote_time S.E d) hvoteLo hvoteHi w hw).2
  have hfrontierNamed :
      (Internal.NamedRecoveryRead.voteDutyStore S rho w d).h_max = M := by
    simpa only [Internal.NamedRecoveryRead.voteDutyStore,
      Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime] using hfrontierRead
  have hdesc := voteDutyPreparedAnchor_bandDescendant_processed
    S adm hfb hc hframe hpost hhorNext hw hd1 hd2 hround
  have hhead := voteDutyHead_height_ge_frontier_sub_one_of_anchorDescendant
    S adm hw (d - 1) (by rw [hdSucc]; exact hdesc)
  simpa only [hdSucc, hfrontierNamed] using hhead





/-! ## The two K3 obligations, reduced to their round-local cores -/
















/-
/-- **K5.** Every honest round-`c` vote-duty head reaches the local band,
unconditionally. -/
theorem voteDutyHead_band_at_duty
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {c: Round} (hc: 1 ≤ c)
    (hframe: GateOffFrameAt S rho M (c - 1) (c + 1))
    (hpost: S.E.t_GST ≤ S.a (c - 1))
    (hhorNext: S.a (c + 1) ≤ rho.horizon)
    {w: V} (hw: w ∈ rho.honest) {d: Slot}
    (hd1: S.hc.opening_slot c ≤ d) (hd2: d ≤ seedRoundLastSlot S c)
    (hround: S.hc.round_of d = c):
    M - 1 ≤ (derived_state S.E S.cfg (voteDutyHead S rho w d)).h:= by
  have hcPos: 0 < c:= Nat.succ_le_iff.mp hc
  have hpredSucc: c - 1 + 1 = c:= Nat.sub_add_cancel hc
  have haPredC: S.a (c - 1) ≤ S.a c:=
    Assembly.a_mono S (Nat.sub_le c 1)
  have haCSucc: S.a c ≤ S.a (c + 1):=
    Assembly.a_mono S (Nat.le_succ c)
  have hhorC: S.a c ≤ rho.horizon:= haCSucc.trans hhorNext
  have hoPos: 0 < S.hc.opening_slot c:= by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hcPos
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hdPos: 0 < d:= lt_of_lt_of_le hoPos hd1
  have hdSucc: d - 1 + 1 = d:= Nat.sub_add_cancel hdPos
  have hΓ0Action: S.hc.Γ_0 S.E.Δ c ≤ S.a c:= by
    rw [Protocol.Γ_0_eq_proposal_time, Setup.a,
      Protocol.a_eq_confirmation_time]
    exact Protocol.proposal_time_le_confirmation_time S.E _
  have hΓ0Vote: S.hc.Γ_0 S.E.Δ c ≤ Protocol.vote_time S.E d:= by
    rw [Protocol.Γ_0_eq_proposal_time]
    exact (Protocol.proposal_time_mono S.E hd1).trans
      (le_of_lt (Protocol.proposal_time_lt_vote_time S.E d))
  have hvoteLo: S.a (c - 1) ≤ Protocol.vote_time S.E d:= by
    have hpredLt: c - 1 < c:= Nat.sub_lt hcPos Nat.zero_lt_one
    have h1:= action_add_delta_le_openingProposal_of_round_lt S hpredLt
    exact ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1).trans
      ((Protocol.proposal_time_mono S.E hd1).trans
        (le_of_lt (Protocol.proposal_time_lt_vote_time S.E d)))
  have hvoteHi: Protocol.vote_time S.E d ≤ S.a (c + 1):= by
    have hdNext: d ≤ S.hc.opening_slot (c + 1):= by
      exact hd2.trans (by
        unfold seedRoundLastSlot
        exact Nat.sub_le _ _)
    have hconfMono: Protocol.confirmation_time S.E d ≤
        Protocol.confirmation_time S.E (S.hc.opening_slot (c + 1)):= by
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E d,
        ← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E
          (S.hc.opening_slot (c + 1))]
      exact Int.add_le_add_right
        (Protocol.vote_time_mono_slots S.E (Nat.succ_le_succ hdNext)) _
    exact (Protocol.vote_time_le_confirmation_time S.E d).trans
      (hconfMono.trans (by
        rw [Setup.a, Protocol.a_eq_confirmation_time]))
  have hvoteHor: Protocol.vote_time S.E d ≤ rho.horizon:=
    hvoteHi.trans hhorNext
  have hfreezeLe: Protocol.view_freeze S.E (d - 1) ≤
      Protocol.vote_time S.E d:= by
    have h:= Protocol.view_freeze_lt_vote_time_succ S.E (d - 1)
    rw [hdSucc] at h
    exact le_of_lt h
  have hprevLeCut: S.a (c - 1) ≤
      Protocol.support_cutoff S.E (d - 1):= by
    have h1:= k5_prevAction_add_two_delta_le_openingProposal S hc
    have h2:= k5_supportCutoff_pred_add_two_delta S.E hdPos
    have h3: Protocol.proposal_time S.E (S.hc.opening_slot c) ≤
        Protocol.proposal_time S.E d:=
      Protocol.proposal_time_mono S.E hd1
    have h4: S.a (c - 1) + 2 * S.E.Δ ≤
        Protocol.support_cutoff S.E (d - 1) + 2 * S.E.Δ:= by
      rw [h2]
      exact h1.trans h3
    exact le_of_add_le_add_right h4
  have hcutLeFreeze: Protocol.support_cutoff S.E (d - 1) ≤
      Protocol.view_freeze S.E (d - 1):= by
    rw [← Protocol.support_cutoff_add_delta_eq_view_freeze]
    exact le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  have hprevLeFreeze: S.a (c - 1) ≤
      Protocol.view_freeze S.E (d - 1):=
    hprevLeCut.trans hcutLeFreeze
  have hcutIn: S.E.t_GST ≤ Protocol.support_cutoff S.E (d - 1):=
    hpost.trans hprevLeCut
  have hfreezeHor: Protocol.view_freeze S.E (d - 1) ≤ rho.horizon:=
    hfreezeLe.trans hvoteHor
  have hgateRead:
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).h_j + 2 ≤ M:=
    (hframe (Protocol.vote_time S.E d) hvoteLo hvoteHi w hw).1
  have hfrontierRead:
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).h_max = M:=
    (hframe (Protocol.vote_time S.E d) hvoteLo hvoteHi w hw).2
  have hgateDuty: (voteDutyStore S rho w d).h_j + 2 ≤ M:= by
    simpa only [voteDutyStore, voteStore, tickStore] using hgateRead
  have hfrontierDuty: (voteDutyStore S rho w d).h_max = M:= by
    simpa only [voteDutyStore, voteStore, tickStore] using hfrontierRead
  have hrootEq: Protocol.get_fg_root
      (voteDutyStore S rho w d).toHealing.toFG =
        (voteDutyStore S rho w d).F:=
    fgRoot_eq_F_of_frame hgateDuty hfrontierDuty
  have hslot: (voteDutyStore S rho w d).toHealing.s = d:= by
    simpa only [Proofs.Optimistic.toHealing_slot] using
      voteDutyStore_slot S rho w d
  rcases healAnchor_cases S adm hfb hc hframe hpost hhorNext
      hw hd1 hd2 hround with ⟨A, hA, hheal⟩ | ⟨_, hheal⟩
  · have hAG1Duty: Protocol.G1 S.E
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E d)).toHealing.gradeView S.hc c A = true:= by
      have hmem:= Proofs.Engine.deepest?_mem hA
      simpa only [voteDutyStore, voteStore, tickStore,
        Protocol.Store.toHealing] using (Finset.mem_filter.mp hmem).2
    have hAG1Read: Protocol.G1 S.E
        (rho.storeBeforeTime S w (S.a c)).toHealing.gradeView
          S.hc c A = true:= by
      rcases le_total (Protocol.vote_time S.E d) (S.a c) with hle | hle
      · exact G1_persists_after_cutoff
          S adm hw hΓ0Vote hle hAG1Duty
      · exact G1_reflects_after_cutoff
          S adm hw hΓ0Action hle hAG1Duty
    have hAG1: Protocol.G1 S.E (gradeViewAt S rho w c)
        S.hc c A = true:= by
      simpa only [gradeViewAt, healStoreAt] using hAG1Read
    have hcutHor: S.hc.Γ_neg1 S.E.Δ (c - 1 + 1) ≤ rho.horizon:= by
      rw [hpredSucc]
      exact (le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0
        S.hc S.E.Δ_pos c)).trans (hΓ0Action.trans hhorC)
    obtain ⟨u, hu, hAcarrier⟩:=
      G1_preceq_honestPreviousActionCarrier
        S adm hfb hw (c - 1) hpost hcutHor
          (by simpa only [hpredSucc] using hAG1)
    have hprevFrontier:
        (rho.storeBeforeTime S u (S.a (c - 1))).h_max = M:=
      (hframe (S.a (c - 1)) le_rfl
        (haPredC.trans haCSucc) u hu).2
    obtain ⟨W, hWT, hcarrierW, hWh⟩:=
      actionSGBlockAt_frontierWitness S adm hprevFrontier
    have hfields:= Proofs.Optimistic.attestStore_fields S
      (rho.stateBeforeTime S (S.a (c - 1)) u).st (S.a (c - 1))
    have hWpre: W ∈
        (rho.storeBeforeTime S u (S.a (c - 1))).T:= by
      simpa only [actionStoreAt, hfields.2.1, Run.storeBeforeTime] using hWT
    have hWrun: RunBlock S rho W:= by
      obtain ⟨n, hn, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore
        S adm.toScheduleWellFormed (S.a (c - 1))
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S hu (i:= n)
      rw [← hn]
      exact hWpre
    have hAW: Block.Preceq A W:=
      Block.preceq_trans hAcarrier hcarrierW
    have hFW: Block.Preceq
        (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).F W:=
      finalizedRoot_preceq_of_band
        S adm hfb hw hgateRead hWrun hWh
    have hFhist: Protocol.BlockFinalizedBelowAtDeliveriesBefore
        S rho w W (Protocol.view_freeze S.E (d - 1)):=
      finalizedBelowAtDeliveriesBefore_of_finalizedPreceqAtLaterRead
        S adm hfreezeLe hFW (Block.preceq_self W)
    have hrelay: W = Block.genesis ∨
        AdmittedBefore S rho w W (Protocol.view_freeze S.E (d - 1)):= by
      rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime
          S adm.toScheduleWellFormed u (S.a (c - 1)) hWpre with
        hgen | ⟨i, t, hacc, ht⟩
      · exact Or.inl hgen
      · right
        have htIn: t < Protocol.support_cutoff S.E (d - 1):=
          lt_of_lt_of_le ht hprevLeCut
        have hWpos: 0 < W.slot:=
          Nat.zero_lt_of_lt
            (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
        exact Protocol.block_admittedBefore_of_accepted_after_cutoff
          S adm hu hw hWpos hacc htIn hcutIn
            (Protocol.support_cutoff_add_delta_eq_view_freeze
              S.E (d - 1))
            hfreezeHor hFhist
    have hvisible:= relayedWitness_mem_and_stamp
      S adm hfreezeLe hrelay
    have hWmemDuty: W ∈ (voteDutyStore S rho w d).T:= by
      simpa only [voteDutyStore, voteStore, tickStore] using hvisible.1
    have hWstampDuty: stampedBefore
        (voteDutyStore S rho w d).timestamp_block
          (Protocol.view_freeze S.E (d - 1)) W = true:= by
      simpa only [voteDutyStore, voteStore, tickStore] using hvisible.2
    have hWprocessed: W ∈ Protocol.voter_processed_block_tree S.E
        (voteDutyStore S rho w d).toHealing.toFG.toSG.toGoldfishStore
        (voteDutyStore S rho w d).toHealing.s:= by
      simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      rw [hslot]
      exact ⟨by simpa only [Protocol.Store.toHealing] using hWmemDuty,
        Or.inl (by
          simpa only [Protocol.Store.toHealing] using hWstampDuty)⟩
    have hdesc: ∃ C: Block V,
        Block.Preceq
          (healAnchor S.E S.hc (voteDutyStore S rho w d).toHealing) C ∧
        C ∈ Protocol.voter_processed_block_tree S.E
          (voteDutyStore S rho w d).toHealing.toFG.toSG.toGoldfishStore
          (voteDutyStore S rho w d).toHealing.s ∧
        (voteDutyStore S rho w d).h_max ≤
          (derived_state S.E S.cfg C).h + 1:= by
      refine ⟨W, ?_, hWprocessed, ?_⟩
      · rw [hheal]
        exact hAW
      · rw [hfrontierDuty]
        exact Nat.sub_le_iff_le_add.mp hWh
    have hhead:=
      voteDutyHead_height_ge_frontier_sub_one_of_anchorDescendant
        S adm hw (d - 1) (by simpa only [hdSucc] using hdesc)
    simpa only [hdSucc, hfrontierDuty] using hhead
  · let pre:= rho.storeBeforeTime S w (S.a (c - 1))
    have hdep: DepReachableStore S.E S.hc S.cfg (S.node w) pre:= by
      simpa only [pre, Run.storeBeforeTime] using
        (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
          adm.toDeliveryWellFormed (S.a (c - 1)) w)
    obtain ⟨X, hXT, hmaxX⟩:=
      hMaxInTree_depReachable S.E S.hc S.cfg (S.node w) hdep
    have hagree: DerivedStateAgrees S.E S.cfg pre:=
      derivedStateAgrees_depReachable
        S.E S.hc S.cfg (S.node w) pre hdep
    have hprevFrontier: pre.h_max = M:= by
      simpa only [pre] using
        (hframe (S.a (c - 1)) le_rfl
          (haPredC.trans haCSucc) w hw).2
    have hXh: M ≤ (derived_state S.E S.cfg X).h:= by
      calc
        M = pre.h_max:= hprevFrontier.symm
        _ ≤ (pre.σ X).h:= hmaxX
        _ = (derived_state S.E S.cfg X).h:=
          congrArg (fun cs => cs.h) (hagree X hXT)
    have hXband: M - 1 ≤ (derived_state S.E S.cfg X).h:=
      (Nat.sub_le M 1).trans hXh
    have hXrun: RunBlock S rho X:= by
      obtain ⟨n, hn, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore
        S adm.toScheduleWellFormed (S.a (c - 1))
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i:= n)
      rw [← hn]
      simpa only [pre] using hXT
    have hFX: Block.Preceq
        (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).F X:=
      finalizedRoot_preceq_of_band
        S adm hfb hw hgateRead hXrun hXband
    have hXrelay: X = Block.genesis ∨
        AdmittedBefore S rho w X (Protocol.view_freeze S.E (d - 1)):= by
      rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime
          S adm.toScheduleWellFormed w (S.a (c - 1))
            (by simpa only [pre] using hXT) with
        hgen | ⟨i, t, hacc, ht⟩
      · exact Or.inl hgen
      · exact Or.inr ⟨i, t, hacc, lt_of_lt_of_le ht hprevLeFreeze⟩
    have hvisible:= relayedWitness_mem_and_stamp
      S adm hfreezeLe hXrelay
    have hXmemDuty: X ∈ (voteDutyStore S rho w d).T:= by
      simpa only [voteDutyStore, voteStore, tickStore] using hvisible.1
    have hXstampDuty: stampedBefore
        (voteDutyStore S rho w d).timestamp_block
          (Protocol.view_freeze S.E (d - 1)) X = true:= by
      simpa only [voteDutyStore, voteStore, tickStore] using hvisible.2
    have hXprocessed: X ∈ Protocol.voter_processed_block_tree S.E
        (voteDutyStore S rho w d).toHealing.toFG.toSG.toGoldfishStore
        (voteDutyStore S rho w d).toHealing.s:= by
      simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      rw [hslot]
      exact ⟨by simpa only [Protocol.Store.toHealing] using hXmemDuty,
        Or.inl (by
          simpa only [Protocol.Store.toHealing] using hXstampDuty)⟩
    have hdesc: ∃ C: Block V,
        Block.Preceq
          (healAnchor S.E S.hc (voteDutyStore S rho w d).toHealing) C ∧
        C ∈ Protocol.voter_processed_block_tree S.E
          (voteDutyStore S rho w d).toHealing.toFG.toSG.toGoldfishStore
          (voteDutyStore S rho w d).toHealing.s ∧
        (voteDutyStore S rho w d).h_max ≤
          (derived_state S.E S.cfg C).h + 1:= by
      refine ⟨X, ?_, hXprocessed, ?_⟩
      · rw [hheal, hrootEq]
        simpa only [voteDutyStore, voteStore, tickStore] using hFX
      · rw [hfrontierDuty]
        exact hXh.trans (Nat.le_add_right _ 1)
    have hhead:=
      voteDutyHead_height_ge_frontier_sub_one_of_anchorDescendant
        S adm hw (d - 1) (by simpa only [hdSucc] using hdesc)
    simpa only [hdSucc, hfrontierDuty] using hhead
-/

#print axioms finalizedBelowAtDeliveriesBefore_of_finalizedPreceqAtLaterRead
#print axioms preparedAnchor_compatible_carrier_or_activePrefix
#print axioms voteDutyPreparedAnchor_bandDescendant_processed
#print axioms voteDutyHead_band_at_duty

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
