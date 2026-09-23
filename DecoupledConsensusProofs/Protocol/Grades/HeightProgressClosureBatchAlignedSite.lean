module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.FixedHeightRootAdmission
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowGateOff
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressClosureBatchAlignedPreceq
public import DecoupledConsensusProofs.Protocol.Grades.HeightProgressClosureg0ClearAtAction

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Height-progress closure: batch alignment at the lifecycle's own site

`fixedHeightJustificationRoot_boundedProposalLifecycle_closed`
(`FixedHeightRootClaimFourOuterRun.lean`) carries `_of_actionBatchAligned` as
its last protocol pin. This module closes it from the lifecycle's round-local
facts at round `q`.

The producer of the pre-rewrite scope is already available:
`nextActionBatchAligned_preceq_of_carriersPreceq_at_latest`
(`HeightProgressClosureBatchAlignedPreceqRun.lean`) bounds the head of an
honest author's LATEST interpreted round-`q` input by any block above the
author's round-`(q - 1)` action carrier. It asks one thing the lifecycle did
not have: that the author's own round-`(q - 1)` action vote is among its
interpreted inputs at the reader's round-`q` ACTION read, which is what makes
`q - 1` the maximal input round.

`previousActionVote_mem_interpretedInputs_actionRead_of_fixedRoot` below
supplies it. `RelativeCarrierWindowAt` is NOT the route: its reader, cutoff
and author set are all the wrong ones, and this module neither imports
`RelativeCarrierWindowFixedRootRun` nor applies any window theorem. What is
reused is the transport that window is built from, re-run at the action read.
The three differences settle as follows:

* **Reader.** The window transports inputs to `stateBeforeTime S rho (domain
  S.E S.hc q p) v`, the batch producer reads at `actionReadAt S rho v q`. The
  underlying producer `action_vote_mem_interpretedInputs_after_gst_common_upper`
  takes the read time as a parameter, so the transport is re-run at `S.a q`
  directly; no frame-level bridge is involved, and the window's `hFmono` step
  from the phase read up to the action read simply disappears.
* **Token.** The window exhibits SOME interpreted input of round `q - 1`; the
  batch producer names `Protocol.sgVote (actionAttestationAt S rho u
  (q - 1)).erase`. That IS the token the window's own witness is built from,
  so naming it costs nothing once the transport is re-run directly.
* **Author.** The window quantifies over `honestRoundVoters S rho (q - 1)`,
  the batch producer over `rho.honest`. The window's proof uses its
  round-voter hypothesis for exactly one step, `huHon: u ∈ rho.honest`
  (`RelativeCarrierWindowFixedRootRun.lean`, first line after `intro`), and
  never again, so plain honesty is the true premise of the transport.

The cutoffs need no reconciliation: `allPhasesCutoff E hc q` is `late E hc q
.g0`, and `Phase.earlyOffset.g0 = Phase.lateOffset.g0 = -3`, so it IS
`early E hc q.g0`, the cutoff the window transports at.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.NamedOutageEntry
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]




/-- The G0 phase opens and closes at the same cutoff, and that cutoff is the
one every node-level query reads at. -/
theorem allPhasesCutoff_eq_early_g0 (S : Setup V) (q : Round) :
    allPhasesCutoff S.E S.hc q = early S.E S.hc q .g0 := rfl


/-- The same-tick confirmation duty changes no field the batch reads. -/
private theorem batchSite_gradeView_eq (S : Setup V) (rho : Run V)
    (v : V) (q : Round) :
    (actionReadAt S rho v q).st.core.toHealing.gradeView =
      (NamedRun.stateBeforeTime S rho (S.a q) v).st.core.toHealing.gradeView := rfl

private theorem batchSite_F_eq (S : Setup V) (rho : Run V)
    (v : V) (q : Round) :
    (actionReadAt S rho v q).st.core.F =
      (NamedRun.stateBeforeTime S rho (S.a q) v).st.core.F := rfl

set_option maxHeartbeats 400000 in
/-- Under fixed-root retention with no frontier rise, every honest author's own
round-`(q - 1)` action vote is an interpreted input of every honest reader's
round-`q` action read. -/
theorem previousActionVote_mem_interpretedInputs_actionRead_of_fixedRoot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) {q : Round} (hq : 0 < q)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    (hpostRead : S.E.t_GST ≤ read)
    (hpost : S.E.t_GST ≤ S.a (q - 1))
    (hprevDelay : read + S.E.Δ ≤ S.a (q - 1))
    (hprevHor : S.a (q - 1) ≤ rho.horizon)
    (hprevCap : honestHMaxAt S rho (S.a (q - 1)) ≤ H)
    (hactionDelay : read + S.E.Δ ≤ S.a q)
    (hactionHor : S.a q ≤ rho.horizon)
    (hactionCap : honestHMaxAt S rho (S.a q) ≤ H) :
    ∀ v ∈ rho.honest, ∀ u ∈ rho.honest,
      Protocol.sgVote (actionAttestationAt S rho u (q - 1)).erase ∈
        DecoupledConsensusModel.Protocol.interpretedInputs
          (actionReadAt S rho v q).st.core.toHealing.gradeView
          (actionReadAt S rho v q).st.core.F
          S.hc.η_SG q (allPhasesCutoff S.E S.hc q) u := by
  have hsb : Internal.NamedOutageEntry.SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hprevPkg : ∀ x ∈ rho.honest,
      Protocol.get_fg_root
            (rho.storeBeforeTime S x (S.a (q - 1))).toHealing.toFG =
          (rho.storeBeforeTime S w read).J ∧
        (rho.storeBeforeTime S x (S.a (q - 1))).h_max = H := by
    intro x hx
    exact
      fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
        S adm hsb hfix hx hpostRead hprevDelay hprevHor hprevCap
  have hactionPkg : ∀ x ∈ rho.honest,
      Protocol.get_fg_root
            (rho.storeBeforeTime S x (S.a q)).toHealing.toFG =
          (rho.storeBeforeTime S w read).J ∧
        (rho.storeBeforeTime S x (S.a q)).h_max = H := by
    intro x hx
    exact
      fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
        S adm hsb hfix hx hpostRead hactionDelay hactionHor hactionCap
  have hqr : q - 1 < q := Nat.sub_lt hq (by decide)
  have hk : q - 1 ∈ Protocol.latest_window S.hc.η_SG q := by
    apply NamedOutageClosure.mem_latest_window
    · exact Nat.sub_le_sub_left S.hc.η_SG_ge_one q
    · exact hqr
  have hdeadline : max (S.a (q - 1)) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc q .g0 := by
    rw [max_eq_left hpost]
    apply (NamedOutageClosure.action_delta_le_early
      S S.hc.R_ge_three hqr).trans
    simp only [early, Phase.earlyOffset]
    linarith [S.E.Δ_pos]
  have hearlyDomain : early S.E S.hc q .g0 ≤ domain S.E S.hc q .g0 := by
    simp only [early, domain, Phase.earlyOffset, Phase.domainOffset]
    linarith [S.E.Δ_pos]
  have horder : early S.E S.hc q .g0 ≤ S.a q :=
    hearlyDomain.trans (FrameForward.domain_le_a S q .g0)
  have hcut : early S.E S.hc q .g0 ≤ rho.horizon := horder.trans hactionHor
  intro v hv u huHon
  let a := actionAttestationAt S rho u (q - 1)
  have hshape : a.val_index = u ∧ a.round = q - 1 ∧
      a.confirmed = some (actionSGBlockAt S rho u (q - 1)).root := by
    simpa only [a] using actionAttestationAt_shape S rho u (q - 1)
  have hemit : NamedRun.emits S rho u (Object.attest a) (S.a (q - 1)) := by
    simpa only [a] using
      honest_emits_exact_actionAttestationAt S adm huHon (q - 1) hprevHor
  obtain ⟨i, hi, _, hhead⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
  dsimp at hhead
  obtain ⟨Hb, hHb, hconfirmed⟩ := hhead
  obtain ⟨W, hWbody, hcarrierW, hWheight⟩ :=
    actionSGBlockAt_frontierWitness S adm (hprevPkg u huHon).2
  have hWsource : W ∈
      (rho.storeBeforeTime S u (S.a (q - 1))).bodies := by
    simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hWbody
  have hcarrierFiltered : actionSGBlockAt S rho u (q - 1) ∈
      Protocol.get_filtered_block_tree
        (actionStoreAt S rho u (q - 1)).toHealing.toFG :=
    actionSGBlockAt_mem_filtered_actionStore S adm u (q - 1)
  have hrootCarrier : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S u (S.a (q - 1))).toHealing.toFG)
      (actionSGBlockAt S rho u (q - 1)) := by
    have hmem := Proofs.Records.preceq_get_fg_root_of_mem_filtered hcarrierFiltered
    rwa [actionStoreAt_fgRoot_eq_storeBeforeTime S rho u (q - 1)] at hmem
  have hJcarrier : Block.Preceq (rho.storeBeforeTime S w read).J
      (actionSGBlockAt S rho u (q - 1)) := by
    rw [← (hprevPkg u huHon).1]
    exact hrootCarrier
  have hJW : Block.Preceq (rho.storeBeforeTime S w read).J W.erase :=
    Block.preceq_trans hJcarrier hcarrierW
  have hFroot : Block.Preceq (rho.storeBeforeTime S v (S.a q)).F
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v (S.a q)).toHealing.toFG) :=
    StoreFinality.finalized_preceq_fgRoot
      (st := (rho.storeBeforeTime S v (S.a q)).core)
      (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (S.a q) v)
  have hFC : Block.Preceq
      (NamedRun.stateBeforeTime S rho (S.a q) v).st.core.F W.erase := by
    refine Block.preceq_trans hFroot ?_
    rw [(hactionPkg v hv).1]
    exact hJW
  have hbodySource : Hb ∈
      (NamedRun.stateBeforeTime S rho (S.a (q - 1)) u).st.bodies := by
    have hi' : rho.events[i]? = some (.tick u (S.a (q - 1))) := by
      simpa only [hshape.2.1] using hi
    have hstate := NamedActionSources.action_read_index S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed i u (q - 1) hi'
    change Hb ∈ (NamedRun.stateBefore S rho i u).st.bodies at hHb
    rw [← hstate]
    exact hHb
  have hcarrierMem : actionSGBlockAt S rho u (q - 1) ∈
      (NamedRun.stateBeforeTime S rho (S.a (q - 1)) u).st.core.T :=
    actionSGBlockAt_mem_storeBeforeTime S rho u (q - 1)
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a (q - 1)) u hcarrierMem
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a (q - 1))
  have hDprefix : D ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hDbody
  have hHprefix : Hb ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hbodySource
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon (i := n) hDprefix
  have hHrun : RunBlock S rho Hb :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon (i := n) hHprefix
  have hroot : D.root = Hb.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase]
    exact Option.some.inj (hshape.2.2.symm.trans hconfirmed)
  have hDH : D = Hb :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective D Hb
      hDrun hHrun D Hb (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self Hb)) hroot
  have hHErase : Hb.erase = actionSGBlockAt S rho u (q - 1) := by
    rw [← hDH, hDerase]
  have hHC : Block.Preceq Hb.erase W.erase := by
    rw [hHErase]
    exact hcarrierW
  have hpostA : S.E.t_GST ≤ S.a a.round := by
    simpa only [hshape.2.1] using hpost
  have hdeadlineA : max (S.a a.round) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc q .g0 := by
    simpa only [hshape.2.1] using hdeadline
  have hinput : Protocol.sgVote a.erase ∈
      DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho (S.a q) v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (S.a q) v).st.core.F
        S.hc.η_SG q (early S.E S.hc q .g0) u :=
    action_vote_mem_interpretedInputs_after_gst_common_upper
      S adm.toNamedAdmissibleCore .g0 hk huHon hv
      ⟨hshape.1, hshape.2.1, hemit⟩
      ⟨i, hi, hHb, hconfirmed⟩ hHC hFC hpostA hdeadlineA horder hcut
  simpa only [a, allPhasesCutoff_eq_early_g0, batchSite_gradeView_eq,
    batchSite_F_eq] using hinput

set_option maxHeartbeats 400000 in
/-- The lifecycle's `_of_actionBatchAligned` premise, closed at round `q` from
the fixed-root facts and the opening parent ceilings.

The conclusion is `Internal.PhaseGrades.BatchAlignedAt` in its restored
latest-input scope, exactly the shape the lifecycle's `_of_actionBatchAligned`
premise asks for. -/
theorem actionBatchAlignedAt_of_fixedRoot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) {q : Round} (hq : 0 < q)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    (hpostRead : S.E.t_GST ≤ read)
    (hpost : S.E.t_GST ≤ S.a (q - 1))
    (hprevDelay : read + S.E.Δ ≤ S.a (q - 1))
    (hprevHor : S.a (q - 1) ≤ rho.horizon)
    (hprevCap : honestHMaxAt S rho (S.a (q - 1)) ≤ H)
    (hactionDelay : read + S.E.Δ ≤ S.a q)
    (hactionHor : S.a q ≤ rho.horizon)
    (hactionCap : honestHMaxAt S rho (S.a q) ≤ H)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hparents : FixedHeightRootOpeningParentRun S rho q) :
    ∀ v ∈ rho.honest,
      let n := actionReadAt S rho v q
      Internal.PhaseGrades.BatchAlignedAt S.hc
        n.st.core.toHealing.gradeView n.st.core.F rho.honest q
        (allPhasesCutoff S.E S.hc q) P.erase := by
  have hparentP : Block.Preceq
      (proposedParent S rho (S.hc.opening_slot q)) P.erase :=
    proposedParent_preceq_proposedBlockAt S rho (S.hc.opening_slot q) hP
  have hcarriers : ∀ x ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho x (q - 1)) P.erase := by
    intro x hx
    exact Block.preceq_trans (hparents.actionTargetParent x hx) hparentP
  have hprev := previousActionVote_mem_interpretedInputs_actionRead_of_fixedRoot
    S adm hfb hq hfix hpostRead hpost hprevDelay hprevHor hprevCap
      hactionDelay hactionHor hactionCap
  intro v hv n x hx u hu hmax head hconf hfind
  exact nextActionBatchAligned_preceq_of_carriersPreceq_at_latest
    S adm hactionHor hcarriers v hv x hx (hprev v hv x hx) u hu hmax head
    hconf hfind



set_option maxHeartbeats 400000 in
/-- Under the gate-off frame, every honest author's own round-`(q - 1)` action
vote is an interpreted input of every honest reader's round-`q` action read. -/
theorem previousActionVote_mem_interpretedInputs_actionRead_of_gateOff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) {q : Round} (hq : 0 < q)
    {M : Height}
    (hpost : S.E.t_GST ≤ S.a (q - 1))
    (hactionHor : S.a q ≤ rho.horizon)
    (hprev : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1))).h_max = M)
    (hfrontier : ∀ x ∈ rho.honest,
      (rho.storeBeforeTime S x (S.a q)).h_max = M)
    (hgateOff : ∀ x ∈ rho.honest,
      (rho.storeBeforeTime S x (S.a q)).h_j + 2 ≤ M) :
    ∀ v ∈ rho.honest, ∀ u ∈ rho.honest,
      Protocol.sgVote (actionAttestationAt S rho u (q - 1)).erase ∈
        DecoupledConsensusModel.Protocol.interpretedInputs
          (actionReadAt S rho v q).st.core.toHealing.gradeView
          (actionReadAt S rho v q).st.core.F
          S.hc.η_SG q (allPhasesCutoff S.E S.hc q) u := by
  have hsb : Internal.NamedOutageEntry.SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hqr : q - 1 < q := Nat.sub_lt hq (by decide)
  have hk : q - 1 ∈ Protocol.latest_window S.hc.η_SG q := by
    apply NamedOutageClosure.mem_latest_window
    · exact Nat.sub_le_sub_left S.hc.η_SG_ge_one q
    · exact hqr
  have hdeadline : max (S.a (q - 1)) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc q .g0 := by
    rw [max_eq_left hpost]
    apply (NamedOutageClosure.action_delta_le_early
      S S.hc.R_ge_three hqr).trans
    simp only [early, Phase.earlyOffset]
    linarith [S.E.Δ_pos]
  have hearlyDomain : early S.E S.hc q .g0 ≤ domain S.E S.hc q .g0 := by
    simp only [early, domain, Phase.earlyOffset, Phase.domainOffset]
    linarith [S.E.Δ_pos]
  have horder : early S.E S.hc q .g0 ≤ S.a q :=
    hearlyDomain.trans (FrameForward.domain_le_a S q .g0)
  have hcut : early S.E S.hc q .g0 ≤ rho.horizon := horder.trans hactionHor
  have hprevHor : S.a (q - 1) ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.sub_le q 1)).trans hactionHor
  intro v hv u huHon
  let a := actionAttestationAt S rho u (q - 1)
  have hshape : a.val_index = u ∧ a.round = q - 1 ∧
      a.confirmed = some (actionSGBlockAt S rho u (q - 1)).root := by
    simpa only [a] using actionAttestationAt_shape S rho u (q - 1)
  have hemit : NamedRun.emits S rho u (Object.attest a) (S.a (q - 1)) := by
    simpa only [a] using
      honest_emits_exact_actionAttestationAt S adm huHon (q - 1) hprevHor
  obtain ⟨i, hi, _, hhead⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
  dsimp at hhead
  obtain ⟨Hb, hHb, hconfirmed⟩ := hhead
  obtain ⟨W, hWbody, hcarrierW, hWheight⟩ :=
    actionSGBlockAt_frontierWitness S adm (hprev u huHon)
  have hWsource : W ∈
      (rho.storeBeforeTime S u (S.a (q - 1))).bodies := by
    simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hWbody
  have hWrun : RunBlock S rho W := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a (q - 1))
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S huHon (i := n)
    rw [← hn]
    exact hWsource
  -- The one changed step: with the gate off the reader's selected FG root is
  -- its finalized block, and that is below the frontier witness.
  have hrootW : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v (S.a q)).toHealing.toFG) W.erase :=
    frontierRoot_preceq_of_gateOff S adm hsb hv
      (X := W.erase) (Xn := W) rfl hWrun hWheight
      (hfrontier v hv) (hgateOff v hv)
  have hgate : ¬ (rho.storeBeforeTime S v (S.a q)).h_max =
      (rho.storeBeforeTime S v (S.a q)).h_j + 1 := by
    apply Nat.ne_of_gt
    rw [hfrontier v hv]
    exact Nat.lt_of_succ_le (by
      simpa only [Nat.add_assoc] using hgateOff v hv)
  have hrootF : Protocol.get_fg_root
      (rho.storeBeforeTime S v (S.a q)).toHealing.toFG =
      (rho.storeBeforeTime S v (S.a q)).F := by
    simp only [Protocol.get_fg_root, Protocol.Store.toHealing, if_neg hgate]
  have hFfrontier : Block.Preceq
      (rho.storeBeforeTime S v (S.a q)).F W.erase := by
    rw [← hrootF]
    exact hrootW
  have hFC : Block.Preceq
      (NamedRun.stateBeforeTime S rho (S.a q) v).st.core.F W.erase :=
    hFfrontier
  have hbodySource : Hb ∈
      (NamedRun.stateBeforeTime S rho (S.a (q - 1)) u).st.bodies := by
    have hi' : rho.events[i]? = some (.tick u (S.a (q - 1))) := by
      simpa only [hshape.2.1] using hi
    have hstate := NamedActionSources.action_read_index S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed i u (q - 1) hi'
    change Hb ∈ (NamedRun.stateBefore S rho i u).st.bodies at hHb
    rw [← hstate]
    exact hHb
  have hcarrierMem : actionSGBlockAt S rho u (q - 1) ∈
      (NamedRun.stateBeforeTime S rho (S.a (q - 1)) u).st.core.T :=
    actionSGBlockAt_mem_storeBeforeTime S rho u (q - 1)
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a (q - 1)) u hcarrierMem
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a (q - 1))
  have hDprefix : D ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hDbody
  have hHprefix : Hb ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hbodySource
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon (i := n) hDprefix
  have hHrun : RunBlock S rho Hb :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon (i := n) hHprefix
  have hroot : D.root = Hb.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase]
    exact Option.some.inj (hshape.2.2.symm.trans hconfirmed)
  have hDH : D = Hb :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective D Hb
      hDrun hHrun D Hb (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self Hb)) hroot
  have hHErase : Hb.erase = actionSGBlockAt S rho u (q - 1) := by
    rw [← hDH, hDerase]
  have hHC : Block.Preceq Hb.erase W.erase := by
    rw [hHErase]
    exact hcarrierW
  have hpostA : S.E.t_GST ≤ S.a a.round := by
    simpa only [hshape.2.1] using hpost
  have hdeadlineA : max (S.a a.round) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc q .g0 := by
    simpa only [hshape.2.1] using hdeadline
  have hinput : Protocol.sgVote a.erase ∈
      DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho (S.a q) v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (S.a q) v).st.core.F
        S.hc.η_SG q (early S.E S.hc q .g0) u :=
    action_vote_mem_interpretedInputs_after_gst_common_upper
      S adm.toNamedAdmissibleCore .g0 hk huHon hv
      ⟨hshape.1, hshape.2.1, hemit⟩
      ⟨i, hi, hHb, hconfirmed⟩ hHC hFC hpostA hdeadlineA horder hcut
  simpa only [a, allPhasesCutoff_eq_early_g0, batchSite_gradeView_eq,
    batchSite_F_eq] using hinput

set_option maxHeartbeats 400000 in

/-- The gate-off batch alignment at an honest reader's round-`q` action read,
from the round-`(q - 1)` carrier bound alone. -/
theorem actionBatchAlignedAt_of_gateOff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) {q : Round} (hq : 0 < q)
    {M : Height}
    (hpost : S.E.t_GST ≤ S.a (q - 1))
    (hactionHor : S.a q ≤ rho.horizon)
    (hprev : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1))).h_max = M)
    (hfrontier : ∀ x ∈ rho.honest,
      (rho.storeBeforeTime S x (S.a q)).h_max = M)
    (hgateOff : ∀ x ∈ rho.honest,
      (rho.storeBeforeTime S x (S.a q)).h_j + 2 ≤ M)
    {Can : Block V}
    (hcarriers : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1)) Can) :
    ∀ v ∈ rho.honest,
      let n := actionReadAt S rho v q
      Internal.PhaseGrades.BatchAlignedAt S.hc
        n.st.core.toHealing.gradeView n.st.core.F rho.honest q
        (allPhasesCutoff S.E S.hc q) Can := by
  have hprevInput := previousActionVote_mem_interpretedInputs_actionRead_of_gateOff
    S adm hfb hq hpost hactionHor hprev hfrontier hgateOff
  intro v hv n x hx u hu hmax head hconf hfind
  exact nextActionBatchAligned_preceq_of_carriersPreceq_at_latest
    S adm hactionHor hcarriers v hv x hx (hprevInput v hv x hx) u hu hmax head
    hconf hfind

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
