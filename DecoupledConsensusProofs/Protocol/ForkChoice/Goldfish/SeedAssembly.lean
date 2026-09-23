module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
/-
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeilingStep
-/
/-
public import DecoupledConsensusProofs.Protocol.ChainState.RawHeightCoverage
-/
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedActivity
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionConfirmationCore
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# Round-ceiling seed assembly

This module isolates the boundary fact that is still needed to start the
half-open round-ceiling induction. It also keeps the initial opening proposal
below every later ceiling and carrier parent. That ancestry is the chain
input needed by the two-round Rule A wait.

The one-chain action batch always has a common thin upper block: select its
deepest carrier, then use that carrier's viability witness. What is not
forced by the fixed-frontier and gate-off hypotheses is that the last
Goldfish votes of the round extend this particular thin block. The base
constructor below therefore takes that vote cone directly.
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
variable {delayExtra : Nat}

/-- An actual deepest honest action carrier, together with the processed
frontier witness that makes it viable. The carrier can be below the thin
frontier band; only its witness must reach that band. -/
structure DeepestActionCarrierCeilingAt
    (S : Setup V) (rho : Run V) (M : Height) (q : Round) (C : Block V) :
    Prop where
  sourceAndWitness : ∃ v ∈ rho.honest,
    actionSGBlockAt S rho v q = C ∧
      ∃ W : NamedBlock V,
        W.erase ∈ (actionStoreAt S rho v q).st.core.T ∧
          Block.Preceq C W.erase ∧
          RunBlock S rho W ∧
            M - 1 ≤ (Protocol.derive_named S.E S.cfg W).h
  run : ∃ D : NamedBlock V,
    D.erase = C ∧ RunBlock S rho D
  previousCarriers : ∀ v ∈ rho.honest,
    Block.Preceq (actionSGBlockAt S rho v q) C


private def actionCarrierCandidates
    (S : Setup V) (rho : Run V) (q : Round) : Finset (Block V) :=
  rho.honest.image (fun v => actionSGBlockAt S rho v q)

private theorem honest_nonempty_of_committees
    (S : Setup V) {rho : Run V}
    (hcom : HonestCommittees S rho.honest) :
    rho.honest.Nonempty := by
  have hpositive : 0 < ((S.E.committee 0) ∩ rho.honest).card := by
    have hc := hcom 0
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpositive
  exact ⟨v, (Finset.mem_inter.mp hv).2⟩

private theorem actionCarrierFrontierWitness
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {M : Height}
    (hfrontier : (rho.storeBeforeTime S v (S.a r)).h_max = M) :
    ∃ W : NamedBlock V,
      W.erase ∈ (actionStoreAt S rho v r).st.core.T ∧
        Block.Preceq (actionSGBlockAt S rho v r) W.erase ∧
        RunBlock S rho W ∧
          M - 1 ≤ (Protocol.derive_named S.E S.cfg W).h := by
  have hfiltered := actionSGBlockAt_mem_filtered_actionStore S adm v r
  simp only [Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq,
    Protocol.Store.toHealing] at hfiltered
  obtain ⟨⟨⟨-, -⟩, W, hWT, hcarrierW, hheight⟩, -⟩ := hfiltered
  have hWTaction := hWT
  have hmax : (actionStoreAt S rho v r).st.core.h_max = M := by
    rw [actionStoreAt_eq_update_confirmation_confStore]
    simp only [Protocol.update_confirmation_with]
    simpa only [Run.storeBeforeTime] using hfrontier
  rw [hmax] at hheight
  have hWTpre : W ∈ (rho.storeBeforeTime S v (S.a r)).core.T := by
    have hWT' := hWT
    rw [actionStoreAt_eq_update_confirmation_confStore] at hWT'
    simpa only [Protocol.update_confirmation_with] using hWT'
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho (S.a r) v hWTpre
  have hDrun : RunBlock S rho D := by
    obtain ⟨n, hn, _⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := n)
    rw [← hn]
    exact hDbody
  have hsig : (actionStoreAt S rho v r).st.core.σ D.erase =
      Protocol.derive_named S.E S.cfg D := by
    rw [actionStoreAt_eq_update_confirmation_confStore]
    simpa only [Protocol.update_confirmation_with, hDerase] using
      (Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho (S.a r) v D hDbody)
  refine ⟨D, ?_, ?_, hDrun, ?_⟩
  · rw [hDerase]
    exact hWTaction
  · simpa only [hDerase] using hcarrierW
  · rw [← congrArg (fun cs => cs.h) hsig]
    simpa only [hDerase] using hheight


/-- A one-chain honest action batch has an actual deepest carrier. Its local
viability witness reaches the thin frontier band. No boundary-vote ordering
is claimed here. -/
theorem exists_deepestActionCarrierCeiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {M : Height} {q : Round}
    (hfrontier : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a q)).h_max = M)
    (hchain : HonestActionCarriersOneChainAt S rho q) :
    ∃ C : Block V, DeepestActionCarrierCeilingAt S rho M q C := by
  let candidates := actionCarrierCandidates S rho q
  have hcompatible : ∀ X ∈ candidates, ∀ Y ∈ candidates,
      Block.compatible X Y = true := by
    intro X hX Y hY
    obtain ⟨u, hu, huX⟩ := Finset.mem_image.mp hX
    obtain ⟨v, hv, hvY⟩ := Finset.mem_image.mp hY
    subst X
    subst Y
    exact hchain u hu v hv
  have hnonempty : candidates.Nonempty := by
    obtain ⟨v, hv⟩ := honest_nonempty_of_committees S hcom
    exact ⟨actionSGBlockAt S rho v q,
      Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp
    (deepest?_isSome_of_compatible hcompatible hnonempty)
  have hCmem : C ∈ candidates := Proofs.Engine.deepest?_mem hC
  obtain ⟨v, hv, hvC⟩ := Finset.mem_image.mp hCmem
  have hcarrierPre : C ∈ (rho.storeBeforeTime S v (S.a q)).T := by
    simpa only [hvC] using actionSGBlockAt_mem_storeBeforeTime S rho v q
  obtain ⟨CNamed, hCerase, hCrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hcarrierPre
  obtain ⟨W, hWT, hCW, hWrun, hthin⟩ :=
    actionCarrierFrontierWitness S adm hv (hfrontier v hv)
  refine ⟨C, ⟨?_, ⟨CNamed, hCerase, hCrun⟩, ?_⟩⟩
  · exact ⟨v, hv, hvC, W, hWT, by simpa only [hvC] using hCW, hWrun, hthin⟩
  · intro u hu
    have huMem : actionSGBlockAt S rho u q ∈ candidates :=
      Finset.mem_image.mpr ⟨u, hu, rfl⟩
    exact deepest?_dominates hC huMem
      (hcompatible _ huMem C hCmem)



/- /-- Two actual honest boundary heads whose common run-block prefixes all lie
below the thin band refute the existence of a round ceiling. This is the
formal shape of the split-height-`M - 1` obstruction described above. -/
/-- Two actual honest boundary heads whose common run-block prefixes all lie
below the thin band refute the existence of a round ceiling. This is the
formal shape of the split-height-`M - 1` obstruction described above. -/
theorem no_roundCeiling_of_boundaryHeads_commonPrefix_low
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {M: Height} {q: Round} {X Y: Block V}
    (hX: HonestHead S rho (S.hc.opening_slot (q + 1) - 1) X)
    (hY: HonestHead S rho (S.hc.opening_slot (q + 1) - 1) Y)
    (hlow: ∀ C: Block V, RunBlock S rho C →
      Block.Preceq C X → Block.Preceq C Y →
        (derived_state S.E S.cfg C).h < M - 1):
    ¬ ∃ C: Block V, RoundCeilingAt S rho M (q + 1) C ∧
      M - 1 ≤ (derived_state S.E S.cfg C).h:= by
  rintro ⟨C, hceiling, hthin⟩
  obtain ⟨v, hv, hvCommittee, hXrun, hXemit⟩:= hX
  obtain ⟨w, hw, hwCommittee, hYrun, hYemit⟩:= hY
  obtain ⟨X', hCX', hX'run, hX'emit⟩:=
    hceiling.lastVotes v hv hvCommittee
  obtain ⟨Y', hCY', hY'run, hY'emit⟩:=
    hceiling.lastVotes w hw hwCommittee
  have hXvote:
      (⟨v, S.hc.opening_slot (q + 1) - 1, X.root⟩: GoldfishVote V) =
        ⟨v, S.hc.opening_slot (q + 1) - 1, X'.root⟩:=
    Proofs.Optimistic.emits_gfVote_unique S adm.toScheduleWellFormed
      hXemit hX'emit rfl
  have hYvote:
      (⟨w, S.hc.opening_slot (q + 1) - 1, Y.root⟩: GoldfishVote V) =
        ⟨w, S.hc.opening_slot (q + 1) - 1, Y'.root⟩:=
    Proofs.Optimistic.emits_gfVote_unique S adm.toScheduleWellFormed
      hYemit hY'emit rfl
  have hXX': X = X':=
    Protocol.runBlock_eq_of_root_eq adm.toRootCollisionFree
      hXrun hX'run (congrArg GoldfishVote.head hXvote)
  have hYY': Y = Y':=
    Protocol.runBlock_eq_of_root_eq adm.toRootCollisionFree
      hYrun hY'run (congrArg GoldfishVote.head hYvote)
  have hCX: Block.Preceq C X:= by simpa only [hXX'] using hCX'
  have hCY: Block.Preceq C Y:= by simpa only [hYY'] using hCY'
  exact (Nat.not_lt_of_ge hthin)
    (hlow C hceiling.run hCX hCY)
/-- A supplied boundary-vote cone constructs the first half-open round
ceiling. Timing and next-round regime facts are explicit premises. -/
theorem roundCeiling_base_of_boundaryVotes
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {q: Round}
    (hpostAction: S.E.t_GST ≤ S.a q)
    (hpostBoundaryVote: S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot (q + 1) - 1))
    (hboundaryConfirmationInHorizon:
      Protocol.confirmation_time S.E
        (S.hc.opening_slot (q + 1) - 1) ≤ rho.horizon)
    (hregime: RoundCeilingNextRegimeAt S rho M q)
    (h: ∃ C: Block V,
      ThinActionCarrierCeilingAt S rho M q C ∧
        HonestVotesCone S rho (S.hc.opening_slot (q + 1) - 1)
          (fun X => Block.Preceq C X)):
    ∃ C: Block V, RoundCeilingAt S rho M (q + 1) C:= by
  obtain ⟨C, hceiling, hboundaryVotes⟩:= h
  have hcone: RoundCeilingBoundaryConeAt S rho M q C:=
    { run:= hceiling.run
      boundaryThinHead:=
        thinHonestHeadAt_of_thin_endpoint S hcom hceiling.thin hboundaryVotes
      postAction:= hpostAction
      postBoundaryVote:= hpostBoundaryVote
      boundaryVotes:= hboundaryVotes
      previousCarriers:= hceiling.previousCarriers
      rootOrder:= RoundCeilingNextRootOrderAt.of_thin S adm
        (slashableBound_of_admissible_belowOneThird S adm hfb)
        hceiling.run hceiling.thin hregime }
  have hnext:= roundCeilingStepResidual_of_boundaryCone
    S adm hcom hfb hcone hregime
  have hreadSupport:= roundCeiling_readSupport_of_inputs S
    (q:= q + 1) (C:= C) (Nat.succ_pos q)
      hnext.openingStepInputs hnext.roundInputs hnext.actionActive
      hnext.proposerActive
  exact
    ⟨C,
      { roundPositive:= Nat.succ_pos q
        run:= hceiling.run
        boundaryThinHead:=
          thinHonestHeadAt_of_thin_endpoint S hcom hceiling.thin hboundaryVotes
        aboveRoot:= hreadSupport.1
        active:= hreadSupport.2
        postPreviousVote:= hpostBoundaryVote
        previousConfirmationInHorizon:= hboundaryConfirmationInHorizon
        postOpeningProposal:= hnext.postOpeningProposal
        postOpeningVote:= hnext.postOpeningProposal.trans
          (le_of_lt (Protocol.proposal_time_lt_vote_time S.E _))
        roundConfirmationInHorizon:= hnext.roundConfirmationInHorizon
        lastVotes:= hboundaryVotes
        openingStepInputs:= hnext.openingStepInputs
        roundInputs:= hnext.roundInputs
        voteActive:= hnext.voteActive
        actionActive:= hnext.actionActive
        voteAnchor:= hnext.voteAnchor
        confirmationAnchor:= hnext.confirmationAnchor
        actionAnchor:= hnext.actionAnchor
        proposerAnchorCeiling:= hnext.proposerAnchorCeiling
        proposerActive:= hnext.proposerActive
        previousCarriers:= hceiling.previousCarriers
        gateOff:= hnext.gateOff
        genuineRun:= hnext.genuineRun }⟩
private theorem seedHonestVotesCone_of_commonRoot
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} (hs: 0 < s)
    (hhor: Protocol.vote_time S.E s ≤ rho.horizon)
    {F: Block V}
    (hroot: ∀ w ∈ rho.honest,
      Block.Preceq F
        (Protocol.get_fg_root
          (voteDutyStore S rho w s).toHealing.toFG)):
    HonestVotesCone S rho s (fun X => Block.Preceq F X):= by
  intro w hw hcommittee
  let duty:= voteDutyStore S rho w s
  let raw:= Protocol.voter_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s
  let support:= Protocol.voter_support_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s
  let X:= voteDutyHead S rho w s
  have hFX: Block.Preceq F X:= by
    simpa only [X, voteDutyHead, duty, raw, support] using
      (get_head_in_tree_of_preceq_fgRoot S.E S.hc duty
        (Protocol.voter_filtered_block_tree S.E duty duty.s) F raw support
        (duty.s - 1) (hroot w hw))
  have hXrun: RunBlock S rho X:= by
    simpa only [X, duty, raw, support] using
      voteDutyHead_runBlock S adm hw s
  have hslot: duty.s = s:= voteDutyStore_slot S rho w s
  have hout: (Protocol.goldfish_vote S.E S.hc (S.node w) duty).2 =
      some (⟨w, s, X.root⟩: GoldfishVote V):= by
    simp only [Protocol.goldfish_vote, X, voteDutyHead, duty,
      S.node_val_index, hslot, hcommittee, if_true]
  have hemit: rho.emits S w (Object.gfVote ⟨w, s, X.root⟩)
      (Protocol.vote_time S.E s):= by
    apply emits_of_on_tick_emit S adm.toScheduleWellFormed hw
      (publicTime_vote_time S s) (vote_time_nonneg S.E s) hhor
    apply on_tick_emit_vote_mem S (S.node w)
      (rho.storeBeforeTime S w (Protocol.vote_time S.E s))
      (rho.stateBeforeTime S (Protocol.vote_time S.E s) w).Λ s hs
    simpa only [duty, voteDutyStore] using hout
  exact ⟨X, hFX, hXrun, hemit⟩
/-- A thin common root that is above all preceding action carriers supplies
the first round ceiling. The vote cone follows from root ancestry at each
boundary vote duty. This is the complete sound reveal-rebase case when the
revealed root is already in the thin frontier band. -/
theorem roundCeiling_base_of_commonRoot
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {q: Round} {F: Block V}
    (hpostAction: S.E.t_GST ≤ S.a q)
    (hpostBoundaryVote: S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot (q + 1) - 1))
    (hboundaryConfirmationInHorizon:
      Protocol.confirmation_time S.E
        (S.hc.opening_slot (q + 1) - 1) ≤ rho.horizon)
    (hregime: RoundCeilingNextRegimeAt S rho M q)
    (hceiling: ThinActionCarrierCeilingAt S rho M q F)
    (hroot: ∀ w ∈ rho.honest,
      Block.Preceq F
        (Protocol.get_fg_root
          (voteDutyStore S rho w
            (S.hc.opening_slot (q + 1) - 1)).toHealing.toFG)):
    ∃ C: Block V, RoundCeilingAt S rho M (q + 1) C:= by
  let s:= S.hc.opening_slot (q + 1) - 1
  have hs: 0 < s:= by
    unfold s Protocol.HealConfig.opening_slot
    have hR: 2 ≤ S.hc.R:= S.hc.R_ge_two
    have hq: 1 ≤ q + 1:= Nat.succ_le_succ (Nat.zero_le q)
    have hmul: 2 ≤ (q + 1) * S.hc.R:= by
      simpa only [Nat.one_mul] using Nat.mul_le_mul hq hR
    exact Nat.sub_pos_iff_lt.mpr
      ((by decide: 1 < 2).trans_le hmul)
  have hvoteHor: Protocol.vote_time S.E s ≤ rho.horizon:=
    (Protocol.vote_time_le_confirmation_time S.E s).trans
      (by simpa only [s] using hboundaryConfirmationInHorizon)
  have hvotes: HonestVotesCone S rho
      (S.hc.opening_slot (q + 1) - 1) (fun X => Block.Preceq F X):= by
    simpa only [s] using
      seedHonestVotesCone_of_commonRoot S adm hs hvoteHor
        (by simpa only [s] using hroot)
  exact roundCeiling_base_of_boundaryVotes S adm hcom hfb
    hpostAction hpostBoundaryVote hboundaryConfirmationInHorizon hregime
      ⟨F, hceiling, hvotes⟩
/-- The regime-only ceiling induction can retain the initial ceiling as an
explicit prefix of every later ceiling. -/
theorem roundCeiling_through'_with_base_prefix
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {base last: Round} {C: Block V}
    (hbase: RoundCeilingAt S rho M base C)
    (hregime: ∀ k: Round, base ≤ k → k < last →
      RoundCeilingNextRegimeAt S rho M k):
    ∀ k: Round, base ≤ k → k ≤ last →
      ∃ B: Block V,
        RoundCeilingAt S rho M k B ∧ Block.Preceq C B:=
  roundCeiling_through_or_rebase S adm hcom hfb hbase hregime
/-- The proposal made at a ceiling carrier is below a ceiling at every later
round in the same gate-off regime. -/
theorem openingProposal_preceq_laterRoundCeiling
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {q last: Round} {C: Block V}
    (hqlast: q < last)
    (hcarrier: ProposerCarrierAt S rho q)
    (hceiling: RoundCeilingAt S rho M q C)
    (hwindow: GateOffOpeningWindowAt S rho M q)
    (hregime: ∀ k: Round, q ≤ k → k < last →
      RoundCeilingNextRegimeAt S rho M k):
    ∃ B: Block V,
      RoundCeilingAt S rho M last B ∧
        Block.Preceq
          (proposedBlock S rho (S.hc.opening_slot q)) B:= by
  have hadoption:= gateOff_openingLifecycle_of_roundCeiling
    S adm hcom hfb hcarrier hceiling hwindow
  obtain ⟨Cnext, hnext, -, houtputs⟩:=
    roundCeiling_step_or_rebase S adm hcom hfb hceiling
      (hregime q (le_refl q) hqlast)
  have hproposalNext: Block.Preceq
      (proposedBlock S rho (S.hc.opening_slot q)) Cnext:= by
    let p:= S.E.proposer (S.hc.opening_slot q)
    have hout:= houtputs p hcarrier.1
    rw [roundCeilingOpeningOutput,
      ← actionStoreAt_eq_update_confirmation_confStore,
      hadoption.lifecycle.liveConfirmed p hcarrier.1] at hout
    exact hout
  obtain ⟨B, hB, hCnextB⟩:=
    roundCeiling_through'_with_base_prefix S adm hcom hfb hnext
      (fun k hklo hklt =>
        hregime k ((Nat.le_succ q).trans hklo) hklt)
      last (Nat.succ_le_iff.mpr hqlast) (le_refl last)
  exact ⟨B, hB, Block.preceq_trans hproposalNext hCnextB⟩
/-- At a later carrier, the previous opening proposal is below the actual selected
proposal parent. -/
theorem openingProposal_preceq_laterCarrierParent
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {q last: Round} {C: Block V}
    (hqlast: q < last)
    (hcarrier: ProposerCarrierAt S rho q)
    (hlastCarrier: ProposerCarrierAt S rho last)
    (hceiling: RoundCeilingAt S rho M q C)
    (hwindow: GateOffOpeningWindowAt S rho M q)
    (hregime: ∀ k: Round, q ≤ k → k < last →
      RoundCeilingNextRegimeAt S rho M k):
    Block.Preceq
      (proposedBlock S rho (S.hc.opening_slot q))
      (proposedParent S rho (S.hc.opening_slot last)):= by
  obtain ⟨B, hB, hproposalB⟩:=
    openingProposal_preceq_laterRoundCeiling
      S adm hcom hfb hqlast hcarrier hceiling hwindow hregime
  have haligned:= openingAnchorsAligned_of_roundCeiling
    S adm hcom hlastCarrier hB
  exact Block.preceq_trans hproposalB haligned.ceilingBelowParent
/-- The opening parent at a carrier at least two rounds later satisfies Rule A
when it is still at the previous opening proposal's height. -/
theorem openingProposal_laterCarrier_timeoutMature_of_sameHeight
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    (hdelay: TimeoutDelayBound S delayExtra)
    {M: Height} {q last: Round} {C: Block V}
    (hspace: q + 2 + delayExtra ≤ last)
    (hcarrier: ProposerCarrierAt S rho q)
    (hlastCarrier: ProposerCarrierAt S rho last)
    (hceiling: RoundCeilingAt S rho M q C)
    (hwindow: GateOffOpeningWindowAt S rho M q)
    (hregime: ∀ k: Round, q ≤ k → k < last →
      RoundCeilingNextRegimeAt S rho M k)
    (hsameHeight:
      (derived_state S.E S.cfg
        (proposedParent S rho (S.hc.opening_slot last))).h =
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot q))).h):
    ProposalTimeoutMatureAt S rho (S.hc.opening_slot last):= by
  apply laterOpening_timeoutMature_of_sameHeight
    S adm hdelay hceiling.roundPositive hspace
  · exact openingProposal_preceq_laterCarrierParent
      S adm hcom hfb
        (lt_of_lt_of_le
          (Nat.lt_add_of_pos_right (by omega: 0 < 2 + delayExtra)) (by simpa only [Nat.add_assoc]
            using hspace))
        hcarrier hlastCarrier hceiling hwindow hregime
  · exact hsameHeight
-/



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
