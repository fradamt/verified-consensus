module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.StableCoverageConsumer
public import DecoupledConsensusInternal.Legacy.Claims
public import DecoupledConsensusProofs.Protocol.ChainState.WholeRunFinalitySafety
public import DecoupledConsensusProofs.Protocol.ChainState.ValidatorVoteSafety
public import DecoupledConsensusProofs.Protocol.ChainState.LeakFairnessL1
public import DecoupledConsensusProofs.Protocol.Handlers.NestedOutputs
public import DecoupledConsensusProofs.Generic.W4B1HonestProposalConfirmation
public import DecoupledConsensusProofs.Generic.W4B2AvailableChainGrowth
public import DecoupledConsensusProofs.Execution.W4StableRecordGrowthClosed
public import DecoupledConsensusProofs.Protocol.Schedule.W4FinalitySkeleton
public import DecoupledConsensusProofs.Protocol.Schedule.W4NamedExecutionStage0
public import DecoupledConsensusProofs.Protocol.Schedule.W4FoldOnlyHead
public import DecoupledConsensusProofs.Execution.W4D2GradeCallsite
public import DecoupledConsensusProofs.Execution.W4CarrierFinalityField
public import DecoupledConsensusProofs.Protocol.Schedule.W4CarrierAtField

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.Optimistic Proofs.HealingLemmas
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! This is the private selector from `W4FinalitySkeletonRun`, copied with the
required glue prefix because the original declaration is private. -/
private theorem w4close_select_openingCarrier
    (S : Setup V) {rho : Run V}
    {extra : Nat}
    {gap : Round} (hop : ProposerOpeningCarrierRecurrence S rho gap)
    (rGST : Round) (hpost : S.E.t_GST ≤ S.a rGST)
    (hhor : healingBoundaryTime S
      (rGST + w4UniformHandoffLag S gap extra) ≤ rho.horizon)
    (hdeadlineUniform :
      fgSafetyProgressDeadline S rho rGST gap extra ≤
        rGST + w4UniformFGSafetyDeadline S gap extra) :
    ∃ q : Round,
      rGST ≤ q ∧
      q ≤ rGST + w4UniformHandoffLag S gap extra ∧
      fgSafetyProgressDeadline S rho rGST gap extra +
        3 * progressLag' gap extra + 3 ≤ q ∧
      ProposerOpeningCarrierAt S rho q ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon := by
  let U := w4UniformMovingBoundaryRound S gap extra
  let L := progressLag' gap extra
  have hGSTwindow : S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot (rGST + U)) := by
    have hrlt : rGST < rGST + U := by
      have hu : 0 < U := by
        simpa only [U, w4UniformMovingBoundaryRound, Nat.succ_eq_add_one] using
          (Nat.zero_lt_succ
            (w4UniformFGSafetyDeadline S gap extra +
              3 * progressLag' gap extra))
      exact Nat.lt_add_of_pos_right hu
    exact hpost.trans ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (action_add_delta_le_openingProposal_of_round_lt S hrlt))
  have hwindowRound : rGST + U + gap ≤
      rGST + w4UniformHandoffLag S gap extra := by
    simpa only [w4UniformHandoffLag, Nat.add_assoc] using
      (Nat.le_add_right (rGST + U + gap) 3)
  have hhorWindow := (openingProposal_window_le_action S (rGST + U) gap).trans
    ((Assembly.a_mono S hwindowRound).trans
      ((a_le_healingBoundaryTime S _).trans hhor))
  obtain ⟨q, hqlo, hqhi, hopening⟩ := hop (rGST + U) hGSTwindow hhorWindow
  have hqGST : rGST ≤ q :=
    (Nat.le_add_right rGST (U + 2)).trans hqlo
  have hqWindow : q ≤ rGST + w4UniformHandoffLag S gap extra := by
    have hqhi' : q + 3 ≤ rGST + U + gap + 3 := Nat.add_le_add_right hqhi 3
    have hlag : rGST + U + gap + 3 ≤
        rGST + w4UniformHandoffLag S gap extra := by
      simpa only [U, w4UniformHandoffLag, Nat.add_assoc] using
        (Nat.le_refl (rGST + U + gap + 3))
    exact (Nat.le_add_right q 3).trans (hqhi'.trans hlag)
  have hlate : fgSafetyProgressDeadline S rho rGST
      gap extra + 3 * L + 3 ≤ q := by
    have h1 := Nat.add_le_add_right hdeadlineUniform (3 * L + 3)
    have h3 : (rGST + w4UniformFGSafetyDeadline S gap extra) + (3 * L + 3) =
        rGST + U + 2 := by
      dsimp only [U, w4UniformMovingBoundaryRound, L]
      simp only [Nat.add_assoc, Nat.reduceAdd]
    exact (h1.trans_eq h3).trans hqlo
  have hq3 : q + 3 ≤ rGST + w4UniformHandoffLag S gap extra := by
    have hqhi' : q + 3 ≤ rGST + U + gap + 3 := Nat.add_le_add_right hqhi 3
    exact hqhi'.trans (by
      simpa only [U, w4UniformHandoffLag, Nat.add_assoc] using
        (Nat.le_refl (rGST + U + gap + 3)))
  have hslot : S.hc.opening_slot q + 3 + 2 ≤
      S.hc.opening_slot (rGST + w4UniformHandoffLag S gap extra) + 2 := by
    have hslotGap : S.hc.opening_slot q + 3 ≤ S.hc.opening_slot (q + 3) := by
      simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul] using
        Nat.add_le_add_left
          (Nat.mul_le_mul_left 3
            (show (1 : Nat) ≤ S.hc.R from
              (by decide : (1 : Nat) ≤ 2).trans S.hc.R_ge_two))
          (q * S.hc.R)
    have hslot' : S.hc.opening_slot (q + 3) ≤
        S.hc.opening_slot (rGST + w4UniformHandoffLag S gap extra) := by
      simpa only [Protocol.HealConfig.opening_slot] using
        Nat.mul_le_mul_right S.hc.R hq3
    exact Nat.add_le_add_right (hslotGap.trans hslot') 2
  have hconf : Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
      rho.horizon := by
    let x := S.hc.opening_slot q + 3
    calc
      Protocol.confirmation_time S.E x =
          Protocol.vote_time S.E (x + 1) + S.E.Δ :=
        (vote_time_succ_add_delta_eq_confirmation_time S.E x).symm
      _ = Protocol.support_cutoff S.E (x + 1) := vote_time_add_delta S.E (x + 1)
      _ ≤ Protocol.vote_time S.E (x + 2) :=
        support_cutoff_le_vote_time_succ S.E (x + 1)
      _ ≤ Protocol.vote_time S.E
          (S.hc.opening_slot (rGST + w4UniformHandoffLag S gap extra) + 2) :=
        vote_time_mono_slots S.E (by simpa only [x] using hslot)
      _ = healingBoundaryTime S
          (rGST + w4UniformHandoffLag S gap extra) := rfl
      _ ≤ rho.horizon := hhor
  exact ⟨q, hqGST, hqWindow, hlate, hopening, hconf⟩

/-- The uniform finality pin, closed by the named carrier exporter. -/
private theorem w4close_uniformRecoveryFinalityPin
    (S : Setup V) : UniformRecoveryFinalityPin S := by
  intro extra hdelay gap
  have hfinalityStartup :
      Statements.Instantiation.finalityStartup S gap extra =
        w4UniformHandoffLag S gap extra :=
    finalityStartup_eq_w4UniformHandoffLag S gap extra
  have hfinalityDeadline :
      Statements.Instantiation.finalityDeadline S gap extra =
        recurringFinalityDeadline S
          (recurringFinalityPhaseLag (progressLag' gap extra) gap) gap := by
    exact finalityDeadline_eq_recurringFinalityDeadline S gap extra
  rw [hfinalityStartup, hfinalityDeadline]
  intro rho rGST adm hcom hbelow hop hpost hK hhor
  have hdeadline : fgSafetyProgressDeadline S rho rGST gap extra ≤
      rGST + w4UniformFGSafetyDeadline S gap extra :=
    w4_fgSafetyProgressDeadline_le_uniform (delayExtra := extra)
      S adm rGST gap hpost
  obtain ⟨q, hqlo, hqhi, hlateWide, hopening, hbaseHor⟩ :=
    w4close_select_openingCarrier S hop rGST hpost hhor hdeadline
  let q0 := fgSafetyProgressDeadline S rho rGST gap extra + 3
  have hlate : fgSafetyProgressDeadline S rho rGST gap extra +
      3 * progressLag' gap extra + 1 ≤ q := by
    exact (Nat.add_le_add_left (by decide : (1 : Nat) ≤ 3)
      (fgSafetyProgressDeadline S rho rGST gap extra +
        3 * progressLag' gap extra)).trans hlateWide
  have hdeadline3 :
      fgSafetyProgressDeadline S rho rGST gap extra + 3 ≤ q := by
    have hthree : 3 ≤ 3 * progressLag' gap extra + 3 :=
      Nat.le_add_left 3 (3 * progressLag' gap extra)
    exact (Nat.add_le_add_left hthree
      (fgSafetyProgressDeadline S rho rGST gap extra)).trans
        hlateWide
  have hwindow : q0 + 3 * progressLag' gap extra ≤ q := by
    dsimp only [q0]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlateWide
  obtain ⟨Dn, hDn⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot q + 1)
  have hcap := w4LaterReadFrontierCap_at_openingCarrier_public S adm hcom hbelow
    hop hdelay hpost
    (q := q) (q0 := q0) (by rfl) hwindow hopening hbaseHor hDn
  obtain ⟨carrier, hhandoff, hboundary⟩ :=
    w4PreparedNamedHandoffBoundary_of_frontierCap S adm hcom hbelow hop hdelay
      hpost (q := q) (q0 := q0) (by rfl)
      hwindow hopening hbaseHor hDn hcap
  have hbaseTiming := w4_handoffBaseTiming_after_GST S
    hpost hdeadline3 hbaseHor
  have hrec : MultiProposerRecurrence S rho gap :=
    proposerRecurrence_of_openingCarrierRecurrence S hop
  have hprefix := w4NamedExecutionPrefix_of_stage0 S adm hcom hbelow hrec hdelay
    hpost hdeadline3 hhandoff hboundary
    hbaseTiming
  have hfold : W4SelectedNamedFoldAtEverySlot S rho q
      (derive_named S.E S.cfg Dn).h Dn := hprefix.2.2.2
  have hexec : CanonicalSuffixExecutionPrepared S rho q :=
    canonicalSuffixExecutionPrepared_named_of_prefix_and_fold S adm hcom hbelow
      hbaseTiming hprefix
  have hchain : MovingChainAtCarrierFrom S rho q :=
    w4_carrierAtField_of_namedFold S adm hcom hbelow hrec hdelay hpost hqlo
      hqhi hdeadline3 hhandoff hboundary hbaseTiming hfold
  have hpostQ : S.E.t_GST ≤ S.a q := hpost.trans (Assembly.a_mono S hqlo)
  have hprogress : EventualHeightProgressFrom S rho q (progressLag' gap extra) :=
    heightProgress_public S hdelay adm hcom hbelow hpostQ hrec
  have hnotLost : ∀ r : Round, q + 2 < r →
      S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest →
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon →
      ¬ LostRoundAt S rho r :=
    w4NonLost_of_named_at S adm hcom hbelow hrec hdelay rGST hpost q hlate
  have hsource : W4PreparedSelectedSourceAt S rho q extra :=
    w4PreparedSelectedSourceAt_of_fold S adm hcom hbelow hrec hdelay
      rGST hpost hlate hfold
  have hgraded : W4PreparedSelectedGradeAt S rho q extra :=
    w4PreparedSelectedGradeAt_of_chain S adm hcom hbelow hrec hdelay
      rGST hpost hlate
      hsource hchain
  have hfirst : W4PreparedSelectedFirstHalfAt S rho q :=
    w4_firstHalfField_of_arms S adm hcom hbelow hrec hdelay hpost hlate hpostQ
      hexec hchain hprogress hnotLost
  have hanchor := w4PreparedD3AnchorAt_of_executionPrepared S hcom hexec
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissibleCore_belowOneThird S adm.toNamedAdmissibleCore hbelow
  have hround_gt : ∀ r : Round, CanonicalRegimeRoundAt S rho q r → q < r := by
    intro r hround
    have hd := openingSlot_three_le_of_healingBoundary_lt_proposal S
      hround.afterBoundary
    exact Nat.lt_of_mul_lt_mul_right
      ((Nat.lt_add_of_pos_right (by decide : 0 < 3)).trans_le hd)
  have hgst : ∀ r : Round, CanonicalRegimeRoundAt S rho q r →
      S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot r + 1) := by
    intro r hround
    have hqr := hround_gt r hround
    exact hpostQ.trans ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      ((action_add_delta_le_openingProposal_of_round_lt S hqr).trans
        ((Protocol.proposal_time_lt_vote_time S.E (S.hc.opening_slot r)).le.trans
          (vote_time_mono_slots S.E
            (Nat.le_add_right (S.hc.opening_slot r) 1)))))
  have hframe : ∀ r : Round, CanonicalRegimeRoundAt S rho q r →
      ∃ C End : Block V,
        MovingChainAtCarrierFor S rho q r C End ∧
        S.E.t_GST ≤ S.a (r - 1) ∧
        S.hc.opening_slot
            (fgSafetyProgressDeadline S rho rGST gap extra + 2) ≤
          S.hc.opening_slot r + 1 := by
    intro r hround
    have hqr := hround_gt r hround
    obtain ⟨C, End, hchainR⟩ :=
      hchain r hround.afterBoundary hround.carrier hround.inHorizon
    have hqPrev : q ≤ r - 1 := Nat.le_sub_of_add_le hqr
    have hpostPrev : S.E.t_GST ≤ S.a (r - 1) :=
      hpostQ.trans (Assembly.a_mono S hqPrev)
    have hdeadlineQ :
        fgSafetyProgressDeadline S rho rGST gap extra + 2 ≤ q := by
      have hL : 1 ≤ progressLag' gap extra := progressLag'_pos gap
      have hmul : 3 * 1 ≤ 3 * progressLag' gap extra := Nat.mul_le_mul_left 3 hL
      have htail : 2 ≤ 3 * progressLag' gap extra + 1 :=
        (by decide : (2 : Nat) ≤ 4).trans
          (by simpa only [Nat.mul_one] using Nat.add_le_add_right hmul 1)
      exact (Nat.add_le_add_left htail
        (fgSafetyProgressDeadline S rho rGST gap extra)).trans hlate
    have hdeadlineRound :
        S.hc.opening_slot
            (fgSafetyProgressDeadline S rho rGST gap extra + 2) ≤
          S.hc.opening_slot r + 1 := by
      have hroundIndex :
          fgSafetyProgressDeadline S rho rGST gap extra + 2 ≤ r :=
        hdeadlineQ.trans hqr.le
      exact (Nat.mul_le_mul_right S.hc.R hroundIndex).trans
        (Nat.le_add_right (S.hc.opening_slot r) 1)
    exact ⟨C, End, hchainR, hpostPrev, hdeadlineRound⟩
  have hcarrierFinality : W4CarrierChainFinalityPin S rho q :=
    w4CarrierChainFinalityPin_of_fields_of_frame_inputs S adm hbelow hcom
      hexec.canonicalSuffixFrom hexec.duty hrec hdelay
      hpost hgst hframe
      (w4ProcessedFinalityAdvancePin_of_slashableBound S adm hsb)
  have hafterAll : ∀ r : Round, q + 1 < r →
      healingBoundaryTime S q <
        Protocol.proposal_time S.E (S.hc.opening_slot r) := by
    intro r hr
    have hfirstSlot := Nat.add_le_add_right
      (openingSlot_add_two_le_openingSlot_of_lt S (Nat.lt_succ_self q)) 1
    have hslots : S.hc.opening_slot q + 3 ≤ S.hc.opening_slot r :=
      hfirstSlot.trans ((Nat.le_succ (S.hc.opening_slot (q + 1) + 1)).trans
        (openingSlot_add_two_le_openingSlot_of_lt S hr))
    exact lt_of_lt_of_le
      (lt_trans (by rw [← vote_time_add_delta]
                    exact Int.lt_add_of_pos_right _ S.E.Δ_pos)
        (support_cutoff_lt_proposal_time_succ S.E (S.hc.opening_slot q + 2)))
      (proposal_time_mono S.E hslots)
  have hcoreAt : ∀ r : Round,
      healingBoundaryTime S q < Protocol.proposal_time S.E (S.hc.opening_slot r) →
      ProposerCarrierAt S rho r →
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon →
      CanonicalRegimeRoundExecutionFactsAt S rho q r :=
    w4ExecutionCoreFactsAt_of_executionPrepared S adm hcom hexec
  have hregime : W4CanonicalRegimeRoundFactsPinGraded S rho q :=
    w4CanonicalRegimeRoundFactsPinGraded_closed S adm hbelow hpostQ
  have hdensity := w4CarrierDensityPinAtPrepared_landed S rho q adm hcom hbelow
    hexec hafterAll hchain hpostQ
  let phase := recurringFinalityPhaseLag (progressLag' gap extra) gap
  let deadline := recurringFinalityDeadline S phase gap
  have hlag : phase ≤ deadline :=
    (recurringFinalityOneHeightLag_bounds S phase gap).1.trans
      (recurringFinalityOneHeightLag_le_deadline S phase gap)
  have hproduce : ∀ start : Round, q ≤ start → S.a (start + phase) ≤ rho.horizon →
      ∃ H : Height, honestHMaxAt S rho (S.a start) < H ∧
        AlreadyCommonFinalizedAtOrAbove S rho q start (start + phase) H := by
    intro start hs hh
    exact commonFinalityAboveFrontier_of_openingCarrierRecurrence_of_pins_preparedFactsGradeCallsite
      S adm hcom hbelow hop hdelay rGST hpost hK hexec hlate hgraded hprogress
      hpostQ hnotLost
      hcoreAt hregime hdensity hfirst hcarrierFinality hanchor hsource hs hh
  have hfinality : RecurringFinalityFrom S rho q deadline ∧
      HonestProposalFinalityFrom S rho q deadline := by
    constructor
    · exact (w4RecurringProjectionPin_landed S rho q phase deadline adm hbelow
        hlag hproduce).toRecurringFinalityFrom
    · refine w4ProposalProjectionPin_landed S rho q deadline adm hcom
        hexec.canonicalSuffixFrom hexec.duty ?_
      intro start hs hh
      have htime := Assembly.a_mono S (Nat.add_le_add_left hlag start)
      obtain ⟨H, hfrontier, s, B, checkpoint, height, hspos, hafter, hprop, hB,
        hrun, hfin, hHle, hheight, hne, hsource', hsourceConf, hconfEnd, hstores⟩ :=
        hproduce start hs (htime.trans hh)
      exact ⟨H, hfrontier, s, B, checkpoint, height, hspos, hafter, hprop, hB,
        hrun, hfin, hHle, hheight, hne, hsource', hsourceConf,
        hconfEnd.trans htime, hstores⟩
  exact ⟨q, hqlo, hqhi, hfinality.1, hfinality.2⟩


/-- Public finalized-chain growth with no hypothesis beyond the setup. -/
theorem finalizedChainGrowth_closed (S : Setup V) :
    Statements.FinalizedChainGrowth S :=
  finalizedChainGrowth_of_uniformRecoveryFinality S
    (w4close_uniformRecoveryFinalityPin S)

/-- Public honest-proposal finalization with no hypothesis beyond the setup. -/
theorem honestProposalFinalization_closed (S : Setup V) :
    Statements.HonestProposalFinalization S :=
  honestProposalFinalization_of_uniformRecoveryFinality S
    (w4close_uniformRecoveryFinalityPin S)

#print axioms finalizedChainGrowth_closed
#print axioms honestProposalFinalization_closed

end HealingSurface

open Internal Execution Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The complete public liveness bundle with no residual premise. -/
theorem liveness_closed (S : Setup V) : Statements.Liveness S := {
  honestProposalConfirmation := Proofs.HealingSurface.honestProposalConfirmation S
  availableChainGrowth := W4.availableChainGrowth S
  stableRecordGrowth := stableRecordGrowth_closed S
  finalizedChainGrowth := Proofs.HealingSurface.finalizedChainGrowth_closed S
  honestProposalFinalization :=
    Proofs.HealingSurface.honestProposalFinalization_closed S
}

/-- The complete public consensus bundle with no residual premise. -/
theorem legacy_consensus_closed (S : Setup V) : Statements.LegacyConsensus S := {
  finality := Proofs.HealingSurface.finalitySafety S
  voteSafetyOfClients := validatorVoteSafety S
  finalizedPrefix := by
    intro rho v t
    have h := NestedOutputs.nestedOutputs_holds S rho v t
    exact Block.preceq_trans h.1 h.2
  nestedOutputs := NestedOutputs.nestedOutputs_holds S
  gstZeroGuarantees := Proofs.HealingSurface.gstZeroGuarantees_of_weakGenesis S
  boundedSafety := boundedSafetyRecovery_closed S
  leakFairness := LeakFairnessL1.leakFairnessL1CurrentProduction S
  stableSafety := stableRecordSafety_closed S
  liveness := liveness_closed S
  asynchronyResilience :=
    NamedOutageClosure.stable_chain_outage_resilience_public S
}

#print axioms liveness_closed
#print axioms legacy_consensus_closed

end Proofs
end DecoupledConsensusModel

end
