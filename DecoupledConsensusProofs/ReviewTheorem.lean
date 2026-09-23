module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusStatements
public import DecoupledConsensusInternal.Legacy.Internal
public import DecoupledConsensusProofs.Protocol.Grades.StableCoverageConsumer
public import DecoupledConsensusProofs.Execution.GSTZeroSafetyClosedNamed
public import DecoupledConsensusProofs.Execution.VoteSafetyPreparedV4
public import DecoupledConsensusProofs.Protocol.ChainState.WholeRunFinalitySafety
public import DecoupledConsensusProofs.Protocol.ChainState.ValidatorVoteSafety
public import DecoupledConsensusProofs.Protocol.ChainState.LeakFairnessL1
public import DecoupledConsensusProofs.Protocol.Handlers.NestedOutputs
public import DecoupledConsensusProofs.Execution.BoundedSafetyRecoveryPreparedV4Window
public import DecoupledConsensusProofs.Execution.StableRecordSafetyPreparedV4Window
public import DecoupledConsensusProofs.Execution.RecoveryWindowClosure
public import DecoupledConsensusProofs.Execution.W4StableRecordGrowthClosed
public import DecoupledConsensusProofs.Generic.W4FinalityClosed
public import DecoupledConsensusProofs.Bridge.StandardVocabulary
public import DecoupledConsensusProofs.Bridge.StableIncludedAnySlot
public import DecoupledConsensusProofs.Bridge.StableIncludedFresh
public import DecoupledConsensusProofs.Bridge.GenericVocabulary
public import DecoupledConsensusProofs.Bridge.GenericRegimes
public import DecoupledConsensusProofs.Bridge.FinalizedLive
public import DecoupledConsensusProofs.Generic.Lemmas

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Kernel-checked implementation of the final review statements

The manual review target is `DecoupledConsensusStatements.Instantiation`, not the
proofs or helper statements imported here. This file connects that target to
the existing checked proofs without adding assumptions.
-/

namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The public asynchrony-resilience field, proved without residual premises. -/
theorem asynchronyResilience (S : Setup V) :
    Internal.NamedStableChainOutage.StableChainOutageResilience S :=
  NamedOutageClosure.stable_chain_outage_resilience_public S

#print axioms asynchronyResilience


/-- The public GST-zero guarantees field: safety and liveness from the weak-genesis
    premises, with no residual premise (closed, standard axioms). -/
theorem gstZeroGuarantees (S : Setup V) :
    ∀ rho, WeakGenesis S rho → GSTZeroGuarantees S rho :=
  Proofs.HealingSurface.gstZeroGuarantees_of_weakGenesis S

#print axioms gstZeroGuarantees


/-- The public finality-safety field. -/
theorem finalitySafety (S : Setup V) : FinalitySafety S :=
  Proofs.HealingSurface.finalitySafety S

#print axioms finalitySafety

/-- Honest validators following the validator-client signing rules are never
slashable, for actual emissions or honest-attributed store evidence. -/
theorem voteSafetyOfClients (S : Setup V) : ValidatorVoteSafety S :=
  validatorVoteSafety S

#print axioms voteSafetyOfClients

/-- Current-production L1 leak fairness under schedule well-formedness,
run-scoped root collision freedom, and the whole-run slashable bound. No
delivery, vote-target validity, authenticity, synchrony, participation, or
faulty-weight premise is used. -/
theorem leakFairness (S : Setup V) :
    LeakFairness.LeakFairnessL1CurrentProduction S :=
  LeakFairnessL1.leakFairnessL1CurrentProduction S

#print axioms leakFairness

/-- The public nested-outputs field: finalized ⪯ stable ⪯ confirmed at every read. -/
theorem nestedOutputs (S : Setup V) : Internal.NestedOutputs S :=
  NestedOutputs.nestedOutputs_holds S

#print axioms nestedOutputs

/-- The public finalized-prefix field, from the nested outputs. -/
theorem finalizedPrefix (S : Setup V) : ∀ rho, FinalizedPrefixConfirmed S rho := by
  intro rho v t
  have h := NestedOutputs.nestedOutputs_holds S rho v t
  exact Block.preceq_trans h.1 h.2

#print axioms finalizedPrefix


/-- Bounded safety recovery when the recovery window satisfies
`D + 2L + max (1 + η_SG) (gap + 3) ≤ n`. -/
theorem boundedSafetyRecovery_window (S : Setup V)
    (hwindow : ∀ rho rGST gap extra n,
      Statements.StrongRecoveryPrefix S rho rGST gap extra n →
      Proofs.HealingSurface.fgSafetyProgressDeadline S rho rGST gap extra +
        2 * Proofs.HealingSurface.progressLag' gap extra +
        max (1 + S.hc.η_SG) (gap + 3) ≤ n) :
    Statements.BoundedSafetyRecovery S :=
  boundedSafetyRecovery_of_window S hwindow

#print axioms boundedSafetyRecovery_window

/-- Stable-record safety under the same corrected recovery window. -/
theorem stableRecordSafety_window (S : Setup V)
    (hwindow : ∀ rho rGST gap extra n,
      Statements.StrongRecoveryPrefix S rho rGST gap extra n →
      Proofs.HealingSurface.fgSafetyProgressDeadline S rho rGST gap extra +
        2 * Proofs.HealingSurface.progressLag' gap extra +
        max (1 + S.hc.η_SG) (gap + 3) ≤ n) :
    Statements.StableRecordSafety S :=
  stableRecordSafety_holds_of_window S hwindow

#print axioms stableRecordSafety_window


/-- The public bounded-safety-recovery field under the closed recovery window. -/
theorem boundedSafety (S : Setup V) : Statements.BoundedSafetyRecovery S :=
  boundedSafetyRecovery_closed S

#print axioms boundedSafety

/-- The public stable-record-safety field, pin-free (same window). -/
theorem stableSafety (S : Setup V) : Statements.StableRecordSafety S :=
  stableRecordSafety_closed S

#print axioms stableSafety

/-! The complete public stable-record growth field. -/
theorem stableRecordGrowth (S : Setup V) :
    Statements.StableRecordGrowth S :=
  stableRecordGrowth_closed S

#print axioms stableRecordGrowth

/-- Key internal height-progress statement.

In protocol terms, after the selected post-GST round, every covered recurrence
window produces a strict increase of the maximum height held by honest nodes
within `Proofs.HealingSurface.progressLag' gap delayExtra` rounds. Its premises are:

* `TimeoutDelayBound S delayExtra`;
* `Admissible S rho`, whose fields are `ExecutionValid S rho`,
  `PartialSynchrony S rho`, and full honest participation at covered actions;
* an honest strict majority in every Goldfish committee;
* faulty weight below one third of the electorate;
* `t_GST ≤ S.a rGST`; and
* `MultiProposerRecurrence S rho gap`.

This result is not a field of `Statements.Consensus`. Recovery proofs use it to
cross successive height frontiers, establish the recovered canonical suffix,
and then discharge the available-chain and finality liveness assemblies. -/
def HeightProgress (S : Setup V) : Prop :=
  ∀ {delayExtra : Nat}, TimeoutDelayBound S delayExtra →
    ∀ {gap : Round} {rho : Run V} {rGST : Round},
      Admissible S rho →
      HonestCommittees S rho.honest →
      BelowOneThird S rho.honest →
      S.E.t_GST ≤ S.a rGST →
      MultiProposerRecurrence S rho gap →
      EventualHeightProgressFrom S rho rGST
        (Proofs.HealingSurface.progressLag' gap delayExtra)

/-- The checked proof of `HeightProgress`. See the definition for the protocol
meaning, complete premise list, and its role between safety recovery and the
public liveness theorems. -/
theorem heightProgress (S : Setup V) : HeightProgress S := by
  intro delayExtra hdelay gap rho rGST adm hcom hbelow hpost hrec
  exact Proofs.HealingSurface.heightProgress_public S hdelay adm hcom hbelow hpost hrec

#print axioms heightProgress

/-- Vote-source safety after recovery: after the safety cut, every honest input to the finality gadget, SG vote and confirmation stays below the honest Goldfish vote heads. Internal building block of the record results; not a bundle field. -/
theorem voteSafety (S : Setup V) : VoteSafetyAfterRecovery S :=
  Proofs.HealingSurface.voteSafety S

#print axioms voteSafety

/-! The public honest-proposal confirmation field. -/
theorem honestProposalConfirmation (S : Setup V) :
    Statements.HonestProposalConfirmation S :=
  Proofs.HealingSurface.honestProposalConfirmation S

#print axioms honestProposalConfirmation

/-! The public available-chain growth field. -/
theorem availableChainGrowth (S : Setup V) :
    Statements.AvailableChainGrowth S :=
  W4.availableChainGrowth S

#print axioms availableChainGrowth

/-! The public finalized-chain growth field. -/
theorem finalizedChainGrowth (S : Setup V) :
    Statements.FinalizedChainGrowth S :=
  Proofs.HealingSurface.finalizedChainGrowth_closed S

#print axioms finalizedChainGrowth

/-! The public honest-proposal finalization field. -/
theorem honestProposalFinalization (S : Setup V) :
    Statements.HonestProposalFinalization S :=
  Proofs.HealingSurface.honestProposalFinalization_closed S

#print axioms honestProposalFinalization

/-! The complete public liveness bundle. -/
theorem liveness (S : Setup V) : Statements.Liveness S :=
  liveness_closed S

#print axioms liveness

/-! The historical bundle remains available to the bridge as proof-side
vocabulary. -/
theorem legacyConsensus (S : Setup V) : Statements.LegacyConsensus S :=
  legacy_consensus_closed S

#print axioms legacyConsensus

/-! The internal surface records the protocol reads that are deliberately not
part of the standard public bundle. -/
theorem reviewedInternal (S : Setup V) : Statements.Internal S := {
  confirmationRecordSafety := fun rho h =>
    let g := gstZeroGuarantees S rho h
    ⟨g.availableChain.1, g.availableChain.2.1⟩
  stableRecordCanonical := fun rho h => (legacyConsensus S).stableSafety.gstZero rho h
  exactConfirmation := fun rho h =>
    (gstZeroGuarantees S rho h).availableChain.2.2
  handoverSeed := boundedSafety S
  phaseShiftInternals := boundedSafety S
  gstZeroInternals := fun rho h => gstZeroGuarantees S rho h
  finalityChains :=
    ⟨fun rho h => (legacyConsensus S).finality.runAccountable rho h,
      (legacyConsensus S).finality.agreement⟩
  outageInternals := (legacyConsensus S).asynchronyResilience
  voteSourceSafety := voteSafety S
}

#print axioms reviewedInternal

/-! The named healing decomposition. The first theorem exposes the existing
settled-bootstrap predicate; the second packages the public Available
conclusions from the recovered-state wrapper and sleepy regime. -/
theorem recoveryProducesHealedState (S : Setup V) :
    ∀ source t₀ gap extra,
      Statements.RecoveryRegime S (Statements.«instance» S)
        (Statements.ourConstants S) source t₀ gap extra →
      ∃ rGST n m P, n + gap = Statements.Instantiation.recoveryRound S t₀ gap extra ∧
        n ≤ m ∧ m ≤ n + gap ∧
        Internal.ProposerCarrierAt S source m ∧
        Statements.Instantiation.proposedBlockAt S source
            (S.hc.opening_slot m) = some P ∧
        ∃ cap : Height,
          Proofs.HealingSurface.Handover.SettledBootstrapPreparedV4 S source
            (Proofs.HealingSurface.fgSafetyProgressDeadline S source rGST gap extra + 1)
            (Proofs.HealingSurface.fgSafetyProgressDeadline S source rGST gap extra +
              2 * Proofs.HealingSurface.progressLag' gap extra + 1)
            (S.hc.opening_slot m) P cap := by
  intro source t₀ gap extra hrec
  obtain ⟨rGST, n, hstrong, hsum⟩ :=
    strongRecovery_of_recovery S hrec
  have hwindow := window_of_strongRecoveryPrefix S source rGST gap extra n hstrong
  have hn : Proofs.HealingSurface.fgSafetyProgressDeadline S source rGST gap extra +
      2 * Proofs.HealingSurface.progressLag' gap extra + 1 + S.hc.η_SG ≤ n := by
    have hmax : 1 + S.hc.η_SG ≤ max (1 + S.hc.η_SG) (gap + 3) :=
      le_max_left _ _
    have hstep := (Nat.add_le_add_left hmax
      (Proofs.HealingSurface.fgSafetyProgressDeadline S source rGST gap extra +
        2 * Proofs.HealingSurface.progressLag' gap extra)).trans hwindow
    simpa [Nat.add_assoc] using hstep
  have hsourceHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (n + gap)) ≤ source.horizon := by
    rw [Proofs.HealingSurface.opening_confirmation_time_eq_action, hstrong.horizon]
  obtain ⟨m, hmlo, hmhi, hcarrier, P, hP, hboot⟩ :=
    Proofs.HealingSurface.Handover.settledBootstrap_of_strong_preparedV4
      S hstrong.admissible hstrong.committees hstrong.belowThird hstrong.timeout
      hstrong.recurrence hstrong.postGST hn hsourceHor
  exact ⟨rGST, n, m, P, hsum, hmlo, hmhi, hcarrier, hP,
    ⟨_, hboot.1⟩⟩

theorem concreteConsensus (S : Setup V) : Statements.Instantiation.Consensus S := by
  let gC : Internal.Output V := Protocol.get_confirmed
  let gS : Internal.Output V := Protocol.get_stable
  let gF : Internal.Output V := fun st => st.F
  refine {
    constants := constants_valid S
    nested := ?_
    certificatesAccountable := ?_
    finalizedAccountable := ?_
    finalizedMonotone := ?_
    honestNeverSlashed := ?_
    finalizedSafe := ?_
    available := ?_
    confirmedLive := ?_
    stableLive := ?_
    stableIncludedFast := stableIncludedFast_concrete S
    finalized := ?_
    stableAsynchronyResilient := ?_ }
  · intro rho
    refine { finalizedBelowStable := ?_, stableBelowConfirmed := ?_ }
    · simpa [gC, gS, gF, Instantiation.interface, Statements.instance] using
        (prefix_iff S rho gF gS).mpr (unconditional_finalizedBelowStable S rho)
    · simpa [gC, gS, gF, Instantiation.interface, Statements.instance] using
        (prefix_iff S rho gS gC).mpr (unconditional_stableBelowConfirmed S rho)
  · intro c c' T T' hcf hfin hfin'
    simpa [Block.Compatible, Instantiation.interface, Statements.instance] using
      unconditional_pureFinality S c c' T T' hcf hfin hfin'
  · intro rho hwell
    have hstd := unconditional_finalizedAccountable S rho
      (finalityExecution_of_generic_runWellFormed S rho hwell)
    simpa [gF, Instantiation.interface, Statements.instance] using
      (accountablyConsistentFrom_iff S rho gF gF 0).mpr hstd
  · intro rho hwell
    simpa [Instantiation.interface, Statements.instance] using
      accountable_finalizedMonotone S rho hwell
  · intro rho hexec v hv hslashes
    have hsch := voteSafetySchedule_of_generic_unforgeableRun S rho hexec
    have hauth := attestationAuthenticity_of_generic_unforgeableRun S rho hexec
    rcases hslashes with ⟨u, u', t, t', hs⟩
    have hsafe := (unconditional_voteSafetyOfClients S).attributed
      rho hsch hauth u u' t t' v hv
    apply hsafe
    simpa [Instantiation.interface] using hs
  · intro rho hreg
    simpa [gF, Instantiation.interface, Statements.instance] using
      (agreeFrom_iff S rho gF 0).mpr
        (accountable_finalizedAgree S rho
          (finalityExecution_of_generic_runWellFormed S rho hreg.toRunWellFormed)
          (slashableBound_of_generic S rho hreg.slashableBound))
  · intro rho t₀ hsleep
    have hs := sleepyRegime_of_generic S rho t₀ hsleep
    have hr := recoveredBy_of_generic S rho t₀ hsleep.start
    refine {
      confirmedSafe := ?_
      confirmedIncluded := ?_
      stableSafe := ?_
      stableIncluded := ?_ }
    · simpa [gC, Instantiation.interface, Statements.instance] using
        (safeFrom_iff S rho gC t₀).mpr
          (available_confirmedSafe S rho t₀ hs hr)
    · exact included_of_named S
        (available_confirmedIncluded S rho t₀ hs hr)
    · simpa [gS, Instantiation.interface, Statements.instance] using
        (safeFrom_iff S rho gS t₀).mpr
          (available_stableSafe S rho t₀ hs hr)
    · simpa [stableInclusionDelay_eq_constant] using
        included_of_named S (available_stableIncluded_any S rho t₀ hs hr)
  · intro rho t₀ gap hlive
    have hs := sleepyRegime_of_generic S rho t₀ hlive.toSleepyRegime
    have hr := recoveredBy_of_generic S rho t₀ hlive.start
    have hsafe := available_confirmedSafe S rho t₀ hs hr
    have hmono : Statements.Generic.MonotoneFrom
        (DecoupledConsensusModel.Execution.spec S) rho
        (Statements.Instantiation.interface S).confirmed t₀ := by
      simpa [gC, Instantiation.interface, Statements.instance] using
        ((safeFrom_iff S rho gC t₀).mpr hsafe).monotone
    have hfuture := noFutureRead_confirmed S rho hlive.toSleepyRegime.execution
    have hincl : Statements.Generic.IncludedFrom
        (DecoupledConsensusModel.Execution.spec S) (Statements.Instantiation.interface S) rho
        (Statements.Instantiation.interface S).confirmed t₀
          (Statements.Instantiation.constants S).confirmationDelay := by
      simpa [gC, Instantiation.interface, Statements.instance] using
        (included_of_named S
          (available_confirmedIncluded S rho t₀ hs hr))
    have ht₀ : 0 ≤ t₀ := S.E.t_GST_nonneg.trans hlive.toSleepyRegime.gst
    have hD : 0 ≤ (Statements.Instantiation.constants S).confirmationDelay := by
      dsimp [Statements.Instantiation.constants]
      exact mul_nonneg (by norm_num) S.E.Δ_pos.le
    have hperiod : 0 < (Statements.Instantiation.constants S).period := by
      simpa [Statements.Instantiation.constants] using concretePeriod_pos S
    have hlive' := DecoupledConsensusModel.Proofs.Generic.liveFrom_of_includedFrom
      hmono hfuture hincl hlive.recurrence ht₀ hD hperiod
      (fun hAB hBC => Block.preceq_trans hAB hBC)
      (fun A => Block.preceq_self A)
      (fun hAC hBC => Block.compatible_of_preceq_common hAC hBC)
    simpa [gC, Instantiation.interface, Statements.instance] using hlive'
  · intro rho t₀ gap hlive
    have hs := sleepyRegime_of_generic S rho t₀ hlive.toSleepyRegime
    have hr := recoveredBy_of_generic S rho t₀ hlive.start
    have hsafe := available_stableSafe S rho t₀ hs hr
    have hmono : Statements.Generic.MonotoneFrom
        (DecoupledConsensusModel.Execution.spec S) rho
        (Statements.Instantiation.interface S).stable t₀ := by
      simpa [gS, Instantiation.interface, Statements.instance] using
        ((safeFrom_iff S rho gS t₀).mpr hsafe).monotone
    have hfuture := noFutureRead_stable S rho hlive.toSleepyRegime.execution
    have hincl : Statements.Generic.IncludedFrom
        (DecoupledConsensusModel.Execution.spec S) (Statements.Instantiation.interface S) rho
        (Statements.Instantiation.interface S).stable t₀
          (Statements.Instantiation.constants S).stableInclusionDelay := by
      simpa [stableInclusionDelay_eq_constant] using
        included_of_named S (available_stableIncluded_any S rho t₀ hs hr)
    have ht₀ : 0 ≤ t₀ := S.E.t_GST_nonneg.trans hlive.toSleepyRegime.gst
    have hperiod : 0 < (Statements.Instantiation.constants S).period := by
      simpa [Statements.Instantiation.constants] using concretePeriod_pos S
    have hD : 0 ≤ (Statements.Instantiation.constants S).stableInclusionDelay := by
      dsimp [Statements.Instantiation.constants]
      have hΔ : (0 : Time) ≤ S.E.Δ := S.E.Δ_pos.le
      have hL : (0 : Time) ≤ S.a 1 - S.a 0 := hperiod.le
      positivity
    have hlive' := DecoupledConsensusModel.Proofs.Generic.liveFrom_of_includedFrom
      hmono hfuture hincl hlive.recurrence ht₀ hD hperiod
      (fun hAB hBC => Block.preceq_trans hAB hBC)
      (fun A => Block.preceq_self A)
      (fun hAC hBC => Block.compatible_of_preceq_common hAC hBC)
    simpa [Statements.Instantiation.constants] using hlive'
  · intro rho t₀ gap hreg
    refine { finalizedIncluded := ?_, finalizedLive := ?_ }
    · have hlegacy := finalityRegime_of_generic S rho t₀ gap hreg
      have hhor : t₀ + (Statements.ourConstants S).finalityStartup
          gap S.extraRounds ≤ rho.horizon := by
        simpa [Statements.Instantiation.constants, Statements.ourConstants] using
          hreg.longEnough
      exact included_of_named S
        (finalized_included S rho t₀ gap S.extraRounds hlegacy hhor)
    · exact finalized_growth S rho t₀ gap hreg hreg.longEnough
  · intro rho T b₀ b₁ hreg
    intro v hv B hpre t ht htime
    have hstd := outage_stablePersists S rho b₀ b₁ T v B
      (outageRegime_of_generic S rho T b₀ b₁ hreg)
      (slashableBound_of_generic S rho hreg.slashableBound) hv
      (by simpa [gS, Instantiation.interface, Statements.instance] using
        (readAt_eq S rho gS v T ▸ hpre))
      (by simpa [Statements.Instantiation.constants, Statements.ourConstants, add_assoc] using
        hreg.window.1)
      (by simpa [Statements.Instantiation.constants, Statements.ourConstants] using
        hreg.window.2.1)
      (by simpa [Statements.Instantiation.constants, Statements.ourConstants] using
        hreg.window.2.2)
    exact (inBy_iff S rho gS B t).mpr (hstd t ht htime)

#print axioms recoveryProducesHealedState
#print axioms concreteConsensus

end Proofs
end DecoupledConsensusModel

end
