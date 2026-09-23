module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.RecoveryActionLiveSourceSplit
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroReorgResilience
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.StoreFinalityConsequences
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryFinalityFilterRetainedVoteConeSeed
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryFreshGradeProvenance
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusInternal.Execution.Run
public import DecoupledConsensusProofs.Execution.Concentration
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterRetention
public import DecoupledConsensusProofs.Protocol.Handlers.FrameFloorBridge
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.RecoveryVoteCone
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryG1AfterCutoffReflection
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeDelivery
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingBoundaryCanonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoverySelectedActionG2VoteCone
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryConeConfirmation
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryProposalConfirmationRead
public import DecoupledConsensusProofs.Protocol.Grades.CleanReadBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryProposalWindow
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HonestMajorityCore
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Protocol.Handlers.StoreFinality
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordClean
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Objects.EmittedHeightBound
public import DecoupledConsensusProofs.Execution.ProgressCanonicality
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Execution.RecoveryActionInterval
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.ChainState.NjGap
public import DecoupledConsensusProofs.Protocol.ChainState.ProgressQuorumCore
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusInternal.Healing
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Execution.FrontierWitnessRelay
public import DecoupledConsensusProofs.Execution.RecoveryFilterSchedule
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingReuse
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradePersistence
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.RecoverySourceProgress
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.Actions
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionActivity
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.ChainState.NamedNjGap
public import DecoupledConsensusProofs.Protocol.ChainState.CheckpointHeights
public import DecoupledConsensusProofs.Execution.RecoveryReadFGClassification
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Execution.CertificateUniqueness
public import DecoupledConsensusProofs.Protocol.Handlers.Staleness
public import DecoupledConsensusModel.Protocol.ChainState
public import DecoupledConsensusProofs.Protocol.Handlers.BlockProcessingDefaults
public import DecoupledConsensusProofs.Protocol.ChainState.TargetedTimeoutBinding
public import DecoupledConsensusProofs.Protocol.ChainState.TimeoutBindingDefaults
public import DecoupledConsensusProofs.Execution.ReleasedCertificateHeightProgress
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressSeedRegime

@[expose] public section

/-!
# Seed obstruction flush support transport

This module isolates the sound confirmation-to-freeze part of the proposed
selective-obstruction flush. A vote that supplies early confirmation support
for a block reaches the next honest frozen support view, unless that view has
already detected an equivocation by the same validator. The complete
confirmation majority therefore remains a strict plain-support majority in
that next view.

The next-slot capture theorem below makes the slot boundary explicit. It does
not persist a branch through later slots. The fresh-anchor classification then
records the exact three sources below an honest previous action carrier:
genuine confirmation, FG-root fallback, or selected grade 2.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]



/-! ## (A) The exact next-slot capture boundary -/


/-! ## (B) Honest provenance and source classification -/



/-
/-- The previous carrier below a selected opening fresh anchor has exactly the
three sources relevant to the next-carrier argument: a genuine confirmation,
the actual FG-root fallback, or a selected grade-2 block. In the selected-G2
case, the persistent common grade is below that selected block.

This is a classification theorem. It does not orient sources from different
honest stores or different slots. -/
theorem openingVoteFreshAnchor_confirmation_or_root_or_selectedG2
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {q: Round} (hq: 0 < q)
    (hpostPrevious: S.E.t_GST ≤ S.a (q - 1))
    (hcut: S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    {Q: Block V} (hforms: GradeFormsAt S rho (q - 1) Q)
    {v: V} (hv: v ∈ rho.honest) {A: Block V}
    (hA: Protocol.fresh_anchor S.E S.hc
      (Proofs.Optimistic.voteDutyStore S rho v
        (S.hc.opening_slot q)).toHealing q = some A):
    (∃ u ∈ rho.honest, ∃ C: Block V,
      GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc
          (Proofs.Optimistic.confStore S rho u (S.hc.opening_slot (q - 1)))
          (S.hc.opening_slot (q - 1)) C ∧
        Block.Preceq A C) ∨
    (∃ u ∈ rho.honest, ∃ R: Block V,
      R = Protocol.get_fg_root
          (Proofs.Optimistic.confStore S rho u
            (S.hc.opening_slot (q - 1))).toHealing.toFG ∧
        Block.Preceq A R) ∨
    ∃ u ∈ rho.honest, ∃ Q₂: Block V,
      Protocol.grade2_block S.E S.hc
          (actionStoreAt S rho u (q - 1)).toHealing (q - 1) = some Q₂ ∧
        Block.Preceq Q Q₂ ∧ Block.Preceq A Q₂:= by
  obtain ⟨u, hu, hAcarrier⟩:=
    openingVoteFreshAnchor_preceq_honestPreviousActionCarrier
      S adm hfb hq hpostPrevious hcut hv hA
  have hsome: (Protocol.grade2_block S.E S.hc
      (actionStoreAt S rho u (q - 1)).toHealing (q - 1)).isSome = true:= by
    refine deepest?_isSome_of_compatible ?_ ⟨Q, ?_⟩
    · intro X hX Y hY
      exact G2_compatible S.E (Finset.mem_filter.mp hX).2
        (Finset.mem_filter.mp hY).2
    · obtain ⟨hQmem, hQG2⟩:= gradeFormsAt_actionStore S hforms hu
      exact Finset.mem_filter.mpr ⟨hQmem, hQG2⟩
  obtain ⟨Q₂, hQ₂⟩:= Option.isSome_iff_exists.mp hsome
  rcases get_sg_vote_preceq_liveConfirmed_or_eq_grade2
      S.E S.hc (actionStoreAt S rho u (q - 1)).toHealing (q - 1) hQ₂ with
    hclear | hselected
  · have hcarrierLive: Block.Preceq (actionSGBlockAt S rho u (q - 1))
        (actionStoreAt S rho u (q - 1)).live_confirmed:= by
      simpa only [actionSGBlockAt] using hclear
    have hAlive: Block.Preceq A
        (actionStoreAt S rho u (q - 1)).live_confirmed:=
      Block.preceq_trans hAcarrier hcarrierLive
    rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot
        S rho u (q - 1) with hgenuine | hroot
    · obtain ⟨C, hC, hClive⟩:= hgenuine
      left
      refine ⟨u, hu, C, hC, ?_⟩
      rw [hClive]
      exact hAlive
    · obtain ⟨R, hRroot, hRlive⟩:= hroot
      right
      left
      refine ⟨u, hu, R, hRroot, ?_⟩
      rw [hRlive]
      exact hAlive
  · right
    right
    have hcarrierEq: actionSGBlockAt S rho u (q - 1) = Q₂:= by
      simpa only [actionSGBlockAt] using hselected
    refine ⟨u, hu, Q₂, hQ₂,
      gradeFormsAt_preceq_selectedActionG2 S hforms hu hQ₂, ?_⟩
    rw [← hcarrierEq]
    exact hAcarrier

/-! ## (C) A common upper ceiling, with all source cases explicit -/

/-- The source classification gives a common ceiling for an opening vote
anchor once genuine confirmations, FG-root fallbacks, and selected grade-2
blocks are each bounded by the same block.

This conclusion is only `A ⪯ Cstar`. It cannot be reversed, and two anchors
which are both below `Cstar` need not be ordered relative to each other. -/
theorem openingVoteFreshAnchor_preceq_commonCeiling
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {q: Round} (hq: 0 < q)
    (hpostPrevious: S.E.t_GST ≤ S.a (q - 1))
    (hcut: S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    {Q Cstar: Block V} (hforms: GradeFormsAt S rho (q - 1) Q)
    (hconfirmation: ∀ u ∈ rho.honest, ∀ C: Block V,
      GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc
          (Proofs.Optimistic.confStore S rho u (S.hc.opening_slot (q - 1)))
          (S.hc.opening_slot (q - 1)) C →
        Block.Preceq C Cstar)
    (hroot: ∀ u ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (Proofs.Optimistic.confStore S rho u
            (S.hc.opening_slot (q - 1))).toHealing.toFG) Cstar)
    (hselected: ∀ u ∈ rho.honest, ∀ Q₂: Block V,
      Protocol.grade2_block S.E S.hc
          (actionStoreAt S rho u (q - 1)).toHealing (q - 1) = some Q₂ →
        Block.Preceq Q Q₂ → Block.Preceq Q₂ Cstar)
    {v: V} (hv: v ∈ rho.honest) {A: Block V}
    (hA: Protocol.fresh_anchor S.E S.hc
      (Proofs.Optimistic.voteDutyStore S rho v
        (S.hc.opening_slot q)).toHealing q = some A):
    Block.Preceq A Cstar:= by
  rcases openingVoteFreshAnchor_confirmation_or_root_or_selectedG2
      S adm hfb hq hpostPrevious hcut hforms hv hA with
    hgenuine | hrootSource | hgrade2
  · obtain ⟨u, hu, C, hC, hAC⟩:= hgenuine
    exact Block.preceq_trans hAC (hconfirmation u hu C hC)
  · obtain ⟨u, hu, R, hReq, hAR⟩:= hrootSource
    exact Block.preceq_trans hAR (by
      rw [hReq]
      exact hroot u hu)
  · obtain ⟨u, hu, Q₂, hQ₂, hQQ₂, hAQ₂⟩:= hgrade2
    exact Block.preceq_trans hAQ₂ (hselected u hu Q₂ hQ₂ hQQ₂)

/-! ## (D) Persistence of the common grade -/

/-- A thin common grade persists through a bounded action window when every
honest action read stays at the same gate-off frontier. This is the gate-off
specialization of the L5 persistence induction; activity at each successor
read follows from `frontierBlock_filtered_at_healStoreAt_of_gateOff`. -/
theorem gradeFormsAt_persists_through_gateOffActionWindow
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {r₀ q: Round} {Q: Block V}
    (hseed: GradeFormsAt S rho r₀ Q)
    (hQrun: RunBlock S rho Q)
    (hQheight: M - 1 ≤ (derived_state S.E S.cfg Q).h)
    (hM: 1 ≤ M)
    (hpost: S.E.t_GST ≤ S.a r₀)
    (hendpoint: S.a q ≤ rho.horizon)
    (hfrontier: ∀ k, r₀ ≤ k → k ≤ q → ∀ w ∈ rho.honest,
      (healStoreAt S rho w k).h_max = M)
    (hgateOff: ∀ k, r₀ ≤ k → k ≤ q → ∀ w ∈ rho.honest,
      (healStoreAt S rho w k).h_j + 2 ≤ M):
    ∀ k, r₀ ≤ k → k ≤ q → GradeFormsAt S rho k Q:= by
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hactive: ∀ k, r₀ ≤ k → k ≤ q → ∀ w ∈ rho.honest,
      Q ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w k).toFG:= by
    intro k hr₀k hkq w hw
    have hread: S.a k ≤ rho.horizon:=
      ((action_strictMono S).monotone hkq).trans hendpoint
    have hprocessed: Q ∈ (healStoreAt S rho w k).T:=
      gradeFormsAt_processedAtRead_of_action_le S adm hseed hw
        ((action_strictMono S).monotone hr₀k)
    exact frontierBlock_filtered_at_healStoreAt_of_gateOff
      S adm hsb hw hread hprocessed hQrun hQheight hM
        (hfrontier k hr₀k hkq w hw) (hgateOff k hr₀k hkq w hw)
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hr₀k hkq
      rcases eq_or_lt_of_le hr₀k with hEq | hlt
      · subst k
        exact hseed
      · cases k with
        | zero => exact (Nat.not_lt_zero _ hlt).elim
        | succ k =>
            have hr₀k': r₀ ≤ k:= Nat.le_of_lt_succ hlt
            have hkq': k ≤ q:= (Nat.le_succ k).trans hkq
            have hprev: GradeFormsAt S rho k Q:=
              ih k (Nat.lt_succ_self k) hr₀k' hkq'
            have hpost': S.E.t_GST ≤ S.a k:=
              hpost.trans ((action_strictMono S).monotone hr₀k')
            have hcut: S.hc.Γ_neg1 S.E.Δ (k + 1) ≤ rho.horizon:=
              (le_of_lt (next_Γ_neg1_lt_action S k)).trans
                (((action_strictMono S).monotone hkq).trans hendpoint)
            exact gradeFormsAt_succ_of_gradeFormsAt_and_next_active
              S adm hfb hprev hpost' hcut
                (hactive (k + 1)
                  (by simpa only [Nat.succ_eq_add_one] using Nat.le_of_lt hlt)
                  hkq)

 -/

/-! ## (D) Persistence of the common grade, over the named grade -/


/-- **The named common grade persists through a gate-off window**, and it keeps
its block active at each round's own action read.

earlier's route of `gradeFormsAt_persists_through_gateOffActionWindow`, over
`NamedGradeFormsAt`. Two things change, and neither adds a protocol premise.

The gate-off input is a window over READS rather than over round action
stores. The named successor step also reads the next round's G2-domain read
`Gamma[-1](k+1)`, which is not a round action time, so the round-indexed form
of the premise cannot reach it. Every caller already holds the read window,
and the round action reads are instances of it.

The action-read activity travels with the grade in the conclusion. It is what
the named successor step consumes at each round, and it is produced from the
grade and the same window, so carrying the two together is the induction
invariant rather than an extra obligation.

`hr0` is the round positivity that the named clean-read producer requires; a
seed window never starts at round zero. -/
theorem namedGradeFormsAt_persists_through_gateOffActionWindow
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {r0 q : Round} {Q : NamedBlock V}
    (hr0 : 0 < r0)
    (hseed : NamedGradeFormsAt S rho r0 Q.erase)
    (hQrun : RunBlock S rho Q)
    (hQheight : M - 1 ≤ (Protocol.derive_named S.E S.cfg Q).h)
    (hM : 1 ≤ M)
    (hpost : S.E.t_GST ≤ S.a r0)
    (hendpoint : S.a q ≤ rho.horizon)
    (hframe : ∀ read : Time, S.a r0 ≤ read → read ≤ S.a q →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_max = M ∧
          (rho.storeBeforeTime S w read).h_j + 2 ≤ M) :
    ∀ k, r0 ≤ k → k ≤ q →
      NamedGradeFormsAt S rho k Q.erase ∧
        ∀ w ∈ rho.honest,
          Q.erase ∈ PhaseGrades.filteredTree (actionReadAt S rho w k) := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  -- the protected block is retained by the finality filter at every read of
  -- the window that the grade has already reached
  have hretain : ∀ (k : Round), NamedGradeFormsAt S rho k Q.erase →
      ∀ read : Time, S.a k ≤ read → S.a r0 ≤ read → read ≤ S.a q →
      ∀ w ∈ rho.honest,
        Q.erase ∈ Protocol.get_filtered_block_tree
          (rho.storeBeforeTime S w read).toHealing.toFG := by
    intro k hforms read hread hlo hhi w hw
    have hprocessed : Q.erase ∈ (rho.storeBeforeTime S w read).T :=
      namedGradeFormsAt_processedAtRead_of_action_le S adm hforms hw hread
    have hfr := hframe read hlo hhi w hw
    exact frontierBlock_filtered_of_gateOff S adm hsb hw (hhi.trans hendpoint)
      hprocessed rfl hQrun hQheight hM hfr.1 hfr.2
  -- the read-local action activity, from the grade and the same window
  have hactivity : ∀ (k : Round), r0 ≤ k → k ≤ q →
      NamedGradeFormsAt S rho k Q.erase →
      ∀ w ∈ rho.honest,
        Q.erase ∈ PhaseGrades.filteredTree (actionReadAt S rho w k) := by
    intro k hlo hhi hforms w hw
    refine namedGradeFormsAt_actionStore_of_window S hforms hw ?_
    exact hretain k hforms (S.a k) le_rfl (Assembly.a_mono S hlo)
      (Assembly.a_mono S hhi) w hw
  have hgrade : ∀ k, r0 ≤ k → k ≤ q → NamedGradeFormsAt S rho k Q.erase := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hr0k hkq
        rcases eq_or_lt_of_le hr0k with hEq | hlt
        · subst k
          exact hseed
        · cases k with
          | zero => exact (Nat.not_lt_zero _ hlt).elim
          | succ k =>
              have hr0k' : r0 ≤ k := Nat.le_of_lt_succ hlt
              have hkq' : k ≤ q := (Nat.le_succ k).trans hkq
              have hprev : NamedGradeFormsAt S rho k Q.erase :=
                ih k (Nat.lt_succ_self k) hr0k' hkq'
              have hkpos : 0 < k := lt_of_lt_of_le hr0 hr0k'
              have hpostk : S.E.t_GST ≤ S.a k :=
                hpost.trans (Assembly.a_mono S hr0k')
              have hloNext : S.a r0 ≤ S.a (k + 1) :=
                Assembly.a_mono S (hr0k'.trans (Nat.le_succ k))
              have hhiNext : S.a (k + 1) ≤ S.a q := Assembly.a_mono S hkq
              have hcut : S.hc.Γ_neg1 S.E.Δ (k + 1) ≤ rho.horizon :=
                (le_of_lt (next_Γ_neg1_lt_action S k)).trans
                  (hhiNext.trans hendpoint)
              have hcutLo : S.a k ≤ S.hc.Γ_neg1 S.E.Δ (k + 1) :=
                le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
                  (action_add_delta_le_next_Γ_neg1 S k)
              have hcutHi : S.hc.Γ_neg1 S.E.Δ (k + 1) ≤ S.a q :=
                (le_of_lt (next_Γ_neg1_lt_action S k)).trans hhiNext
              have hactiveNext : ∀ w ∈ rho.honest,
                  Q.erase ∈ Protocol.get_filtered_block_tree
                    (healStoreAt S rho w (k + 1)).toFG := by
                intro w hw
                have h := hretain k hprev (S.a (k + 1))
                  (Assembly.a_mono S (Nat.le_succ k)) hloNext hhiNext w hw
                simpa only [healStoreAt, Run.storeBeforeTime] using h
              have hdomain : ∀ w ∈ rho.honest,
                  Q.erase ∈ PhaseGrades.filteredTree
                    (relativeG2Read S rho (k + 1) w) := by
                refine activeDomain_of_retainedAtDomainRead S ?_
                intro x hx
                have hdom : DecoupledConsensusModel.Protocol.domain S.E S.hc (k + 1) .g2 =
                    S.hc.Γ_neg1 S.E.Δ (k + 1) :=
                  (gammaNeg1_eq_domain_g2_succ S k).symm
                rw [hdom]
                exact hretain k hprev (S.hc.Γ_neg1 S.E.Δ (k + 1)) hcutLo
                  ((Assembly.a_mono S hr0k').trans hcutLo) hcutHi x hx
              exact namedGradeFormsAt_of_cleanActionRead S adm hmajority
                (cleanActionReadFor_of_namedGradeFormsAt_and_next_active
                  S adm hkpos hprev hpostk hcut
                  (hactivity k hr0k' hkq' hprev) hactiveNext hdomain)
  exact fun k hlo hhi => ⟨hgrade k hlo hhi, hactivity k hlo hhi (hgrade k hlo hhi)⟩

#print axioms namedGradeFormsAt_persists_through_gateOffActionWindow

end HealingSurface
end Proofs

end DecoupledConsensusModel

end
