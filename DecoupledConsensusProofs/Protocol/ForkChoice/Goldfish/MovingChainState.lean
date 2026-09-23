module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
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
public import DecoupledConsensusProofs.Generic.FixedHeightRootAdmission
public import DecoupledConsensusProofs.Generic.PrefixFGSelectorWitness
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HonestMajorityCore
public import DecoupledConsensusProofs.Protocol.Handlers.StoreFinality
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordClean
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Objects.EmittedHeightBound
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Execution.ProgressCanonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.RecoveryVoteCone
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusInternal.Execution.Run
public import DecoupledConsensusProofs.Execution.Concentration
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.ChainState.NjGap
public import DecoupledConsensusProofs.Protocol.ChainState.ProgressQuorumCore
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusInternal.Healing
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
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGProposalLifecycle
public import DecoupledConsensusProofs.Objects.HealingDirectedHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeiling
public import DecoupledConsensusInternal.Definitions.NamedDutyReads

@[expose] public section

/-! # Moving-frontier chain state
This module isolates the event-indexed state needed by the regime-free healing
route. The endpoint is a function of the run-event index. Numeric frontier
changes do not reset the history cursor or the previous-frontier bound.
The state deliberately records proposal-chain observations, genuine
confirmations, SG action carriers, and attestation outputs as separate facts.
This prevents a later fold from treating a numeric `h_max` increase as an exit
or from hiding a missing source-direction argument in a per-read callback.
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


/-- Every genuine confirmation selected at event `i` is below `B`. -/
def GenuineConfirmationsPreceqAtIndex
    (S : Setup V) (rho : Run V) (i : Nat) (B : Block V) : Prop :=
  ∀ v ∈ rho.honest, ∀ C : Block V,
    (∃ s : Slot,
      rho.events[i]? = some
        (Event.tick v (Protocol.confirmation_time S.E s)) ∧
      GenuineConfirmation (contract := Protocol.GradeContract.current)
        S.E S.hc (Proofs.Optimistic.confStore S rho v s) s C) →
      Block.Preceq C B

/-- Every named genuine confirmation selected at event `i` is below `B`. -/
def NamedGenuineConfirmationsPreceqAtIndex
    (S : Setup V) (rho : Run V) (i : Nat) (B : Block V) : Prop :=
  ∀ (v : V), v ∈ rho.honest → ∀ C : Block V,
    (∃ s : Slot,
      rho.events[i]? = some
        (Event.tick v (Protocol.confirmation_time S.E s)) ∧
      GenuineConfirmationWith
        (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho v s) s C) →
      Block.Preceq C B

/-- Every honest Section 7 SG carrier emitted at event `i` is below `B`. -/
def HonestActionSGCarriersPreceqAtIndex
    (S : Setup V) (rho : Run V) (i : Nat) (B : Block V) : Prop :=
  ∀ {v : V} {q : Round} {a : NamedAttestation V},
    v ∈ rho.honest →
      rho.events[i]? = some (Event.tick v (S.a q)) →
      Object.attest a ∈
        NamedRun.emittedAt S rho i v (S.a q) →
      Block.Preceq (actionSGBlockAt S rho v q) B


/-
set_option maxHeartbeats 800000 in
/-- A common action grade puts the exact SG carrier below the genuine
confirmation selected at that action. This is independent of the current FG
root regime and of numeric frontier changes. -/
theorem actionSGBlockAt_preceq_genuine_of_gradeFormsAt
    (S: Setup V) {rho: Run V} {q: Round} {B D: Block V}
    (hforms: GradeFormsAt S rho q B) {v: V} (hv: v ∈ rho.honest)
    (hD: GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc
      (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))
      (S.hc.opening_slot q) D):
    Block.Preceq (actionSGBlockAt S rho v q) D:= by
  let ast:= actionStoreAt S rho v q
  obtain ⟨hBactive, hBG2⟩:= gradeFormsAt_actionStore S hforms hv
  have hsome:
      (Protocol.grade2_block S.E S.hc ast.toHealing q).isSome = true:= by
    refine deepest?_isSome_of_compatible ?_
      ⟨B, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · intro X hX Y hY
      exact G2_compatible S.E (Finset.mem_filter.mp hX).2
        (Finset.mem_filter.mp hY).2
    · simpa only [ast] using hBactive
    · simpa only [ast] using hBG2
  obtain ⟨Q₂, hQ₂⟩:= Option.isSome_iff_exists.mp hsome
  obtain ⟨A, hAaction⟩:= Option.isSome_iff_exists.mp
    (fresh_anchor_isSome_of_grade2 S.E hQ₂)
  have hanchorEq:
      Protocol.fresh_anchor S.E S.hc ast.toHealing q =
        Protocol.fresh_anchor S.E S.hc
          (Proofs.Optimistic.confStore S rho v
            (S.hc.opening_slot q)).toHealing q:= by
    simp only [ast]
    rw [actionStoreAt_eq_update_confirmation_confStore]
    exact fresh_anchor_update_confirmation_eq S.E S.hc
      (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))
      (S.hc.opening_slot q) q
  have hAconf:
      Protocol.fresh_anchor S.E S.hc
          (Proofs.Optimistic.confStore S rho v
            (S.hc.opening_slot q)).toHealing q = some A:= by
    rw [← hanchorEq]
    exact hAaction
  have hconfRound: S.hc.round_of
      (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)).s = q:= by
    simp only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      opening_confirmation_time_eq_action]
    exact round_of_slotOf_a S q
  have hconfAnchorEq: confAnchor S.E S.hc
      (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)) = A:= by
    simp only [confAnchor, hconfRound, Protocol.get_sg_root, hAconf]
  have hAD: Block.Preceq A D:= by
    rw [← hconfAnchorEq]
    exact confAnchor_preceq_of_genuineConfirmation S.E S.hc
      (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))
      (S.hc.opening_slot q) D hD
  change Block.Preceq
    (Protocol.get_sg_vote S.E S.hc ast.toHealing q
      (Protocol.grade2_block S.E S.hc ast.toHealing q)) D
  rw [Protocol.get_sg_vote.eq_def]
  cases hwalk: Protocol.deepest_clear
      (some (Protocol.get_sg_root S.E S.hc ast.toHealing q))
      ast.toHealing.live_confirmed
      (fun X => Protocol.g0_clear S.E ast.toHealing.gradeView S.hc q X) with
  | some X =>
      have hXD: Block.Preceq X D:= by
        have hXlive: Block.Preceq X ast.toHealing.live_confirmed:=
          Proofs.Engine.deepest_clear_preceq hwalk
        change Block.Preceq X (actionStoreAt S rho v q).live_confirmed at hXlive
        rw [actionStoreAt_eq_update_confirmation_confStore, hD.selected] at hXlive
        exact hXlive
      exact hXD
  | none =>
      rw [hQ₂]
      exact Block.preceq_trans
        (grade2_preceq_fresh_anchor S.E hQ₂ hAaction) hAD
-/

/-- Every proposal-chain observation at event `i` lies between two consecutive
moving endpoints. -/
def ProposalChainObservationsSandwichedAtIndex
    (S : Setup V) (rho : Run V) (i : Nat)
    (before after : Block V) : Prop :=
  ∀ stage B, ProposalChainStage stage →
    HonestCanonicalObservationAtIndex S rho i stage B →
      Block.Preceq before B ∧ Block.Preceq B after

/-- Vote and confirmation anchors read at one exact tick are compatible with
the endpoint selected after that event. Direction from an SG provenance
witness is kept separate until the provenance record is constructed. -/
structure ReadAnchorsAtIndex
    (S : Setup V) (rho : Run V) (i : Nat) (B : Block V) : Prop where
  voteCompatible : ∀ {v : V} {s : Slot},
    v ∈ rho.honest →
      rho.events[i]? = some (Event.tick v (Protocol.vote_time S.E s)) →
      Block.compatible
        (Proofs.Optimistic.healAnchor S.E S.hc
          (Proofs.Optimistic.voteDutyStore S rho v s).toHealing) B = true
  confirmationCompatible : ∀ {v : V} {s : Slot},
    v ∈ rho.honest →
      rho.events[i]? = some
        (Event.tick v (Protocol.confirmation_time S.E s)) →
      Block.compatible
        (confAnchor S.E S.hc (Proofs.Optimistic.confStore S rho v s)) B = true

/-- Named vote and confirmation anchors read at one exact tick are compatible
with the endpoint selected after that event. -/
structure NamedReadAnchorsAtIndex
    (S : Setup V) (rho : Run V) (i : Nat) (B : Block V) : Prop where
  voteCompatible : ∀ {v : V} {s : Slot},
    v ∈ rho.honest →
      rho.events[i]? = some (Event.tick v (Protocol.vote_time S.E s)) →
      Block.compatible (voterAnchorAt S rho v s) B = true
  confirmationCompatible : ∀ {v : V} {s : Slot},
    v ∈ rho.honest →
      rho.events[i]? = some
        (Event.tick v (Protocol.confirmation_time S.E s)) →
      Block.compatible (confirmationAnchorAt S rho v s) B = true


/-- Additive named moving-frontier state.
This is the compatibility state with the erased `oldRows` callback and unused erased
`baseHeight` field removed. The named row callback, the `M0` frontier floor,
the boundary-target threshold, and every event-local field stay in the shared
record shape. The named fold can carry the same event history without an
erased-height bridge. -/
structure MovingFrontierChainStateN
    (S : Setup V) (rho : Run V) (t1 : Time) (M0 : Height)
    (n0 i : Nat) (End : Nat → Block V) : Prop where
  historyStart : n0 = strictEventIndex rho t1
  start_le : n0 ≤ i
  endpointRun : ∀ j, n0 ≤ j → j ≤ i →
    ∃ E : NamedBlock V, E.erase = End j ∧ RunBlock S rho E
  endpointMono : ∀ j, n0 ≤ j → j < i →
    Block.Preceq (End j) (End (j + 1))
  proposalChain : ∀ j, n0 ≤ j → j < i →
    ProposalChainObservationsSandwichedAtIndex
      S rho j (End j) (End (j + 1))
  genuineConfirmations : ∀ j, n0 ≤ j → j < i →
    NamedGenuineConfirmationsPreceqAtIndex S rho j (End (j + 1))
  sgCarriers : ∀ j, n0 ≤ j → j < i →
    HonestActionSGCarriersPreceqAtIndex S rho j (End (j + 1))
  outputs : ∀ j, n0 ≤ j → j < i →
    HonestAttestationOutputPreceqAtIndex S rho j (End (j + 1))
  anchors : ∀ j, n0 ≤ j → j < i →
    NamedReadAnchorsAtIndex S rho j (End (j + 1))
  oldRows_named : ∀ {j : Nat} {a : NamedAttestation V} {time : Time},
    a.val_index ∈ rho.honest →
    rho.events[j]? = some (Event.tick a.val_index time) →
    Object.attest a ∈
      NamedRun.emittedAt S rho j a.val_index time →
    j < n0 → ∀ hh : Height, a.height_pair.erase.height? = some hh →
    ∀ E : NamedBlock V, E.erase = End n0 → RunBlock S rho E →
    hh ≤ (Protocol.derive_named S.E S.cfg E).h
  frontierFloor : ∀ v ∈ rho.honest, ∀ k : Nat, n0 ≤ k →
    M0 ≤ (rho.stateBefore S k v).st.h_max
  boundaryTargets : ∀ (a : NamedAttestation V) (ta : Time),
    a.val_index ∈ rho.honest →
    rho.emits S a.val_index (Object.attest a) ta →
    ta < t1 →
    ∀ (hh : Height) (target : BlockId), M0 - 1 ≤ hh →
    a.height_pair = NamedHeightPair.vote hh target false →
    ∀ X : NamedBlock V, RunBlock S rho X → X.erase.root = target →
    Block.Preceq X.erase (End n0)






/-- The initial named endpoint is below every checked named endpoint. -/
theorem MovingFrontierChainStateN.initialHeight_le_endpointHeight_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {E0 Ei : NamedBlock V}
    (hE0 : E0.erase = End n0) (hEi : Ei.erase = End i)
    (hE0run : RunBlock S rho E0) (hEirun : RunBlock S rho Ei) :
    (Protocol.derive_named S.E S.cfg E0).h ≤
      (Protocol.derive_named S.E S.cfg Ei).h := by
  have hmono : ∀ {j k : Nat}, n0 ≤ j → j ≤ k → k ≤ i →
      Block.Preceq (End j) (End k) := by
    intro j k hj hjk hki
    induction hjk with
    | refl => exact Block.preceq_self _
    | @step k hjk ih =>
        exact Block.preceq_trans (ih (Nat.le_trans (Nat.le_succ k) hki))
          (h.endpointMono k (hj.trans hjk) (Nat.lt_of_succ_le hki))
  have hgeom : Block.Preceq E0.erase Ei.erase := by
    simpa only [hE0, hEi] using hmono (j := n0) (k := i)
      (Nat.le_refl n0) h.start_le (Nat.le_refl i)
  have hnamed : NamedBlock.Preceq E0 Ei :=
    Protocol.namedPreceq_of_runBlock_erase_preceq adm hE0run hEirun hgeom
  exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hnamed



/-- An earlier honest row is no higher than the current named endpoint. -/
theorem MovingFrontierChainStateN.oldRow_le_endpointHeight_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {j : Nat} {a : NamedAttestation V} {time : Time}
    (ha : a.val_index ∈ rho.honest)
    (hevent : rho.events[j]? = some (Event.tick a.val_index time))
    (hemit : Object.attest a ∈
      NamedRun.emittedAt S rho j a.val_index time)
    (hj : j < n0) {hh : Height}
    (hrow : a.height_pair.erase.height? = some hh)
    {E : NamedBlock V} (hE : E.erase = End i) (hErun : RunBlock S rho E) :
    hh ≤ (Protocol.derive_named S.E S.cfg E).h := by
  obtain ⟨E0, hE0, hE0run⟩ :=
    h.endpointRun n0 (Nat.le_refl n0) h.start_le
  exact (h.oldRows_named ha hevent hemit hj hh hrow E0 hE0 hE0run).trans
    (h.initialHeight_le_endpointHeight_named S adm hE0 hE hE0run hErun)







private theorem movingFrontierChainStateN_endpoint_mono
    {S : Setup V} {rho : Run V} {t1 : Time} {M0 : Height}
    {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {j k : Nat} (hj : n0 ≤ j) (hjk : j ≤ k) (hki : k ≤ i) :
    Block.Preceq (End j) (End k) := by
  induction hjk with
  | refl => exact Block.preceq_self _
  | @step k hjk ih =>
      exact Block.preceq_trans (ih (Nat.le_trans (Nat.le_succ k) hki))
        (h.endpointMono k (hj.trans hjk) (Nat.lt_of_succ_le hki))

omit [DecidableEq V] [Fintype V] in
private theorem movingFrontierChainStateN_named_height_of_matches_endpoint
    {a : NamedAttestation V} {h : Height} {root : BlockId}
    (hmatch : a.height_pair.matchesEntry h root = true) :
    a.height_pair.erase.height? = some h := by
  cases hp : a.height_pair with
  | empty =>
      simp [hp, NamedHeightPair.matchesEntry] at hmatch
  | vote height entry timeout =>
      simp only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] at hmatch
      cases timeout <;>
        simp [NamedHeightPair.erase, HeightPair.height?, hmatch.1]

omit [Fintype V] in
private theorem movingFrontierChainStateN_named_preceq_cases_endpoint
    {A B : NamedBlock V} (h : NamedBlock.Preceq A B) :
    A = B ∨ NamedBlock.Preceq A B.parent := by
  cases B with
  | genesis =>
      left
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using h
  | node parent slot root votes support rows proposer =>
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, NamedBlock.parent,
        Bool.or_eq_true, decide_eq_true_eq] using h

omit [Fintype V] in
private theorem movingFrontierChainStateN_named_chain_attestations_own_endpoint
    {A : NamedBlock V} {a : NamedAttestation V}
    (ha : a ∈ A.attestations) :
    a ∈ Protocol.named_chain_attestations A := by
  cases A with
  | genesis => simp [NamedBlock.attestations] at ha
  | node p s r gv gsv rows proposer =>
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr ha)

omit [Fintype V] in
private theorem movingFrontierChainStateN_named_chain_attestations_mono_endpoint
    {A B : NamedBlock V} (hAB : NamedBlock.Preceq A B) :
    Protocol.named_chain_attestations A ⊆
      Protocol.named_chain_attestations B := by
  induction B with
  | genesis =>
      have hA : A = .genesis := by
        simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using hAB
      subst hA
      exact Finset.Subset.refl _
  | node p s r gv sup rows pr ih =>
      rcases movingFrontierChainStateN_named_preceq_cases_endpoint hAB with rfl | hAp
      · exact Finset.Subset.refl _
      · exact (ih hAp).trans Finset.subset_union_left

omit [Fintype V] in
private theorem movingFrontierChainStateN_named_chain_attestations_of_carrier_endpoint
    {carrier D : NamedBlock V} {a : NamedAttestation V}
    (hcarrier : NamedBlock.Preceq carrier D)
    (ha : a ∈ carrier.attestations) :
    a ∈ Protocol.named_chain_attestations D :=
  movingFrontierChainStateN_named_chain_attestations_mono_endpoint hcarrier
    (movingFrontierChainStateN_named_chain_attestations_own_endpoint ha)

/-- The named moving honest frontier is at most one height above the endpoint. -/
theorem MovingFrontierChainStateN.honestHMaxBeforeIndex_le_endpoint_succ_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {E : NamedBlock V} (hE : E.erase = End i) (hErun : RunBlock S rho E) :
    honestHMaxBeforeIndex S rho i ≤
      (Protocol.derive_named S.E S.cfg E).h + 1 := by
  unfold honestHMaxBeforeIndex
  apply Finset.sup_le
  intro v hv
  by_contra hnot
  have hhigh : (Protocol.derive_named S.E S.cfg E).h + 1 <
      (rho.stateBefore S i v).st.h_max := Nat.lt_of_not_ge hnot
  obtain ⟨W, hW, hmaxW⟩ :=
    NamedMaximumCarrier.maximum_carrier_stateBefore S rho i v
  have hcross : (Protocol.derive_named S.E S.cfg E).h + 1 <
      (Protocol.derive_named S.E S.cfg W).h := by
    rw [hmaxW]
    exact hhigh
  obtain ⟨_X, _hX, _hXheight, Q, hQ, hwitness⟩ :=
    NamedFinalityCertificates.height_crossing S.E S.cfg W
      ((Protocol.derive_named S.E S.cfg E).h + 1)
      (Nat.succ_le_succ (Nat.zero_le _)) hcross
  obtain ⟨signer, hsignerQ, hsignerHonest⟩ :=
    HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
  obtain ⟨carrier, a, hcarrier, ha, haSigner, hmatch⟩ :=
    hwitness signer hsignerQ
  have haHonest : a.val_index ∈ rho.honest := by
    rw [haSigner]
    exact hsignerHonest
  have haChain : a ∈ Protocol.named_chain_attestations W :=
    movingFrontierChainStateN_named_chain_attestations_of_carrier_endpoint
      hcarrier ha
  have haHeight : a.height_pair.erase.height? = some
      ((Protocol.derive_named S.E S.cfg E).h + 1) :=
    movingFrontierChainStateN_named_height_of_matches_endpoint hmatch
  obtain ⟨j, _ta, hji, hjevent, hja, _hemit⟩ :=
    honestCarriedAttestation_emittedBeforeIndex S adm hW haChain haHonest
  by_cases hj0 : j < n0
  · exact (Nat.not_succ_le_self _)
      (h.oldRow_le_endpointHeight_named S adm haHonest hjevent hja hj0
        haHeight hE hErun)
  · have hn0j : n0 ≤ j := Nat.le_of_not_gt hj0
    obtain ⟨G, hGrun, hGheight, hGnext⟩ :=
      (h.outputs j hn0j hji).height_gate_sources
        haHonest hjevent hja
          ((Protocol.derive_named S.E S.cfg E).h + 1) haHeight
    obtain ⟨Enext, hEnext, hEnextrun⟩ :=
      h.endpointRun (j + 1) (hn0j.trans (Nat.le_succ j))
        (Nat.succ_le_iff.mpr hji)
    have hGnextNamed : NamedBlock.Preceq G Enext :=
      Protocol.namedPreceq_of_runBlock_erase_preceq adm hGrun hEnextrun (by
        simpa only [hEnext] using hGnext)
    have hnextEnd : Block.Preceq (End (j + 1)) (End i) :=
      movingFrontierChainStateN_endpoint_mono h
        (hn0j.trans (Nat.le_succ j))
        (Nat.succ_le_iff.mpr hji) (Nat.le_refl i)
    have hEnextE : NamedBlock.Preceq Enext E :=
      Protocol.namedPreceq_of_runBlock_erase_preceq adm hEnextrun hErun (by
        simpa only [hEnext, hE] using hnextEnd)
    have hrowEnd : (Protocol.derive_named S.E S.cfg E).h + 1 ≤
        (Protocol.derive_named S.E S.cfg E).h := by
      calc
        (Protocol.derive_named S.E S.cfg E).h + 1 =
            (Protocol.derive_named S.E S.cfg G).h := hGheight.symm
        _ ≤ (Protocol.derive_named S.E S.cfg Enext).h :=
          Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hGnextNamed
        _ ≤ (Protocol.derive_named S.E S.cfg E).h :=
          Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hEnextE
    exact (Nat.not_succ_le_self _) hrowEnd

/-- The named moving honest frontier floor at the endpoint. -/
theorem MovingFrontierChainStateN.frontier_sub_one_le_endpointHeight_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {E : NamedBlock V} (hE : E.erase = End i) (hErun : RunBlock S rho E) :
    honestHMaxBeforeIndex S rho i - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h := by
  exact Nat.sub_le_iff_le_add.mpr
    (h.honestHMaxBeforeIndex_le_endpoint_succ_named
      S adm hmajority hE hErun)

/-- A tick inside the strict prefix occurs before its cutoff. -/
theorem eventTime_lt_of_index_lt_strictEventIndex
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {j : Nat} {v : V} {time t1 : Time}
    (hj : rho.events[j]? = some (Event.tick v time))
    (hlt : j < strictEventIndex rho t1) : time < t1 := by
  by_contra hnot
  have hle : strictEventIndex rho t1 ≤ j :=
    filterBefore_length_le_tickIndex S sch hj (le_of_not_gt hnot)
  exact absurd hlt (Nat.not_lt.mpr hle)







/-
/-- Advance the endpoint at one honest action event.

The next endpoint is the deeper of the previous endpoint and the action's
genuine confirmation. Same-chain compatibility makes this choice total. A
common grade directs the SG carrier and every emitted attestation field to the
same confirmation. Numeric frontier changes are not inspected. -/
theorem MovingFrontierChainState.succ_action
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {q: Round} {B D: Block V} (hforms: GradeFormsAt S rho q B)
    {v: V} {a: CombinedAttestation V} (hv: v ∈ rho.honest)
    (hi: rho.events[i]? = some (Event.tick v (S.a q)))
    (ha: Object.attest a ∈
      (on_tick_emit S (S.node v) (rho.stateBefore S i v).st
        (rho.stateBefore S i v).Λ (S.a q)).2.2)
    (hD: GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc
      (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))
      (S.hc.opening_slot q) D)
    (hcompat: Block.compatible (End i) D = true):
    ∃ End': Nat → Block V,
      (∀ j, j ≤ i → End' j = End j) ∧
      Block.Preceq (End i) (End' (i + 1)) ∧
      MovingFrontierChainState S rho t1 M0 n0 (i + 1) End':= by
  have hdir:= directedHonestActionAtIndex_of_gradeFormsAt_genuine
    S adm hforms hv hi ha hD hcompat
  obtain ⟨_hDorigin, _hcompat, hDrun, _hemits, houtD⟩:= hdir
  have horient: Block.Preceq (End i) D ∨ Block.Preceq D (End i):= by
    simpa only [Block.compatible, Bool.or_eq_true] using hcompat
  let Next: Block V:= if Block.Preceq (End i) D then D else End i
  let End': Nat → Block V:= fun j => if j = i + 1 then Next else End j
  have hEndNext: Block.Preceq (End i) Next:= by
    by_cases hED: Block.Preceq (End i) D
    · simp only [Next, if_pos hED]
      exact hED
    · simp only [Next, if_neg hED]
      exact Block.preceq_self _
  have hDNext: Block.Preceq D Next:= by
    by_cases hED: Block.Preceq (End i) D
    · simp only [Next, if_pos hED]
      exact Block.preceq_self _
    · rcases horient with hED' | hDE
      · exact False.elim (hED hED')
      · simpa only [Next, if_neg hED] using hDE
  have hNextRun: RunBlock S rho Next:= by
    by_cases hED: Block.Preceq (End i) D
    · simpa only [Next, if_pos hED] using hDrun
    · simpa only [Next, if_neg hED] using
        h.endpointRun i h.start_le (Nat.le_refl i)
  have hcarrierNext: Block.Preceq (actionSGBlockAt S rho v q) Next:=
    Block.preceq_trans
      (actionSGBlockAt_preceq_genuine_of_gradeFormsAt S hforms hv hD)
      hDNext
  have houtNext: HonestAttestationOutputPreceqAtIndex S rho i Next:=
    houtD.mono hDNext
  have hsgNext: HonestActionSGCarriersPreceqAtIndex S rho i Next:= by
    intro w r att hw hwi hatt
    have heq:= Option.some.inj (hwi.symm.trans hi)
    obtain ⟨rfl, htime⟩:= Event.tick.inj heq
    have hr: r = q:= (actionTime_strictMono S).injective htime
    subst r
    exact hcarrierNext
  have hanchorsNext: ReadAnchorsAtIndex S rho i Next:= by
    refine { voteCompatible:= ?_, confirmationCompatible:= ?_ }
    · intro w s hw hwi
      have heq:= Option.some.inj (hwi.symm.trans hi)
      obtain ⟨rfl, htime⟩:= Event.tick.inj heq
      have hslot: s = S.E.slotOf (S.a q):= by
        simpa only [Proofs.Optimistic.slotOf_vote_time] using
          congrArg S.E.slotOf htime
      exact False.elim
        ((Proofs.Optimistic.a_ne_vote_time S (rfl: S.a q = S.a q)) (by
          rw [← hslot]
          exact htime.symm))
    · intro w s hw hwi
      have heq:= Option.some.inj (hwi.symm.trans hi)
      obtain ⟨rfl, htime⟩:= Event.tick.inj heq
      have hs: s = S.hc.opening_slot q:= by
        have htime': Protocol.confirmation_time S.E s =
            Protocol.confirmation_time S.E (S.hc.opening_slot q):=
          htime.trans (Protocol.a_eq_confirmation_time S.hc S.E q)
        have hslot:= congrArg S.E.slotOf htime'
        simp only [Proofs.Optimistic.slotOf_confirmation_time] at hslot
        exact Nat.add_right_cancel hslot
      subst s
      have hanchorD: Block.Preceq
          (confAnchor S.E S.hc
            (Proofs.Optimistic.confStore S rho w (S.hc.opening_slot q))) D:=
        confAnchor_preceq_of_genuineConfirmation S.E S.hc
          (Proofs.Optimistic.confStore S rho w (S.hc.opening_slot q))
          (S.hc.opening_slot q) D hD
      exact Block.compatible_of_preceq_common
        (Block.preceq_trans hanchorD hDNext) (Block.preceq_self Next)
  refine ⟨End', ?_, ?_, ?_⟩
  · intro j hji
    have hjne: j ≠ i + 1:= by omega
    simp only [End', if_neg hjne]
  · simp only [End', if_pos rfl]
    exact hEndNext
  · refine
      { historyStart:= h.historyStart
        start_le:= h.start_le.trans (Nat.le_succ i)
        endpointRun:= ?_
        endpointMono:= ?_
        proposalChain:= ?_
        genuineConfirmations:= ?_
        sgCarriers:= ?_
        outputs:= ?_
        anchors:= ?_
        oldRows:= by
          have hn0ne: n0 ≠ i + 1:= Nat.ne_of_lt (h.start_le.trans_lt (Nat.lt_succ_self i))
          intro j a time ha hevent hemit hj hh hrow
          simpa only [End', if_neg hn0ne] using h.oldRows ha hevent hemit hj hh hrow
        baseHeight:= ?_
        frontierFloor:= h.frontierFloor
        boundaryTargets:= by
          have hn0ne: n0 ≠ i + 1:= by
            have hn0le: n0 ≤ i:= h.start_le
            omega
          simpa only [End', if_neg hn0ne] using h.boundaryTargets }
    · intro j hj hjupper
      by_cases hji: j = i + 1
      · subst j
        simpa only [End', if_pos rfl] using hNextRun
      · have hjold: j ≤ i:= by omega
        simpa only [End', if_neg hji] using h.endpointRun j hj hjold
    · intro j hj hjupper
      by_cases hji: j = i
      · subst j
        have hine: i ≠ i + 1:= by omega
        simp only [End', if_neg hine, if_pos rfl]
        exact hEndNext
      · have hjold: j < i:= by omega
        have hjne: j ≠ i + 1:= by omega
        have hjsne: j + 1 ≠ i + 1:= by omega
        simpa only [End', if_neg hjne, if_neg hjsne] using
          h.endpointMono j hj hjold
    · intro j hj hjupper
      by_cases hji: j = i
      · subst j
        have hine: i ≠ i + 1:= by omega
        simpa only [End', if_neg hine, if_pos rfl] using
          proposalChainObservationsSandwichedAtIndex_of_actionEvent
            S hi (End i) Next
      · have hjold: j < i:= by omega
        have hjne: j ≠ i + 1:= by omega
        have hjsne: j + 1 ≠ i + 1:= by omega
        simpa only [End', if_neg hjne, if_neg hjsne] using
          h.proposalChain j hj hjold
    · intro j hj hjupper
      by_cases hji: j = i
      · subst j
        simp only [End', if_pos rfl]
        intro w hw C hC
        rcases hC with ⟨s, hCi, hCgenuine⟩
        have heq:= Option.some.inj (hCi.symm.trans hi)
        obtain ⟨rfl, htime⟩:= Event.tick.inj heq
        have hs: s = S.hc.opening_slot q:= by
          have htime': Protocol.confirmation_time S.E s =
              Protocol.confirmation_time S.E (S.hc.opening_slot q):=
            htime.trans (Protocol.a_eq_confirmation_time S.hc S.E q)
          have hslot:= congrArg S.E.slotOf htime'
          simp only [Proofs.Optimistic.slotOf_confirmation_time] at hslot
          exact Nat.add_right_cancel hslot
        subst s
        have hCD: C = D:= hCgenuine.selected.symm.trans hD.selected
        simpa only [hCD] using hDNext
      · have hjold: j < i:= by omega
        have hjsne: j + 1 ≠ i + 1:= by omega
        simpa only [End', if_neg hjsne] using
          h.genuineConfirmations j hj hjold
    · intro j hj hjupper
      by_cases hji: j = i
      · subst j
        simpa only [End', if_pos rfl] using hsgNext
      · have hjold: j < i:= by omega
        have hjsne: j + 1 ≠ i + 1:= by omega
        simpa only [End', if_neg hjsne] using h.sgCarriers j hj hjold
    · intro j hj hjupper
      by_cases hji: j = i
      · subst j
        simpa only [End', if_pos rfl] using houtNext
      · have hjold: j < i:= by omega
        have hjsne: j + 1 ≠ i + 1:= by omega
        simpa only [End', if_neg hjsne] using h.outputs j hj hjold
    · intro j hj hjupper
      by_cases hji: j = i
      · subst j
        simpa only [End', if_pos rfl] using hanchorsNext
      · have hjold: j < i:= by omega
        have hjsne: j + 1 ≠ i + 1:= by omega
        simpa only [End', if_neg hjsne] using h.anchors j hj hjold
    · have hn0le: n0 ≤ i:= h.start_le
      have hn0ne: n0 ≠ i + 1:= by omega
      simpa only [End', if_neg hn0ne] using h.baseHeight
-/




/-
/-- The directed suffix history derives the moving one-unit frontier debt.

This proof is regime-free. A crossing quorum above the endpoint contains an
honest height row. A row before `n0` is bounded by `oldRows`; a later row
has a concrete source below the event endpoint, which is below `End i` by
endpoint monotonicity. -/
theorem MovingFrontierChainState.honestHMaxBeforeIndex_le_endpoint_succ
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End):
    honestHMaxBeforeIndex S rho i ≤
      (derived_state S.E S.cfg (End i)).h + 1:= by
  unfold honestHMaxBeforeIndex
  apply Finset.sup_le
  intro v hv
  by_contra hnot
  have hhigh: (derived_state S.E S.cfg (End i)).h + 1 <
      (rho.stateBefore S i v).st.h_max:= Nat.lt_of_not_ge hnot
  let st:= (rho.stateBefore S i v).st
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v) st:= by
    simpa only [st] using
      (Proofs.Bridges.depReachable_of_admissible S adm.toDeliveryWellFormed v i)
  have hagree: DerivedStateAgrees S.E S.cfg st:=
    derivedStateAgrees_depReachable S.E S.hc S.cfg (S.node v) st hdep
  obtain ⟨W, hWT, hmaxW⟩:=
    hMaxInTree_depReachable S.E S.hc S.cfg (S.node v) hdep
  have hcross: (derived_state S.E S.cfg (End i)).h + 1 <
      (derived_state S.E S.cfg W).h:= by
    rw [← hagree W hWT]
    exact hhigh.trans_le hmaxW
  obtain ⟨Q, _X, hQ, _hXW, hwitness⟩:=
    Protocol.height_crossing S.E S.cfg
      ((derived_state S.E S.cfg (End i)).h + 1)
      (Nat.succ_le_succ (Nat.zero_le _)) W hcross
  obtain ⟨signer, hsignerQ, hsignerHonest⟩:=
    HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
  obtain ⟨a, haW, haSigner, haPair⟩:= hwitness signer hsignerQ
  have haHonest: a.val_index ∈ rho.honest:= by
    rw [haSigner]
    exact hsignerHonest
  have haHeight: a.height_pair.height? =
      some ((derived_state S.E S.cfg (End i)).h + 1):= by
    rcases haPair with htarget | htimeout
    · rw [htarget]
      rfl
    · rw [htimeout]
      rfl
  obtain ⟨j, _ta, hji, hjevent, hja, _hemit⟩:=
    honestCarriedAttestation_emittedBeforeIndex
      S adm (by simpa only [st] using hWT) haW haHonest
  by_cases hj0: j < n0
  · exact (Nat.not_succ_le_self _)
      (h.oldRow_le_endpointHeight S haHonest hjevent hja hj0 haHeight)
  · have hn0j: n0 ≤ j:= Nat.le_of_not_gt hj0
    obtain ⟨G, _hGrun, hGheight, hGnext⟩:=
      (h.outputs j hn0j hji).height_gate_sources
        haHonest hjevent hja
          ((derived_state S.E S.cfg (End i)).h + 1) haHeight
    have hjSucc: j + 1 ≤ i:= hji
    have hnextEnd: Block.Preceq (End (j + 1)) (End i):=
      h.endpoint_mono (hn0j.trans (Nat.le_succ j)) hjSucc (Nat.le_refl i)
    have hrowEnd: (derived_state S.E S.cfg (End i)).h + 1 ≤
        (derived_state S.E S.cfg (End i)).h:= by
      calc
        (derived_state S.E S.cfg (End i)).h + 1 =
            (derived_state S.E S.cfg G).h:= hGheight.symm
        _ ≤ (derived_state S.E S.cfg (End (j + 1))).h:=
          Protocol.derived_h_mono S.E S.cfg hGnext
        _ ≤ (derived_state S.E S.cfg (End i)).h:=
          Protocol.derived_h_mono S.E S.cfg hnextEnd
    exact (Nat.not_succ_le_self _) hrowEnd

/-- Event-index form of the directed `h_max - 1` floor. -/
theorem MovingFrontierChainState.frontier_sub_one_le_endpointHeight
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End):
    honestHMaxBeforeIndex S rho i - 1 ≤
      (derived_state S.E S.cfg (End i)).h:= by
  exact Nat.sub_le_iff_le_add.mpr
    (h.honestHMaxBeforeIndex_le_endpoint_succ S adm hmajority)
-/


/-
/-- In the root-below regime, a processed moving endpoint is active at the
exact event-prefix store. The directed floor makes the endpoint its own
viability witness. -/
theorem MovingFrontierChainState.endpoint_mem_filtered_atIndex
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {v: V} (hv: v ∈ rho.honest)
    (hmem: End i ∈ (rho.stateBefore S i v).st.T)
    (hroot: Block.Preceq
      (Protocol.get_fg_root
        (rho.stateBefore S i v).st.toHealing.toFG) (End i)):
    End i ∈ Protocol.get_filtered_block_tree
      (rho.stateBefore S i v).st.toHealing.toFG:= by
  let st:= (rho.stateBefore S i v).st.core
  obtain ⟨E, hEbody, hEerase⟩:=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho i v hmem
  have hErun: RunBlock S rho E:=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hv hEbody
  have hHmax:= honestHMaxBeforeIndex_le_endpoint_named
    S adm hmajority h hEerase hErun
  have hlocal: st.h_max ≤ honestHMaxBeforeIndex S rho i:= by
    simpa only [st] using localHMax_le_honestHMaxBeforeIndex S rho i hv
  have hfloorNamed: st.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h:=
    (Nat.sub_le_sub_right hlocal 1).trans
      (Nat.sub_le_iff_le_add.mpr hHmax)
  have hderive: st.σ (End i) =
      Protocol.derive_named S.E S.cfg E:= by
    simpa only [st, hEerase] using
      Proofs.NamedStoreBridge.derivedView_stateBefore S rho i v E hEbody
  have hfloor: st.h_max - 1 ≤ (st.σ (End i)).h:= by
    rw [hderive]
    exact hfloorNamed
  have hFJ: Block.Preceq st.F st.J:= by
    simpa only [st] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBefore S rho i v
  have hFEnd: Block.Preceq st.F (End i):=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st:= st.toHealing.toFG) hFJ)
      (by simpa only [st] using hroot)
  have hV: End i ∈ Protocol.V_tree st.toHealing.toFG:= by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
    exact ⟨⟨by simpa only [st] using hmem, hFEnd⟩,
      End i, by simpa only [st] using hmem, Block.preceq_self _, hfloor⟩
  exact Proofs.Records.mem_filtered_of_mem_V_tree hV (by simpa only [st] using hroot)

/-- Every block on the selected-root-to-endpoint path is active at the exact
event-prefix store.

The endpoint supplies the viability witness for the whole path. Its directed
height floor is the only numeric fact used here. -/
theorem MovingFrontierChainState.endpointPath_mem_filtered_atIndex
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {v: V} (hv: v ∈ rho.honest)
    (hmem: End i ∈ (rho.stateBefore S i v).st.T)
    {D: Block V}
    (hroot: Block.Preceq
      (Protocol.get_fg_root
        (rho.stateBefore S i v).st.toHealing.toFG) D)
    (hDEnd: Block.Preceq D (End i)):
    D ∈ Protocol.get_filtered_block_tree
      (rho.stateBefore S i v).st.toHealing.toFG:= by
  let st:= (rho.stateBefore S i v).st.core
  have hpc: ParentClosed st:= by
    simpa only [st] using
      Proofs.NamedStoreBridge.parentClosed_stateBefore S rho i v
  have hDmem: D ∈ st.T:= by
    apply Proofs.Records.mem_of_preceq ((parentClosed_iff st).mp hpc).2 D (End i)
    · simpa only [st] using hmem
    · exact hDEnd
  obtain ⟨E, hEbody, hEerase⟩:=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho i v hmem
  have hErun: RunBlock S rho E:=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hv hEbody
  have hHmax:= honestHMaxBeforeIndex_le_endpoint_named
    S adm hmajority h hEerase hErun
  have hlocal: st.h_max ≤ honestHMaxBeforeIndex S rho i:= by
    simpa only [st] using localHMax_le_honestHMaxBeforeIndex S rho i hv
  have hfloorNamed: st.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h:=
    (Nat.sub_le_sub_right hlocal 1).trans
      (Nat.sub_le_iff_le_add.mpr hHmax)
  have hderive: st.σ (End i) =
      Protocol.derive_named S.E S.cfg E:= by
    simpa only [st, hEerase] using
      Proofs.NamedStoreBridge.derivedView_stateBefore S rho i v E hEbody
  have hfloor: st.h_max - 1 ≤ (st.σ (End i)).h:= by
    rw [hderive]
    exact hfloorNamed
  have hFJ: Block.Preceq st.F st.J:= by
    simpa only [st] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBefore S rho i v
  have hFD: Block.Preceq st.F D:=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st:= st.toHealing.toFG) hFJ)
      (by simpa only [st] using hroot)
  have hV: D ∈ Protocol.V_tree st.toHealing.toFG:= by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
    exact ⟨⟨hDmem, hFD⟩,
      End i, by simpa only [st] using hmem, hDEnd, hfloor⟩
  exact Proofs.Records.mem_filtered_of_mem_V_tree hV (by simpa only [st] using hroot)

/-- Exact-prefix root-side data, including the complete active path to the
moving endpoint. This is the full-store part of a primed Goldfish input; a
vote-duty caller must additionally prove frozen processed-tree admission. -/
theorem MovingFrontierChainState.endpoint_rootSideWithPath_atIndex
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {v: V} (hv: v ∈ rho.honest)
    (hmem: End i ∈ (rho.stateBefore S i v).st.T)
    (hcompat: Block.compatible
      (Protocol.get_fg_root
        (rho.stateBefore S i v).st.toHealing.toFG) (End i) = true):
    (Block.Preceq
        (Protocol.get_fg_root
          (rho.stateBefore S i v).st.toHealing.toFG) (End i) ∧
      End i ∈ Protocol.get_filtered_block_tree
        (rho.stateBefore S i v).st.toHealing.toFG ∧
      ∀ D: Block V,
        Block.Preceq
          (Protocol.get_fg_root
            (rho.stateBefore S i v).st.toHealing.toFG) D →
        Block.Preceq D (End i) →
        D ∈ Protocol.get_filtered_block_tree
          (rho.stateBefore S i v).st.toHealing.toFG) ∨
    Block.Preceq (End i)
      (Protocol.get_fg_root
        (rho.stateBefore S i v).st.toHealing.toFG):= by
  simp only [Block.compatible, Bool.or_eq_true] at hcompat
  rcases hcompat with hroot | hend
  · exact Or.inl ⟨hroot,
      h.endpoint_mem_filtered_atIndex S adm hmajority hv hmem hroot,
      fun D hrootD hDEnd =>
        h.endpointPath_mem_filtered_atIndex
          S adm hmajority hv hmem hrootD hDEnd⟩
  · exact Or.inr hend

/-- The two local FG-root orientations required by the primed Goldfish input.
The root-below arm includes endpoint activity; the root-above arm needs no
candidate fact. -/
theorem MovingFrontierChainState.endpoint_rootSide_atIndex
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {v: V} (hv: v ∈ rho.honest)
    (hmem: End i ∈ (rho.stateBefore S i v).st.T)
    (hcompat: Block.compatible
      (Protocol.get_fg_root
        (rho.stateBefore S i v).st.toHealing.toFG) (End i) = true):
    (Block.Preceq
        (Protocol.get_fg_root
          (rho.stateBefore S i v).st.toHealing.toFG) (End i) ∧
      End i ∈ Protocol.get_filtered_block_tree
        (rho.stateBefore S i v).st.toHealing.toFG) ∨
    Block.Preceq (End i)
      (Protocol.get_fg_root
        (rho.stateBefore S i v).st.toHealing.toFG):= by
  simp only [Block.compatible, Bool.or_eq_true] at hcompat
  rcases hcompat with hroot | hend
  · exact Or.inl ⟨hroot,
      h.endpoint_mem_filtered_atIndex S adm hmajority hv hmem hroot⟩
  · exact Or.inr hend
-/





/-
/-- The permitted post-start source residual gives the directed floor at a
strict read. If the row is already below the endpoint, its bound is immediate.
Otherwise it is above the floor, and an earlier row would contradict `oldRows`.
Thus the post-start source bound applies without a two-rise premise. -/
theorem MovingFrontierChainState.frontier_sub_one_le_endpointHeight_of_postStartSources
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    (hsources: PostStartHeightGateSourcesPreceq S rho t1 M0 End)
    {t: Time} {v: V}
    (hcursor: strictEventIndex rho t ≤ i):
    (rho.storeBeforeTime S v t).h_max - 1 ≤
      (derived_state S.E S.cfg (End i)).h:= by
  by_contra hnot
  have hhighEnd: (derived_state S.E S.cfg (End i)).h <
      (rho.storeBeforeTime S v t).h_max - 1:= Nat.lt_of_not_ge hnot
  have hhigh: M0 < (rho.storeBeforeTime S v t).h_max - 1:=
    (h.oldFrontier_le_endpointHeight S).trans_lt hhighEnd
  have hlarge: 1 < (rho.storeBeforeTime S v t).h_max:=
    Nat.sub_pos_iff_lt.mp ((Nat.zero_le _).trans_lt hhighEnd)
  obtain ⟨_W, _hWT, _Q, _X, a, ta, _hmaxW, _hQ, _hXW, _haW,
      haHon, hemit, hta, haHeight⟩:=
    Protocol.frontierQuorumWitness_stateBeforeTime
      S adm hmajority hlarge
  obtain ⟨j, hjevent, hja⟩:= hemit
  have hjread: j < strictEventIndex rho t:=
    emission_index_lt_beforeTime_prefix
      S adm.toScheduleWellFormed hjevent hta
  have hji: j < i:= lt_of_lt_of_le hjread hcursor
  have ht1ta: t1 ≤ ta:= by
    by_contra hnot
    have htat1: ta < t1:= lt_of_not_ge hnot
    have hjstart: j < strictEventIndex rho t1:=
      emission_index_lt_beforeTime_prefix
        S adm.toScheduleWellFormed hjevent htat1
    have hj0: j < n0:= by simpa only [h.historyStart] using hjstart
    exact (not_le_of_gt hhighEnd)
      (h.oldRow_le_endpointHeight S haHon hjevent hja hj0 haHeight)
  have hn0j: n0 ≤ j:= by
    rw [h.historyStart]
    exact filterBefore_length_le_tickIndex
      S adm.toScheduleWellFormed hjevent ht1ta
  obtain ⟨G, _hGrun, hGheight, hGnext⟩:=
    hsources j a.val_index ta a haHon hjevent hja ht1ta
      ((rho.storeBeforeTime S v t).h_max - 1) haHeight hhigh
  have hnextEnd: Block.Preceq (End (j + 1)) (End i):=
    h.endpoint_mono (hn0j.trans (Nat.le_succ j))
      (Nat.succ_le_iff.mpr hji) (Nat.le_refl i)
  apply (not_le_of_gt hhighEnd)
  calc
    (rho.storeBeforeTime S v t).h_max - 1 =
        (derived_state S.E S.cfg G).h:= hGheight.symm
    _ ≤ (derived_state S.E S.cfg (End (j + 1))).h:=
      Protocol.derived_h_mono S.E S.cfg hGnext
    _ ≤ (derived_state S.E S.cfg (End i)).h:=
      Protocol.derived_h_mono S.E S.cfg hnextEnd
-/


#print axioms eventTime_lt_of_index_lt_strictEventIndex


/-
/-- Complete-state form of the directed floor. The source history is
derived internally, so callers do not supply `PostStartHeightGateSourcesPreceq`.
-/
theorem MovingFrontierChainState.frontier_sub_one_le_endpointHeight_of_complete
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    (hcomplete: rho.events.length ≤ i)
    {t: Time} {v: V}
    (hcursor: strictEventIndex rho t ≤ i):
    (rho.storeBeforeTime S v t).h_max - 1 ≤
      (derived_state S.E S.cfg (End i)).h:= by
  exact h.frontier_sub_one_le_endpointHeight_of_postStartSources
    S adm hmajority (h.postStartHeightGateSourcesPreceq S adm hcomplete)
      hcursor
-/

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
